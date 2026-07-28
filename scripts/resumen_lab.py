#!/usr/bin/env python3
"""
Resumen LAB - lee la casilla de Gmail por IMAP, categoriza los mails nuevos
y los guarda en una tabla de Supabase (Postgres), via su API REST/RPC.

Corre desde GitHub Actions, usando estas variables de entorno (secrets):
  GMAIL_USER, GMAIL_APP_PASSWORD, SUPABASE_URL, SUPABASE_SERVICE_ROLE_KEY

No depende de la computadora del usuario ni de que Cowork este abierto, y
ya no escribe nada en index.html: la pagina lee los datos directo de
Supabase (con la clave publica "anon"), asi que un despliegue de la pagina
solo hace falta cuando cambia el CODIGO, no cada vez que llegan mails.

IMPORTANTE sobre rendimiento: todo el fetch de IMAP se hace en LOTES (varios
UIDs en una sola consulta), no uno por uno. Un round-trip IMAP individual
puede tardar varios segundos; con 100+ mails candidatos, hacerlo uno por uno
tardaba mas de 20 minutos. Agrupando en tandas de ~100-150 UIDs por consulta,
el mismo trabajo se hace en unas pocas consultas en total.
"""

import email
import email.utils
import imaplib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from email.header import decode_header

IMAP_HOST = "imap.gmail.com"

AFECTACION_MASIVA_SENDER = "argentinaafectacionmasiva@claro.com.ar"
REPORTES_TECNICA_HINT = "reportestecnica"  # matches reportestecnica@ and reportestecnicas@
MARIA_INES_HINT = "maria ines emiliani"

# --- Especificas de "Resumen por lapso" (reglas propias, no comparten logica
# con las otras solapas aunque el nombre se parezca) ---
AFECTACION_MASIVA_CLIENTES_ADDR = "argentinaafectacionmasivaaclientes@claro.com.ar"
REMEDY_AMX_SENDER = "remedy.amx@mail.telcel.com"

# Sub-division de "Escalamientos IT" del lapso, por area exacta (remitente):
GIM_ADDR = "incidentereportado@claro.com.ar"
HDB_ADDR = "hdbilletera@claro.com.ar"
HELPDESK_ADDR = "helpdesk@claro.com.ar"

# Sub-division de "Escalamientos ING" del lapso, por destinatario ("para"):
VOC_ADDR = "voc@claro.com.ar"
SOC_ADDR = "soc@claro.com.ar"
NOC_ADDR = "noc@claro.com.ar"

IT_RECIPIENT_KEYWORDS = [
    "gestion de incidentes masivos",
    "gestión de incidentes masivos",
    "help desk billetera",
    "help desk",
]
# admite singular/plural y con/sin tilde: "Gestión de Incidente Masivo",
# "Gestion de Incidentes Masivos", etc. (el nombre para mostrar varía según
# quién firme el mail, aunque la dirección de correo es siempre la misma)
IT_RECIPIENT_RE = re.compile(r"gesti[oó]n\s+de\s+incidentes?\s+masivos?", re.IGNORECASE)

# Las 3 areas de IT (direcciones exactas, segun especifico el usuario):
#   Gestion de Incidentes -> incidentereportado@claro.com.ar
#   Help Desk             -> HelpDesk@claro.com.ar
#   Help Desk Billetera   -> HDBilletera@claro.com.ar
IT_AREA_ADDR_HINTS = [
    "incidentereportado@claro.com.ar",
    "helpdesk@claro.com.ar",
    "hdbilletera@claro.com.ar",
]
IT_RECIPIENT_ADDR_HINTS = IT_AREA_ADDR_HINTS
ING_RECIPIENT_KEYWORDS = ["soc", "voc", "noc"]

# "Operacion X": cualquier mail (de cualquier remitente) que tenga esta
# direccion en To o Cc. Nuevo/EnCurso se resuelve en el frontend segun la
# antiguedad de la cadena (umbral de 6hs, igual que la ventana en vivo del
# Resumen).
OPERACION_TECNICA_ADDR = "dl-ar-supervisionsacsci@claro.com.ar"
OPERACION_MSK_ADDR = "comunicacionescec_msk@claro.com.ar"
OPERACION_LY_ADDR = "loyaltyclaro@claro.com.ar"

CLOSURE_PATTERNS = [
    r"evento\s+solucionado",
    r"\bsolucionado\b",
    r"\bresuelto\b",
    r"\bfinalizado\b",
    r"\bnormalizado\b",
]
CLOSURE_RE = re.compile("|".join(CLOSURE_PATTERNS), re.IGNORECASE)
WBS_RE = re.compile(r"\bWBS\b", re.IGNORECASE)

MAX_BODY_CHARS = 20000  # tope defensivo, por si algun mail viene con un cuerpo gigante

# Categorias que necesitan el X-GM-THRID (para agrupar respuestas del mismo
# hilo a lo largo de corridas / detectar cuanto hace que arranco la cadena).
CATEGORIES_NEEDING_THRID = {
    "afectacionMasiva", "it", "ingenieria", "escalamientosIT", "afectacionesMasivasIT",
    "operacionTecnica", "operacionMSK", "operacionLY",
    "afectacionMasivaLapso",
    "escalamientosIT_GIM", "escalamientosIT_HDB", "escalamientosIT_HelpDesk",
    "escalamientosING_VOC", "escalamientosING_SOC", "escalamientosING_NOC",
}


def log(msg):
    print(msg, flush=True)


# ---------------------------------------------------------------------------
# Parseo de mails
# ---------------------------------------------------------------------------

def decode_mime_header(value):
    if not value:
        return ""
    parts = decode_header(value)
    out = []
    for text, enc in parts:
        if isinstance(text, bytes):
            try:
                out.append(text.decode(enc or "utf-8", errors="replace"))
            except LookupError:
                out.append(text.decode("utf-8", errors="replace"))
        else:
            out.append(text)
    return "".join(out)


def strip_html(html):
    text = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", html, flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"&nbsp;", " ", text)
    text = re.sub(r"\s+", " ", text)
    return text


def truncate_body(text):
    if len(text) > MAX_BODY_CHARS:
        return text[:MAX_BODY_CHARS] + "\n[...cortado...]"
    return text


def addr_list_text(msg, header_name):
    raw = msg.get_all(header_name, [])
    decoded = " ".join(decode_mime_header(r) for r in raw)
    return decoded


def epoch_ms_from_date_header(msg):
    date_hdr = msg.get("Date")
    if not date_hdr:
        return None
    try:
        dt = email.utils.parsedate_to_datetime(date_hdr)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return int(dt.timestamp() * 1000)
    except Exception:
        return None


def is_first_of_chain(msg):
    """True si el mail no tiene 'In-Reply-To' ni 'References' (o sea, no es
    una respuesta a nada que Gmail conozca). Se lee directo del encabezado
    del mail ya descargado — cero consultas IMAP extra."""
    return not msg.get("In-Reply-To") and not msg.get("References")


MESES_ES = {
    "enero": 1, "febrero": 2, "marzo": 3, "abril": 4, "mayo": 5, "junio": 6,
    "julio": 7, "agosto": 8, "septiembre": 9, "setiembre": 9, "octubre": 10,
    "noviembre": 11, "diciembre": 12,
}
# Matchea las lineas de cita tipo Outlook: "Enviado: lunes, 20 de julio de 2026 13:44"
QUOTED_DATE_RE = re.compile(
    r"Enviado:\s*(?:[A-Za-zñÑáéíóúÁÉÍÓÚ]+,?\s*)?(\d{1,2})\s+de\s+([A-Za-zñÑáéíóúÁÉÍÓÚ]+)\s+de\s+(\d{4})\s+(\d{1,2}):(\d{2})",
    re.IGNORECASE,
)
ARG_UTC_OFFSET_MS = 3 * 3600 * 1000  # Argentina es UTC-3, sin horario de verano


def arg_calendar_date_str(ms):
    """Fecha calendario (YYYY-MM-DD) en horario Argentina para un ms epoch
    UTC dado. Se usa para registrar en que dia calendario (Argentina) hubo
    actividad de un mail/hilo, sin importar si la cadena sigue mas adelante."""
    dt_utc = datetime.fromtimestamp(ms / 1000, tz=timezone.utc)
    dt_arg = dt_utc - timedelta(hours=3)
    return dt_arg.strftime("%Y-%m-%d")


def earliest_quoted_date_ms(body):
    """Busca fechas de mensajes citados (encabezados 'Enviado: ...' que Outlook
    agrega al citar respuestas previas) y devuelve la mas antigua encontrada,
    en ms epoch UTC. Sirve para detectar que una cadena viene de mas atras
    aunque el reenvio a esta casilla haya arrancado recien con el ultimo mail."""
    found = []
    for day, mes_name, year, hour, minute in QUOTED_DATE_RE.findall(body):
        mes = MESES_ES.get(mes_name.lower())
        if not mes:
            continue
        try:
            dt = datetime(int(year), mes, int(day), int(hour), int(minute), tzinfo=timezone.utc)
            found.append(int(dt.timestamp() * 1000) + ARG_UTC_OFFSET_MS)
        except ValueError:
            continue
    return min(found) if found else None


def is_it_escalation_recipient(recipients_text):
    return (
        any(k in recipients_text for k in IT_RECIPIENT_KEYWORDS)
        or bool(IT_RECIPIENT_RE.search(recipients_text))
        or any(addr in recipients_text for addr in IT_RECIPIENT_ADDR_HINTS)
    )


# ---------------------------------------------------------------------------
# Fetch de IMAP EN LOTES (varios UIDs por consulta, no uno por uno)
# ---------------------------------------------------------------------------

def _uid_str(u):
    return u.decode() if isinstance(u, bytes) else str(u)


def _parse_uid_from_meta(meta):
    s = meta.decode(errors="replace") if isinstance(meta, bytes) else str(meta)
    m = re.search(r"UID (\d+)", s)
    return m.group(1) if m else None


def _fetch_literal_batch(imap, uids, spec, chunk_size):
    """Trae UID + <spec> (algo con literal, tipo BODY[HEADER] o RFC822) para
    una lista de UIDs, en tandas de chunk_size por consulta IMAP. Devuelve
    {uid_str: email.message.Message}."""
    results = {}
    uid_strs = [_uid_str(u) for u in uids]
    for i in range(0, len(uid_strs), chunk_size):
        chunk = uid_strs[i:i + chunk_size]
        uid_set = ",".join(chunk)
        typ, data = imap.uid("fetch", uid_set, f"(UID {spec})")
        if typ != "OK" or not data:
            raise RuntimeError(f"fetch en lote fallo (typ={typ}) para spec={spec}")
        for item in data:
            if isinstance(item, tuple) and len(item) == 2:
                meta, literal = item
                uid_str = _parse_uid_from_meta(meta)
                if uid_str and literal:
                    try:
                        results[uid_str] = email.message_from_bytes(literal)
                    except Exception:
                        pass
        if i + chunk_size < len(uid_strs):
            time.sleep(0.5)  # pequeño respiro entre tandas, evita picos de transferencia
    return results


def fetch_headers_batch(imap, uids, chunk_size=150):
    """Solo encabezados (sin cuerpo) — para descartar mails fuera de ventana
    de tiempo sin pagar el costo de bajar el cuerpo completo."""
    return _fetch_literal_batch(imap, uids, "BODY.PEEK[HEADER]", chunk_size)


def fetch_thrids_batch(imap, uids, chunk_size=150):
    """X-GM-THRID (extension de Gmail) para varios UIDs de una — se usa como
    clave estable para agrupar respuestas del mismo hilo a lo largo de
    corridas, no para recorrer el hilo entero."""
    results = {}
    uid_strs = [_uid_str(u) for u in uids]
    for i in range(0, len(uid_strs), chunk_size):
        chunk = uid_strs[i:i + chunk_size]
        uid_set = ",".join(chunk)
        typ, data = imap.uid("fetch", uid_set, "(UID X-GM-THRID)")
        if typ != "OK" or not data:
            raise RuntimeError(f"fetch en lote fallo (typ={typ}) para X-GM-THRID")
        for item in data:
            if item is None:
                continue
            s = item.decode(errors="replace") if isinstance(item, bytes) else str(item)
            uid_m = re.search(r"UID (\d+)", s)
            thrid_m = re.search(r"X-GM-THRID\s+(\d+)", s)
            if uid_m and thrid_m:
                results[uid_m.group(1)] = format(int(thrid_m.group(1)), "x")
    return results


# ---------------------------------------------------------------------------
# BODYSTRUCTURE: identifica QUE parte de cada mail es el texto (plano o
# html), para poder pedirle a IMAP solo esa parte puntual — nunca las
# imagenes/adjuntos. BODYSTRUCTURE en si es solo metadata (tipos, tamanos),
# no baja contenido, asi que consultarla es practicamente gratis.
# ---------------------------------------------------------------------------

MAX_TEXT_PART_FETCH_BYTES = 80_000  # tope defensivo por si el texto plano fuera enorme


def _tokenize_imap_list(s):
    tokens = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c in "()":
            tokens.append(c)
            i += 1
        elif c == '"':
            j = i + 1
            buf = []
            while j < n and s[j] != '"':
                if s[j] == "\\" and j + 1 < n:
                    buf.append(s[j + 1])
                    j += 2
                else:
                    buf.append(s[j])
                    j += 1
            tokens.append("".join(buf))
            i = j + 1
        elif c.isspace():
            i += 1
        else:
            j = i
            while j < n and s[j] not in "() \t\r\n":
                j += 1
            atom = s[i:j]
            tokens.append(None if atom.upper() == "NIL" else atom)
            i = j
    return tokens


def _parse_imap_tokens(tokens):
    pos = [0]

    def parse():
        tok = tokens[pos[0]]
        if tok == "(":
            pos[0] += 1
            lst = []
            while tokens[pos[0]] != ")":
                lst.append(parse())
            pos[0] += 1
            return lst
        pos[0] += 1
        return tok

    return parse()


def _extract_balanced(s, start):
    """Devuelve el substring balanceado en parentesis que empieza en s[start]
    (que debe ser '('), hasta su cierre correspondiente."""
    depth = 0
    in_quotes = False
    for i in range(start, len(s)):
        c = s[i]
        if c == '"' and (i == 0 or s[i - 1] != "\\"):
            in_quotes = not in_quotes
        elif not in_quotes:
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    return s[start:i + 1]
    return s[start:]


def parse_bodystructure(raw_line):
    """raw_line: la linea de respuesta IMAP completa (str) que contiene
    'BODYSTRUCTURE (...)'. Devuelve el arbol parseado (lista anidada) o None."""
    m = re.search(r"BODYSTRUCTURE\s*(\()", raw_line, re.IGNORECASE)
    if not m:
        return None
    start = m.start(1)
    balanced = _extract_balanced(raw_line, start)
    try:
        tokens = _tokenize_imap_list(balanced)
        return _parse_imap_tokens(tokens)
    except Exception:
        return None


def _resolve_text_leaf(node, prefix):
    """node: nodo parseado de bodystructure. prefix: lista de ints (path).
    Devuelve (part_num_str, subtype, charset, encoding) del mejor candidato
    de texto (prefiere text/plain sobre text/html), o None si no hay texto."""
    if not isinstance(node, list) or not node:
        return None

    if isinstance(node[0], list):
        # Es multipart: los primeros elementos (listas) son las sub-partes,
        # hasta que aparece el string con el subtipo ("alternative","mixed",...).
        children = []
        for item in node:
            if isinstance(item, list):
                children.append(item)
            else:
                break
        candidates = []
        for idx, child in enumerate(children, start=1):
            r = _resolve_text_leaf(child, prefix + [idx])
            if r:
                candidates.append(r)
        for r in candidates:
            if r[1] == "plain":
                return r
        for r in candidates:
            if r[1] == "html":
                return r
        return None

    # Nodo hoja: (type, subtype, params, id, description, encoding, size, ...)
    type_ = (node[0] or "").lower() if isinstance(node[0], str) else ""
    if type_ != "text":
        return None
    subtype = (node[1] or "").lower() if len(node) > 1 and isinstance(node[1], str) else ""
    charset = "utf-8"
    params = node[2] if len(node) > 2 else None
    if isinstance(params, list):
        for k in range(0, len(params) - 1, 2):
            if isinstance(params[k], str) and params[k].upper() == "CHARSET" and params[k + 1]:
                charset = params[k + 1]
    encoding = "7BIT"
    if len(node) > 5 and isinstance(node[5], str):
        encoding = node[5]
    part_num = ".".join(str(x) for x in prefix) if prefix else "1"
    return (part_num, subtype, charset, encoding)


def fetch_bodystructures_batch(imap, uids, chunk_size=150):
    """BODYSTRUCTURE (solo metadata, no baja contenido) para varios UIDs de
    una. Devuelve {uid_str: (part_num, subtype, charset, encoding) | None}."""
    results = {}
    uid_strs = [_uid_str(u) for u in uids]
    for i in range(0, len(uid_strs), chunk_size):
        chunk = uid_strs[i:i + chunk_size]
        uid_set = ",".join(chunk)
        typ, data = imap.uid("fetch", uid_set, "(UID BODYSTRUCTURE)")
        if typ != "OK" or not data:
            raise RuntimeError(f"fetch en lote fallo (typ={typ}) para BODYSTRUCTURE")
        for item in data:
            if item is None:
                continue
            s = item.decode(errors="replace") if isinstance(item, bytes) else str(item)
            uid_m = re.search(r"UID (\d+)", s)
            if not uid_m:
                continue
            tree = parse_bodystructure(s)
            resolved = _resolve_text_leaf(tree, []) if tree else None
            results[uid_m.group(1)] = resolved
        if i + chunk_size < len(uid_strs):
            time.sleep(0.3)
    return results


def build_body_text(subtype, charset, encoding, raw_bytes):
    """Arma un mini-mensaje MIME de una sola parte (encabezado sintetico +
    los bytes ya bajados de esa parte) para reusar el decoder estandar de
    Content-Transfer-Encoding (base64/quoted-printable/etc.) de la libreria
    email, sin tener que reimplementarlo a mano."""
    header = f"Content-Type: text/{subtype}; charset={charset}\r\nContent-Transfer-Encoding: {encoding}\r\n\r\n".encode("ascii", errors="replace")
    try:
        part_msg = email.message_from_bytes(header + raw_bytes)
        payload = part_msg.get_payload(decode=True)
        text = payload.decode(charset or "utf-8", errors="replace") if payload is not None else ""
    except Exception:
        text = raw_bytes.decode("utf-8", errors="replace")
    if subtype == "html":
        text = strip_html(text)
    return truncate_body(text)


def fetch_body_texts_batch(imap, resolved_by_uid, chunk_size=100):
    """Baja SOLO la parte de texto resuelta por BODYSTRUCTURE para cada UID
    (nunca imagenes/adjuntos). Agrupa por numero de parte (normalmente son
    pocos grupos distintos: "1", "1.1", etc.) para seguir haciendo pocas
    consultas IMAP en total. Devuelve {uid_str: texto_ya_decodificado}."""
    by_part = {}
    for uid_str, resolved in resolved_by_uid.items():
        if not resolved:
            continue
        part_num, subtype, charset, encoding = resolved
        by_part.setdefault(part_num, []).append(uid_str)

    texts = {}
    for part_num, uid_strs in by_part.items():
        spec = f"BODY.PEEK[{part_num}]<0.{MAX_TEXT_PART_FETCH_BYTES}>"
        for i in range(0, len(uid_strs), chunk_size):
            chunk = uid_strs[i:i + chunk_size]
            uid_set = ",".join(chunk)
            typ, data = imap.uid("fetch", uid_set, f"(UID {spec})")
            if typ != "OK" or not data:
                raise RuntimeError(f"fetch en lote fallo (typ={typ}) para {spec}")
            for item in data:
                if isinstance(item, tuple) and len(item) == 2:
                    meta, literal = item
                    uid_str = _parse_uid_from_meta(meta)
                    if uid_str and literal is not None:
                        _, subtype, charset, encoding = resolved_by_uid[uid_str]
                        texts[uid_str] = build_body_text(subtype, charset, encoding, literal)
            if i + chunk_size < len(uid_strs):
                time.sleep(0.3)
    return texts


# ---------------------------------------------------------------------------
# Clasificacion: devuelve una lista de categorias aplicables (un mail puede
# pertenecer a mas de una a la vez, ej. "it" + "escalamientosIT"), mas los
# datos que necesita cada categoria (origen del hilo, cierre detectado).
# No hace NINGUNA consulta IMAP propia — recibe el encabezado (ya bajado en
# lote) y el texto del cuerpo (ya resuelto/bajado via BODYSTRUCTURE, sin
# imagenes) por separado; el X-GM-THRID se resuelve aparte, en lote, en
# process_candidate_uids().
# ---------------------------------------------------------------------------

def classify(msg, body):
    subject = decode_mime_header(msg.get("Subject")) or ""
    sender_raw = decode_mime_header(msg.get("From")) or ""
    sender_name, sender_addr = email.utils.parseaddr(sender_raw)
    sender_addr = (sender_addr or "").lower()
    to_text = addr_list_text(msg, "To")
    cc_text = addr_list_text(msg, "Cc")
    recipients_text = (to_text + " " + cc_text).lower()
    subject_lower = subject.lower()
    own_ms = epoch_ms_from_date_header(msg)

    categories = []
    closure_detected = False
    first_seen_candidate = own_ms

    def add_origin_candidates():
        nonlocal first_seen_candidate
        quoted_ms = earliest_quoted_date_ms(body)
        if quoted_ms:
            first_seen_candidate = min(first_seen_candidate, quoted_ms)

    # 1. Tareas (WBS): categoria EXCLUYENTE. Un mail con codigo WBS en el
    # asunto/cuerpo es una tarea de proyecto, no una escalacion real, aunque
    # lo hayan mandado por Reportes Tecnica hacia SOC/VOC/NOC/IT (pasa
    # seguido). Por eso se corta aca y no sigue evaluando el resto de reglas.
    if WBS_RE.search(subject) or WBS_RE.search(body):
        return {
            "categories": ["tareas"],
            "subject": subject,
            "sender_name": sender_name,
            "sender_address": sender_addr,
            "to_recipients": to_text,
            "cc_recipients": cc_text,
            "sent_at_ms": own_ms,
            "first_seen_ms": first_seen_candidate,
            "is_first_of_chain": is_first_of_chain(msg),
            "closure_detected": False,
            "needs_thrid": "tareas" in CATEGORIES_NEEDING_THRID,
            "body_text": body,
        }

    # 2. Afectaciones masivas
    if sender_addr == AFECTACION_MASIVA_SENDER:
        categories.append("afectacionMasiva")
        closure_detected = bool(CLOSURE_RE.search(subject) or CLOSURE_RE.search(body))

    # 3. Reportes Tecnica -> IT / Ingenieria / Informes
    if REPORTES_TECNICA_HINT in sender_addr:
        if is_it_escalation_recipient(recipients_text):
            categories.append("it")
            # "escalamientosIT" (solapa aparte): mismo mail, misma condicion
            # (Reportes Tecnica -> alguna de las 3 areas de IT). Antes esta
            # categoria no exigia remitente especifico; el usuario pidio
            # restringirla a Reportes Tecnica igual que "it".
            categories.append("escalamientosIT")
            add_origin_candidates()
        elif any(re.search(r"\b" + re.escape(k) + r"\b", recipients_text) for k in ING_RECIPIENT_KEYWORDS):
            categories.append("ingenieria")
            add_origin_candidates()
        elif "informe" in subject_lower:
            if "fija" in subject_lower:
                categories.append("informesFija")
            elif "611" in subject_lower:
                categories.append("informesMovil")
            else:
                log(f"[sin clasificar] Informe con patron desconocido: {subject!r}")

    # 4. Pedidos Referentes
    if MARIA_INES_HINT in sender_name.lower() and REPORTES_TECNICA_HINT in recipients_text.lower():
        categories.append("pedidosReferentes")

    # 5. Informes desde cualquier otro remitente (por si aparece uno nuevo)
    if "informe" in subject_lower and "informesFija" not in categories and "informesMovil" not in categories:
        if "fija" in subject_lower:
            categories.append("informesFija")
        elif "611" in subject_lower:
            categories.append("informesMovil")

    # 6. "Afectaciones masivas IT": cadenas NUEVAS enviadas desde alguna de
    # las 3 areas de IT (Gestion de Incidentes / Help Desk / Help Desk
    # Billetera) hacia Afectacion Masiva. Es el flujo inverso al de la
    # categoria "afectacionMasiva" (que es Afectacion Masiva -> nosotros).
    # Solo cuenta el mail de apertura de cada cadena (is_first_of_chain),
    # no las respuestas dentro del mismo hilo.
    if (
        sender_addr in IT_AREA_ADDR_HINTS
        and AFECTACION_MASIVA_SENDER in recipients_text
        and is_first_of_chain(msg)
    ):
        categories.append("afectacionesMasivasIT")
        add_origin_candidates()

    # 7. "Operacion Tecnica / MSK / LY": cualquier mail (de cualquier
    # remitente) que tenga la direccion correspondiente en To o Cc. El split
    # Nuevo/EnCurso se resuelve en el frontend segun cuanto hace que arranco
    # la cadena (first_seen_ms), no aca.
    if OPERACION_TECNICA_ADDR in recipients_text:
        categories.append("operacionTecnica")
        add_origin_candidates()
    if OPERACION_MSK_ADDR in recipients_text:
        categories.append("operacionMSK")
        add_origin_candidates()
    if OPERACION_LY_ADDR in recipients_text:
        categories.append("operacionLY")
        add_origin_candidates()

    # 8. Especificas de "Resumen por lapso": listan asuntos dentro de un
    # rango puntual, sin split Nuevo/EnCurso. Reglas propias, DISTINTAS de
    # las que arman las otras solapas (mismo nombre de tema, criterio distinto):
    #  - Afectaciones masivas: mail ENVIADO A (To/Cc) la direccion de clientes.
    #  - Escalamientos IT: se divide por area de origen (remitente exacto):
    #    GIM (incidentereportado), HDB (hdbilletera), HelpDesk (helpdesk).
    #  - Escalamientos ING: se divide por destinatario ("para"): VOC, SOC,
    #    NOC. Cualquier remitente cuenta, solo importa el "para".
    if AFECTACION_MASIVA_CLIENTES_ADDR in recipients_text:
        categories.append("afectacionMasivaLapso")

    if sender_addr == GIM_ADDR:
        categories.append("escalamientosIT_GIM")
    if sender_addr == HDB_ADDR:
        categories.append("escalamientosIT_HDB")
    if sender_addr == HELPDESK_ADDR:
        categories.append("escalamientosIT_HelpDesk")

    if VOC_ADDR in to_text.lower():
        categories.append("escalamientosING_VOC")
    if SOC_ADDR in to_text.lower():
        categories.append("escalamientosING_SOC")
    if NOC_ADDR in to_text.lower():
        categories.append("escalamientosING_NOC")

    if not categories:
        return None

    return {
        "categories": categories,
        "subject": subject,
        "sender_name": sender_name,
        "sender_address": sender_addr,
        "to_recipients": to_text,
        "cc_recipients": cc_text,
        "sent_at_ms": own_ms,
        "first_seen_ms": first_seen_candidate,
        "is_first_of_chain": is_first_of_chain(msg),
        "closure_detected": closure_detected,
        "needs_thrid": any(c in CATEGORIES_NEEDING_THRID for c in categories),
        "body_text": body,
    }


# ---------------------------------------------------------------------------
# Supabase (API REST + RPC)
# ---------------------------------------------------------------------------

def ms_to_iso(ms):
    if ms is None:
        return None
    return datetime.fromtimestamp(ms / 1000, tz=timezone.utc).isoformat()


class SupabaseClient:
    def __init__(self, url, service_role_key):
        self.url = url.rstrip("/")
        self.key = service_role_key

    def _request(self, method, path, body=None):
        url = f"{self.url}{path}"
        data = json.dumps(body).encode("utf-8") if body is not None else None
        req = urllib.request.Request(url, data=data, method=method)
        req.add_header("apikey", self.key)
        req.add_header("Authorization", f"Bearer {self.key}")
        req.add_header("Content-Type", "application/json")
        if method == "GET":
            req.add_header("Accept", "application/json")
        with urllib.request.urlopen(req, timeout=25) as resp:
            raw = resp.read()
            if not raw:
                return None
            return json.loads(raw)

    def upsert_mail(self, record_id, thrid, category, classification, own_ms):
        payload = {
            "id": record_id,
            "thread_id": thrid,
            "subject": classification["subject"],
            "sender_name": classification["sender_name"],
            "sender_address": classification["sender_address"],
            "to_recipients": classification["to_recipients"],
            "cc_recipients": classification["cc_recipients"],
            "sent_at": ms_to_iso(own_ms),
            "first_seen_at": ms_to_iso(classification["first_seen_ms"]),
            "is_first_of_chain": classification["is_first_of_chain"],
            "closure_detected": classification["closure_detected"],
            "category": category,
            "body_text": classification["body_text"],
        }
        self._request("POST", "/rest/v1/rpc/upsert_mail", {"payload": payload})

    def record_activity(self, record_id, category, date_str):
        self._request("POST", "/rest/v1/rpc/record_mail_activity", {
            "p_id": record_id,
            "p_category": category,
            "p_date": date_str,
        })

    def set_meta(self, key, value):
        self._request("POST", "/rest/v1/rpc/set_meta", {"p_key": key, "p_value": value})

    def get_meta(self, key):
        result = self._request("GET", f"/rest/v1/meta?key=eq.{key}&select=value")
        if result:
            return result[0]["value"]
        return None

    def max_sent_at_ms(self):
        result = self._request("GET", "/rest/v1/mails?select=sent_at&order=sent_at.desc&limit=1")
        if result:
            iso = result[0]["sent_at"]
            dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
            return int(dt.timestamp() * 1000)
        return None


QUOTA_ERROR_HINTS = ("overquota", "bandwidth", "command or bandwidth limits")
QUOTA_COOLDOWN_MS = 90 * 60 * 1000  # 90 min de enfriamiento tras un OVERQUOTA


def is_quota_error(exc):
    s = str(exc).lower()
    return any(hint in s for hint in QUOTA_ERROR_HINTS)


def process_candidate_uids(imap, sb, uids, window_start_ms=None, window_end_ms=None, prefilter_headers=False):
    """Clasifica y guarda en Supabase una lista de UIDs candidatos (ya
    ordenados o no).

    Los encabezados SIEMPRE se bajan primero (son livianos y ya nos sirven
    tanto para el prefiltro de fecha como para clasificar despues). Si
    prefilter_headers=True, se descartan los que caen fuera de
    [window_start_ms, window_end_ms] antes de seguir.

    Para el cuerpo, en vez de bajar el mensaje completo (que incluye
    imagenes/adjuntos que no usamos), se consulta primero BODYSTRUCTURE
    (metadata pura, no baja contenido) para saber exactamente que parte es
    texto, y se baja SOLO esa parte puntual. Esto es lo que evita gastar el
    ancho de banda de Gmail en imagenes que despues se tiran.

    Devuelve la cantidad de mails guardados (con >=1 categoria). Puede tirar
    una excepcion si algun fetch en lote falla (el llamador decide que hacer
    con el checkpoint en ese caso)."""
    if not uids:
        return 0

    uids_sorted = sorted(uids, key=lambda u: int(_uid_str(u)))
    headers = fetch_headers_batch(imap, uids_sorted)

    fetch_targets = []
    for u in uids_sorted:
        uid_str = _uid_str(u)
        hmsg = headers.get(uid_str)
        if hmsg is None:
            continue
        if prefilter_headers:
            h_ms = epoch_ms_from_date_header(hmsg)
            if h_ms is None:
                continue
            if window_start_ms is not None and h_ms < window_start_ms:
                continue
            if window_end_ms is not None and h_ms > window_end_ms:
                continue
        fetch_targets.append(u)
    if prefilter_headers:
        log(f"Dentro de ventana tras chequear encabezados: {len(fetch_targets)}")

    resolved = fetch_bodystructures_batch(imap, fetch_targets)
    body_texts = fetch_body_texts_batch(imap, resolved)

    results_by_uid = {}
    for u in fetch_targets:
        uid_str = _uid_str(u)
        hmsg = headers.get(uid_str)
        if hmsg is None:
            continue
        body = body_texts.get(uid_str, "")
        result = classify(hmsg, body)
        if result is not None:
            results_by_uid[uid_str] = result

    needing_thrid = [uid_str for uid_str, r in results_by_uid.items() if r["needs_thrid"]]
    thrids = fetch_thrids_batch(imap, needing_thrid) if needing_thrid else {}

    processed = 0
    for u in fetch_targets:
        uid_str = _uid_str(u)
        result = results_by_uid.get(uid_str)
        if result is None:
            continue
        thrid = thrids.get(uid_str)
        record_id = thrid or f"uid-{uid_str}"
        activity_date = arg_calendar_date_str(result["sent_at_ms"])
        for category in result["categories"]:
            sb.upsert_mail(record_id, thrid, category, result, result["sent_at_ms"])
            try:
                sb.record_activity(record_id, category, activity_date)
            except Exception as e:
                log(f"[activity] no se pudo registrar {record_id}/{category}/{activity_date}: {type(e).__name__}: {e}")
        processed += 1

    return processed


def set_quota_cooldown(sb, now_ms):
    """Gmail bloquea la cuenta por IMAP (OVERQUOTA) normalmente ~1h, a veces
    hasta 24hs si se repite. Guardamos hasta cuando conviene NO intentar de
    nuevo, para que las corridas automaticas se salteen solas en vez de
    seguir golpeando la cuenta (lo que puede extender el bloqueo)."""
    until_ms = now_ms + QUOTA_COOLDOWN_MS
    try:
        sb.set_meta("quota_cooldown_until", until_ms)
        log(f"[CUOTA] Se detecto OVERQUOTA. Enfriamiento hasta {ms_to_iso(until_ms)}.")
    except Exception as e:
        log(f"No se pudo guardar el enfriamiento de cuota: {type(e).__name__}: {e}")


def run_backfill(sb, gmail_user, gmail_pass, now_ms, backfill_hours):
    """Barrido UNICO por fecha (SINCE), pensado para completar historial que
    el checkpoint de UID de las corridas en vivo ya dejo atras. A proposito
    NO toca 'last_uid' ni 'last_run': es independiente de la maquinaria
    incremental, para no arriesgar el estado de las corridas automaticas."""
    error_msg = None
    processed = 0
    try:
        imap = imaplib.IMAP4_SSL(IMAP_HOST, timeout=25)
        imap.login(gmail_user, gmail_pass)
        imap.select("INBOX")

        window_start_ms = now_ms - int(backfill_hours * 3600 * 1000)
        since_dt = datetime.fromtimestamp(window_start_ms / 1000, tz=timezone.utc) - timedelta(days=1)
        since_date = since_dt.strftime("%d-%b-%Y")
        typ, data_uids = imap.uid("search", None, f"(SINCE {since_date})")
        uids = data_uids[0].split() if typ == "OK" and data_uids and data_uids[0] else []
        log(f"[BACKFILL] Candidatos (SINCE {since_date}, ultimas {backfill_hours}h): {len(uids)}")

        processed = process_candidate_uids(
            imap, sb, uids,
            window_start_ms=window_start_ms,
            window_end_ms=now_ms + 5 * 60 * 1000,
            prefilter_headers=True,
        )
        imap.logout()
    except Exception as e:
        error_msg = f"{type(e).__name__}: {e}"
        log(f"[BACKFILL] ERROR: {error_msg}")
        if is_quota_error(e):
            set_quota_cooldown(sb, now_ms)

    try:
        sb.set_meta("last_backfill", {
            "timestamp": now_ms,
            "hours": backfill_hours,
            "processed": processed,
            "error": error_msg,
        })
    except Exception as e:
        log(f"[BACKFILL] No se pudo guardar el estado: {type(e).__name__}: {e}")

    log(f"[BACKFILL] Listo. Mails procesados: {processed}.")
    if error_msg:
        log(f"[BACKFILL] Con errores: {error_msg}")


def run_incremental(sb, gmail_user, gmail_pass, now_ms):
    """Corrida normal: incremental por UID una vez que existe checkpoint, o
    bootstrap acotado (MAX_LOOKBACK_MS) la primera vez que corre el proyecto."""
    last_uid = None
    try:
        raw_last_uid = sb.get_meta("last_uid")
        if raw_last_uid is not None:
            last_uid = int(raw_last_uid)
    except Exception as e:
        log(f"No se pudo leer el ultimo checkpoint (last_uid) de la base: {type(e).__name__}: {e}")

    MAX_LOOKBACK_MS = 60 * 60 * 1000

    error_msg = None
    processed = 0
    max_ok_uid = last_uid

    try:
        imap = imaplib.IMAP4_SSL(IMAP_HOST, timeout=25)
        imap.login(gmail_user, gmail_pass)
        imap.select("INBOX")

        if last_uid is not None:
            typ, data_uids = imap.uid("search", None, f"(UID {last_uid + 1}:*)")
            uids = data_uids[0].split() if typ == "OK" and data_uids and data_uids[0] else []
            uids = [u for u in uids if int(_uid_str(u)) > last_uid]
            log(f"Candidatos nuevos (UID > {last_uid}): {len(uids)}")
            processed = process_candidate_uids(imap, sb, uids, prefilter_headers=False)
        else:
            search_window_start = now_ms - MAX_LOOKBACK_MS
            since_dt = datetime.fromtimestamp(search_window_start / 1000, tz=timezone.utc) - timedelta(days=1)
            since_date = since_dt.strftime("%d-%b-%Y")
            typ, data_uids = imap.uid("search", None, f"(SINCE {since_date})")
            uids = data_uids[0].split() if typ == "OK" and data_uids and data_uids[0] else []
            log(f"Primera corrida (sin checkpoint de UID) - candidatos (SINCE {since_date}): {len(uids)}")
            processed = process_candidate_uids(
                imap, sb, uids,
                window_start_ms=search_window_start,
                window_end_ms=now_ms + 5 * 60 * 1000,
                prefilter_headers=True,
            )

        if uids:
            max_ok_uid = int(_uid_str(max(uids, key=lambda u: int(_uid_str(u)))))

        imap.logout()
    except Exception as e:
        error_msg = f"{type(e).__name__}: {e}"
        log(f"ERROR durante la corrida: {error_msg}")
        if is_quota_error(e):
            set_quota_cooldown(sb, now_ms)

    if max_ok_uid is not None and max_ok_uid != last_uid:
        try:
            sb.set_meta("last_uid", max_ok_uid)
        except Exception as e:
            log(f"No se pudo guardar el checkpoint de UID: {type(e).__name__}: {e}")

    try:
        sb.set_meta("last_run", {
            "timestamp": now_ms,
            "lastUid": max_ok_uid,
            "processed": processed,
            "error": error_msg,
        })
    except Exception as e:
        log(f"No se pudo guardar el estado de la corrida: {type(e).__name__}: {e}")

    log(f"Listo. Mails procesados: {processed}.")
    if error_msg:
        log(f"Con errores: {error_msg}")


def main():
    gmail_user = os.environ.get("GMAIL_USER")
    gmail_pass = os.environ.get("GMAIL_APP_PASSWORD")
    supabase_url = os.environ.get("SUPABASE_URL")
    supabase_key = os.environ.get("SUPABASE_SERVICE_ROLE_KEY")
    now_ms = int(time.time() * 1000)

    missing = [
        name for name, val in [
            ("GMAIL_USER", gmail_user), ("GMAIL_APP_PASSWORD", gmail_pass),
            ("SUPABASE_URL", supabase_url), ("SUPABASE_SERVICE_ROLE_KEY", supabase_key),
        ] if not val
    ]
    if missing:
        log(f"ERROR: faltan variables de entorno: {', '.join(missing)}")
        sys.exit(0)

    sb = SupabaseClient(supabase_url, supabase_key)

    try:
        cooldown_until = sb.get_meta("quota_cooldown_until")
    except Exception as e:
        cooldown_until = None
        log(f"No se pudo leer el enfriamiento de cuota: {type(e).__name__}: {e}")

    if cooldown_until is not None and now_ms < int(cooldown_until):
        remaining_min = int((int(cooldown_until) - now_ms) / 60000)
        log(f"[CUOTA] Todavia en enfriamiento por OVERQUOTA (quedan ~{remaining_min} min). Se saltea esta corrida.")
        return

    backfill_hours_raw = (os.environ.get("BACKFILL_HOURS") or "").strip()
    if backfill_hours_raw:
        try:
            backfill_hours = float(backfill_hours_raw)
            run_backfill(sb, gmail_user, gmail_pass, now_ms, backfill_hours)
            return
        except ValueError:
            log(f"BACKFILL_HOURS invalido: {backfill_hours_raw!r}, se ignora y corre normal")

    run_incremental(sb, gmail_user, gmail_pass, now_ms)


if __name__ == "__main__":
    main()
