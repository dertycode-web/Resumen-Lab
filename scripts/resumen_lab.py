#!/usr/bin/env python3
"""
Resumen LAB - lee la casilla de Gmail via Gmail API (OAuth), categoriza los
mails nuevos y los guarda en una tabla de Supabase (Postgres), via su API
REST/RPC.

Corre desde GitHub Actions, usando estas variables de entorno (secrets):
  GMAIL_OAUTH_CLIENT_ID, GMAIL_OAUTH_CLIENT_SECRET, GMAIL_OAUTH_REFRESH_TOKEN,
  SUPABASE_URL, SUPABASE_SERVICE_ROLE_KEY

Historial: originalmente esto se conectaba por IMAP con una contrasena de
aplicacion (GMAIL_USER/GMAIL_APP_PASSWORD). Google trata ese mecanismo como
"acceso de apps menos seguras" y termino inhabilitando la cuenta por el
patron de acceso automatizado. Se migro a Gmail API con OAuth (metodo
oficial de Google para automatizacion, scope de solo lectura
"gmail.readonly"), que ademas simplifica mucho la lectura de mails: Gmail
API nunca baja el contenido de adjuntos/imagenes salvo que se pida
explicitamente por su attachmentId (cosa que este script nunca hace), asi
que el problema de gastar cuota de banda ancha en imagenes que se
descartaban tampoco existe mas.

No depende de la computadora del usuario ni de que Cowork este abierto, y
ya no escribe nada en index.html: la pagina lee los datos directo de
Supabase (con la clave publica "anon"), asi que un despliegue de la pagina
solo hace falta cuando cambia el CODIGO, no cada vez que llegan mails.
"""

import base64
import email
import email.utils
import html
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from email.header import decode_header
from email.message import Message

GMAIL_API_BASE = "https://gmail.googleapis.com/gmail/v1/users/me"
GMAIL_TOKEN_URL = "https://oauth2.googleapis.com/token"

# Dominio sintetico para los "usuarios" del login (no son casillas reales).
# Supabase Auth exige un email como identificador; el usuario que ve la
# persona en la pantalla de login sigue siendo su nombre (ej. Lautaro_Rojas),
# y se lo mapea a "lautaro_rojas@resumenlab.local" puertas adentro.
AUTH_EMAIL_DOMAIN = "resumenlab.local"

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
# Otros patrones de "tareas" que no usan codigo WBS pero son el mismo tipo de
# item (tareas de proyecto), segun indico el usuario: obras de modernizacion
# GPON en Salta (traen codigo "GSLT-R####") y avisos de AVIFO (habilitacion/
# carga de corte).
TAREAS_EXTRA_RE = re.compile(r"gslt-r\d+|\bavifo\b", re.IGNORECASE)
# Detecta un reenvio MANUAL (Outlook "Reenviar", no un redirect automatico):
# el asunto queda con prefijo Fwd/FW/RV/RR y el mail no tiene In-Reply-To ni
# References (no es una respuesta dentro de un hilo que Gmail ya conoce).
# Sirve para, en estos casos puntuales, usar la fecha ORIGINAL citada en el
# cuerpo ("Enviado: ...") en vez de la fecha del reenvio (que es "ahora"),
# para que un mail recuperado a mano por un hueco de caida no aparezca como
# "nuevo" hoy sino en la fecha/hora en la que realmente se envio.
MANUAL_FORWARD_SUBJECT_RE = re.compile(r"^\s*(fw|fwd|rv|rr)\s*:", re.IGNORECASE)

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
# Gmail API (OAuth) — reemplaza el viejo fetch por IMAP en lotes. Con
# format=full, una sola consulta por mensaje trae encabezados Y cuerpo, y
# Gmail API nunca incluye los bytes de adjuntos/imagenes salvo que se pida
# su attachmentId explicitamente (cosa que nunca hacemos), asi que el texto
# viene ya "limpio" de imagenes sin tener que resolver nada manualmente.
# ---------------------------------------------------------------------------

def get_access_token(client_id, client_secret, refresh_token):
    data = urllib.parse.urlencode({
        "client_id": client_id,
        "client_secret": client_secret,
        "refresh_token": refresh_token,
        "grant_type": "refresh_token",
    }).encode("utf-8")
    req = urllib.request.Request(GMAIL_TOKEN_URL, data=data, method="POST")
    with urllib.request.urlopen(req, timeout=20) as resp:
        return json.loads(resp.read())["access_token"]


def gmail_api_get(access_token, path, params=None):
    url = f"{GMAIL_API_BASE}{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, method="GET")
    req.add_header("Authorization", f"Bearer {access_token}")
    with urllib.request.urlopen(req, timeout=25) as resp:
        return json.loads(resp.read())


def is_quota_error(exc):
    if isinstance(exc, urllib.error.HTTPError) and exc.code == 429:
        return True
    s = str(exc).lower()
    return any(hint in s for hint in ("ratelimitexceeded", "quotaexceeded", "429", "userratelimitexceeded"))


class HistoryIdTooOldError(Exception):
    """Gmail purga el historial despues de un tiempo (tipicamente ~1 semana).
    Si el checkpoint guardado ya es demasiado viejo, history.list devuelve
    404 en vez de la lista de cambios — hay que re-establecer el punto de
    partida (sin reprocesar mails viejos, ya estan todos guardados)."""
    pass


def gmail_list_message_ids(access_token, query, max_results_per_page=500):
    """Pagina messages.list con un query de busqueda de Gmail (ej.
    'after:1699999999'). Devuelve la lista completa de message IDs."""
    ids = []
    page_token = None
    while True:
        params = {"q": query, "maxResults": max_results_per_page}
        if page_token:
            params["pageToken"] = page_token
        data = gmail_api_get(access_token, "/messages", params)
        for m in data.get("messages", []) or []:
            ids.append(m["id"])
        page_token = data.get("nextPageToken")
        if not page_token:
            break
    return ids


def gmail_list_history_message_ids(access_token, start_history_id):
    """Incremental real (equivalente al viejo UID > last_uid, pero con la
    API de Gmail): trae SOLO los mensajes agregados desde start_history_id,
    sin tener que re-listar ni re-filtrar por fecha. Devuelve
    (message_ids, nuevo_history_id)."""
    ids = set()
    page_token = None
    new_history_id = start_history_id
    while True:
        params = {"startHistoryId": start_history_id, "historyTypes": "messageAdded", "maxResults": 500}
        if page_token:
            params["pageToken"] = page_token
        try:
            data = gmail_api_get(access_token, "/history", params)
        except urllib.error.HTTPError as e:
            if e.code == 404:
                raise HistoryIdTooOldError(str(e))
            raise
        for rec in data.get("history", []) or []:
            for added in rec.get("messagesAdded", []) or []:
                msg = added.get("message") or {}
                if msg.get("id"):
                    ids.add(msg["id"])
        if "historyId" in data:
            new_history_id = data["historyId"]
        page_token = data.get("nextPageToken")
        if not page_token:
            break
    return list(ids), new_history_id


def _decode_b64url(data):
    if not data:
        return b""
    padded = data + "=" * (-len(data) % 4)
    try:
        return base64.urlsafe_b64decode(padded)
    except Exception:
        return b""


def _find_best_text_part(payload):
    """Recorre el arbol de 'parts' de un mensaje de Gmail API buscando la
    mejor parte de texto (prefiere text/plain sobre text/html). Nunca baja
    adjuntos: si una parte no trae 'body.data' inline (o sea, es un adjunto
    referenciado solo por attachmentId), se ignora sin pedir nada mas."""
    mime = (payload.get("mimeType") or "").lower()
    body = payload.get("body") or {}
    parts = payload.get("parts") or []

    if not parts:
        if mime in ("text/plain", "text/html") and body.get("data"):
            return (mime, body["data"])
        return None

    candidates = []
    for part in parts:
        r = _find_best_text_part(part)
        if r:
            candidates.append(r)
    for r in candidates:
        if r[0] == "text/plain":
            return r
    for r in candidates:
        if r[0] == "text/html":
            return r
    return None


def extract_body_text(payload):
    best = _find_best_text_part(payload)
    if not best:
        return ""
    mime, b64data = best
    raw = _decode_b64url(b64data)
    text = raw.decode("utf-8", errors="replace")
    if mime == "text/html":
        text = strip_html(text)
    return truncate_body(text)


def build_synthetic_message(headers_list):
    """Arma un email.message.Message a partir de la lista de headers que
    devuelve Gmail API (payload.headers: [{name, value}, ...]), para poder
    reusar TAL CUAL toda la logica de clasificacion existente (que espera
    msg.get(...)/msg.get_all(...) como un mensaje real de la libreria email)."""
    msg = Message()
    for h in headers_list or []:
        name = h.get("name")
        value = h.get("value")
        if name is not None:
            msg[name] = value
    return msg


def fetch_message_full(access_token, message_id):
    return gmail_api_get(access_token, f"/messages/{message_id}", {"format": "full"})


# ---------------------------------------------------------------------------
# Clasificacion: devuelve una lista de categorias aplicables (un mail puede
# pertenecer a mas de una a la vez, ej. "it" + "escalamientosIT"), mas los
# datos que necesita cada categoria (origen del hilo, cierre detectado).
# No hace NINGUNA consulta a Gmail API propia — recibe un email.message.Message
# sintetico (armado a partir de los headers que ya trajo Gmail API) y el
# texto del cuerpo ya resuelto, por separado. El threadId se resuelve aparte,
# en process_candidate_messages().
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

    # Si es un reenvio manual (ver MANUAL_FORWARD_SUBJECT_RE), usar la fecha
    # original citada en el cuerpo como fecha real del mail, no la fecha del
    # reenvio en si. Asi, mails recuperados a mano para tapar un hueco de
    # caida se guardan en su fecha real y no aparecen como "nuevos" hoy.
    # Nota: no se exige is_first_of_chain aca porque algunas versiones de
    # Outlook/OWA igual agregan un header "References" al reenviar (para
    # mantener la conversacion agrupada), aunque sea un reenvio nuevo y no
    # una respuesta real. El prefijo del asunto (Fwd/FW/RV/RR) ya es una
    # señal suficientemente especifica de que es un reenvio manual.
    if MANUAL_FORWARD_SUBJECT_RE.match(subject):
        original_ms = earliest_quoted_date_ms(body)
        if original_ms:
            own_ms = original_ms

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
    if WBS_RE.search(subject) or WBS_RE.search(body) or TAREAS_EXTRA_RE.search(subject) or TAREAS_EXTRA_RE.search(body):
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
    #
    # No solo el remitente automatico (argentinaafectacionmasiva@claro.com.ar):
    # tambien vale cualquier mail dirigido (To/Cc) a la casilla de clientes
    # (AFECTACION_MASIVA_CLIENTES_ADDR), aunque lo mande una persona real de
    # Claro a mano (ej. yesica.maciel@claro.com.ar) en vez del sistema
    # automatico. Antes esto solo se usaba para "afectacionMasivaLapso"
    # (regla 8 mas abajo) y esos mails no aparecian en la solapa Resumen.
    if sender_addr == AFECTACION_MASIVA_SENDER or AFECTACION_MASIVA_CLIENTES_ADDR in recipients_text:
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

    def _request(self, method, path, body=None, prefer=None):
        url = f"{self.url}{path}"
        data = json.dumps(body).encode("utf-8") if body is not None else None
        req = urllib.request.Request(url, data=data, method=method)
        req.add_header("apikey", self.key)
        req.add_header("Authorization", f"Bearer {self.key}")
        req.add_header("Content-Type", "application/json")
        if method == "GET":
            req.add_header("Accept", "application/json")
        if prefer:
            req.add_header("Prefer", prefer)
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

    def create_auth_user(self, email, password, username):
        # Alta de usuario en Supabase Auth via API de administracion (requiere
        # la service_role key). email_confirm=true: no se manda ningun mail de
        # confirmacion (el email es sintetico, no una casilla real).
        payload = {
            "email": email,
            "password": password,
            "email_confirm": True,
            "user_metadata": {"username": username},
        }
        result = self._request("POST", "/auth/v1/admin/users", payload)
        return result["id"]

    def upsert_profile(self, user_id, username):
        payload = {
            "id": user_id,
            "username": username,
            "must_change_password": True,
        }
        # on_conflict + resolution=merge-duplicates: si se corre el
        # aprovisionamiento dos veces para el mismo usuario, actualiza en vez
        # de fallar por PK duplicada.
        self._request(
            "POST", "/rest/v1/profiles?on_conflict=id", payload,
            prefer="resolution=merge-duplicates",
        )

    def get_user_id_by_username(self, username):
        result = self._request("GET", f"/rest/v1/profiles?username=eq.{urllib.parse.quote(username)}&select=id")
        if not result:
            return None
        return result[0]["id"]

    def reset_user_password(self, user_id, new_temp_password):
        # PUT admin: pisa la contraseña actual (aunque el usuario no la
        # recuerde ni la sepamos nosotros, no hace falta conocerla para
        # resetearla). Ademas volvemos a poner must_change_password=true,
        # asi la proxima vez que entre el login lo obliga a elegir una
        # contraseña nueva de una, igual que en el alta original.
        self._request("PUT", f"/auth/v1/admin/users/{user_id}", {"password": new_temp_password})
        self._request(
            "PATCH", f"/rest/v1/profiles?id=eq.{user_id}", {"must_change_password": True},
        )

    def max_sent_at_ms(self):
        result = self._request("GET", "/rest/v1/mails?select=sent_at&order=sent_at.desc&limit=1")
        if result:
            iso = result[0]["sent_at"]
            dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
            return int(dt.timestamp() * 1000)
        return None


QUOTA_COOLDOWN_MS = 30 * 60 * 1000  # 30 min de enfriamiento tras un 429 de Gmail API


def process_candidate_messages(access_token, sb, message_ids, window_start_ms=None, window_end_ms=None, prefilter_headers=False):
    """Clasifica y guarda en Supabase una lista de message IDs candidatos.

    Los encabezados SIEMPRE se bajan primero (son livianos y ya nos sirven
    tanto para el prefiltro de fecha como para clasificar despues). Si
    prefilter_headers=True, se descartan los que caen fuera de
    [window_start_ms, window_end_ms] antes de seguir.

    Para el cuerpo, Gmail API (format=full) nunca incluye los bytes de
    adjuntos/imagenes salvo que se pida su attachmentId por separado (cosa
    que este script nunca hace), asi que alcanza con UNA consulta por
    mensaje para tener encabezados + cuerpo de texto ya resuelto.

    record_id = threadId de Gmail (siempre disponible via la API, a
    diferencia del viejo X-GM-THRID de IMAP que a veces habia que resolver
    aparte) — asi una conversacion entera sigue colapsando en una sola fila
    de "mails" que se va actualizando, igual que antes.

    Devuelve la cantidad de mails guardados (con >=1 categoria). Puede tirar
    una excepcion si algun fetch falla (el llamador decide que hacer con el
    checkpoint en ese caso)."""
    if not message_ids:
        return 0

    processed = 0
    for msg_id in message_ids:
        try:
            full = fetch_message_full(access_token, msg_id)
        except Exception as e:
            log(f"[gmail] no se pudo bajar el mensaje {msg_id}: {type(e).__name__}: {e}")
            continue

        payload = full.get("payload") or {}
        hmsg = build_synthetic_message(payload.get("headers"))

        if prefilter_headers:
            h_ms = epoch_ms_from_date_header(hmsg)
            if h_ms is None:
                continue
            if window_start_ms is not None and h_ms < window_start_ms:
                continue
            if window_end_ms is not None and h_ms > window_end_ms:
                continue

        body = extract_body_text(payload)
        result = classify(hmsg, body)
        if result is None:
            continue

        thread_id = full.get("threadId")
        record_id = thread_id or f"msg-{msg_id}"
        activity_date = arg_calendar_date_str(result["sent_at_ms"])
        for category in result["categories"]:
            sb.upsert_mail(record_id, thread_id, category, result, result["sent_at_ms"])
            try:
                sb.record_activity(record_id, category, activity_date)
            except Exception as e:
                log(f"[activity] no se pudo registrar {record_id}/{category}/{activity_date}: {type(e).__name__}: {e}")
        processed += 1

    return processed


def set_quota_cooldown(sb, now_ms):
    """Si Gmail API devuelve un 429 (rate limit), guardamos hasta cuando
    conviene NO intentar de nuevo, para que las corridas automaticas se
    salteen solas un rato en vez de seguir golpeando la API."""
    until_ms = now_ms + QUOTA_COOLDOWN_MS
    try:
        sb.set_meta("quota_cooldown_until", until_ms)
        log(f"[CUOTA] Se detecto rate limit de Gmail API. Enfriamiento hasta {ms_to_iso(until_ms)}.")
    except Exception as e:
        log(f"No se pudo guardar el enfriamiento de cuota: {type(e).__name__}: {e}")


def run_backfill(sb, access_token, now_ms, backfill_hours):
    """Barrido UNICO por fecha (busqueda 'after:' de Gmail, granularidad de
    dia), pensado para completar historial que el checkpoint incremental ya
    dejo atras. A proposito NO toca 'gmail_history_id' ni 'last_run': es
    independiente de la maquinaria incremental, para no arriesgar el estado
    de las corridas automaticas."""
    error_msg = None
    processed = 0
    try:
        window_start_ms = now_ms - int(backfill_hours * 3600 * 1000)
        after_epoch_s = int(window_start_ms / 1000) - 86400  # 1 dia de margen (Gmail "after:" es por dia)
        query = f"after:{after_epoch_s}"
        message_ids = gmail_list_message_ids(access_token, query)
        log(f"[BACKFILL] Candidatos ({query}, ultimas {backfill_hours}h): {len(message_ids)}")

        processed = process_candidate_messages(
            access_token, sb, message_ids,
            window_start_ms=window_start_ms,
            window_end_ms=now_ms + 5 * 60 * 1000,
            prefilter_headers=True,
        )
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


def run_incremental(sb, access_token, now_ms):
    """Corrida normal: incremental por historyId (Gmail API) una vez que
    existe checkpoint, o bootstrap la primera vez que corre el proyecto (o
    si el checkpoint ya quedo demasiado viejo y Gmail purgo ese historial).

    El bootstrap NO reprocesa mails viejos: la casilla nueva arranca vacia de
    verdad (el historial previo ya esta migrado en Supabase desde la casilla
    anterior), asi que alcanza con establecer el punto de partida."""
    last_history_id = None
    try:
        raw = sb.get_meta("gmail_history_id")
        if raw is not None:
            last_history_id = str(raw)
    except Exception as e:
        log(f"No se pudo leer el ultimo checkpoint (gmail_history_id) de la base: {type(e).__name__}: {e}")

    error_msg = None
    processed = 0
    new_history_id = last_history_id

    try:
        if last_history_id is not None:
            try:
                message_ids, new_history_id = gmail_list_history_message_ids(access_token, last_history_id)
                log(f"Candidatos nuevos (history desde {last_history_id}): {len(message_ids)}")
                processed = process_candidate_messages(access_token, sb, message_ids, prefilter_headers=False)
            except HistoryIdTooOldError:
                log("[historyId] El checkpoint ya era muy viejo (Gmail lo purgo) — se re-establece el punto de partida, sin reprocesar historial.")
                profile = gmail_api_get(access_token, "/profile")
                new_history_id = profile.get("historyId")
        else:
            profile = gmail_api_get(access_token, "/profile")
            new_history_id = profile.get("historyId")
            log(f"Primera corrida (sin checkpoint) - estableciendo punto de partida en historyId={new_history_id}, sin procesar historial previo.")
    except Exception as e:
        error_msg = f"{type(e).__name__}: {e}"
        log(f"ERROR durante la corrida: {error_msg}")
        if is_quota_error(e):
            set_quota_cooldown(sb, now_ms)

    if new_history_id is not None and str(new_history_id) != str(last_history_id):
        try:
            sb.set_meta("gmail_history_id", str(new_history_id))
        except Exception as e:
            log(f"No se pudo guardar el checkpoint de historyId: {type(e).__name__}: {e}")

    try:
        sb.set_meta("last_run", {
            "timestamp": now_ms,
            "historyId": new_history_id,
            "processed": processed,
            "error": error_msg,
        })
    except Exception as e:
        log(f"No se pudo guardar el estado de la corrida: {type(e).__name__}: {e}")

    log(f"Listo. Mails procesados: {processed}.")
    if error_msg:
        log(f"Con errores: {error_msg}")


def run_provision_users(sb, mapping_text):
    # Alta de usuarios para el login. mapping_text: pares "usuario:codigo"
    # separados por coma, punto y coma y/o salto de linea (se admite
    # cualquier combinacion, porque el campo de workflow_dispatch en la web
    # de GitHub es de una sola linea y pegar texto con saltos de linea ahi
    # puede romperse). Se pega como input del workflow al momento de
    # correrlo, nunca se commitea a git. Cada codigo se enmascara del log de
    # GitHub Actions apenas se lee, asi nunca queda expuesto ni siquiera en
    # la corrida.
    lines = [ln.strip() for ln in re.split(r"[,;\n]+", mapping_text) if ln.strip()]
    ok, failed = 0, 0
    for line in lines:
        if ":" not in line:
            log(f"[provision] linea invalida (esperaba usuario:codigo): {line!r}")
            failed += 1
            continue
        username, code = line.split(":", 1)
        username = username.strip()
        code = code.strip()
        if not username or not code:
            failed += 1
            continue
        # Enmascara el codigo ANTES de cualquier otra cosa: si algo de esto
        # se llegara a imprimir mas adelante por error, GitHub lo reemplaza
        # por *** en el log.
        print(f"::add-mask::{code}")
        email_addr = f"{username.lower()}@{AUTH_EMAIL_DOMAIN}"
        try:
            user_id = sb.create_auth_user(email_addr, code, username)
            sb.upsert_profile(user_id, username)
            log(f"[provision] {username}: OK")
            ok += 1
        except Exception as e:
            log(f"[provision] {username}: ERROR {type(e).__name__}: {e}")
            failed += 1
    log(f"[provision] Listo. OK: {ok}, con error: {failed}.")


def run_reset_password(sb, mapping_text):
    # Mismo formato que provision_users ("usuario:codigo_temporal"), pero
    # para usuarios que YA existen y se olvidaron la contraseña. No hace
    # falta (ni es posible) conocer la contraseña vieja: se pisa por una
    # nueva temporal y se lo obliga a cambiarla en el proximo login.
    lines = [ln.strip() for ln in re.split(r"[,;\n]+", mapping_text) if ln.strip()]
    ok, failed = 0, 0
    for line in lines:
        if ":" not in line:
            log(f"[reset] linea invalida (esperaba usuario:codigo): {line!r}")
            failed += 1
            continue
        username, code = line.split(":", 1)
        username = username.strip()
        code = code.strip()
        if not username or not code:
            failed += 1
            continue
        print(f"::add-mask::{code}")
        try:
            user_id = sb.get_user_id_by_username(username)
            if not user_id:
                log(f"[reset] {username}: no existe ese usuario")
                failed += 1
                continue
            sb.reset_user_password(user_id, code)
            log(f"[reset] {username}: OK")
            ok += 1
        except Exception as e:
            log(f"[reset] {username}: ERROR {type(e).__name__}: {e}")
            failed += 1
    log(f"[reset] Listo. OK: {ok}, con error: {failed}.")


# ---------------------------------------------------------------------------
# Fixture de equipos de futbol (widget del dashboard, solo para algunos
# usuarios puntuales, cada uno con SU equipo). Se actualiza como mucho una
# vez por semana (los lunes, hora Argentina), leyendo la pagina publica de
# Promiedos. Si el scraping falla por lo que sea (la pagina cambio de
# estructura, no responde, etc.) simplemente se loguea el error y se sigue
# de largo — nunca debe romper la corrida normal de clasificacion de mails.
# ---------------------------------------------------------------------------

# Cada equipo tiene su URL de Promiedos y su propia clave en la tabla "meta"
# (fixture_<team>), para que cada usuario vea el fixture de su propio equipo
# sin pisarse entre ellos.
TEAM_FIXTURES = {
    "boca": "https://www.promiedos.com.ar/team/boca-juniors/igg",
    "river": "https://www.promiedos.com.ar/team/river-plate/igi",
    "belgrano": "https://www.promiedos.com.ar/team/belgrano/fhid",
}
BOCA_DATE_RE = re.compile(r"^\d{2}/\d{2}$")
BOCA_LV_RE = re.compile(r"^[LV]$")
BOCA_TIME_RE = re.compile(r"^\d{1,2}:\d{2}$")
BOCA_SCORE_RE = re.compile(r"^\d+\s*-\s*\d+$")


def _html_to_lines(raw_html):
    # Sin dependencias externas (no hay BeautifulSoup instalado): saca
    # scripts/estilos, convierte cierres de fila/celda/salto de linea en
    # saltos de linea reales, tira el resto de las etiquetas, y devuelve
    # las lineas de texto visibles, sin vacias.
    html_clean = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", raw_html)
    html_clean = re.sub(r"(?i)<(br|/tr|/td|/div|/li|/p)\s*/?>", "\n", html_clean)
    html_clean = re.sub(r"<[^>]+>", "", html_clean)
    html_clean = html.unescape(html_clean)
    lines = [ln.strip() for ln in html_clean.splitlines()]
    return [ln for ln in lines if ln]


def _find_section(lines, start_pattern, end_patterns):
    start_re = re.compile(start_pattern, re.IGNORECASE)
    start_idx = None
    for i, ln in enumerate(lines):
        if start_re.search(ln):
            start_idx = i + 1
            break
    if start_idx is None:
        return []
    end_res = [re.compile(p, re.IGNORECASE) for p in end_patterns]
    end_idx = len(lines)
    for i in range(start_idx, len(lines)):
        if any(er.search(lines[i]) for er in end_res):
            end_idx = i
            break
    return lines[start_idx:end_idx]


def _parse_boca_rows(section_lines, last_field_re, max_rows=5):
    rows = []
    i = 0
    while i < len(section_lines) and len(rows) < max_rows:
        if BOCA_DATE_RE.match(section_lines[i]):
            if i + 3 < len(section_lines):
                dia, lv, rival, last = section_lines[i:i + 4]
                if BOCA_LV_RE.match(lv) and last_field_re.match(last.replace(" ", "")):
                    rows.append({"dia": dia, "lv": lv, "rival": rival, "valor": last.replace(" ", "")})
                    i += 4
                    continue
        i += 1
    return rows


def scrape_team_fixture(team_url):
    req = urllib.request.Request(
        team_url,
        headers={"User-Agent": "Mozilla/5.0 (compatible; ResumenLabBot/1.0)"},
    )
    with urllib.request.urlopen(req, timeout=20) as resp:
        raw_html = resp.read().decode("utf-8", errors="replace")

    lines = _html_to_lines(raw_html)
    proximos_section = _find_section(lines, r"PR[OÓ]XIMOS PARTIDOS", [r"^VER\s+M[AÁ]S$", r"^Resultados$"])
    resultados_section = _find_section(lines, r"^Resultados$", [r"^VER\s+M[AÁ]S$", r"PLANTEL"])

    proximos = _parse_boca_rows(proximos_section, BOCA_TIME_RE)
    resultados = _parse_boca_rows(resultados_section, BOCA_SCORE_RE)

    if not proximos and not resultados:
        raise ValueError("no se pudo extraer ningun partido (la pagina puede haber cambiado de estructura)")

    return {
        "proximos": [{"dia": r["dia"], "lv": r["lv"], "rival": r["rival"], "hora": _correct_fixture_hora(r["valor"])} for r in proximos],
        "resultados": [{"dia": r["dia"], "lv": r["lv"], "rival": r["rival"], "resultado": r["valor"]} for r in resultados],
    }


# Promiedos muestra el horario de los partidos segun la ubicacion/huso
# horario de quien pide la pagina, no el de Argentina. El servidor de
# GitHub Actions no esta en Argentina, asi que el horario que devuelve la
# pagina viene corrido. Comprobado empiricamente (comparando contra lo que
# ve un usuario real en su navegador en Argentina): siempre +2 horas. Se
# asume el mismo desfase para cualquier equipo (depende del servidor que
# pide la pagina, no del equipo).
FIXTURE_HORA_CORRECTION_HOURS = 2


def _correct_fixture_hora(hora_str):
    m = re.match(r"^(\d{1,2}):(\d{2})$", hora_str)
    if not m:
        return hora_str
    h, mnt = int(m.group(1)), int(m.group(2))
    h = (h + FIXTURE_HORA_CORRECTION_HOURS) % 24
    return f"{h:02d}:{mnt:02d}"


def update_team_fixture(sb, now_ms, team, team_url, force=False):
    dt_arg = datetime.fromtimestamp(now_ms / 1000, tz=timezone.utc) - timedelta(hours=3)
    if not force and dt_arg.weekday() != 0:  # 0 = lunes
        return
    today_str = dt_arg.strftime("%Y-%m-%d")
    checkpoint_key = f"fixture_{team}_last_monday"
    try:
        last_monday = sb.get_meta(checkpoint_key)
    except Exception as e:
        log(f"[fixture:{team}] no se pudo leer checkpoint: {type(e).__name__}: {e}")
        last_monday = None
    if not force and last_monday == today_str:
        return  # ya se actualizo este lunes

    try:
        data = scrape_team_fixture(team_url)
        data["updated_at"] = now_ms
        sb.set_meta(f"fixture_{team}", data)
        sb.set_meta(checkpoint_key, today_str)
        log(f"[fixture:{team}] actualizado: {len(data['proximos'])} proximos, {len(data['resultados'])} resultados")
    except Exception as e:
        log(f"[fixture:{team}] ERROR actualizando: {type(e).__name__}: {e}")


def update_all_fixtures(sb, now_ms, force=False):
    for team, team_url in TEAM_FIXTURES.items():
        update_team_fixture(sb, now_ms, team, team_url, force=force)


def main():
    supabase_url = os.environ.get("SUPABASE_URL")
    supabase_key = os.environ.get("SUPABASE_SERVICE_ROLE_KEY")
    now_ms = int(time.time() * 1000)

    provision_users_raw = os.environ.get("PROVISION_USERS") or ""
    if provision_users_raw.strip():
        if not supabase_url or not supabase_key:
            log("ERROR: faltan SUPABASE_URL / SUPABASE_SERVICE_ROLE_KEY para aprovisionar usuarios")
            sys.exit(0)
        sb = SupabaseClient(supabase_url, supabase_key)
        run_provision_users(sb, provision_users_raw)
        return

    reset_password_raw = os.environ.get("RESET_PASSWORD") or ""
    if reset_password_raw.strip():
        if not supabase_url or not supabase_key:
            log("ERROR: faltan SUPABASE_URL / SUPABASE_SERVICE_ROLE_KEY para resetear contraseñas")
            sys.exit(0)
        sb = SupabaseClient(supabase_url, supabase_key)
        run_reset_password(sb, reset_password_raw)
        return

    gmail_client_id = os.environ.get("GMAIL_OAUTH_CLIENT_ID")
    gmail_client_secret = os.environ.get("GMAIL_OAUTH_CLIENT_SECRET")
    gmail_refresh_token = os.environ.get("GMAIL_OAUTH_REFRESH_TOKEN")
    now_ms = int(time.time() * 1000)

    missing = [
        name for name, val in [
            ("GMAIL_OAUTH_CLIENT_ID", gmail_client_id),
            ("GMAIL_OAUTH_CLIENT_SECRET", gmail_client_secret),
            ("GMAIL_OAUTH_REFRESH_TOKEN", gmail_refresh_token),
            ("SUPABASE_URL", supabase_url), ("SUPABASE_SERVICE_ROLE_KEY", supabase_key),
        ] if not val
    ]
    if missing:
        log(f"ERROR: faltan variables de entorno: {', '.join(missing)}")
        sys.exit(0)

    sb = SupabaseClient(supabase_url, supabase_key)

    try:
        access_token = get_access_token(gmail_client_id, gmail_client_secret, gmail_refresh_token)
    except Exception as e:
        log(f"ERROR: no se pudo obtener el access token de Gmail API: {type(e).__name__}: {e}")
        sys.exit(0)

    # Widgets de fixture de equipos (solo se actualizan los lunes; no-op el
    # resto de los dias, salvo que se fuerce con BOCA_FORCE_UPDATE=1 para
    # probar). Nunca debe frenar la corrida de mails si falla.
    try:
        force_fixtures = (os.environ.get("BOCA_FORCE_UPDATE") or "").strip().lower() in ("1", "true", "yes")
        update_all_fixtures(sb, now_ms, force=force_fixtures)
    except Exception as e:
        log(f"[fixture] ERROR inesperado: {type(e).__name__}: {e}")

    try:
        cooldown_until = sb.get_meta("quota_cooldown_until")
    except Exception as e:
        cooldown_until = None
        log(f"No se pudo leer el enfriamiento de cuota: {type(e).__name__}: {e}")

    if cooldown_until is not None and now_ms < int(cooldown_until):
        remaining_min = int((int(cooldown_until) - now_ms) / 60000)
        log(f"[CUOTA] Todavia en enfriamiento (quedan ~{remaining_min} min). Se saltea esta corrida.")
        return

    backfill_hours_raw = (os.environ.get("BACKFILL_HOURS") or "").strip()
    if backfill_hours_raw:
        try:
            backfill_hours = float(backfill_hours_raw)
            run_backfill(sb, access_token, now_ms, backfill_hours)
            return
        except ValueError:
            log(f"BACKFILL_HOURS invalido: {backfill_hours_raw!r}, se ignora y corre normal")

    run_incremental(sb, access_token, now_ms)


if __name__ == "__main__":
    main()
