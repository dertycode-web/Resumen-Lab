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
IT_RECIPIENT_ADDR_HINTS = ["incidentereportado@claro.com.ar"]
ING_RECIPIENT_KEYWORDS = ["soc", "voc", "noc"]

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
CATEGORIES_NEEDING_THRID = {"afectacionMasiva", "it", "ingenieria", "escalamientosIT"}


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


def get_body_text(msg):
    chunks = []
    if msg.is_multipart():
        for part in msg.walk():
            ctype = part.get_content_type()
            disp = str(part.get("Content-Disposition") or "")
            if "attachment" in disp:
                continue
            if ctype == "text/plain":
                try:
                    chunks.append(part.get_payload(decode=True).decode(part.get_content_charset() or "utf-8", errors="replace"))
                except Exception:
                    pass
            elif ctype == "text/html" and not chunks:
                try:
                    html = part.get_payload(decode=True).decode(part.get_content_charset() or "utf-8", errors="replace")
                    chunks.append(strip_html(html))
                except Exception:
                    pass
    else:
        ctype = msg.get_content_type()
        try:
            payload = msg.get_payload(decode=True).decode(msg.get_content_charset() or "utf-8", errors="replace")
            chunks.append(strip_html(payload) if ctype == "text/html" else payload)
        except Exception:
            pass
    text = "\n".join(chunks)
    if len(text) > MAX_BODY_CHARS:
        text = text[:MAX_BODY_CHARS] + "\n[...cortado...]"
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
    return results


def fetch_headers_batch(imap, uids, chunk_size=150):
    """Solo encabezados (sin cuerpo) — para descartar mails fuera de ventana
    de tiempo sin pagar el costo de bajar el cuerpo completo."""
    return _fetch_literal_batch(imap, uids, "BODY.PEEK[HEADER]", chunk_size)


def fetch_full_batch(imap, uids, chunk_size=100):
    """Mensaje completo (con cuerpo) — solo para los UIDs que realmente vamos
    a clasificar y guardar."""
    return _fetch_literal_batch(imap, uids, "RFC822", chunk_size)


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
# Clasificacion: devuelve una lista de categorias aplicables (un mail puede
# pertenecer a mas de una a la vez, ej. "it" + "escalamientosIT"), mas los
# datos que necesita cada categoria (origen del hilo, cierre detectado).
# No hace NINGUNA consulta IMAP propia — trabaja solo sobre el mensaje ya
# descargado (el X-GM-THRID se resuelve aparte, en lote, en main()).
# ---------------------------------------------------------------------------

def classify(msg):
    subject = decode_mime_header(msg.get("Subject")) or ""
    sender_raw = decode_mime_header(msg.get("From")) or ""
    sender_name, sender_addr = email.utils.parseaddr(sender_raw)
    sender_addr = (sender_addr or "").lower()
    to_text = addr_list_text(msg, "To")
    cc_text = addr_list_text(msg, "Cc")
    recipients_text = (to_text + " " + cc_text).lower()
    body = get_body_text(msg)
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

    # 1. Tareas (WBS)
    if WBS_RE.search(subject) or WBS_RE.search(body):
        categories.append("tareas")

    # 2. Afectaciones masivas
    if sender_addr == AFECTACION_MASIVA_SENDER:
        categories.append("afectacionMasiva")
        closure_detected = bool(CLOSURE_RE.search(subject) or CLOSURE_RE.search(body))

    # 3. Reportes Tecnica -> IT / Ingenieria / Informes
    if REPORTES_TECNICA_HINT in sender_addr:
        if is_it_escalation_recipient(recipients_text):
            categories.append("it")
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

    # 6. "Escalamientos IT": cualquier mail (de cualquier remitente) enviado a
    # Gestion de Incidentes / Help Desk / Help Desk Billetera. Independiente
    # de todo lo anterior, puede coexistir con otra categoria del mismo mail.
    if is_it_escalation_recipient(recipients_text):
        categories.append("escalamientosIT")
        add_origin_candidates()

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


def process_candidate_uids(imap, sb, uids, window_start_ms=None, window_end_ms=None, prefilter_headers=False):
    """Clasifica y guarda en Supabase una lista de UIDs candidatos (ya
    ordenados o no). Si prefilter_headers=True, primero chequea la fecha via
    encabezado liviano (sin cuerpo) y descarta lo que cae fuera de
    [window_start_ms, window_end_ms] ANTES de bajar el mensaje completo —
    asi evita pagar el costo de RFC822 para mails que se van a descartar de
    todas formas. Devuelve la cantidad de mails guardados (con >=1 categoria).
    Puede tirar una excepcion si algun fetch en lote falla (el llamador
    decide que hacer con el checkpoint en ese caso)."""
    if not uids:
        return 0

    uids_sorted = sorted(uids, key=lambda u: int(_uid_str(u)))

    if prefilter_headers:
        headers = fetch_headers_batch(imap, uids_sorted)
        fetch_targets = []
        for u in uids_sorted:
            uid_str = _uid_str(u)
            hmsg = headers.get(uid_str)
            if hmsg is None:
                continue
            h_ms = epoch_ms_from_date_header(hmsg)
            if h_ms is None:
                continue
            if window_start_ms is not None and h_ms < window_start_ms:
                continue
            if window_end_ms is not None and h_ms > window_end_ms:
                continue
            fetch_targets.append(u)
        log(f"Dentro de ventana tras chequear encabezados: {len(fetch_targets)}")
    else:
        fetch_targets = uids_sorted

    full_msgs = fetch_full_batch(imap, fetch_targets)

    results_by_uid = {}
    for u in fetch_targets:
        uid_str = _uid_str(u)
        msg = full_msgs.get(uid_str)
        if msg is None:
            continue
        result = classify(msg)
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
        for category in result["categories"]:
            sb.upsert_mail(record_id, thrid, category, result, result["sent_at_ms"])
        processed += 1

    return processed


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
