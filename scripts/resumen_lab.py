#!/usr/bin/env python3
"""
Resumen LAB - lee la casilla de Gmail por IMAP, categoriza los mails nuevos
y actualiza el bloque <script id="resumen-data" type="application/json">
dentro de index.html (mismo formato que usa el artifact de Cowork / la
página en Vercel).

Corre desde GitHub Actions cada 6hs, usando GMAIL_USER / GMAIL_APP_PASSWORD
como variables de entorno (secrets del repo). No depende de la computadora
del usuario ni de que Cowork esté abierto.
"""

import email
import email.utils
import imaplib
import json
import os
import re
import sys
import time
from datetime import datetime, timedelta, timezone
from email.header import decode_header

IMAP_HOST = "imap.gmail.com"
INDEX_HTML_PATH = os.path.join(os.path.dirname(__file__), "..", "index.html")
PRUNE_DAYS = 30
IT_ING_AGE_HOURS_THRESHOLD = 5  # informational only; real split happens client-side in the page

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


def log(msg):
    print(msg, flush=True)


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
    return "\n".join(chunks)


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


# Cache por corrida (el proceso arranca de cero cada vez que corre el
# workflow): evita pedir el thread id dos veces para el mismo mail cuando
# tanto classify() como classify_escalamientos_it() lo necesitan.
_THRID_CACHE = {}


def gm_thread_id_hex(imap, uid):
    """Fetch Gmail's X-GM-THRID extension y lo devuelve en hex. Es UNA sola
    consulta extra por mail (no recorre el resto del hilo) — se usa solo
    como clave estable para agrupar respuestas del mismo hilo a lo largo
    de corridas, no para recalcular fechas viejas."""
    uid_key = uid.decode() if isinstance(uid, bytes) else uid
    if uid_key in _THRID_CACHE:
        return _THRID_CACHE[uid_key]
    try:
        typ, data = imap.uid("fetch", uid, "(X-GM-THRID)")
        if typ != "OK" or not data or not data[0]:
            _THRID_CACHE[uid_key] = None
            return None
        raw = data[0]
        if isinstance(raw, bytes):
            raw = raw.decode(errors="replace")
        m = re.search(r"X-GM-THRID\s+(\d+)", raw)
        if not m:
            _THRID_CACHE[uid_key] = None
            return None
        thrid_int = int(m.group(1))
        result = format(thrid_int, "x")
        _THRID_CACHE[uid_key] = result
        return result
    except Exception as e:
        log(f"[gm_thread_id_hex] uid={uid} excepcion: {type(e).__name__}: {e}")
        _THRID_CACHE[uid_key] = None
        return None


def fetch_message(imap, uid):
    typ, data = imap.uid("fetch", uid, "(RFC822)")
    if typ != "OK" or not data or not data[0]:
        return None
    raw = data[0][1]
    return email.message_from_bytes(raw)


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


def classify_escalamientos_it(imap, uid, subject, body, recipients_text, own_ms):
    """Solapa 'Escalamientos IT': cualquier mail (de cualquier remitente)
    enviado a Gestion de Incidentes / Help Desk / Help Desk Billetera.
    Independiente de la clasificacion principal (puede coexistir con ella).
    El origen real del hilo se arma solo, mail a mail, con el "firstSeen"
    minimo que va viendo cada corrida (ver merge_result en main) — no hace
    falta re-bajar el hilo entero para saberlo."""
    if not is_it_escalation_recipient(recipients_text):
        return None
    thrid = gm_thread_id_hex(imap, uid)
    origin_ms = own_ms
    quoted_ms = earliest_quoted_date_ms(body)
    if quoted_ms:
        origin_ms = min(origin_ms, quoted_ms)
    return {
        "category": "escalamientosIT", "timestamp": own_ms, "firstSeen": origin_ms,
        "subject": subject, "thread_id": thrid,
    }


def classify(imap, uid, msg):
    subject = decode_mime_header(msg.get("Subject")) or ""
    sender_raw = decode_mime_header(msg.get("From")) or ""
    sender_name, sender_addr = email.utils.parseaddr(sender_raw)
    sender_addr = (sender_addr or "").lower()
    to_text = addr_list_text(msg, "To").lower()
    cc_text = addr_list_text(msg, "Cc").lower()
    recipients_text = to_text + " " + cc_text
    body = get_body_text(msg)
    subject_lower = subject.lower()
    own_ms = epoch_ms_from_date_header(msg)

    # 1. Tareas (WBS)
    if WBS_RE.search(subject) or WBS_RE.search(body):
        return {"category": "tareas", "timestamp": own_ms, "subject": subject}

    # 2. Afectaciones masivas
    # "resolved" se acumula mail a mail: si ESTE mensaje puntual tiene la
    # palabra de cierre, se marca resuelto (y merge_result en main() hace
    # que, una vez resuelto, se quede resuelto aunque no vuelva a aparecer).
    if sender_addr == AFECTACION_MASIVA_SENDER:
        thrid = gm_thread_id_hex(imap, uid)
        resolved = bool(CLOSURE_RE.search(subject) or CLOSURE_RE.search(body))
        return {
            "category": "afectacionMasiva",
            "timestamp": own_ms,
            "subject": subject,
            "resolved": resolved,
            "thread_id": thrid,
        }

    # 3. Reportes Tecnica -> IT / Ingenieria
    # "firstSeen" tambien se acumula mail a mail (ver merge_result): cada
    # corrida aporta como candidato de origen la fecha de ESTE mensaje mas
    # cualquier fecha citada en su cuerpo, y el minimo historico gana. No
    # hace falta re-bajar el hilo completo para saber cuando empezo.
    if REPORTES_TECNICA_HINT in sender_addr:
        matched_it = is_it_escalation_recipient(recipients_text)
        if matched_it:
            thrid = gm_thread_id_hex(imap, uid)
            origin_ms = own_ms
            quoted_ms = earliest_quoted_date_ms(body)
            if quoted_ms:
                origin_ms = min(origin_ms, quoted_ms)
            return {
                "category": "it", "timestamp": own_ms, "firstSeen": origin_ms,
                "subject": subject, "thread_id": thrid,
            }

        matched_ing = any(re.search(r"\b" + re.escape(k) + r"\b", recipients_text) for k in ING_RECIPIENT_KEYWORDS)
        if matched_ing:
            thrid = gm_thread_id_hex(imap, uid)
            origin_ms = own_ms
            quoted_ms = earliest_quoted_date_ms(body)
            if quoted_ms:
                origin_ms = min(origin_ms, quoted_ms)
            return {
                "category": "ingenieria", "timestamp": own_ms, "firstSeen": origin_ms,
                "subject": subject, "thread_id": thrid,
            }

        # 5. Informes (subject-based, sender is reportestecnica in practice)
        if "informe" in subject_lower:
            if "fija" in subject_lower:
                return {"category": "informesFija", "timestamp": own_ms, "subject": subject}
            if "611" in subject_lower:
                return {"category": "informesMovil", "timestamp": own_ms, "subject": subject}
            log(f"[sin clasificar] Informe con patron desconocido: {subject!r}")
            return None

    # 4. Pedidos Referentes
    if MARIA_INES_HINT in sender_name.lower() and REPORTES_TECNICA_HINT in recipients_text:
        return {"category": "pedidosReferentes", "timestamp": own_ms, "subject": subject}

    # 5b. Informes desde cualquier otro remitente (por si aparece uno nuevo)
    if "informe" in subject_lower:
        if "fija" in subject_lower:
            return {"category": "informesFija", "timestamp": own_ms, "subject": subject}
        if "611" in subject_lower:
            return {"category": "informesMovil", "timestamp": own_ms, "subject": subject}
        log(f"[sin clasificar] Informe con patron desconocido: {subject!r}")
        return None

    return None


def load_data():
    with open(INDEX_HTML_PATH, "r", encoding="utf-8") as f:
        html = f.read()
    m = re.search(
        r'(<script id="resumen-data" type="application/json">)(.*?)(</script>)',
        html,
        re.DOTALL,
    )
    if not m:
        raise RuntimeError("No se encontró el bloque resumen-data en index.html")
    data = json.loads(m.group(2))
    data.setdefault("mails", [])
    data.setdefault("lastRun", None)
    return html, m, data


def save_data(html, m, data):
    new_json = json.dumps(data, ensure_ascii=False, indent=2)
    new_block = m.group(1) + "\n" + new_json + "\n" + m.group(3)
    new_html = html[: m.start()] + new_block + html[m.end():]
    with open(INDEX_HTML_PATH, "w", encoding="utf-8") as f:
        f.write(new_html)


def prune_mails(mails, now_ms):
    cutoff = now_ms - PRUNE_DAYS * 24 * 3600 * 1000
    kept = []
    for m in mails:
        if m.get("timestamp", 0) >= cutoff:
            kept.append(m)
            continue
        if m.get("category") == "afectacionMasiva" and m.get("resolved") is not True:
            kept.append(m)  # afectación masiva sin resolver: nunca se poda
            continue
        # se poda (queda afuera)
    return kept


def main():
    gmail_user = os.environ.get("GMAIL_USER")
    gmail_pass = os.environ.get("GMAIL_APP_PASSWORD")
    now_ms = int(time.time() * 1000)

    html, match, data = load_data()
    last_run = data.get("lastRun") or {}
    range_from = last_run.get("rangeTo") or (now_ms - 6 * 3600 * 1000)
    # Tope maximo de cuanto se puede volver hacia atras, sin importar que tan
    # vieja sea la ultima corrida GUARDADA. Si una corrida se cuelga y muere
    # antes de escribir "lastRun", la proxima corrida volveria a intentar el
    # mismo backlog enorme, se colgaria de nuevo, y nunca avanzaria (circulo
    # vicioso). Con este tope, en el peor caso se puede perder algun mail
    # viejo si hubo un corte muy largo, pero el script siempre puede terminar.
    MAX_LOOKBACK_MS = 60 * 60 * 1000
    search_window_start = max(range_from, now_ms - MAX_LOOKBACK_MS)

    error_msg = None
    new_or_updated = 0

    if not gmail_user or not gmail_pass:
        error_msg = "Faltan las variables de entorno GMAIL_USER / GMAIL_APP_PASSWORD"
        log(f"ERROR: {error_msg}")
    else:
        try:
            imap = imaplib.IMAP4_SSL(IMAP_HOST, timeout=25)
            imap.login(gmail_user, gmail_pass)
            imap.select("INBOX")

            # IMAP SINCE solo filtra por fecha (sin hora), asi que restamos 1 dia
            # de colchon sobre el inicio real de la ventana para no perder nada
            # por husos horarios, sin volver a bajar 2 dias enteros cada vez.
            since_dt = datetime.fromtimestamp(search_window_start / 1000, tz=timezone.utc) - timedelta(days=1)
            since_date = since_dt.strftime("%d-%b-%Y")
            typ, data_uids = imap.uid("search", None, f'(SINCE {since_date})')
            uids = data_uids[0].split() if typ == "OK" and data_uids and data_uids[0] else []
            log(f"Candidatos encontrados (SINCE {since_date}): {len(uids)}")

            mails_by_id = {m["id"]: m for m in data["mails"]}

            def merge_result(record_id, result, own_ms):
                existing = mails_by_id.get(record_id)
                new_ts = result["timestamp"] if result["timestamp"] is not None else own_ms
                if existing:
                    existing["subject"] = result["subject"]
                    existing["category"] = result["category"]
                    # "timestamp" = ultima actividad conocida (para que el item
                    # se siga mostrando en rangos recientes mientras haya novedades)
                    existing["timestamp"] = max(existing.get("timestamp", 0), new_ts)
                    if "firstSeen" in result:
                        existing["firstSeen"] = min(existing.get("firstSeen", result["firstSeen"]), result["firstSeen"])
                    if "resolved" in result:
                        if result["resolved"] is True:
                            existing["resolved"] = True
                        else:
                            existing.setdefault("resolved", False)
                else:
                    record = {
                        "id": record_id,
                        "timestamp": new_ts,
                        "subject": result["subject"],
                        "category": result["category"],
                    }
                    if "firstSeen" in result:
                        record["firstSeen"] = result["firstSeen"]
                    if "resolved" in result:
                        record["resolved"] = result["resolved"]
                    mails_by_id[record_id] = record

            for uid in uids:
                msg = fetch_message(imap, uid)
                if msg is None:
                    continue
                own_ms = epoch_ms_from_date_header(msg)
                if own_ms is None or own_ms < search_window_start or own_ms > now_ms + 5 * 60 * 1000:
                    continue
                uid_str = uid.decode() if isinstance(uid, bytes) else uid

                result = classify(imap, uid, msg)
                if result is not None:
                    thrid = result.pop("thread_id", None)
                    record_id = thrid or f"uid-{uid_str}"
                    merge_result(record_id, result, own_ms)
                    new_or_updated += 1

                # Solapa "Escalamientos IT": independiente de la clasificacion
                # principal, por eso usa su propio namespace de id (sufijo ':escIT')
                subject = decode_mime_header(msg.get("Subject")) or ""
                to_text = addr_list_text(msg, "To").lower()
                cc_text = addr_list_text(msg, "Cc").lower()
                recipients_text = to_text + " " + cc_text
                body = get_body_text(msg)
                esc_result = classify_escalamientos_it(imap, uid, subject, body, recipients_text, own_ms)
                if esc_result is not None:
                    thrid = esc_result.pop("thread_id", None)
                    esc_record_id = (thrid or f"uid-{uid_str}") + ":escIT"
                    merge_result(esc_record_id, esc_result, own_ms)
                    new_or_updated += 1

            data["mails"] = list(mails_by_id.values())
            imap.logout()
        except Exception as e:
            error_msg = f"{type(e).__name__}: {e}"
            log(f"ERROR durante la corrida: {error_msg}")

    data["mails"] = prune_mails(data["mails"], now_ms)
    data["mails"].sort(key=lambda m: m.get("timestamp", 0), reverse=True)

    data["lastRun"] = {
        "timestamp": now_ms,
        "rangeFrom": range_from,
        "rangeTo": now_ms,
        "error": error_msg,
    }

    save_data(html, match, data)
    log(f"Listo. Mails nuevos/actualizados: {new_or_updated}. Total en log: {len(data['mails'])}.")
    if error_msg:
        sys.exit(0)  # no falla el job igual; el error queda registrado en lastRun


if __name__ == "__main__":
    main()
