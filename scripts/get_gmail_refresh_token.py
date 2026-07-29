#!/usr/bin/env python3
"""
Herramienta de UNA SOLA VEZ para conseguir el Refresh Token de Gmail API.

No hace falta instalar nada (usa solo la libreria estandar de Python). Se
corre en TU computadora (no en GitHub Actions), porque necesita abrir tu
navegador para que autorices el acceso con la cuenta de Gmail nueva
(resumen.lab.c@gmail.com).

Como usarlo:
  1. Tene a mano el Client ID y el Client Secret que te dio Google Cloud
     Console (Credenciales -> tu ID de cliente de OAuth de escritorio).
  2. Corre: python3 get_gmail_refresh_token.py
  3. Pega el Client ID y el Client Secret cuando te los pida.
  4. Se va a abrir (o te va a dar un link para abrir) tu navegador. Iniciá
     sesion con resumen.lab.c@gmail.com y aceptá el permiso de solo lectura
     de Gmail.
  5. El script imprime el Refresh Token al final. Guardalo como el secret
     de GitHub GMAIL_OAUTH_REFRESH_TOKEN (junto con GMAIL_OAUTH_CLIENT_ID y
     GMAIL_OAUTH_CLIENT_SECRET). NUNCA lo subas a git ni lo compartas.
"""

import http.server
import json
import threading
import urllib.parse
import urllib.request
import webbrowser

REDIRECT_PORT = 8080
REDIRECT_URI = f"http://localhost:{REDIRECT_PORT}/"
SCOPE = "https://www.googleapis.com/auth/gmail.readonly"

_received_code = {}


class _CallbackHandler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        params = urllib.parse.parse_qs(parsed.query)
        if "code" in params:
            _received_code["code"] = params["code"][0]
            body = "Listo, ya podes cerrar esta pestana y volver a la terminal."
        else:
            body = "No se recibio el codigo de autorizacion. Revisa la terminal."
        self.send_response(200)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.end_headers()
        self.wfile.write(body.encode("utf-8"))

    def log_message(self, format, *args):
        pass  # silencia el log de requests en consola


def main():
    client_id = input("Client ID: ").strip()
    client_secret = input("Client Secret: ").strip()

    auth_url = "https://accounts.google.com/o/oauth2/v2/auth?" + urllib.parse.urlencode({
        "client_id": client_id,
        "redirect_uri": REDIRECT_URI,
        "response_type": "code",
        "scope": SCOPE,
        "access_type": "offline",
        "prompt": "consent",
    })

    server = http.server.HTTPServer(("localhost", REDIRECT_PORT), _CallbackHandler)
    server_thread = threading.Thread(target=server.handle_request)
    server_thread.start()

    print("\nAbriendo el navegador para autorizar...")
    print("Si no se abre solo, copia y pega esta URL en tu navegador:\n")
    print(auth_url)
    print("\nIMPORTANTE: iniciar sesion con resumen.lab.c@gmail.com\n")
    webbrowser.open(auth_url)

    server_thread.join(timeout=180)
    code = _received_code.get("code")
    if not code:
        print("No llego el codigo de autorizacion (timeout o cancelado). Volve a correr el script.")
        return

    token_req = urllib.request.Request(
        "https://oauth2.googleapis.com/token",
        data=urllib.parse.urlencode({
            "code": code,
            "client_id": client_id,
            "client_secret": client_secret,
            "redirect_uri": REDIRECT_URI,
            "grant_type": "authorization_code",
        }).encode("utf-8"),
        method="POST",
    )
    with urllib.request.urlopen(token_req, timeout=20) as resp:
        tokens = json.loads(resp.read())

    refresh_token = tokens.get("refresh_token")
    if not refresh_token:
        print("No vino refresh_token en la respuesta. Respuesta completa:")
        print(json.dumps(tokens, indent=2))
        print("\nTip: si ya habias autorizado esta app antes, Google a veces no")
        print("vuelve a mandar el refresh_token. Anda a")
        print("https://myaccount.google.com/permissions , quita el acceso de")
        print("'Resumen Lab Desktop' y volve a correr este script.")
        return

    print("\n" + "=" * 60)
    print("Refresh Token (guardalo como secret GMAIL_OAUTH_REFRESH_TOKEN):")
    print(refresh_token)
    print("=" * 60)


if __name__ == "__main__":
    main()
