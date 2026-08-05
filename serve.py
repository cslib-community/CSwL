#!/usr/bin/env python3
"""Serve localmente a versão web do livro gerada pelo Verso.

Uso:

    ./build-web.sh      # gera o HTML
    ./serve.py          # serve em http://localhost:8000/
    ./serve.py 9000     # em outra porta

O site é estático e autocontido: dá para simplesmente abrir os arquivos, mas
alguns recursos (busca, links relativos) só funcionam servidos por HTTP.
"""

import os
from functools import partial
from http.server import SimpleHTTPRequestHandler, HTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
SITE = os.path.join(HERE, '.lake', 'build', 'literate-html')


class Handler(SimpleHTTPRequestHandler):
    def do_GET(self):
        # Evita mensagens de erro espúrias por causa de /favicon.ico
        if self.path == '/favicon.ico' and not os.path.exists(
                os.path.join(SITE, 'favicon.ico')):
            self.send_response(204)
            self.end_headers()
            return
        super().do_GET()

    def log_message(self, fmt, *args):
        # Silencia 200s; mostra só o que deu errado.
        status = args[1] if len(args) > 1 else ''
        if not str(status).startswith('2'):
            super().log_message(fmt, *args)


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('port', default=8000, type=int, nargs='?',
                        help='porta (padrão: %(default)s)')
    args = parser.parse_args()

    if not os.path.isdir(SITE):
        raise SystemExit(
            f"{SITE} não existe.\nRode ./build-web.sh antes de servir.")

    handler = partial(Handler, directory=SITE)
    with HTTPServer(("", args.port), handler) as httpd:
        print(f"Servindo {SITE}")
        print(f"        em http://localhost:{args.port}/")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print()
