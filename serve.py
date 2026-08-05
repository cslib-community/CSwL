#!/usr/bin/env python3
"""Serve localmente a versão web do projeto, no mesmo arranjo do GitHub Pages.

    /           o livro gerado pelo Verso   (.lake/build/literate-html/)
    /docs/      a referência de API doc-gen4 (.lake/build/doc/)

Uso:

    ./build-web.sh      # gera as duas saídas
    ./serve.py          # serve em http://localhost:8000/
    ./serve.py 9000     # em outra porta

O site é estático e autocontido: dá para simplesmente abrir os arquivos, mas
alguns recursos (busca, links relativos) só funcionam servidos por HTTP.

A documentação é opcional: se `.lake/build/doc/` não existir (só rodou
`lake build :literateHtml`), o livro é servido normalmente e /docs/ dá 404.
"""

import os
import posixpath
import urllib.parse
from functools import partial
from http.server import SimpleHTTPRequestHandler, HTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
BOOK = os.path.join(HERE, '.lake', 'build', 'literate-html')
DOCS = os.path.join(HERE, '.lake', 'build', 'doc')


class Handler(SimpleHTTPRequestHandler):
    def translate_path(self, path):
        # As duas saídas ficam em diretórios separados do `.lake`; aqui elas são
        # montadas sob a mesma raiz, como no site publicado. Sem cópia: o que o
        # `lake` gerou é servido de onde está.
        clean = urllib.parse.urlsplit(path).path
        clean = urllib.parse.unquote(clean, errors='surrogatepass')
        clean = posixpath.normpath(clean)
        if clean == '/docs' or clean.startswith('/docs/'):
            rel = clean[len('/docs'):]
            # Descarta '' e '..' — nada de escapar do diretório servido.
            parts = [p for p in rel.split('/')
                     if p and p not in (os.curdir, os.pardir)]
            return os.path.join(DOCS, *parts)
        return super().translate_path(path)

    def do_GET(self):
        # Evita mensagens de erro espúrias por causa de /favicon.ico
        if self.path == '/favicon.ico' and not os.path.exists(
                os.path.join(BOOK, 'favicon.ico')):
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

    if not os.path.isdir(BOOK):
        raise SystemExit(
            f"{BOOK} não existe.\nRode ./build-web.sh antes de servir.")

    handler = partial(Handler, directory=BOOK)
    with HTTPServer(("", args.port), handler) as httpd:
        print(f"Servindo  /       {BOOK}")
        if os.path.isdir(DOCS):
            print(f"          /docs/  {DOCS}")
        else:
            print(f"          /docs/  (ausente: rode `lake build CSwL:docs`)")
        print(f"       em http://localhost:{args.port}/")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print()
