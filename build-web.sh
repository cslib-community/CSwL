#!/bin/bash

# Gera localmente as duas saídas web do projeto — as mesmas que o workflow
# `.github/workflows/pages.yml` publica no GitHub Pages:
#
#   .lake/build/literate-html/   o livro (Verso), a partir dos arquivos `.lean`
#   .lake/build/doc/             a referência de API (doc-gen4)
#
# Para ver no navegador (o `serve.py` junta as duas, a documentação em /docs/):
#
#     ./serve.py
#
# Configuração do site (títulos, ordem dos capítulos): `literate.toml`.

set -e -o pipefail   # para no primeiro comando que falhar

cd "$(dirname "$0")"

lake exe cache get        # cache de Mathlib, para não recompilá-la
lake build                # a biblioteca em si tem de compilar primeiro
lake build CSwL:docs      # referência de API  ->  .lake/build/doc/
lake query :literateHtml  # livro              ->  .lake/build/literate-html/
