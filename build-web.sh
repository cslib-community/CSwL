#!/bin/bash

# Gera a versão web (HTML) do livro a partir dos mesmos arquivos `.lean`.
# A saída fica em `.lake/build/literate-html/`; para ver no navegador:
#
#     ./serve.py
#
# Configuração do site (títulos, ordem dos capítulos): `literate.toml`.

set -e -o pipefail   # para no primeiro comando que falhar

cd "$(dirname "$0")"

lake exe cache get     # cache de Mathlib, para não recompilá-la
lake build             # a biblioteca em si tem de compilar primeiro
lake query :literateHtml
