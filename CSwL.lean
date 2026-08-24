/-!
# Semântica computacional com Lean

Tradução para Lean de van Eijck & Unger, *Computational Semantics with
Functional Programming* (CUP, 2010).

Raiz da biblioteca `CSwL`, gênero `Literate`. Os quatro capítulos do livro
migraram para o gênero `Manual` (ver `Book.lean`); nenhum capítulo resta
aqui para importar. O pipeline `Literate`/`build-web.sh` foi aposentado em
16/08 (`literate.toml` e `serve.py` removidos); este arquivo só permanece
porque é o módulo raiz exigido pelo `[[lean_lib]] name = "CSwL"` do
`lakefile.toml`, que a biblioteca `Book`/doc-gen4 ainda usa.
-/
