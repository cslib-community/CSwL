import VersoManual
import Book
import CSwLMeta.Run

open Verso Genre Manual

/-- Executável `cswl-book`: gera o livro numa variante.

    `lake exe cswl-book <variante>`, com `variante` em
    `student | solutions | terse | grading`; a saída vai para
    `_out/<variante>/{html-multi,lean}`. Na prática use o `Makefile`
    (`make student`, `make all`, ...). -/
def main (args : List String) : IO UInt32 :=
  CSwLMeta.runBook (%doc Book) args
