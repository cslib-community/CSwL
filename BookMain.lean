import VersoManual
import Book
import CSwLMeta.Run

open Verso Genre Manual

/-- Executable `cswl-book`: builds the book in one variant.

    `lake exe cswl-book <variant>`, with `variant` in
    `student | solutions | terse | grading`; output goes to
    `_out/<variant>/{html,lean}`. In practice, use the `Makefile`
    (`make student`, `make all`, ...). -/
def main (args : List String) : IO UInt32 :=
  CSwLMeta.runBook (%doc Book) args
