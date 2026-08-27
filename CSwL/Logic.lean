import CSwLMeta
import Bib
import CSwL.Logic.PL
import CSwL.Logic.FOL

import VersoManual

open Verso Genre Manual

-- Capítulo "cola": reúne, via `{include 1 ...}`, lógica proposicional e
-- lógica de predicados — a ferramenta básica que os fragmentos de inglês do
-- capítulo anterior vão usar para representar significado.
#doc (Manual) "Lógica" =>
%%%
tag := "Logic"
htmlSplit := .never
file := "Logic"
%%%

Como preparação para a semântica de fragmentos de inglês, introduzimos a
lógica proposicional e a lógica de predicados, e mostramos como
implementar sua sintaxe em Lean.

{include 1 CSwL.Logic.PL}

{include 1 CSwL.Logic.FOL}
