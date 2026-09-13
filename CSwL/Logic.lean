import CSwLMeta
import Bib
import CSwL.Logic.Proof
import CSwL.Logic.PL
import CSwL.Logic.FOL
import CSwLCompat

import VersoManual

open Verso Genre Manual

-- Capítulo "cola": reúne, via `{include 1 ...}`, a prova em Lean e as duas
-- lógicas — a ferramenta básica com que os fragmentos de inglês
-- representarão significado.
#doc (Manual) "Lógica" =>
%%%
tag := "Logic"
htmlSplit := .never
file := "Logic"
%%%

O capítulo tem três seções. A primeira é sobre provar em Lean: o tipo `Prop`,
o que conta como prova, e as táticas que constroem uma. As outras duas
implementam a lógica proposicional e a de predicados como tipos de dados,
cada uma com sua sintaxe, sua semântica computável, e a ponte entre a fórmula
como dado e a proposição que ela afirma.

{include 1 CSwL.Logic.Proof}

{include 1 CSwL.Logic.PL}

{include 1 CSwL.Logic.FOL}
