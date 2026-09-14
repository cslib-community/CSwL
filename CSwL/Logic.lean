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
file := "Logic"
%%%

O capítulo tem três seções. Em {ref "Proof"}[Proof] vamos usar Lean como assistente de prova, entendendo como usar o tipo `Prop` e como construir provas de proposições a partir de termos ou táticas. Em {ref "PL"}[PL] trataremos da implementação de lógica proposicional usando Lean como linguagem de programação, daremos a sintática e semântica de PL. Finalmente, em {ref "FOL"}[FOL], vamos implementar a lógica de predicados, novamente com sua sintaxe e semântica computável.

{include 1 CSwL.Logic.Proof}

{include 1 CSwL.Logic.PL}

{include 1 CSwL.Logic.FOL}
