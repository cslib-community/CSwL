import CSwLMeta
import CSwLCompat
import Bib
import Mathlib.Data.List.Chain
import CSwL.Games.SeaBattle
import CSwL.Games.Mastermind

import VersoManual

open Verso Genre Manual

-- Capítulo "cola": reúne, via `{include 1 ...}`, duas linguagens de jogo
-- como primeiros exemplos de gramática.
#doc (Manual) "Gramáticas para jogos" =>
%%%
tag := "Games"
htmlSplit := .never
file := "Games"
%%%

O capítulo trata de como definir uma língua — no sentido amplo: um conjunto de strings bem formadas — por meio de uma gramática. Os dois exemplos são  de linguagens sobre jogos.

{include 1 CSwL.Games.SeaBattle}

{include 1 CSwL.Games.Mastermind}
