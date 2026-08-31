import CSwLMeta
import Bib
import CSwL.IntroL
import CSwL.Morphology.FinnishVowelHarmony
import CSwL.Morphology.SwedishPlural
import CSwL.Morphology.Phonemes

import VersoManual

open Verso Genre Manual

-- `import CSwL.IntroL` aqui (não só em `Morphology/SwedishPlural.lean`, que
-- é quem de fato usa `IntroL.initS`) porque a extração
-- (`CSwLMeta/Save/Project.lean`) só relê o cabeçalho *deste* arquivo — o
-- capítulo — para reconstruir os `import`s do `.lean` gerado; um import só no
-- cabeçalho de uma seção incluída não é visto por ela.
--
-- Capítulo "cola": reúne, via `{include 1 ...}`, as três seções que aplicam o
-- Lean apresentado em `IntroL` a fenômenos linguísticos concretos.
#doc (Manual) "Morfologia" =>
%%%
tag := "Morphology"
htmlSplit := .never
file := "Morphology"
%%%

Três exemplos de PLN que aplicam o Lean visto no capítulo anterior:
harmonia vocálica do finlandês, plural do sueco e uma representação de
fonemas por traços.

{include 1 CSwL.Morphology.FinnishVowelHarmony}

{include 1 CSwL.Morphology.SwedishPlural}

{include 1 CSwL.Morphology.Phonemes}
