import CSwLMeta
import Bib

import CSwL.IntroCS
import CSwL.IntroL
import CSwL.Applications
import CSwL.Foundation
import CSwL.Games
import CSwL.English
import CSwL.Logic

import VersoManual

open Verso Genre Manual

set_option verso.code.warnLineLength 80

-- Raiz do livro no gênero `Manual`. Para acrescentar um capítulo: um
-- `import CSwL.Nome` acima e um `{include CSwL.Nome}` abaixo, na ordem do
-- livro. (O corpo do `#doc` não tem sintaxe de comentário — não escreva
-- comentários entre os `{include}`.) Um capítulo pode ser um arquivo único
-- (`IntroCS`, `Foundation`) ou um arquivo "cola" que reúne seções em
-- arquivo próprio via `{include 1 ...}` (ver `Applications.lean`).
--
-- O pipeline `Literate`/`build-web.sh` foi aposentado em 16/08 (ver
-- `CSwL.lean`); o livro sai só por aqui, nas quatro variantes de
-- `make all`/`Makefile`.
#doc (Manual) "Semântica computacional com Lean" =>
{include CSwL.IntroCS}
{include CSwL.IntroL}
{include CSwL.Applications}
{include CSwL.Foundation}
{include CSwL.Games}
{include CSwL.English}
{include CSwL.Logic}
