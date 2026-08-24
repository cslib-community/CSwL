import CSwLMeta
import Bib

import CSwL.Chapter01
import CSwL.Chapter02
import CSwL.Chapter03
import CSwL.Chapter04

import VersoManual

open Verso Genre Manual

-- Raiz do livro no gênero `Manual`. Para acrescentar um capítulo: um
-- `import CSwL.ChapterNN` acima e um `{include CSwL.ChapterNN}` abaixo, na
-- ordem do livro. (O corpo do `#doc` não tem sintaxe de comentário — não
-- escreva comentários entre os `{include}`.)
--
-- Os quatro capítulos do livro estão todos convertidos. O pipeline
-- `Literate`/`build-web.sh` foi aposentado em 16/08 (ver `CSwL.lean`); o livro
-- sai só por aqui, nas quatro variantes de `make all`/`Makefile`.
#doc (Manual) "Semântica computacional com Lean" =>
{include CSwL.Chapter01}
{include CSwL.Chapter02}
{include CSwL.Chapter03}
{include CSwL.Chapter04}
