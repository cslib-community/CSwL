import CSwLMeta
import Bib

import CSwL.Chapter01
import CSwL.Chapter02
import CSwL.Chapter03

import VersoManual

open Verso Genre Manual

-- Raiz do livro no gênero `Manual`. Para acrescentar um capítulo: um
-- `import CSwL.ChapterNN` acima e um `{include CSwL.ChapterNN}` abaixo, na
-- ordem do livro. (O corpo do `#doc` não tem sintaxe de comentário — não
-- escreva comentários entre os `{include}`.)
--
-- Só os caps. 1–3 foram convertidos até agora; o capítulo 4 continua no
-- gênero `Literate`, saindo pelo `literate.toml` / `build-web.sh` até ser
-- convertido.
#doc (Manual) "Semântica computacional com Lean" =>
{include CSwL.Chapter01}
{include CSwL.Chapter02}
{include CSwL.Chapter03}
