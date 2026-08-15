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
-- Os quatro capítulos do livro estão todos convertidos. O `literate.toml`/
-- `build-web.sh` (gênero `Literate`) ainda existe, mas sem capítulo nenhum
-- para varrer — ver pendência no README da raiz sobre aposentar o pipeline.
#doc (Manual) "Semântica computacional com Lean" =>
{include CSwL.Chapter01}
{include CSwL.Chapter02}
{include CSwL.Chapter03}
{include CSwL.Chapter04}
