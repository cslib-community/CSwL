import CSwLMeta
import Bib

import CSwL.Chapter01

import VersoManual

open Verso Genre Manual

-- Raiz do livro no gênero `Manual`. Para acrescentar um capítulo: um
-- `import CSwL.ChapterNN` acima e um `{include CSwL.ChapterNN}` abaixo, na
-- ordem do livro. (O corpo do `#doc` não tem sintaxe de comentário — não
-- escreva comentários entre os `{include}`.)
--
-- Só o cap. 1 foi convertido até agora; os capítulos 2–4 continuam no gênero
-- `Literate`, saindo pelo `literate.toml` / `build-web.sh` até serem
-- convertidos, um a um.
#doc (Manual) "Semântica computacional com Lean" =>
{include CSwL.Chapter01}
