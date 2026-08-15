import CSwLMeta
import Bib

import CSwL.Placeholder

import VersoManual

open Verso Genre Manual

-- Raiz do livro no gênero `Manual`. Para acrescentar um capítulo: um
-- `import CSwL.ChapterNN` acima e um `{include CSwL.ChapterNN}` abaixo, na
-- ordem do livro. (O corpo do `#doc` não tem sintaxe de comentário — não
-- escreva comentários entre os `{include}`.)
--
-- Hoje só há o `CSwL.Placeholder`: os quatro capítulos ainda estão no gênero
-- `Literate` e continuam saindo pelo `literate.toml` / `build-web.sh` até
-- serem convertidos, um a um.
#doc (Manual) "Semântica computacional com Lean" =>
{include CSwL.Placeholder}
