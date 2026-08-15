import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

/-
TEMPORÁRIO — apagar quando o primeiro capítulo real for convertido.

Este arquivo existe só para que o executável `cswl-book` tenha um `#doc
(Manual)` para gerar: os quatro capítulos ainda estão no gênero `Literate` e
serão convertidos um a um. Ele exercita, de ponta a ponta, os quatro mecanismos
que a migração depende — prosa, `:::exercise` com `solution!`, `:::gradeTheorem`,
`::::quiz`/`:::quizSolution` e `{citep}` — de modo que `make student` continua
sendo uma verificação real do pipeline enquanto não houver capítulo convertido.

Quando o `CSwL/Chapter01.lean` virar `#doc (Manual)`: trocar, em `Book.lean`, o
`import`/`{include}` deste arquivo pelo do capítulo, e apagar este arquivo.

Fica em `CSwL/` (e não numa pasta própria) de propósito: o extrator usa o
caminho do arquivo-fonte do capítulo, `CSwL/<file>.lean`, tanto como chave do
buffer quanto para reler o cabeçalho de `import`s do capítulo e reconstruí-lo no
projeto gerado. Um capítulo fora de `CSwL/` perderia seus `import`s na extração.
-/

#doc (Manual) "Placeholder (temporário)" =>
%%%
tag := "placeholder"
htmlSplit := .never
file := "Placeholder"
%%%

Este capítulo é andaime de migração, não conteúdo do curso: ele só prova que o
livro no gênero `Manual` gera as quatro variantes. Veja o comentário no topo de
`CSwL/Placeholder.lean`.

# Prosa, citação e exercício

Um parágrafo qualquer, com uma citação de verdade contra o `Bib.lean`:
{citep Bib.love2026}[].

::::exercise (rating := 1) (name := "placeholder")

Prove que `1 + 1 = 2`.

```lean
theorem placeholderThm : 1 + 1 = 2 := solution!(by decide)
```

:::gradeTheorem "1" placeholderThm
:::
::::

::::quiz
Para que serve este capítulo?

:::quizSolution
Só para verificar o pipeline das quatro variantes enquanto nenhum capítulo real
foi convertido.
:::
::::
