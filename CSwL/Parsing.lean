import CSwLMeta
import Bib
import CSwL.Parsing.ParseTrees
import CSwL.Parsing.Recognition
import CSwL.Parsing.Combinators

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Análise sintática" =>
%%%
tag := "Parsing"
file := "Parsing"
%%%

:::dev NOW
Plan. The headings follow CSwFP/9.1–9.8 (9.9, further reading, is
omitted). Sections are written `terse` first (see `STYLE-CODE.md`).

- 9.1: `ParseTree α β`, positions, and the tree relations as lists of
  pairs; dominance with Lean's `<+:`.
- 9.2: recognition and parsing by splitting, for the palindrome grammar,
  total by `termination_by`; agreement with Mathlib's `List.Palindrome`
  proved for every word over `{a, b, c}`.
- 9.3: list-of-successes parsers as `StateT (List α) List`, with
  Mathlib's `Monad`/`Alternative List`; recursive parsers are
  `partial def`. Lean's `Std.Internal.Parsec` returns one result, not
  all parses; it can serve the lexer of 9.5.
- 9.4–9.8: to plan. The representation of `Cat` is tied to issue 42.
:::

:::terse
- Até aqui as árvores sintáticas eram construídas à mão. Agora o caminho
  é o inverso: partir de uma sequência de palavras e encontrar as árvores
  que a gramática lhe atribui.
- Primeiro, relações entre os nós de uma árvore. Depois, reconhecer e
  analisar linguagens livres de contexto.
:::

::::full
:::dev BeforeNextRelease
TODO: translate the CSwFP/9 summary.
:::
::::

{include 1 CSwL.Parsing.ParseTrees}

{include 1 CSwL.Parsing.Recognition}

{include 1 CSwL.Parsing.Combinators}
