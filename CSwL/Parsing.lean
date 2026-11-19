import CSwLMeta
import Bib
import CSwL.Parsing.ParseTrees
import CSwL.Parsing.Recognition
import CSwL.Parsing.Combinators
import CSwL.Parsing.Features
import CSwL.Parsing.Lexicon
import CSwL.Parsing.Categories
import CSwL.Parsing.FurtherReading

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Análise sintática" =>
%%%
tag := "Parsing"
file := "Parsing"
%%%

:::dev NOW
Plan. The headings follow CSwFP/9.1–9.9; 9.9, further reading, is
translated and extended, and stays the last section. Sections are
written `terse` first (see `STYLE-CODE.md`).

- 9.1: `ParseTree α β`, positions, and the tree relations as lists of
  pairs; dominance with Lean's `<+:`.
- 9.2: recognition and parsing by splitting, for the palindrome grammar,
  total by `termination_by`; agreement with Mathlib's `List.Palindrome`
  proved for every word over `{a, b, c}`.
- 9.3: list-of-successes parsers as `StateT (List α) List`, with
  Mathlib's `Monad`/`Alternative List`; recursive parsers are
  `partial def`. Lean's `Std.Internal.Parsec` returns one result, not
  all parses; it can serve the lexer of 9.5.
- 9.4: `Feat` as one type, `Agreement` as a list put in a canonical
  order by filtering `allFeats`; `combine` and `assign` return
  `Option`; `Cat` is a structure.
- 9.5: the lexicon as lists of `Cat`, one per word class, looked up by
  form; `noun` and `verb` build the regular pairs;
  `collectCats` returns `Except String` where CSwFP raises an error.
- 9.6: parsers over `Cat` in `do`-notation on the `Parser` of 9.3;
  `fromOption` turns a failed `combine`/`assign` into `failure`; `prs`
  returns `Except String`.
- 9.7–9.8: to plan. The representation of `Cat` is tied to issue 42.
:::

:::terse
- Até aqui as árvores sintáticas eram construídas à mão. Agora o caminho
  é o inverso: partir de uma sequência de palavras e encontrar as árvores
  que a gramática lhe atribui.
- Primeiro, relações entre os nós de uma árvore. Depois, reconhecer e
  analisar linguagens livres de contexto.
:::

::::full
Uma gramática descreve como as palavras se combinam para formar
constituintes e sentenças. Até aqui, construímos à mão as árvores que
representam essa estrutura. Neste capítulo, vamos partir de uma
sequência de palavras e construir as árvores que uma gramática lhe
atribui. Esse processo é a análise sintática, ou *parsing*.

Começamos pela representação das árvores e pelas relações entre suas
posições, como dominância, c-comando e precedência. Com a gramática
dos palíndromos, estudamos como decidir se uma sequência pertence à
linguagem e como construir as árvores das sequências aceitas. Depois,
desenvolvemos parsers por composição de funções menores, de modo que
as alternativas e as sequências das regras tenham operações
correspondentes no programa.

Para analisar um fragmento do inglês, acrescentamos às categorias
sintáticas traços de concordância e listas dos complementos que cada
expressão exige. Um léxico associa as palavras a essas categorias,
e a análise léxica prepara o texto para a consulta. Os parsers passam
então a combinar categorias, verificando a compatibilidade dos traços
e as exigências de subcategorização ao construir as árvores.

As categorias e as árvores resultantes são exibidas como matrizes de
atributos e valores, ou AVMs. Nessa apresentação, cada constituinte
reúne suas informações sintáticas e as estruturas de suas filhas.
Ao final, teremos um programa que recebe uma sentença e devolve as
árvores encontradas, ou informa que alguma palavra é desconhecida ou
que a gramática não admite uma análise para a entrada.
::::

{include 1 CSwL.Parsing.ParseTrees}

{include 1 CSwL.Parsing.Recognition}

{include 1 CSwL.Parsing.Combinators}

{include 1 CSwL.Parsing.Features}

{include 1 CSwL.Parsing.Lexicon}

{include 1 CSwL.Parsing.Categories}

{include 1 CSwL.Parsing.FurtherReading}
