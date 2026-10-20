import CSwLMeta
import Bib
import CSwL.ModelChecking

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "A composição do significado na língua natural" =>
%%%
tag := "Composition"
htmlSplit := .never
file := "Composition"
%%%

```lean
namespace Composition

open ModelChecking
```

:::dev NOW
Plan. The headings follow CSwFP/7.1–7.7 (7.8, further reading, is omitted).
Sections are written `terse` first (see `STYLE-CODE.md`). Code comes in the
section that presents each idea, not only in 7.6:

- 7.2: `every` and `a` (also `some`, `no`, `most`) as relations between
  predicates; EXT, CONS and ISOM as `Prop`s over `Set`; the tree of numbers
  and the numeric quantifiers; ex. 7.7–7.10 as monotonicity theorems; ex.
  7.11 with Mathlib's `DFA` (optional).
- 7.3: Lean's types are the typed logic (`Entity` for e, `Bool` for t); no
  deep embedding, since CSwFP/8 needs intensional types.
- 7.4: `#reduce` shows the β-reductions; free variables and substitution
  from CSLib's `Named.Untyped`; confluence and normal forms only cited.
- 7.5: the semantic rules as Lean functions.
- 7.6: `intSent` and friends over `ModelChecking`'s `Sent`, with `intDET`
  built from the 7.2 definitions; a theorem that the direct interpretation
  agrees with `checkSentence`, if it turns out feasible.
- 7.7: ex. 7.26–7.27 over `ModelChecking`'s `SentPP`; ex. 7.28.

The chapter's key point for the cues: direct interpretation admits
quantifiers, such as *most*, that first-order logic cannot express.

A first draft translation of the chapter opening, 7.1 and 7.2 up to the
conditions on quantifier relations is in commits `76821ee` and `95047b3`.
:::

:::terse
- Em {ref "ModelChecking"}[Verificação de modelos com lógica de primeira
  ordem] o caminho era indireto: sentença, depois fórmula, depois avaliação no
  modelo.
- Agora o caminho é direto: cada expressão da língua é ligada ao modelo, sem
  fórmula intermediária.
- Os modelos da lógica de predicados se estendem à lógica tipada, que dá os
  significados das palavras e o modo de compô-los.
- O ganho central: quantificadores como *most*, que a lógica de primeira ordem
  não exprime, passam a ter interpretação direta.
:::

::::full
:::dev BeforeNextRelease
TODO: translate the CSwFP/7 summary, with Lean in place of Haskell as the
lambda-calculus engine of `ModelChecking`.
:::
::::

# As regras do jogo
%%%
tag := "comp-rules"
%%%

:::terse
- Traduzir sentenças para uma lógica pressupõe entender as fórmulas e as
  sentenças. Por isso a tradução não explica o significado das sentenças.
- O procedimento de {ref "english-lf"}[FOL como linguagem de representação]
  explica: o significado do todo é construído a partir dos significados das
  partes. Os significados das palavras vêm do modelo.
- Princípio da Composicionalidade, já visto em {ref "IntroCS"}[O estudo formal
  da língua natural]: o significado de uma expressão é uma função dos
  significados de seus componentes imediatos e do modo de composição.
- Frege, depois Montague. Em Montague, outro ingrediente-chave: os
  quantificadores.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.1.
:::
::::

# Quantificação
%%%
tag := "comp-quantification"
%%%

:::terse
- Aristóteles ({ref "InfEngine"}[Um motor de inferência]): um quantificador
  por sentença, nada de *most* ou *at least five*, e a pressuposição
  existencial.
- Frege: ∀ e ∃ com variáveis, em combinações arbitrárias. Os dois são
  interdefiníveis com a negação.
- O quadrado das oposições em primeira ordem; *pelo menos dois A são B* com a
  igualdade.
- *Every prince sang a ballad* ("Todo príncipe cantou uma balada"): na
  fórmula, os sintagmas nominais desaparecem.
- *A ballad was sung by every prince* ("Uma balada foi cantada por todo
  príncipe"): duas fórmulas, duas leituras. A lógica de primeira ordem
  desambigua.
- O que falta: manter os sintagmas nominais como constituintes, uma tradução
  que não seja ad hoc, e quantificadores não padrão como *most*.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from the start to "…in a uniform framework with
standard quantifiers." The two paragraphs on the noun phrases of (7.1) and on
"systematically misleading expressions" are cut to a reminder of
`english-form` (see `DEVIATIONS.md`).
:::
::::

## A visão relacional dos quantificadores
%%%
tag := "comp-relational"
%%%

:::terse
- Um quantificador é uma relação binária entre subconjuntos de um domínio
  $`E` (Mostowski {citep Bib.mostowski1957}[]; Barwise e Cooper
  {citep Bib.barwise1981}[]).
- A relação já apareceu em {ref "english-lf"}[FOL como linguagem de
  representação]: os dois argumentos de `lfDET` são a restrição e o escopo.
  Lá, porém, o determinante construía uma fórmula. Aqui ele relaciona
  diretamente dois conjuntos de entidades.
- *Every princess laughed* ("Toda princesa riu"): o determinante é uma função
  de duas propriedades, `every : OnePlacePred → OnePlacePred → Bool`.
  `every p q` verifica que toda entidade com `p` tem `q`.
- Os tipos acompanham a composição: `every princess : OnePlacePred → Bool`,
  e a sentença `every princess laugh : Bool`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, "The relational view of quantifiers", from the
start to the table after (7.3). Decide whether the table keeps the types
e and t or shows the Lean types; e and t are presented in `comp-typed-logic`.
:::
::::

```lean
def every (p q : OnePlacePred) : Bool :=
  entities.all (fun x => !p x || q x)
```

```lean (name := everyPrincessLaughed)
#eval every princess laugh
```

```leanOutput everyPrincessLaughed
true
```

:::terse
- *Every dwarf defeated a giant* ("Todo anão derrotou um gigante"): uma
  sentença com dois quantificadores.
- `a p q` verifica que alguma entidade tem `p` e `q`: a interseção dos dois
  conjuntos não é vazia.
- Um sintagma nominal como `a giant` tem tipo `OnePlacePred → Bool`: espera a
  propriedade do escopo. O verbo transitivo `defeated` toma esse sintagma como
  argumento e devolve uma propriedade do sujeito.
- A sentença inteira é só aplicação de funções. Nenhuma fórmula é construída:
  o `#eval` consulta o modelo diretamente.
- Nessa composição o objeto fica sempre no escopo do sujeito. A outra leitura
  fica para {ref "comp-ambiguity"}[Tratando a ambiguidade].
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "To see how quantifier combinations…" to the
summary tree, with *Every dwarf defeated a giant* in place of (7.4) (see
`DEVIATIONS.md`).
:::
::::

```lean
def a (p q : OnePlacePred) : Bool :=
  entities.any (fun x => p x && q x)

def defeated (X : OnePlacePred → Bool) : OnePlacePred :=
  fun y => X (fun z => defeat y z)
```

```lean (name := everyDwarfDefeatedAGiant)
#eval every dwarf (defeated (a giant))
```

```leanOutput everyDwarfDefeatedAGiant
true
```

# A linguagem da lógica tipada e sua semântica
%%%
tag := "comp-typed-logic"
%%%

:::terse
- A linguagem de tipos da lógica tipada: $`e` para entidades, $`t` para
  valores de verdade, e $`\tau_1 \to \tau_2` para funções.
- No nosso modelo, $`e` é `Entity` e $`t` é `Bool`; os tipos de
  {ref "comp-relational"}[A visão relacional dos quantificadores] são esses.
:::

# Redução de expressões da lógica tipada
%%%
tag := "comp-reduction"
%%%

# Significados tipados para a língua natural
%%%
tag := "comp-typed-meanings"
%%%

# Implementando a interpretação semântica
%%%
tag := "comp-interpretation"
%%%

# Tratando a ambiguidade
%%%
tag := "comp-ambiguity"
%%%

```lean
end Composition
```
