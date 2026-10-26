import CSwLMeta
import Bib
import CSwL.ModelChecking
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Card
import Mathlib.Computability.Language
import CSwL.Composition.Rules
import CSwL.Composition.Quantification
import CSwL.Composition.TypedLogic
import CSwL.Composition.Reduction
import CSwL.Composition.TypedMeanings
import CSwL.Composition.Interpretation
import CSwL.Composition.Ambiguity

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "A composição do significado na língua natural" =>
%%%
tag := "Composition"
htmlSplit := .never
file := "Composition"
%%%

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

{include 1 CSwL.Composition.Rules}

{include 1 CSwL.Composition.Quantification}

{include 1 CSwL.Composition.TypedLogic}

{include 1 CSwL.Composition.Reduction}

{include 1 CSwL.Composition.TypedMeanings}

{include 1 CSwL.Composition.Interpretation}

{include 1 CSwL.Composition.Ambiguity}
