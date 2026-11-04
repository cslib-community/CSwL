import CSwLMeta
import Bib
import CSwL.ModelChecking
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Card
import Mathlib.Computability.Language
import CSwL.Composition.Rules
import CSwL.Composition.Quantification
import CSwL.Composition.TypedMeanings
import CSwL.Composition.Interpretation

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "A composição do significado na língua natural" =>
%%%
tag := "Composition"
file := "Composition"
%%%

:::dev NOW
Plan. The headings follow CSwFP/7.1–7.6, without 7.3 and 7.4 (7.7 is
deferred, issue 43; 7.8, further reading, is omitted).
Sections are written `terse` first (see `STYLE-CODE.md`). Code comes in the
section that presents each idea, not only in 7.6:

- 7.2: `every` and `a` (also `some`, `no`, `most`) as relations between
  predicates; EXT, CONS and ISOM as `Prop`s over `Set`; the tree of numbers
  and the numeric quantifiers; ex. 7.7–7.10 as monotonicity theorems; ex.
  7.11 with Mathlib's `DFA` (optional).
- 7.3 and 7.4 are dropped (see `CSwFP.yaml`): Lean's types are the typed
  logic (`Entity` for e, `Bool` for t), and Lean does the reductions. No
  deep embedding, since CSwFP/8 needs intensional types.
- 7.5: the semantic rules as Lean functions. Its opening says in a few
  lines that e is `Entity` and t is `Bool`.
- 7.6: `intSent` and friends over `ModelChecking`'s `Sent`, with `intDET`
  built from the 7.2 definitions; a theorem that the direct interpretation
  agrees with `checkSentence`, if it turns out feasible.
- 7.7: deferred (issue 43).

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

{include 1 CSwL.Composition.TypedMeanings}

{include 1 CSwL.Composition.Interpretation}
