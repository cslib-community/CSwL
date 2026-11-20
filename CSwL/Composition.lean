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

#doc (Manual) "A Composição do Significado na Língua Natural" =>
%%%
tag := "Composition"
file := "Composition"
%%%

:::dev
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
:::

:::terse
- Em {ref "ModelChecking"}[Verificação de Modelos com Lógica de Primeira Ordem]
  o caminho era indireto: sentença, depois fórmula, depois avaliação no modelo.
- Agora o caminho é direto: cada expressão da língua é ligada ao modelo, sem
  fórmula intermediária.
- Os modelos da lógica de predicados se estendem à lógica tipada, que dá os
  significados das palavras e o modo de compô-los.
- O ganho central: quantificadores como *most*, que a lógica de primeira ordem
  não exprime, passam a ter interpretação direta.
:::

::::full
Em {ref "ModelChecking"}[Verificação de Modelos com Lógica de Primeira Ordem],
interpretamos as sentenças em duas etapas. Primeiro, construímos uma fórmula a
partir da árvore sintática. Depois, avaliamos essa fórmula em um modelo. Neste
capítulo, vamos construir os significados diretamente no modelo, compondo as
interpretações das palavras conforme a estrutura sintática da expressão.

Começamos pelos quantificadores e por sua interpretação como relações entre
conjuntos. Essa perspectiva permite estudar tanto os quantificadores usuais
quanto expressões como *most*. Examinamos suas propriedades por meio de
contagens, árvores numéricas e linguagens formais. Em seguida, atribuímos tipos
aos significados das categorias sintáticas e escrevemos as regras que os
combinam como funções do Lean.

Partimos das entidades e relações do modelo para interpretar também
expressões de tipos funcionais. Uma propriedade pode ser argumento de outra
função, como acontece quando um sintagma nominal quantificado recebe o
significado de um predicado.

Por fim, reunimos essas regras em funções que interpretam as árvores do
fragmento de língua natural. A interpretação direta também permite compor
significados com *most*, cuja comparação entre quantidades não pode ser
expressa, em geral, na lógica de primeira ordem usada na tradução do fragmento.
::::

{include 1 CSwL.Composition.Rules}

{include 1 CSwL.Composition.Quantification}

{include 1 CSwL.Composition.TypedMeanings}

{include 1 CSwL.Composition.Interpretation}
