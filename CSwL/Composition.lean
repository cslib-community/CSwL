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

:::terse
- Em {cref "ModelChecking"}[]
  o caminho era indireto: sentença, depois fórmula, depois avaliação no modelo.
- Agora o caminho é direto: cada expressão da língua é ligada ao modelo, sem
  fórmula intermediária.
- Os modelos da lógica de predicados se estendem à lógica tipada, que dá os
  significados das palavras e o modo de compô-los.
- O ganho central: quantificadores como *most*, que a lógica de primeira ordem
  não exprime, passam a ter interpretação direta.
:::

::::full
Em {cref "ModelChecking"}[],
interpretamos as sentenças em duas etapas. Primeiro, construímos uma fórmula a
partir da árvore sintática. Depois, avaliamos essa fórmula em um modelo. Neste
capítulo, vamos construir os significados diretamente no modelo, compondo as
interpretações das palavras conforme a estrutura sintática da expressão.

Começamos pelos quantificadores e por sua interpretação como relações entre
conjuntos. Essa perspectiva permite estudar tanto os quantificadores usuais
quanto expressões como *most*. Examinamos suas propriedades por meio de
contagens, árvores numéricas e linguagens formais. Em seguida, atribuímos tipos
aos significados das categorias sintáticas. A partir das entidades e relações
do modelo, interpretamos também expressões de tipos funcionais: uma propriedade
pode ser argumento de outra função, como acontece quando um sintagma nominal
quantificado recebe o significado de um predicado. As regras que combinam esses
significados são escritas como funções do Lean.

Por fim, reunimos essas regras em funções que interpretam as árvores do
fragmento de língua natural. A interpretação direta também permite compor
significados com *most*, cuja comparação entre quantidades não pode ser
expressa, em geral, na lógica de primeira ordem usada na tradução do fragmento.
::::

{include 1 CSwL.Composition.Rules}

{include 1 CSwL.Composition.Quantification}

{include 1 CSwL.Composition.TypedMeanings}

{include 1 CSwL.Composition.Interpretation}
