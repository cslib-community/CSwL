import CSwLMeta
import Bib
import CSwL.Composition.TypedMeanings

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Implementando a interpretação semântica" =>
%%%
tag := "comp-interpretation"
%%%

```lean
namespace Composition

open ModelChecking
```

:::terse
- Em {ref "comp-typed-meanings"}[Significados tipados para a língua
  natural], quem escolhia a regra para cada nó da árvore éramos nós.
  Agora uma função de interpretação faz isso: ela recebe a árvore
  sintática, um valor de `Sent`, e devolve o seu valor de verdade.
- Há uma função para cada categoria, com o tipo da categoria. Elas
  começam pelo *léxico*: cada palavra ganha o seu significado no modelo.
- *Some* e *a* têm a mesma interpretação. Os adjetivos e *caught* não
  são interpretados no modelo, como em {ref "ModelChecking"}[Model
  checking]: são falsos para todos.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.6, from the start to the interpretation of
determiners, without the Haskell `intDET` for *most*, which comes below.
:::
::::

```lean
def intCN : CN → OnePlacePred
  | .girl => girl
  | .boy => boy
  | .princess => princess
  | .dwarf => dwarf
  | .giant => giant
  | .wizard => wizard
  | .sword => sword
  | .dagger => dagger

def intADJ : ADJ → OnePlacePred
  | _ => fun _ => false

def intTV : TV → TwoPlacePred
  | .loved => love
  | .admired => admire
  | .helped => help
  | .defeated => defeat
  | .caught => fun _ _ => false

def intDV : DV → ThreePlacePred
  | .gave => give

def intDET : DET → OnePlacePred → OnePlacePred → Bool
  | .a => a
  | .some => a
  | .every => every
  | .no => no
  | .the => the
```

:::terse
- As quatro categorias que se referem umas às outras são interpretadas
  num bloco `mutual`, como os seus tipos foram declarados.
- Cada caso é uma linha: a regra semântica de `Rule` com o mesmo nome do
  construtor, aplicada às interpretações dos filhos. A recursão segue a
  árvore.
- *Everyone* e *someone* são *every* e *a* restritos a `person`.
- *happy wizard*: a interseção do adjetivo com o substantivo, como uma
  oração relativa.
:::

```lean
mutual
  def intSent : Sent → Bool
    | .sent np vp => Rule.sent (intNP np) (intVP vp)

  def intNP : NP → OnePlacePred → Bool
    | .snowWhite => Rule.npName snowWhite
    | .alice => Rule.npName alice
    | .dorothy => Rule.npName dorothy
    | .goldilocks => Rule.npName goldilocks
    | .littleMook => Rule.npName littleMook
    | .atreyu => Rule.npName atreyu
    | .everyone => every person
    | .someone => a person
    | .npDet det cn =>
      Rule.npDet (intDET det) (intCN cn)
    | .npDetRel det rcn =>
      Rule.npDet (intDET det) (intRCN rcn)

  def intVP : VP → OnePlacePred
    | .laughed => laugh
    | .cheered => cheer
    | .shuddered => shudder
    | .vpTrans tv np => Rule.vpTrans (intTV tv) (intNP np)
    | .vpDitrans dv np₁ np₂ =>
      Rule.vpDitrans (intDV dv) (intNP np₁) (intNP np₂)

  def intRCN : RCN → OnePlacePred
    | .rcnSubj cn _ vp => Rule.rcnSubj (intCN cn) (intVP vp)
    | .rcnObj cn _ np tv =>
      Rule.rcnObj (intCN cn) (intNP np) (intTV tv)
    | .rcnAdj adj cn => Rule.rcnSubj (intADJ adj) (intCN cn)
end
```

:::terse
- *Alice admired Dorothy* de novo, agora como árvore: um valor de `Sent`,
  com as palavras `.alice`, `.admired` e `.dorothy`.
- O `rfl` mostra que `intSent` monta a mesma composição que fizemos à mão
  em {ref "comp-typed-meanings"}[Significados tipados para a língua
  natural].
:::

```lean
#eval intSent (.sent .alice (.vpTrans .admired .dorothy))

example :
    intSent (.sent .alice (.vpTrans .admired .dorothy)) =
      Rule.sent (Rule.npName alice)
        (Rule.vpTrans admire (Rule.npName dorothy)) :=
  rfl
```

:::terse
- `sent1` é a árvore de *The dwarf that Snow White helped admired every
  princess*, de {ref "ModelChecking"}[Model checking].
- Lá, a sentença era traduzida para uma fórmula, e a fórmula avaliada no
  modelo. Aqui não há fórmula: a interpretação consulta o modelo
  diretamente.
- Os dois caminhos dão o mesmo valor. O segundo `#eval` confere isso nas
  trinta e duas sentenças de `sentences`.
:::

```lean
#eval (toString sent1, intSent sent1)

open FOL in
#eval sentences.all fun s =>
  intSent s ==
    (lfSent s).eval entities intFairy ass0
      (liftAssign fintFairy)
```

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.6, the interpretation of verb phrases, verbs,
noun phrases and relative clauses, and the examples of queries.
:::
::::

:::terse
- *Most* não tem tradução na lógica de primeira ordem, e por isso ficou
  fora de `DET` em {ref "ModelChecking"}[Model checking]. Na interpretação
  direta ele é uma função como as outras: compara quantos `p` têm `q`
  com quantos não têm.
- Sem mexer na gramática, ele entra pelas regras semânticas: *Most girls
  laughed* é `Rule.sent (Rule.npDet most girl) laugh`.
:::

```lean
def most (p q : OnePlacePred) : Bool :=
  (entities.filter fun x => p x && !q x).length <
    (entities.filter fun x => p x && q x).length

#eval Rule.sent (Rule.npDet most girl) laugh
#eval Rule.sent (Rule.npDet most person)
  (Rule.vpTrans admire (Rule.npName goldilocks))
```

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.6, the interpretation of *most*. CSwFP adds
`Most` to `DET`; here *most* is a meaning only, with no change to the
grammar (see issue 42).
:::
::::

::::exercise (rating := 2) (name := "at-least-at-most")
Defina `atLeastDet n` e `atMostDet n`, as interpretações de *at least n* e
*at most n*. Depois, prove as sentenças abaixo.

```lean
def atLeastDet (n : Nat) (p q : OnePlacePred) : Bool :=
  solution!(
    n ≤ (entities.filter fun x => p x && q x).length)

def atMostDet (n : Nat) (p q : OnePlacePred) : Bool :=
  solution!(
    (entities.filter fun x => p x && q x).length ≤ n)

theorem atLeastTwoGirlsLaughed :
    Rule.sent (Rule.npDet (atLeastDet 2) girl) laugh
      = true := by
  solution!
   decide

theorem atMostOneDwarfLaughed :
    Rule.sent (Rule.npDet (atMostDet 1) dwarf) laugh
      = true := by
  solution!
   decide

theorem notAtLeastThreeGirlsLaughed :
    Rule.sent (Rule.npDet (atLeastDet 3) girl) laugh
      = false := by
  solution!
   decide
```
::::

```lean
end Composition
```
