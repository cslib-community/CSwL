import CSwLMeta
import Bib
import CSwL.Composition.Quantification

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Significados tipados para a língua natural" =>
%%%
tag := "comp-typed-meanings"
file := "TypedMeanings"
%%%

```lean
namespace Composition

open ModelChecking
```

:::terse
- Cada regra da gramática de {ref "ModelChecking"}[Model checking] ganha
  uma regra semântica: como o significado do todo se constrói a partir dos
  significados das partes. Escrevemos ⟦X⟧ para o significado de X.
- Os significados vivem na *lógica tipada*. Há dois tipos básicos, `e`
  para entidades e `t` para valores de verdade, e os tipos de função
  $`\tau_1 \to \tau_2`.
- Em Lean, `e` é `Entity` e $`t` é `Bool`, e os termos da lógica tipada
  são funções do Lean, como em {ref "lambda"}[Lean e o Cálculo Lambda].
- O tipo de cada categoria:
  - S: `Bool`;
  - CN, RCN e VP: `Entity → Bool`, isto é, `OnePlacePred`;
  - TV: `Entity → Entity → Bool`, isto é, `TwoPlacePred`;
  - NP: `OnePlacePred → Bool`;
  - DET: `OnePlacePred → OnePlacePred → Bool`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.5, from the start to the rules for determiners.
Its types e and t are presented in CSwFP/7.3, which is dropped (see
`DEVIATIONS.md`): the translation says in a few words what they are.
:::
::::

:::terse
- A sentença é a aplicação do significado do NP ao do VP:
  ⟦S⟧ = ⟦NP⟧ ⟦VP⟧. O sujeito é a função; o VP é o argumento.
- Um nome próprio não denota uma entidade, e sim um quantificador: o
  conjunto das propriedades da entidade. ⟦Alice⟧ = λP ↦ P a.
- ⟦DET CN⟧ = ⟦DET⟧ ⟦CN⟧. A mesma regra vale para DET RCN.
:::

```lean
namespace Rule

def sent (np : OnePlacePred → Bool)
    (vp : OnePlacePred) : Bool :=
  np vp

def npName (x : Entity) : OnePlacePred → Bool :=
  fun P => P x

def npDet (det : OnePlacePred → OnePlacePred → Bool)
    (cn : OnePlacePred) : OnePlacePred → Bool :=
  det cn

end Rule
```

:::terse
- Os determinantes são relações entre duas propriedades, como em
  {ref "comp-relational"}[A visão relacional dos quantificadores]. *Some* e
  *a* têm o mesmo significado, `a`; *every* é `every`.
- *No*: nenhuma entidade com `p` tem `q`.
- *The*, à maneira de Russell: há exatamente uma entidade com `p`, e ela
  tem `q`.
:::

```lean
def no (p q : OnePlacePred) : Bool :=
  entities.all (fun x => p x → ¬ q x)

def the (p q : OnePlacePred) : Bool :=
  entities.any (fun x =>
    entities.all (fun y => p y ↔ x = y) ∧ q x)

#eval (the princess laugh, no dwarf laugh)
```

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.5, the rules for determiners and common nouns.
:::
::::

:::terse
- Substantivos comuns e verbos intransitivos são as propriedades do
  modelo: ⟦girl⟧ = λx ↦ Girl x, que é `girl`.
- Uma oração relativa é a interseção de duas propriedades.
  *girl that laughed*: ser menina e ter rido.
- *girl that some boy loved*: ser menina e ser amada por algum menino. O
  NP *some boy* recebe a propriedade "amar `x`", `fun y => tv y x`.
:::

```lean
namespace Rule

def rcnSubj (cn vp : OnePlacePred) : OnePlacePred :=
  fun x => cn x && vp x

def rcnObj (cn : OnePlacePred) (np : OnePlacePred → Bool)
    (tv : TwoPlacePred) : OnePlacePred :=
  fun x => cn x && np (fun y => tv y x)

end Rule
```

:::terse
- VP → TV NP é o truque de `defeated`: fixar o sujeito `x` e entregar ao
  NP a propriedade "ser o objeto de `x`". `defeated` é `vpTrans defeat`.
- Com um verbo bitransitivo, o mesmo truque duas vezes, um para cada
  objeto.
- O verbo recebe primeiro o sujeito, depois os objetos, como as relações
  do modelo.
:::

```lean
namespace Rule

def vpTrans (tv : TwoPlacePred)
    (np : OnePlacePred → Bool) : OnePlacePred :=
  fun x => np (fun y => tv x y)

def vpDitrans (dv : ThreePlacePred)
    (np₁ np₂ : OnePlacePred → Bool) : OnePlacePred :=
  fun x => np₁ (fun y => np₂ (fun z => dv x y z))

theorem defeated_eq : defeated = vpTrans defeat :=
  rfl

end Rule
```

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.5, the rules for relative clauses, verb phrases
and transitive verbs. CSwFP's rule for VP → TV NP applies the verb to the
object first, `λx ↦ ⟦NP⟧ (λy ↦ ((⟦TV⟧ y) x))`, and its 7.6 implementation
to the subject first; here both follow the model (see `DEVIATIONS.md`).
:::
::::

:::terse
- *Alice admired Dorothy*: compomos as regras na forma da árvore
  `[S [NP Alice] [VP [TV admired] [NP Dorothy]]]`.
- O `#eval` consulta o modelo. O teorema diz mais: para *qualquer*
  relação `r` no lugar de *admire*, o significado composto é `r alice
  dorothy`. É a forma normal do significado.
- `rfl` basta, porque o Lean faz as β-reduções sozinho: aplica cada
  `fun` ao seu argumento até sobrar `r alice dorothy`.
:::

```lean
namespace Rule

#eval sent (npName alice)
  (vpTrans admire (npName dorothy))

theorem alice_admired_dorothy (r : TwoPlacePred) :
    sent (npName alice) (vpTrans r (npName dorothy)) =
      r alice dorothy :=
  rfl

end Rule
```

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.5, from "As an example, consider the sentence
Alice admired Dorothy…" to the end of the section. The chain of
β-reductions is shown by `alice_admired_dorothy`, proved by `rfl`.
:::
::::

::::exercise (rating := 2) (name := "snow-white-helped")
Componha, com as regras, o significado de *Snow White helped some dwarf*,
com uma relação `r` qualquer no lugar de *help*. Depois, escreva a sua
forma normal, sem as regras, e prove que as duas são iguais.

```lean
namespace Rule

def snowWhiteHelped (r : TwoPlacePred) : Bool :=
  solution!(
    sent (npName snowWhite) (vpTrans r (npDet a dwarf)))

def snowWhiteHelpedNF (r : TwoPlacePred) : Bool :=
  solution!(
    entities.any (fun x => dwarf x ∧ r snowWhite x))

theorem snowWhiteHelped_nf (r : TwoPlacePred) :
    snowWhiteHelped r = snowWhiteHelpedNF r := by
  solution!
   rfl

end Rule
```
::::

```lean
end Composition
```
