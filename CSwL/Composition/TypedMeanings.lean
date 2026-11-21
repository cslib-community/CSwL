import CSwLMeta
import Bib
import CSwL.Composition.Quantification

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Significados Tipados para a Língua Natural" =>
%%%
tag := "comp-typed-meanings"
file := "TypedMeanings"
%%%

```lean
namespace Composition

open ModelChecking
```

:::terse
- Cada regra da gramática de {cref "mc"}[] ganha uma
  regra semântica: como o significado do todo se constrói a partir dos
  significados das partes. Escrevemos `⟦X⟧` para o significado de `X`.
- Os significados vivem na *lógica tipada*. Há dois tipos básicos, `e` para
  entidades e `t` para valores de verdade, e os tipos de função
  $`\tau_1 \to \tau_2`.
- Em Lean, `e` é {name}`Entity` e $`t` é {name}`Bool`, e os termos da lógica
  tipada são funções do Lean, como em {cref "lean-lambda"}[].
- O tipo de cada categoria:
  - `S`: {name}`Bool`;
  - {name}`CN`, {name}`RCN` e {name}`VP`: `Entity → Bool`, isto é,
    {name}`OnePlacePred`;
  - {name}`TV`: `Entity → Entity → Bool`, isto é, {name}`TwoPlacePred`;
  - {name}`NP`: `OnePlacePred → Bool`;
  - {name}`DET`: `OnePlacePred → OnePlacePred → Bool`.
:::

::::full
Cada regra sintática da gramática de
{cref "mc"}[]
recebe uma regra semântica que combina os significados de seus constituintes.
Escrevemos `⟦X⟧` para o significado de uma expressão `X`. Para saber quais
combinações fazem sentido, atribuímos tipos a esses significados.

A lógica tipada usa dois tipos básicos, `e` para entidades e `t` para valores de
verdade, e forma novos tipos de função a partir deles. Aqui, eles são
representados por {name}`Entity` e {name}`Bool`. As expressões dessa lógica são
funções do Lean, como em {cref "lean-lambda"}[].

Uma sentença, de categoria `S`, tem significado de tipo {name}`Bool`. Um
substantivo comum, um substantivo com modificadores ou um sintagma verbal, de
categorias {name}`CN`, {name}`RCN` e {name}`VP`, denota uma propriedade,
{lean}`Entity → Bool`, abreviada por {name}`OnePlacePred`. Um verbo
transitivo, de categoria {name}`TV`, denota uma relação de tipo
{name}`TwoPlacePred`. Um {name}`NP` recebe uma propriedade e produz um valor de
verdade, enquanto um {name}`DET` recebe duas propriedades. Esses tipos permitem
combinar os significados seguindo as regras da gramática.
::::

:::terse
- A sentença é a aplicação do significado do {name}`NP` ao do {name}`VP`:
  `⟦S⟧ = ⟦NP⟧ ⟦VP⟧`. O sujeito é a função; o `VP` é o argumento.
- Um nome próprio não denota uma entidade, e sim um quantificador: o conjunto
  das propriedades da entidade. `⟦Alice⟧ = λP ↦ P a`.
- `⟦DET CN⟧ = ⟦DET⟧ ⟦CN⟧`. A mesma regra vale para `DET RCN`.
:::

::::full
Na regra `S → NP VP`, o significado do sujeito é aplicado ao do predicado. O
sujeito tem tipo `OnePlacePred → Bool`, e o predicado tem tipo
{name}`OnePlacePred`, de modo que a aplicação produz o valor de verdade da
sentença.

Para dar aos nomes próprios o mesmo tipo dos demais sintagmas nominais, a regra
`npName` associa uma entidade `x` à função `fun P => P x`. Assim, o significado
de *Alice* recebe uma propriedade e verifica se Alice a tem. Podemos vê-lo como
a função característica do conjunto das propriedades de Alice.

Na regra que combina determinante e substantivo, aplicamos o significado do
determinante à propriedade denotada pelo substantivo. O resultado continua
esperando uma propriedade, que será fornecida pelo sintagma verbal. A mesma
regra se aplica quando a restrição é um {name}`RCN`.
::::

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
  {cref "comp-relational"}[]. *Some* e
  *a* têm o mesmo significado, `a`; *every* é {name}`every`.
- *No*: nenhuma entidade com `p` tem `q`.
- *The*, à maneira de Russell: há exatamente uma entidade com `p`, e ela tem
  `q`.
:::

::::full
Os determinantes relacionam a propriedade que restringe a quantificação à
propriedade que constitui seu escopo, conforme
{cref "comp-relational"}[].
*Some* e *a* recebem a interpretação {name}`a`, e *every* recebe
{name}`every`.

Para *no*, exigimos que nenhuma entidade com a primeira propriedade tenha a
segunda. Para *the*, usamos a leitura de Russell: existe exatamente uma entidade
com a propriedade da restrição, e essa entidade tem a propriedade do escopo. Na
definição, a equivalência entre `p y` e `x = y` exige que `x` seja o único
elemento que satisfaz `p`.
::::

```lean
def no (p q : OnePlacePred) : Bool :=
  entities.all (fun x => p x → ¬ q x)

def the (p q : OnePlacePred) : Bool :=
  entities.any (fun x =>
    entities.all (fun y => p y ↔ x = y) ∧ q x)

#eval (the princess laugh, no dwarf laugh)
```

:::terse
- Substantivos comuns e verbos intransitivos são as propriedades do modelo:
  `⟦girl⟧` = λx ↦ Girl x, que é {name}`girl`.
- Uma oração relativa é a interseção de duas propriedades.
  *girl that laughed*: ser menina e ter rido.
- *girl that some boy loved*: ser menina e ser amada por algum menino. O
  {name}`NP` *some boy* recebe a propriedade "amar `x`", `fun y => tv y x`.
:::

::::full
Os substantivos comuns e os verbos intransitivos recebem as propriedades
fornecidas pelo modelo. Por exemplo, *girl* é interpretado por {name}`girl`.
Uma oração relativa restringe essa propriedade por interseção com outra.

Em *girl that laughed*, uma entidade deve ser menina e ter rido. A regra
`rcnSubj` combina as duas propriedades por conjunção. Já em
*girl that some boy loved*, a entidade descrita ocupa a posição de
objeto da relação de amar. Para cada menina `x`, o sintagma *some boy* recebe a
propriedade `fun y => tv y x`. A regra `rcnObj` exige que esse quantificador
aceite a propriedade, isto é, que algum menino tenha amado `x`.
::::

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
- `VP → TV NP` é o truque de {name}`defeated`: fixar o sujeito `x` e entregar
  ao {name}`NP` a propriedade "ser o objeto de `x`". {name}`defeated` é
  `vpTrans defeat`.
- Com um verbo ditransitivo, o mesmo truque duas vezes, um para cada objeto.
- O verbo recebe primeiro o sujeito, depois os objetos, como as relações do
  modelo.
:::

::::full
Para a regra `VP → TV NP`, fixamos o sujeito `x` e formamos a propriedade
`fun y => tv x y`. Aplicamos o significado do objeto a essa propriedade e,
abstraindo sobre `x`, obtemos a propriedade denotada pelo sintagma verbal. A
regra `vpTrans` generaliza a construção usada em {name}`defeated`; o teorema
abaixo verifica essa igualdade.

Um verbo ditransitivo exige duas aplicações desse procedimento. Na regra
`vpDitrans`, o primeiro objeto recebe uma propriedade que contém a aplicação do
segundo objeto. A relação do modelo recebe os argumentos na ordem sujeito,
primeiro objeto e segundo objeto. Essa ordem também fixa o escopo dos dois
quantificadores na composição.
::::

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

:::terse
- *Alice admired Dorothy*: compomos as regras na forma da árvore
  `[S [NP Alice] [VP [TV admired] [NP Dorothy]]]`.
- O `#eval` consulta o modelo. O teorema diz mais: para *qualquer* relação `r`
  no lugar de *admire*, o significado composto é `r alice dorothy`. É a forma
  normal do significado.
- `rfl` basta, porque o Lean faz as β-reduções sozinho: aplica cada `fun` ao seu
  argumento até sobrar `r alice dorothy`.
:::

::::full
Podemos compor o significado de *Alice admired Dorothy* seguindo a árvore
`[S [NP Alice] [VP [TV admired] [NP Dorothy]]]`. Aplicamos {name}`Rule.npName`
às entidades dos dois nomes próprios, combinamos a relação de admirar com o
objeto usando {name}`Rule.vpTrans` e aplicamos {name}`Rule.sent` ao sujeito e ao
predicado.

A avaliação consulta a relação do modelo. O teorema enuncia também uma igualdade
que vale para qualquer relação `r`: o resultado da composição é
`r alice dorothy`. A prova por `rfl` verifica as reduções das funções aplicadas
aos seus argumentos. Essa expressão é a forma normal do significado composto.
::::

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

::::exercise (rating := 2) (name := "snow-white-helped")
Componha, com as regras, o significado de *Snow White helped some dwarf*, com
uma relação `r` qualquer no lugar de *help*. Depois, escreva a sua forma normal,
sem as regras, e prove que as duas são iguais.

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
