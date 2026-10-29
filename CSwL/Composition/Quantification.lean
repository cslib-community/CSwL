import CSwLMeta
import Bib
import CSwL.ModelChecking
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Card
import Mathlib.Computability.Language

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Quantificação" =>
%%%
tag := "comp-quantification"
%%%

```lean
namespace Composition

open ModelChecking
```

:::terse
- O objetivo da seção é comparar a visão aristotélica e a visão fregeana dos
  quantificadores. A de Frege é muito superior, mas deixa três problemas em
  aberto, e o resto do capítulo trata deles.
- A teoria da quantificação de Aristóteles, que vimos em
  {ref "InfEngine"}[Um motor de inferência], tem dois defeitos lógicos e uma
  falha menor:
  1. ela não trata combinações de quantificadores, pois só admite um
     quantificador por sentença;
  2. ela não cobre quantificadores "não padrão", como *most*, *half of* e
     *at least five*;
  3. ela supõe a pressuposição existencial.
- Frege remove o primeiro defeito. Os quantificadores ∀ e ∃ ligam variáveis
  e se combinam com fórmulas arbitrárias, de modo que uma fórmula pode ter
  quantos quantificadores quiser. O segundo defeito continua.
- ∀ e ∃ se definem um pelo outro com a negação: $`\exists x P x` vale se e
  somente se $`\neg \forall x \neg P x` vale.
- Os quatro quantificadores do quadrado das oposições se escrevem com ∀ e ∃:
  "todo A é B" é $`\forall x (Ax \to Bx)`, "algum A é B" é
  $`\exists x (Ax \land Bx)`, e assim por diante.
- Por que "esquecer" a pressuposição existencial: a questão não é o domínio
  (em FOL ele é não vazio), mas a extensão de `A`. Se nenhum elemento satisfaz
  `A`, então $`\forall x (Ax \to Bx)` é vacuamente verdadeira e
  $`\exists x (Ax \land Bx)` é falsa.
- Com `A` vazio, só as diagonais (contraditórias) sobrevivem. Caem as
  contrárias ("todo A é B" e "nenhum A é B" ambas verdadeiras), as
  subcontrárias e a subalternação. Ex.: *Darapti* não vale em FOL.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from the start to "…in terms of standard
quantifiers and equality."
:::
::::

:::terse
- Com a igualdade, a lógica de primeira ordem exprime também quantificadores
  numéricos. "Pelo menos dois A são B" é
  $`\exists x \exists y (x \neq y \land Ax \land Ay \land Bx \land By)`.
- A fórmula de "pelo menos dois A são B" em Lean é um valor do tipo `LF`, o
  mesmo de {ref "ModelChecking"}[Model checking]. Os predicados `a` e `b` são
  parâmetros, e a função devolve uma fórmula para cada par de predicados.
- `.neg (.eq tx ty)` é $`x \neq y`. A igualdade já é um construtor de
  `Formula` desde {ref "FOL"}[FOL].
- No modelo do capítulo há três pessoas que riem e só duas meninas que riem.
:::

```lean
open FOL in
def atLeastTwo (a b : String) : LF :=
  .exists_ x (.exists_ y (.conjs
    [.neg (.eq tx ty), .atom a [tx], .atom a [ty],
     .atom b [tx], .atom b [ty]]))


def check (f : LF) : Bool :=
  f.eval entities intFairy ass0 (FOL.liftAssign fintFairy)

#eval toString <| atLeastTwo "person" "laugh"
#eval check (atLeastTwo "person" "laugh")
```

::::exercise (rating := 1) (name := "at-most-two")

Seguindo o modelo de {name}`atLeastTwo`, defina a fórmula de "no máximo dois
A são B". Dica: se três elementos são A e B, dois deles são iguais.

```lean
open FOL in
def atMostTwo (a b : String) : LF :=
  solution!(
    .forall_ x (.forall_ y (.forall_ z (.impl
      (.conjs [.atom a [tx], .atom a [ty], .atom a [tz],
               .atom b [tx], .atom b [ty], .atom b [tz]])
      (.disjs [.eq tx ty, .eq tx tz, .eq ty tz])))))

theorem atMostTwo_girl :
    check (atMostTwo "girl" "laugh") = true :=
  solution!(by native_decide)

theorem atMostTwo_person :
    check (atMostTwo "person" "laugh") = false :=
  solution!(by native_decide)
```

::::

:::terse
- {name}`atLeastTwo` e `atMostTwo` são funções que *geram* fórmulas. A
  função é escrita em Lean, a metalinguagem; o que ela devolve é uma fórmula
  de FOL, a linguagem objeto.
- Todas as disjunções e conjunções de quantificadores das formas *pelo menos
  n* e *no máximo m* podem ser expressas com os quantificadores padrão e a
  igualdade.
- O que a lógica de primeira ordem consegue contar: só números fixos e
  finitos, com uma fórmula diferente para cada `n`.
- Não existe uma única fórmula que expresse "pelo menos n" para `n`
  arbitrário. Cada fórmula tem um número fixo de quantificadores, e isso
  limita até onde ela consegue contar.
- Em Lean, porém, podemos escrever uma única *função* `atLeast n` que, para
  cada `n`, gera a fórmula correspondente. As `n` variáveis distintas saem do
  índice de `Variable`: `⟨"x", [i]⟩` é a variável `xi`.
:::

::::exercise (rating := 3) (name := "at-least-n")

Defina `atLeast n a b`, a fórmula de "pelo menos n A são B", e
`atMost n a b`, a de "no máximo n A são B". Dica: "no máximo n" é a negação
de "pelo menos n + 1". Para `atLeast`, uma função auxiliar recursiva pode
carregar a lista dos termos já quantificados, para exigir que cada nova
variável seja diferente de todos eles.

```lean
open FOL in
def atLeastFrom (a b : String) (n : Nat) (ts : List Term) :
    LF :=
  solution!(
    match n with
    | 0 => .top
    | n + 1 =>
      let v : Variable := ⟨"x", [n]⟩
      let t : Term := .var v
      .exists_ v (.conjs ([.atom a [t], .atom b [t]] ++
        ts.map (fun s => .neg (.eq s t)) ++
        [atLeastFrom a b n (t :: ts)])))

def atLeast (n : Nat) (a b : String) : LF :=
  solution!(atLeastFrom a b n [])

def atMost (n : Nat) (a b : String) : LF :=
  solution!(.neg (atLeast (n + 1) a b))

theorem atLeast_person :
    check (atLeast 3 "person" "laugh") = true ∧
      check (atLeast 4 "person" "laugh") = false :=
  solution!(by native_decide)

theorem atMost_girl :
    check (atMost 2 "girl" "laugh") = true ∧
      check (atMost 1 "girl" "laugh") = false :=
  solution!(by native_decide)
```
::::

:::terse
- *Every prince sang a ballad* ("Todo príncipe cantou uma balada"): na
  fórmula, os sintagmas nominais desaparecem.
- *A ballad was sung by every prince* ("Uma balada foi cantada por todo
  príncipe"): duas fórmulas, duas leituras. A lógica de primeira ordem
  desambigua.
- A visão fregeana deixa três problemas em aberto:
  1. encontrar uma linguagem de representação que preserve os sintagmas
     nominais como constituintes;
  2. encontrar um procedimento de tradução da língua natural que não seja
     ad hoc;
  3. tratar quantificadores não padrão como *most*, de preferência junto com
     os quantificadores padrão.
- O resto desta seção, a partir da visão relacional, responde aos problemas
  1 e 3: *every dwarf* vira uma função, e *most* é uma relação entre
  conjuntos como *every*. A lógica tipada e o cálculo lambda, nas próximas
  seções, respondem ao problema 2.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "To illustrate the claim that first-order
logic has no difficulty…" to "…in a uniform framework with standard
quantifiers." The two paragraphs on the noun phrases of (7.1) and on
"systematically misleading expressions" are cut to a reminder of
`english-form` (see `DEVIATIONS.md`).
:::
::::

# A visão relacional dos quantificadores
%%%
tag := "comp-relational"
%%%

:::terse
- O objetivo da subseção é apresentar a visão relacional dos quantificadores
  e mostrar, em dois exemplos, que com ela os sintagmas nominais continuam
  sendo constituintes, inclusive quando há dois quantificadores na mesma
  sentença.
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
e and t or shows the Lean types; CSwFP/7.3, which presents e and t, is
dropped, so they need a word here or in `comp-typed-meanings`.
:::
::::

```lean
def every (p q : OnePlacePred) : Bool :=
  entities.all (fun x => p x → q x)

#eval (every princess) laugh
```

:::terse
- Lembre de {ref "Sets"}[Conjuntos e Relações]: a função característica de
  um conjunto responde, para cada elemento, se ele pertence ao conjunto.
  `princess : Entity → Bool` é a função característica do conjunto das
  princesas.
- `every princess` aplica a mesma ideia um nível acima. Ele tem tipo
  `OnePlacePred → Bool`, logo é a função característica de um conjunto de
  *propriedades*: as que toda princesa tem, isto é, as `q` com
  $`\textit{princess} \subseteq q`.
- O `#eval` a seguir mostra esse conjunto, restrito a três propriedades. O
  resultado é `["laugh"]`: das três propriedades, só "rir" é de toda
  princesa.
:::

```lean (name := everyPrincessEval)
#eval [("laugh", laugh), ("cheer", cheer),
       ("shudder", shudder)]
  |>.filter (fun (_, q) => every princess q) |>.map (·.1)
```

:::terse
- *Every dwarf defeated a giant* ("Todo anão derrotou um gigante"): uma
  sentença com dois quantificadores.
- `a p q` verifica que alguma entidade tem `p` e `q`: a interseção dos dois
  conjuntos não é vazia.
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
  entities.any (fun x => p x ∧ q x)
```

:::terse
- Há três nomes para `defeated`, em três níveis:
  - `TV.defeated` é a palavra, um construtor da gramática;
  - `defeat : Entity → Entity → Bool` é a relação no modelo;
  - `defeated`, que definimos agora, é a tradução do verbo.
- Lembre que `OnePlacePred` é uma abreviação (`abbrev`) de `Entity → Bool`,
  o tipo das propriedades. O objeto `a giant` tem tipo
  `OnePlacePred → Bool`: ele espera uma propriedade. Mas `defeat` tem dois
  argumentos e não é uma propriedade.
- O truque é fixar o sujeito `y`. `fun z => defeat y z` é a propriedade "ser
  derrotado por `y`", e `X (fun z => defeat y z)` diz que `y` derrotou `X`.
  Abstraindo `y`, obtemos uma propriedade do sujeito.
- Por isso `defeated` toma o significado de um sintagma nominal,
  `X : OnePlacePred → Bool`, e devolve o de um VP, um `OnePlacePred`. A avaliação da lista as entidades com essa propriedade, as que derrotaram um
  gigante: `[B, R]`, que são justamente os dois anões do modelo.
:::

```lean (name := defeatedEval)
def defeated (X : OnePlacePred → Bool) : OnePlacePred :=
  fun y => X (fun z => defeat y z)

#eval entities.filter (defeated (a giant))
```

:::terse
- A sentença inteira é só aplicação de funções. Nenhuma fórmula é construída:
  a avaliação consulta o modelo diretamente.
- Nessa composição o objeto fica sempre no escopo do sujeito. A outra
  leitura, com o objeto de escopo amplo, não é tratada aqui.
:::

```lean
#eval (every dwarf) (defeated (a giant))
#eval every dwarf (defeated (a giant))
```


# Condições sobre as relações quantificadoras
%%%
tag := "comp-conditions"
%%%

::::terse
O objetivo da subseção é dizer quais relações entre conjuntos são
quantificadores. É uma definição, *quantificador* é o nome de uma relação que satisfaz EXT, CONS e ISOM. Uma relação qualquer entre conjuntos pode depender de coisas que um quantificador ignora, e cada uma das três condições exclui um desses casos:

:::table +header
*
  * Condição
  * O que garante
  * O que exclui
*
  * EXT
  * O resultado não depende do tamanho do universo $`E`, só de
    $`A \cup B`.
  * *Many* no sentido de "relativamente muitos", que depende de quantas
    coisas existem no total.
*
  * CONS
  * Nada fora da restrição $`A` importa.
  * *Only*: em *Only dwarfs sing during work*, acrescentar não anões que
    cantam torna a sentença falsa.
*
  * ISOM
  * Importa quantos elementos há, e não quais.
  * Determinantes que falam de um indivíduo, como o possessivo *Alice's*:
    em *Alice's daggers are sharp*, o que importa é quem é o dono, e não
    quantas adagas há.
:::

- EXT e CONS valem para quase todos os determinantes da língua natural.
  ISOM separa, entre eles, os que exprimem quantidade.
- Juntas, as três condições reduzem o valor de `D E A B` a dois números,
  $`|A - B|` e $`|A \cap B|`. É isso que permite a árvore de números de
  {ref "comp-trees"}[Árvores numéricas].
- Para enunciar as condições, saímos de `Bool` e passamos a `Prop` sobre
  `Set`, como em {ref "Sets"}[Conjuntos]: `D E A B` diz que o determinante
  `D` relaciona a *restrição* `A` e o *escopo* `B` no universo `E`.
- O tipo `GQ.Det α` é só uma abreviação para `Set α → Set α → Set α → Prop`.
  Nada no tipo diz que `A` e `B` estão dentro de `E`.
  Essa exigência aparece como as hipóteses `A ⊆ E` e `B ⊆ E` em cada uma das
  três condições.
- Não confundir `DET` com `GQ.Det`. `DET` é a categoria sintática de
  {ref "ModelChecking"}[Model checking], com as palavras *a*, *the*,
  *every*, …. `GQ.Det` é o tipo dos significados dessas palavras. O tipo é
  amplo de propósito: todo quantificador é um `GQ.Det`, mas nem todo
  `GQ.Det` é um quantificador.
::::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, "Conditions on Quantifier Relations", from the
start to Figure 7.2.
:::
::::

```lean
namespace GQ

abbrev Det (α : Type) := Set α → Set α → Set α → Prop

def all  {α} : Det α := fun _ A B => A ⊆ B
def some {α} : Det α := fun _ A B => ∃ x, x ∈ A ∧ x ∈ B
def no   {α} : Det α := fun _ A B => ∀ x, x ∈ A → x ∉ B
def only {α} : Det α := fun _ A B => B ⊆ A
```

:::terse
- {lean}`GQ.all` é a contraparte de {lean}`every` em conjuntos: `every p q` é `true`
  exatamente quando o conjunto das entidades com `p` está contido no das
  entidades com `q`.
- A prova usa {lean}`mem_entities`: toda entidade está na lista `entities`.
:::

```lean
theorem every_iff_all (p q : OnePlacePred) :
    every p q = true ↔
      all Set.univ {x | p x = true} {x | q x = true} := by
  unfold every all
  constructor
  · intro h x hx
    have hx' := List.all_eq_true.mp h x (mem_entities x)
    simp_all
  · intro h
    apply List.all_eq_true.mpr
    intro x _
    by_cases hp : p x = true
    · have hq : q x = true := h hp
      simp [hq]
    · simp [hp]
```

::::exercise (rating := 2) (name := "subalternation")

Em {ref "comp-quantification"}[Quantificação] vimos que, sem a pressuposição
existencial, "todo A é B" não implica "algum A é B". Prove as duas coisas: a
subalternação vale quando `A` tem um elemento, e falha em geral.

```lean
theorem all_imp_some {α : Type} (E A B : Set α)
    (hA : ∃ x, x ∈ A) (h : all E A B) : some E A B := by
  solution!
   obtain ⟨x, hx⟩ := hA
   exact ⟨x, hx, h hx⟩

theorem all_not_imp_some :
    ¬ ∀ (A B : Set Entity),
        all Set.univ A B → some Set.univ A B := by
  solution!
   intro h
   obtain ⟨x, hx, _⟩ := h ∅ ∅ (fun _ hx => hx)
   exact hx
```
::::

:::terse
- *EXT*: o resultado não muda quando o universo cresce; só importa $`A \cup B`.
- *CONS*: tudo o que está fora da restrição é irrelevante, `D E A B` equivale a
  `D E A (A ∩ B)`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "Not all two-place relations on sets of
individuals…" to "…A − B and A ∩ B."
:::
::::

```lean
def Ext {α : Type} (D : Det α) : Prop :=
  ∀ E E' A B, A ⊆ E → B ⊆ E → E ⊆ E' → (D E A B ↔ D E' A B)

def Cons {α : Type} (D : Det α) : Prop :=
  ∀ E A B, A ⊆ E → B ⊆ E → (D E A B ↔ D E A (A ∩ B))
```

:::terse
- Para *all* e *some*, as duas condições valem e as provas são curtas.
- As provas de EXT são só `rfl`: as definições começam com `fun _ A B`, isto
  é, ignoram o universo `E`, e os dois lados do `↔` são a mesma proposição.
:::

```lean
theorem all_ext {α : Type} : Ext (all : Det α) := by
  intro E E' A B _ _ _
  rfl

theorem all_cons {α : Type} : Cons (all : Det α) := by
  intro E A B _ _
  constructor
  · intro h x hx
    exact ⟨hx, h hx⟩
  · intro h x hx
    exact (h hx).2

theorem some_ext {α : Type} : Ext (some : Det α) := by
  intro E E' A B _ _ _
  rfl

theorem some_cons {α : Type} : Cons (some : Det α) := by
  intro E A B _ _
  constructor
  · intro h
    obtain ⟨x, hA, hB⟩ := h
    exact ⟨x, hA, hA, hB⟩
  · intro h
    obtain ⟨x, hA, _, hB⟩ := h
    exact ⟨x, hA, hB⟩
```

::::exercise (rating := 2) (name := "no-cons")
Prove que *no* é conservativo.

```lean
theorem no_cons {α : Type} : Cons (no : Det α) := by
  solution!
   intro E A B _ _
   constructor
   · intro h x hA hAB
     exact h x hA hAB.2
   · intro h x hA hB
     exact h x hA ⟨hA, hB⟩
```
::::

:::terse
- *Many*, no sentido de "relativamente muitos", não satisfaz EXT. Uma versão
  simples: "muitos A são B" quando os A que são B são mais da metade do
  universo `E`. Com um universo maior, a mesma sentença pode ficar falsa.
- `Set.ncard` é o número de elementos de um conjunto finito, a $`|A|` da
  notação matemática. Ela vem de `Mathlib.Data.Set.Card`.
:::

```lean
def many {α : Type} : Det α :=
  fun E A B => E.ncard < 2 * (A ∩ B).ncard
```

::::exercise (rating := 2) (name := "many-not-ext")
Prove que `many` não satisfaz EXT. Basta um universo `E` em que a relação
vale e um universo maior `E'` em que ela deixa de valer.

```lean
theorem many_not_ext : ¬ Ext (many : Det Nat) := by
  solution!
   intro h
   have h1 : (many : Det Nat) {0} {0} {0} := by
     simp [many]
   have h2 := (h {0} {0, 1} {0} {0} le_rfl le_rfl
     (by simp)).1 h1
   simp [many] at h1 h2
```
::::

:::terse
*Only*, como em *Only dwarfs sing during work*, não é conservativo.
:::

::::exercise (rating := 2) (name := "only-not-cons")
Prove que *only* não é conservativo. Basta escolher uma restrição e um escopo
para os quais as duas leituras da definição de `Cons` dão resultados
diferentes.

```lean
theorem only_not_cons : ¬ Cons (only : Det Entity) := by
  solution!
   intro h
   have hcons :
       (only : Det Entity) Set.univ ∅ (∅ ∩ Set.univ) := by
     intro x hx
     exact hx.1
   have hS : Entity.S ∈ (∅ : Set Entity) :=
     (h Set.univ ∅ Set.univ (Set.empty_subset _)
        (Set.subset_univ _)).2 hcons (Set.mem_univ Entity.S)
   exact hS
```
::::

:::terse
- *ISOM*: só importam as quantidades. Se `f` leva `E` bijetivamente em `E'`,
  então `D E A B` implica `D E' (f '' A) (f '' B)`.
- `f '' A` é a imagem de `A` por `f`, o conjunto dos `f x` com `x ∈ A`.
  `Set.BijOn f E E'` diz que `f` é uma bijeção de `E` em `E'`.
- Um quantificador é uma relação que satisfaz EXT, CONS e ISOM. O valor de
  `D E A B` depende então só de $`|A - B|` e $`|A \cap B|`.
- Os artigos também são quantificadores no sentido técnico desta seção. *a*
  tem o mesmo significado que *some*: vale quando $`|A \cap B| \geq 1`. *the*,
  na leitura russelliana de {ref "ModelChecking"}[Model checking], vale
  quando $`|A \cap B| = 1` e $`|A - B| = 0`. A gramática tradicional, porém,
  não vê *the* como expressão de quantidade, e sim como um modo de identificar
  um referente. Quantificador, aqui, é uma propriedade semântica; determinante
  é uma categoria sintática.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "Next, the relational perspective
suggests…" to "…the logical representation of quantifiers."
:::
::::

```lean
def Isom {α : Type} (D : Det α) : Prop :=
  ∀ (f : α → α) E E' A B, A ⊆ E → B ⊆ E →
    Set.BijOn f E E' → D E A B → D E' (f '' A) (f '' B)

theorem all_isom {α : Type} : Isom (all : Det α) := by
  intro f E E' A B _ _ _ h
  exact Set.image_mono h

theorem some_isom {α : Type} : Isom (some : Det α) := by
  intro f E E' A B _ _ _ h
  obtain ⟨x, hA, hB⟩ := h
  exact ⟨f x, ⟨x, hA, rfl⟩, ⟨x, hB, rfl⟩⟩
```

::::exercise (rating := 2) (name := "the-quant")

Na leitura de {ref "ModelChecking"}[Model checking], *The dwarf laughed*
diz que há exatamente um anão e que ele riu. Como relação entre conjuntos,
`the E A B` diz que `A` tem um único elemento e que ele está em `B`. Mostre
que `the` satisfaz EXT, CONS e ISOM. Assim, o artigo *the* é, no sentido
técnico desta seção, um quantificador.

```lean
def the {α : Type} : Det α :=
  fun _ A B => ∃ x, A = {x} ∧ x ∈ B

theorem the_ext {α : Type} : Ext (the : Det α) := by
  solution!
   intro E E' A B _ _ _
   rfl

theorem the_cons {α : Type} : Cons (the : Det α) := by
  solution!
   intro E A B _ _
   constructor
   · intro h
     obtain ⟨x, hA, hB⟩ := h
     exact ⟨x, hA, by rw [hA]; rfl, hB⟩
   · intro h
     obtain ⟨x, hA, _, hB⟩ := h
     exact ⟨x, hA, hB⟩

theorem the_isom {α : Type} : Isom (the : Det α) := by
  solution!
   intro f E E' A B _ _ _ h
   obtain ⟨x, hA, hB⟩ := h
   refine ⟨f x, ?_, ⟨x, hB, rfl⟩⟩
   rw [hA, Set.image_singleton]
```

::::

::::exercise (rating := 3) (name := "poss-not-isom")

O possessivo *Alice's*, como em *Alice's daggers are sharp*, ocupa a posição
de um determinante: `poss owns a A B` diz que todo `A` que `a` possui é `B`.
A relação de posse `owns` é um parâmetro. Mostre que `poss` satisfaz EXT e
CONS, mas não ISOM. Assim, as três condições são independentes: EXT e CONS
não bastam para fazer de um determinante um quantificador.

Dica: para ISOM, basta um exemplo pequeno em `Bool`, em que `false` possui
só `true`, e a bijeção `not`.

```lean
def poss {α : Type} (owns : α → α → Prop) (a : α) : Det α :=
  fun _ A B => ∀ x, x ∈ A → owns a x → x ∈ B

theorem poss_ext {α : Type} (owns : α → α → Prop) (a : α) :
    Ext (poss owns a) := by
  solution!
   intro E E' A B _ _ _
   rfl

theorem poss_cons {α : Type} (owns : α → α → Prop) (a : α) :
    Cons (poss owns a) := by
  solution!
   intro E A B _ _
   constructor
   · intro h x hA ho
     exact ⟨hA, h x hA ho⟩
   · intro h x hA ho
     exact (h x hA ho).2

theorem poss_not_isom :
    ¬ Isom (poss (fun _ x => x = true) false) := by
  solution!
   intro h
   have hb : Set.BijOn not Set.univ Set.univ := by
     refine ⟨fun _ _ => trivial, ?_, ?_⟩
     · intro x _ y _ hxy
       cases x <;> cases y <;> simp_all
     · intro y _
       exact ⟨!y, trivial, by simp⟩
   have h1 : poss (fun _ x => x = true) false
       Set.univ {false} ∅ := by
     intro x hx ho
     simp_all
   have h2 := h not Set.univ Set.univ {false} ∅
     (Set.subset_univ _) (Set.subset_univ _) hb h1
   obtain ⟨_, hx, _⟩ := h2 true ⟨false, rfl, rfl⟩ rfl
   exact hx
```

::::

```lean
end GQ
```

# Árvores numéricas
%%%
tag := "comp-trees"
%%%

:::terse
- Com EXT, CONS e ISOM, o valor de `Q A B` depende só de dois números:
  quantos A não são B ($`m = |A - B|`) e quantos A são B ($`n = |A \cap B|`).
  Cada caso possível é um par `(m, n)`.
- Por EXT e CONS, nem o universo nem $`B - A` importam.
- Nesta seção e na seguinte, os exemplos são sempre os mesmos
  quantificadores: *all*, *some*, *no* e *not all*; *at least three*, *at
  most three* e *exactly three*; *less than half*; e *an even number of*.
  Combinando-os, aparece também *at least three but not all*.

Organizar os pares numa árvore ajuda. Cada linha `row k` reúne os casos em que `A` tem `k` elementos, isto é, os pares com `m + n = k`. Da esquerda para a direita: `m` diminui e `n` aumenta. Na ponta esquerda, nenhum A é B; na direita, todo A é B.
:::

::::full
Em uma frase como *Todo aluno passou*, o determinante relaciona a restrição `A`
(os alunos) e o escopo `B` (quem passou). EXT, CONS e ISOM juntas garantem que
o valor de `Q A B` depende só de dois números: `m`, quantos A não são B, e
`n`, quantos A são B. Cada condição elimina uma informação. Por CONS, o que
está fora de `A` não importa (quem passou sem ser aluno é irrelevante). Por
EXT, o tamanho do universo não importa. Por ISOM, não importa quem são os
objetos, só quantos são.

Se só o par `(m, n)` importa, basta listar todos os pares e marcar em quais o
quantificador é verdadeiro. A árvore de números organiza os pares por linha.
A linha `k` reúne os casos com $`|A| = m + n = k`. Da esquerda para a
direita, `n` cresce. Assim, a borda esquerda é "nenhum A é B" e a borda
direita é "todo A é B". Para ler uma posição, tome `(1, 2)` na linha 3: há
três alunos, um não passou e dois passaram. Se o quantificador tem `+` ali, a
frase é verdadeira nessa situação.

:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, "Numerical Trees", from "Suppose a quantifier Q has
A as a first…" to "…both of these objects have property B.", with Figure 7.5.
:::

:::dev "Claude Opus 5.5" (year := 2026)
Texto gerado por IA. É um rascunho de explicação, não uma tradução do
CSwFP.
:::
::::

```lean
def row (k : Nat) : List (Nat × Nat) :=
  (List.range (k + 1)).map fun x => (k - x, x)
```

:::terse
- A árvore é a lista das suas linhas: `tree k` tem as linhas `0` a `k`. A
  árvore não tem fim, mas uma `List` é sempre finita; por isso o limite `k`.
:::

```lean
def tree (k : Nat) : List (List (Nat × Nat)) :=
  (List.range (k + 1)).map row

#eval tree 3
```

:::terse
- Para desenhar a árvore, `labelTree k cell` troca cada par `(m, n)` de
  `tree k` pelo texto `cell m n`, e `drawTree w` desenha as linhas de textos,
  cada um com largura `w`.
- `numberTree k` é a *árvore de números*: em cada posição, o próprio par. Até
  a linha `9`, todo par cabe em três caracteres.
:::

```lean
def labelTree (k : Nat) (cell : Nat → Nat → String) :
    List (List String) :=
  (tree k).map fun r => r.map fun (m, n) => cell m n

def drawTree (w : Nat) (rows : List (List String)) :
    String :=
  let last := rows.length - 1
  let lines := rows.mapIdx fun k cells =>
    let indent := (last - k) * (w + 1) / 2
    String.ofList (List.replicate indent ' ') ++
      String.intercalate " " cells
  String.intercalate "\n" lines

def numberTree (k : Nat) : String :=
  drawTree 3 (labelTree k fun m n => s!"{m},{n}")

#eval IO.println <| numberTree 3
```

::::exercise (rating := 1) (name := "tree-of-numbers")
Defina `treeOfNumbers k`, a lista dos pares de `tree k`, percorrida de cima
para baixo e da esquerda para a direita.

```lean
def treeOfNumbers (k : Nat) : List (Nat × Nat) :=
  solution!((tree k).flatten)

theorem treeOfNumbers_three :
    treeOfNumbers 3 =
      [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2),
       (3, 0), (2, 1), (1, 2), (0, 3)] :=
  solution!(by rfl)
```
::::

:::terse
- Um quantificador escolhe alguns pares da árvore: aqueles em que ele é
  verdadeiro. Aqui o quantificador é dado direto como uma função de `m` e
  `n`.
- Para saber se `q` vale num caso, basta saber se o par foi escolhido. Então
  a árvore de pares vira uma árvore de `+` e `-`. A função `patternTree k q`
  é o par de `numberTree k`: o mesmo `labelTree`, trocando cada par por `+`,
  se `q` vale nele, ou por `-`. Essa árvore é o *padrão* de `q`.
- Três exemplos de padrão: *at least three* ($`n \geq 3`), *less than
  half* ($`2n < m + n`) e *an even number of* ($`n` par).
:::

```lean
def patternTree (k : Nat) (q : Nat → Nat → Bool) :
    String :=
  drawTree 1 (labelTree k fun m n =>
    if q m n then "+" else "-")
```

```lean
#eval IO.println <| patternTree 5 fun _ n => n ≥ 3
#eval IO.println <| patternTree 5 fun m n => 2 * n < m + n
#eval IO.println <| patternTree 5 fun _ n => n % 2 == 0
```

:::terse
- Um quantificador também pode ser dado como uma função que recebe um
  universo (uma lista) e uma propriedade: o tipo `ListQuant`. {lean}`List.all`
  e {lean}`List.any` já têm esse tipo, e são *all* e *some*. *No* é
  `fun dom p => !dom.any p`: nenhum elemento de `dom` tem `p`.
- Um `ListQuant` é um determinante depois de CONS: o universo é o próprio `A`
  e a propriedade é `B`. Pode ser assim porque, por CONS, nada fora de `A`
  importa.
:::

::::full
Alguns padrões. *All* ($`m = 0`) tem `+` só na borda direita, porque nenhum A
fica fora de B. *No* ($`n = 0`) tem `+` só na borda esquerda. *Less than half*
($`n < m`) tem, na linha 2, `+` em `(2, 0)`, `-` em `(1, 1)` e `(0, 2)`.

O exercício `genTree` liga a árvore ao quantificador dado como uma função de
um universo e uma propriedade. Para cada `(m, n)`, ele monta um
universo concreto `[1, …, m + n]` em que exatamente `n` elementos têm a
propriedade, e pergunta ao quantificador. Qualquer universo
com essas contagens serve (ISOM).

:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "To get used to these representations…" to
the end of Exercise 7.3, without the exercises themselves.
:::

:::dev "Claude Opus 5.5" (year := 2026)
Comentário gerado por IA. É um rascunho de explicação, não uma tradução do
CSwFP.
:::
::::

```lean
abbrev ListQuant := List Nat → (Nat → Bool) → Bool
```

::::exercise (rating := 2) (name := "gen-tree")
Defina `genTree q k`, a lista dos pares `(m, n)` de `tree k` para os quais `q`
é verdadeiro num universo de `m + n` objetos dos quais exatamente `n` têm a
propriedade. Por exemplo, `(0, 3)` está na lista de `List.all`, porque se
todos os A são B, os 3 objetos de um A de 3 objetos têm a propriedade B.

```lean
def genTree (q : ListQuant) (k : Nat) : List (Nat × Nat) :=
  solution!(
    (tree k).flatten.filter fun (m, n) =>
      q (List.range' 1 (m + n)) (fun x => x ≤ n))

theorem genTree_all :
    genTree List.all 3 = [(0, 0), (0, 1), (0, 2), (0, 3)] :=
  solution!(by rfl)

theorem genTree_any :
    genTree List.any 3 =
      [(0, 1), (1, 1), (0, 2), (2, 1), (1, 2), (0, 3)] :=
  solution!(by rfl)

theorem genTree_no :
    genTree (fun dom p => !dom.any p) 3 =
      [(0, 0), (1, 0), (2, 0), (3, 0)] :=
  solution!(by rfl)
```
::::

# Representações lógicas para quantificadores
%%%
tag := "comp-num-repr"
%%%

:::terse
- O objetivo desta subseção é representar cada quantificador por uma
  expressão aritmética em `m` e `n`. Isso é possível porque, com EXT, CONS e
  ISOM, o valor de `Q A B` depende só de $`m = |A - B|` e $`n = |A \cap B|`.
- Os padrões de {ref "comp-trees"}[Árvores numéricas] já eram desenhados a
  partir de funções de `m` e `n`, como `fun _ n => n ≥ 3`: é o tipo do
  argumento de `patternTree`. `NumQuant` dá um nome a esse tipo. Por isso
  todo `NumQuant` pode ser desenhado como árvore.
:::

::::full
Esta subseção tira a conclusão da anterior. Um padrão na árvore é um
subconjunto dos pares de naturais. Por isso, o próprio quantificador pode ser
escrito como uma expressão aritmética em `m` e `n`, sem conjuntos e sem
listas: *all* é $`m = 0`, *no* é $`n = 0`, *at least k* é $`n \geq k` e *at
most k* é $`n \leq k`. Em Lean, essa expressão tem o tipo `NumQuant`, que é
justamente o tipo do argumento de `patternTree`. Por isso todo `NumQuant` pode
ser desenhado.

:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, "Logical Representations for Quantifiers", from
"The pairs of cardinals that characterize…" to the definitions of `allNum`,
`noNum`, `atleastNum` and `atmostNum`.
:::

:::dev "Claude Opus 5.5" (year := 2026)
Comentário gerado por IA. É um rascunho de explicação, não uma tradução do
CSwFP.
:::
::::

```lean
abbrev NumQuant := Nat → Nat → Bool

def allNum : NumQuant := fun m _ => m = 0
def noNum  : NumQuant := fun _ n => n = 0
def atLeastNum (k : Nat) : NumQuant := fun _ n => n ≥ k
def atMostNum  (k : Nat) : NumQuant := fun _ n => n ≤ k
```

:::terse
- Um `ListQuant` também vira um `NumQuant`: na posição `(m, n)`, `toNum q`
  aplica `q` a um universo de `m + n` objetos, `[1, …, m + n]`, com uma
  propriedade que vale para exatamente `n` deles, "ser no máximo `n`".
- Qualquer universo com essas contagens daria a mesma resposta: é ISOM.
- Assim podemos comparar as duas formas: o padrão de `List.all` é o de
  `allNum`, e o de *no* é o de `noNum`.
:::

```lean
def toNum (q : ListQuant) : NumQuant :=
  fun m n => q (List.range' 1 (m + n)) (fun x => x ≤ n)

theorem toNum_all :
    patternTree 5 (toNum List.all) =
      patternTree 5 allNum := by
  rfl

theorem toNum_no :
    patternTree 5 (toNum fun dom p => !dom.any p) =
      patternTree 5 noNum := by
  rfl
```

:::terse
- As operações lógicas sobre quantificadores viram operações sobre essas
  expressões. `Not Q` nega a expressão de `Q`. `Q₁ && Q₂` e `Q₁ || Q₂`
  combinam as duas expressões.
- Na árvore, a negação troca `+` por `-` em todas as posições. A conjunção
  marca com `+` só as posições marcadas nas duas árvores, e a disjunção, as
  marcadas em pelo menos uma.
- Um exemplo é *at least three but not all*, que fica `n ≥ 3` e não `m = 0`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "Logical operations on quantifiers can now be
handled compositionally…" to the definition of `atleast2butnotall`.
:::

:::dev "Claude Opus 5.5" (year := 2026)
Comentário gerado por IA. É um rascunho de explicação, não uma tradução do
CSwFP.

O ganho é a composicionalidade. As operações lógicas entre quantificadores
viram operações ponto a ponto nas expressões, e cada uma tem uma leitura na
árvore. *Not Q* troca `+` por `-` em todas as posições. *Q₁ and Q₂* marca
`+` só onde as duas árvores têm `+`. *Q₁ or Q₂* marca `+` onde pelo menos
uma tem. O padrão de *at least three but not all* é o de *at least three* sem a
borda direita. Ninguém precisou pensar em conjuntos: o significado da
expressão composta saiu do significado das partes.

A subseção seguinte usa essas árvores para perguntas como "se `Q` é
reflexivo, como é o seu padrão?". As árvores transformam propriedades
lógicas dos quantificadores em propriedades geométricas fáceis de ver.
:::
::::

```lean
def notNum (q : NumQuant) : NumQuant :=
  fun m n => !q m n

def andNum (q₁ q₂ : NumQuant) : NumQuant :=
  fun m n => q₁ m n && q₂ m n

def orNum (q₁ q₂ : NumQuant) : NumQuant :=
  fun m n => q₁ m n || q₂ m n

def atLeast3ButNotAll : NumQuant :=
  andNum (atLeastNum 3) (notNum allNum)

#eval IO.println <| patternTree 5 atLeast3ButNotAll
```

::::exercise (rating := 3) (name := "tree-patterns")

Defina `someNum`, `notAllNum` e `exactlyNum k`, as expressões de *some*,
*not all* e *exactly k*. Use `patternTree` para ver os padrões de *all*, *some*,
*no* e *not all*, e os de *at least three*, *at most three* e *exactly
three*. Depois, prove as relações entre eles: *some* é a negação de *no*,
*not all* é a negação de *all*, *exactly k* é a conjunção de *at least k* e
*at most k*, e *at most k* é a negação de *at least k + 1*.

Dica: depois de `funext m n`, `rw [Bool.eq_iff_iff]` transforma a igualdade
entre dois `Bool` numa equivalência entre proposições. Em seguida, `simp`
com as definições simplifica a meta, e `omega` resolve o que sobrar de
aritmética.

```lean
def someNum : NumQuant :=
  solution!(fun _ n => n > 0)

def notAllNum : NumQuant :=
  solution!(fun m _ => m > 0)

def exactlyNum (k : Nat) : NumQuant :=
  solution!(fun _ n => n = k)

theorem someNum_eq : someNum = notNum noNum := by
  solution!
   funext m n
   rw [Bool.eq_iff_iff]
   simp [someNum, notNum, noNum]
   omega

theorem notAllNum_eq : notAllNum = notNum allNum := by
  solution!
   funext m n
   rw [Bool.eq_iff_iff]
   simp [notAllNum, notNum, allNum]
   omega

theorem exactlyNum_eq (k : Nat) :
    exactlyNum k = andNum (atLeastNum k) (atMostNum k) := by
  solution!
   funext m n
   rw [Bool.eq_iff_iff]
   simp [exactlyNum, andNum, atLeastNum, atMostNum]
   omega

theorem atMostNum_eq (k : Nat) :
    atMostNum k = notNum (atLeastNum (k + 1)) := by
  solution!
   funext m n
   rw [Bool.eq_iff_iff]
   simp [atMostNum, notNum, atLeastNum]
```
::::

# Propriedades relacionais
%%%
tag := "comp-rel-props"
%%%

:::terse
- Quantificadores são relações entre conjuntos, então podemos estudar as
  propriedades dessas relações: reflexividade, simetria e monotonicidade.
- Cada propriedade tem dois lados. Nos conjuntos, é uma `Prop` sobre
  `GQ.Det`, como EXT, CONS e ISOM. Na árvore, é uma forma do padrão, uma
  `Prop` sobre `NumQuant`.
- A pergunta que se repete: se `Q` tem a propriedade, como é o seu padrão?

Começamos avaliando se {lean}`GQ.all` é reflexiva. O quantificador {lean}`GQ.some` não é reflexivo se aceitarmos a restrição vazia.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, "Relational Properties", from "As quantifiers are
relations…" to "…the quantifiers no and not all are not." CSwFP calls *some*
reflexive; with its own definition it is not, because of the empty set (see
`DEVIATIONS.md`).
:::
::::

```lean
namespace GQ

def Refl {α : Type} (D : Det α) : Prop :=
  ∀ E A, A ⊆ E → D E A A

theorem all_refl {α : Type} : Refl (all : Det α) := by
  intro E A ha x hx
  exact hx
```

::::exercise (rating := 1) (name := "some-not-refl")
Prove que *some* não é reflexivo.

```lean
theorem some_not_refl : ¬ Refl (some : Det Entity) := by
  solution!
   intro h
   obtain ⟨x, hx, h2⟩ := h Set.univ ∅ (Set.empty_subset _)
   exact hx
```
::::

:::terse
- Em `Q A A`, o escopo é a própria restrição. Nenhum elemento de `A` fica fora
  de `A`, então $`m = 0`; todos ficam dentro, então $`n = |A|`. `Q A A` é a
  posição `(0, |A|)`.
- Variando o tamanho de `A`, essas posições são `(0, 0)`, `(0, 1)`,
  `(0, 2)`, …: a borda direita da árvore. `Q` é reflexivo quando essa borda
  é toda `+`.
- A borda inclui o topo, `(0, 0)`, o caso em que `A` é vazio. É ali que
  *some* falha.
:::

```lean
def ReflNum (q : NumQuant) : Prop :=
  ∀ n, q 0 n

theorem allNum_refl : ReflNum allNum := by
  intro n
  rfl

#eval IO.println <| patternTree 5 allNum
#eval IO.println <| patternTree 5 (notNum noNum)
```

::::quiz
Se a borda direita do padrão de `Q` é toda `-`, que propriedade `Q` tem?
Qual quantificador do nosso elenco tem esse padrão? E *no*, tem?

:::quizSolution
`Q A A` é falso para todo `A`: `Q` é *irreflexivo*. Os padrões de *not all*
e de *no* mostram a borda direita de cada um:

```lean
#eval IO.println <| patternTree 5 (notNum allNum)
#eval IO.println <| patternTree 5 noNum
```

*Not all* é irreflexivo: sua borda direita é toda `-`. *No* não é: o topo,
com `A` vazio, é `+`, porque "nenhum A é A" é verdadeiro. E o resto da borda
é `-`, então *no* não é reflexivo nem irreflexivo.
:::
::::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "One can now study questions about tree
patterns…" to "…which relational property of Q does this reflect?"
:::
::::

:::terse
- `Q` é *simétrico* se `Q A B` e `Q B A` sempre têm o mesmo valor. *Some*
  é simétrico: "algum A é B" e "algum B é A" dizem a mesma coisa.
- Com um verbo intransitivo no escopo, inverter `A` e `B` leva o verbo para
  a restrição: *Alguma menina riu* tem o mesmo valor que *Alguém que riu era
  menina*. Já *Toda princesa riu* é verdadeira no modelo, e *Todos os que
  riram eram princesas* é falsa: *all* não é simétrico.
- Os quantificadores simétricos são exatamente os que cabem na posição `Q`
  de *There are Q*: *There are some dwarfs*, *There are no dragons*, *There
  are three wizards*, mas não \**There are all dwarfs* nem \**There are most
  dragons*.
:::

```lean
#eval (a girl laugh, a laugh girl)
#eval (every princess laugh, every laugh princess)
```

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "A relational property with linguistic
interest is symmetry…" to the end of the paragraph after Exercise 7.4,
"…(sentences of the form There are Q)", without the exercise itself.
:::

:::dev "Claude Opus 5.5" (year := 2026)
Comentário gerado por IA. Material para quem escrever o `full` desta parte,
não uma tradução do CSwFP.

A simetria fica mais visível com um verbo intransitivo no escopo, porque a
inversão leva o verbo para a restrição, numa oração relativa. *Alguns anões
comemoraram* equivale a *Alguns dos que comemoraram eram anões*, e *Nenhum
anão comemorou* a *Ninguém que comemorou era anão*: os dois lados dependem
só de $`|A \cap B|`, e a interseção não muda quando os conjuntos trocam de
lugar. Com *all*, a inversão muda o sentido: *Todos os anões comemoraram*
deixa que gigantes também tenham comemorado, *Todos os que comemoraram eram
anões* não deixa.

Além do elenco, *at most k*, *exactly k* e *an even number of* também são
simétricos, porque só dependem de `n`; *the* e *most* não são. Os exemplos
de *There are Q* marcados com `*` são inaceitáveis, e a razão é semântica, a
falta de simetria, não sintática.
:::
::::

```lean
def Symm {α : Type} (D : Det α) : Prop :=
  ∀ E A B, A ⊆ E → B ⊆ E → (D E A B ↔ D E B A)

theorem some_symm {α : Type} : Symm (some : Det α) := by
  intro E A B _ _
  constructor
  · intro h
    obtain ⟨x, hA, hB⟩ := h
    exact ⟨x, hB, hA⟩
  · intro h
    obtain ⟨x, hB, hA⟩ := h
    exact ⟨x, hA, hB⟩
```

::::exercise (rating := 2) (name := "symm-pattern")
Defina `SymmNum q`, a forma do padrão de um quantificador simétrico. Depois,
prove que *no* e *at least three* têm essa forma, e que *all* não tem.

Dica: em `Q A B`, `m` conta os A que não são B; em `Q B A`, conta os B que
não são A. O que muda entre os dois é só `m`.

```lean
def SymmNum (q : NumQuant) : Prop :=
  solution!(∀ m m' n, q m n = q m' n)

theorem noNum_symm : SymmNum noNum := by
  solution!
   intro m m' n
   rfl

theorem atLeastNum_symm : SymmNum (atLeastNum 3) := by
  solution!
   intro m m' n
   rfl

theorem allNum_not_symm : ¬ SymmNum allNum := by
  solution!
   intro h
   have h' := h 0 1 0
   simp [allNum] at h'
```
::::

:::terse
- `Q` é *MON↑* (monótono para cima no escopo) se `Q A B` continua
  verdadeiro quando `B` cresce. *All*, *some* e *at least three* são MON↑.
- `Q` é *MON↓* se `Q A B` continua verdadeiro quando `B` diminui. *No* e
  *not all* são MON↓.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "Another example of a relational property…"
to "…Examples are not all and no.", without Exercises 7.5 and 7.6, which
became the quizzes below. CSwFP's example *at least five* is *at least
three* here, as in the rest of the cast.
:::
::::

```lean
def MonUp {α : Type} (D : Det α) : Prop :=
  ∀ E A B B', A ⊆ E → B ⊆ B' → B' ⊆ E →
    D E A B → D E A B'

def MonDown {α : Type} (D : Det α) : Prop :=
  ∀ E A B B', A ⊆ E → B' ⊆ B → B ⊆ E →
    D E A B → D E A B'

theorem all_monUp {α : Type} : MonUp (all : Det α) := by
  intro E A B B' _ hB _ h x hx
  exact hB (h hx)
```

::::exercise (rating := 1) (name := "no-mon-down")
Prove que *no* é MON↓.

```lean
theorem no_monDown {α : Type} : MonDown (no : Det α) := by
  solution!
   intro E A B B' _ hB _ h x hA hB'
   exact h x hA (hB hB')
```
::::

```lean
end GQ
```

::::quiz
Compare os padrões de *all* e de *at least three*, que são MON↑. Que forma
tem o padrão de um quantificador MON↑? E o de um MON↓?

:::quizSolution
Acrescentar a `B` um elemento de `A` tira esse elemento de $`A - B` e o põe
em $`A \cap B`: a posição passa de `(m + 1, n)` para `(m, n + 1)`, uma casa à
direita na mesma linha. Então, num padrão MON↑, à direita de um `+` na mesma
linha só há `+`. Num padrão MON↓, o mesmo vale à esquerda.
:::
::::

:::terse
- As duas formas, escritas sobre `NumQuant`: `MonUpNum` e `MonDownNum`.
- *An even number of* não é nem MON↑ nem MON↓: no padrão, `+` e `-`
  alternam em cada linha.
:::

```lean
def MonUpNum (q : NumQuant) : Prop :=
  ∀ m n, q (m + 1) n → q m (n + 1)

def MonDownNum (q : NumQuant) : Prop :=
  ∀ m n, q m (n + 1) → q (m + 1) n

def evenNum : NumQuant := fun _ n => n % 2 == 0

theorem atLeastNum_monUp (k : Nat) :
    MonUpNum (atLeastNum k) := by
  intro m n h
  simp [atLeastNum] at *
  omega

theorem noNum_monDown : MonDownNum noNum := by
  intro m n h
  simp [noNum] at h
```

::::exercise (rating := 2) (name := "even-not-mon")
Prove que *an even number of* não é MON↑ nem MON↓. Basta uma posição do
padrão em que a forma falha.

```lean
theorem evenNum_not_monUp : ¬ MonUpNum evenNum := by
  solution!
   intro h
   have h' := h 0 0 (by decide)
   simp [evenNum] at h'

theorem evenNum_not_monDown : ¬ MonDownNum evenNum := by
  solution!
   intro h
   have h' := h 0 1 (by decide)
   simp [evenNum] at h'
```
::::

:::terse
- A monotonicidade tem uso linguístico. Sintagmas nominais com a mesma
  monotonicidade se coordenam com *and*, e com monotonicidades opostas, com
  *but*: *all men and some women*, *many English but no Dutch*.
- *Itens de polaridade negativa*, como *any* e *lift a finger*, aparecem no
  escopo de sintagmas MON↓: *No dwarf liked any of the elves*, mas não
  *Every dwarf liked any of the elves*. Os de polaridade positiva, como
  *hardly*, fazem o contrário.
- Pelos padrões, dá para responder como negação, conjunção e disjunção
  afetam a monotonicidade.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "An example for a quantifier that satisfies
neither MON↑ nor MON↓…" to "…are in the next exercises.", with examples
(7.10)–(7.15), and the sentence after Exercise 7.10, "The answers to these
questions can be tested…".
:::
::::

::::exercise (rating := 2) (name := "mon-not")
Prove que a negação troca MON↑ por MON↓, e MON↓ por MON↑.

```lean
theorem notNum_monUp (q : NumQuant) (h : MonUpNum q) :
    MonDownNum (notNum q) := by
  solution!
   intro m n hq
   simp [notNum] at *
   by_cases hq' : q (m + 1) n
   · have h' := h m n hq'
     simp_all
   · simpa using hq'

theorem notNum_monDown (q : NumQuant) (h : MonDownNum q) :
    MonUpNum (notNum q) := by
  solution!
   intro m n hq
   simp [notNum] at *
   by_cases hq' : q m (n + 1)
   · have h' := h m n hq'
     simp_all
   · simpa using hq'
```
::::

::::exercise (rating := 2) (name := "mon-and")
Prove que a conjunção de dois quantificadores MON↑ é MON↑, e que a de dois
MON↓ é MON↓.

```lean
theorem andNum_monUp (q₁ q₂ : NumQuant)
    (h₁ : MonUpNum q₁) (h₂ : MonUpNum q₂) :
    MonUpNum (andNum q₁ q₂) := by
  solution!
   intro m n h
   simp [andNum] at *
   exact ⟨h₁ m n h.1, h₂ m n h.2⟩

theorem andNum_monDown (q₁ q₂ : NumQuant)
    (h₁ : MonDownNum q₁) (h₂ : MonDownNum q₂) :
    MonDownNum (andNum q₁ q₂) := by
  solution!
   intro m n h
   simp [andNum] at *
   exact ⟨h₁ m n h.1, h₂ m n h.2⟩
```
::::

::::exercise (rating := 2) (name := "mon-or")
Prove que a disjunção de dois quantificadores MON↑ é MON↑, e que a de dois
MON↓ é MON↓.

```lean
theorem orNum_monUp (q₁ q₂ : NumQuant)
    (h₁ : MonUpNum q₁) (h₂ : MonUpNum q₂) :
    MonUpNum (orNum q₁ q₂) := by
  solution!
   intro m n h
   simp [orNum] at *
   cases h with
   | inl h => exact Or.inl (h₁ m n h)
   | inr h => exact Or.inr (h₂ m n h)

theorem orNum_monDown (q₁ q₂ : NumQuant)
    (h₁ : MonDownNum q₁) (h₂ : MonDownNum q₂) :
    MonDownNum (orNum q₁ q₂) := by
  solution!
   intro m n h
   simp [orNum] at *
   cases h with
   | inl h => exact Or.inl (h₁ m n h)
   | inr h => exact Or.inr (h₂ m n h)
```
::::

::::exercise (rating := 3) (name := "mon-up-down")
Mostre que, combinando um quantificador MON↑ com um MON↓, nada se pode
garantir: nem a conjunção nem a disjunção são sempre MON↑ ou MON↓.

Dica: use *at least one* e *at most three*. Antes de provar, desenhe os
padrões da conjunção e da disjunção com `patternTree`.

```lean
theorem andNum_up_down :
    ¬ ∀ q₁ q₂, MonUpNum q₁ → MonDownNum q₂ →
      MonUpNum (andNum q₁ q₂) ∨
        MonDownNum (andNum q₁ q₂) := by
  solution!
   intro h
   have hup := atLeastNum_monUp 1
   have hdown : MonDownNum (atMostNum 3) := by
     intro m n h
     simp [atMostNum] at *
     omega
   cases h _ _ hup hdown with
   | inl h =>
     have h' := h 0 3 (by decide)
     simp [andNum, atLeastNum, atMostNum] at h'
   | inr h =>
     have h' := h 0 0 (by decide)
     simp [andNum, atLeastNum, atMostNum] at h'

theorem orNum_up_down :
    ¬ ∀ q₁ q₂, MonUpNum q₁ → MonDownNum q₂ →
      MonUpNum (orNum q₁ q₂) ∨
        MonDownNum (orNum q₁ q₂) := by
  solution!
   intro h
   have hup := atLeastNum_monUp 3
   have hdown : MonDownNum (atMostNum 1) := by
     intro m n h
     simp [atMostNum] at *
     omega
   cases h _ _ hup hdown with
   | inl h =>
     have h' := h 0 1 (by decide)
     simp [orNum, atLeastNum, atMostNum] at h'
   | inr h =>
     have h' := h 0 2 (by decide)
     simp [orNum, atLeastNum, atMostNum] at h'
```
::::

:::terse
- A monotonicidade também pode ser na restrição. `Q` é *↑MON* se `Q A B`
  continua verdadeiro quando `A` cresce, e *↓MON* se continua verdadeiro
  quando `A` diminui. *Some* e *not all* são ↑MON; *all* e *no* são ↓MON.
- Ela explica a polaridade dentro da restrição: *All dwarfs who liked any
  of the elves were mistrusted*, mas não *Some dwarfs who liked any of the
  elves were mistrusted*.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "One can also study monotonicity in the
first argument…" to example (7.17).
:::
::::

::::exercise (rating := 2) (name := "left-mon-pattern")
Defina `UpMonNum q` e `DownMonNum q`, as formas do padrão de um quantificador
↑MON e de um ↓MON. Depois, prove que *some* e *not all* são ↑MON, e que
*all* e *no* são ↓MON.

Dica: acrescentar um elemento a `A` aumenta `m` ou `n` em um, conforme o
elemento esteja ou não em `B`.

```lean
def UpMonNum (q : NumQuant) : Prop :=
  solution!(∀ m n, q m n → q (m + 1) n ∧ q m (n + 1))

def DownMonNum (q : NumQuant) : Prop :=
  solution!(
    ∀ m n, (q (m + 1) n → q m n) ∧ (q m (n + 1) → q m n))

theorem some_upMon : UpMonNum (notNum noNum) := by
  solution!
   intro m n h
   simp_all [notNum, noNum]

theorem notAll_upMon : UpMonNum (notNum allNum) := by
  solution!
   intro m n h
   simp [notNum, allNum] at *
   omega

theorem all_downMon : DownMonNum allNum := by
  solution!
   intro m n
   simp [allNum]

theorem no_downMon : DownMonNum noNum := by
  solution!
   intro m n
   simp [noNum]
```
::::

# Quantificadores, autômatos e definibilidade
%%%
tag := "comp-automata"
%%%

:::terse
- Percorrendo os elementos de `A` e anotando `1` para cada um que está em
  `B` e `0` para cada um que não está, obtemos uma *palavra* sobre o
  alfabeto $`\{0, 1\}`. Aqui, `true` faz o papel de `1` e `false` o de `0`.
- O número de zeros é $`|A - B|` e o de uns é $`|A \cap B|`: a palavra
  leva à posição `(m, n)` da árvore.
- Um quantificador `q` determina a linguagem `langOf q`: as palavras cujas
  contagens caem num `+` do padrão de `q`.
- `Language Bool`, do Mathlib, é o tipo das linguagens sobre `Bool`: um
  conjunto de palavras, com as operações das linguagens formais.
:::

```lean
abbrev Word := List Bool

def wordOf (A : List Entity) (B : OnePlacePred) : Word :=
  A.map B

def accepts (q : NumQuant) (w : Word) : Bool :=
  q (w.count false) (w.count true)

def langOf (q : NumQuant) : Language Bool :=
  {w | accepts q w}

theorem mem_langOf (q : NumQuant) (w : Word) :
    w ∈ langOf q ↔ accepts q w :=
  Iff.rfl

#eval wordOf (entities.filter girl) laugh
#eval (accepts allNum (wordOf (entities.filter girl) laugh),
  accepts (notNum noNum)
    (wordOf (entities.filter girl) laugh))
```

:::terse
- *All girls laughed* é falsa e *Some girl laughed* é verdadeira: a palavra
  tem dois zeros e dois uns.
- A ordem dos elementos de `A` não importa: só contam os zeros e os uns.
  Duas palavras que são permutações uma da outra (`List.Perm`) têm as
  mesmas contagens, e `List.Perm.count_eq` diz exatamente isso.
- Então `langOf q` é fechada por permutação. É ISOM, visto nas palavras.
:::

```lean
theorem langOf_perm (q : NumQuant) {v w : Word}
    (h : v.Perm w) (hv : v ∈ langOf q) :
    w ∈ langOf q := by
  rw [mem_langOf, accepts] at *
  rw [← h.count_eq, ← h.count_eq]
  exact hv
```

:::terse
- As operações sobre `NumQuant` são operações sobre linguagens. A negação
  `notNum` dá o complemento, `ᶜ`: as palavras que `q` não aceita.
:::

```lean
theorem langOf_notNum (q : NumQuant) :
    langOf (notNum q) = (langOf q)ᶜ := by
  ext w
  show accepts (notNum q) w ↔ ¬ accepts q w
  simp [accepts, notNum]
```

::::exercise (rating := 2) (name := "lang-and-or")
Prove que a conjunção `andNum` dá a interseção das linguagens, `⊓`, e que
a disjunção `orNum` dá a união, `+`.

```lean
theorem langOf_andNum (q₁ q₂ : NumQuant) :
    langOf (andNum q₁ q₂) = langOf q₁ ⊓ langOf q₂ := by
  solution!
   ext w
   rw [Language.mem_inf, mem_langOf, mem_langOf,
     mem_langOf]
   simp [accepts, andNum]

theorem langOf_orNum (q₁ q₂ : NumQuant) :
    langOf (orNum q₁ q₂) = langOf q₁ + langOf q₂ := by
  solution!
   ext w
   rw [Language.mem_add, mem_langOf, mem_langOf,
     mem_langOf]
   simp [accepts, orNum]
```
::::

:::terse
- *All* aceita as palavras sem nenhum `0`: as feitas só de `1`. É a
  linguagem `1∗`, o fecho de Kleene `∗` da linguagem que tem só a palavra
  `[true]`.
:::

::::exercise (rating := 3) (name := "all-kstar")
Prove que a linguagem de *all* é `{[true]}∗`.

```lean
open Computability in
theorem langOf_allNum :
    langOf allNum = ({[true]} : Language Bool)∗ := by
  solution!
   ext w
   rw [mem_langOf, Language.mem_kstar]
   simp only [accepts, allNum, List.count_eq_zero,
     decide_eq_true_eq]
   constructor
   · intro h
     refine ⟨w.map fun _ => [true], ?_, ?_⟩
     · induction w with
       | nil => rfl
       | cons b w ih =>
         simp only [List.mem_cons, not_or] at h
         obtain ⟨hb, hw⟩ := h
         cases b
         · exact absurd rfl hb
         · rw [List.map_cons, List.flatten_cons, ← ih hw]
           rfl
     · intro y hy
       simp only [List.mem_map] at hy
       obtain ⟨_, _, rfl⟩ := hy
       rfl
   · intro h
     obtain ⟨L, rfl, hL⟩ := h
     simp only [List.mem_flatten, not_exists, not_and]
     intro y hy
     rw [hL y hy]
     simp
```
::::

:::terse
- Um autômato finito que aceita exatamente as palavras de `langOf q`
  computa `q`.
- Os quantificadores definíveis em primeira ordem (com $`\forall`,
  $`\exists`, igualdade e os predicados da restrição e do escopo) são
  exatamente os computados por um autômato finito acíclico e invariante
  por permutação (van Benthem).
- *An even number of* pede um autômato com ciclo. *Most* não tem autômato
  finito nenhum: é preciso memória para comparar $`|A - B|` e
  $`|A \cap B|`. Nenhum dos dois é definível em primeira ordem.
- Por isso *most* ficou fora da tradução para a lógica de primeira ordem
  em {ref "ModelChecking"}[Model checking]. Na interpretação direta, ele é
  uma função como as outras.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.2, from "Quantifiers correspond to automata that
accept strings over a binary alphabet…" to "…the numbers of elements in
A − B and A ∩ B)."
:::
::::

```lean
end Composition
```
