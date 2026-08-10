/-
Exercícios do capítulo 3 — Funções, tipos e abstração

Acompanha `CSwL/Chapter03.lean`. As páginas citadas são as de van Eijck &
Unger, capítulo 2 — que é a fonte deste capítulo, e que aqui é leitura, sem
aula: estes exercícios são o lugar onde ele é cobrado.

Substitua cada `sorry` pela sua resposta. Não altere os enunciados.
As questões marcadas com ✎ são discursivas: responda em `Exercises/RESPOSTAS.md`.

Conjunto, relação, composição e função característica **não** são definidos
aqui: vêm da Mathlib (que chega pela dependência `cslib`). É de propósito —
`Set`, `∅`, `ᶜ`, `⊆`, `∪`, `∩`, `Rel`, `flip`, `Relation.Comp`, `Equivalence`
e `Setoid` já existem, com notação e lemas prontos, e aprender a achá-los é
parte do trabalho.

A consequência é que vários exercícios do capítulo *são* lemas que a Mathlib
já tem provados. Quando for o caso, o enunciado diz qual é o lema e proíbe
usá-lo: o exercício é a prova, não a citação. Onde não há proibição, vale
tudo — inclusive `exact?` para encontrar o lema.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Rel
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Setoid.Basic

namespace Exercises.Chapter03

variable {α β : Type}

/-! ## §2.1 Conjuntos

Na Mathlib, `Set α` é o tipo dos conjuntos de elementos de `α`, e é definido
justamente pela função característica do capítulo (`α → Prop`) — só que com
notação:

| capítulo                       | Lean             |
|--------------------------------|------------------|
| `x ∈ A`                        | `x ∈ A`          |
| compreensão, "os `x` com `p x`"| `{x \| p x}`     |
| `∅`                            | `∅`              |
| complemento de `A`             | `Aᶜ`             |
| `A ⊆ B`                        | `A ⊆ B`          |
| `A ∪ B`, `A ∩ B`               | `A ∪ B`, `A ∩ B` |

Duas coisas valem saber antes de começar:

* `x ∈ A` é, por definição, `A x` — então uma prova de `x ∈ {y | p y}` é uma
  prova de `p x`, e `x ∈ Aᶜ` é `x ∈ A → False`. Não há nada a desembrulhar.
* dois conjuntos são iguais quando têm os mesmos elementos, e é `Set.ext` quem
  diz isso: de `∀ x, x ∈ A ↔ x ∈ B` ele conclui `A = B`. Com `Set.ext` dá para
  provar igualdade de conjuntos direto, sem passar por dupla inclusão.

Os dois exemplos abaixo já estão provados; leia-os como modelo de como as
provas deste arquivo se parecem.
-/

example (A B : Set α) : A ∩ B ⊆ A ∪ B := by
  intro x hx
  exact Or.inl hx.1

example : {n : Nat | n < 3} ∩ {n : Nat | 1 < n} = {2} := by
  apply Set.ext
  intro n
  constructor
  · intro ⟨h1, h2⟩
    have h1' : n < 3 := h1
    have h2' : 1 < n := h2
    show n = 2
    omega
  · intro (h : n = 2)
    exact ⟨show n < 3 by omega, show 1 < n by omega⟩

/-! ### Exercício 2.1 (p. 17)

Explique por que `∅ ⊆ A` vale para todo conjunto `A`.

Aqui, prove. O argumento é vacuoso, e a prova deve exibir isso.

**Não vale usar `Set.empty_subset`** (nem `simp`, que o encontra): esse lema é
exatamente o enunciado, e citá-lo apagaria o exercício.
-/

theorem ex_2_1 (A : Set α) : ∅ ⊆ A := sorry

/-! ### Exercício 2.2 (p. 17)

Explique a diferença entre `∅` e `{∅}`.

Para provar que são diferentes é preciso poder falar de conjuntos *de*
conjuntos: `{∅}` é o conjunto cujo único elemento é `∅`, e portanto vive em
`Set (Set α)`.

**Não vale usar `Set.singleton_ne_empty`, `Set.empty_ne_singleton` nem
`simp`.** Prove à mão: suponha a igualdade, exiba um elemento de `{∅}` e note
que ele teria de pertencer a `∅`.
-/

theorem ex_2_2 : (∅ : Set (Set α)) ≠ ({∅} : Set (Set α)) := sorry

/-! ✎ Em `RESPOSTAS.md`: diga em uma frase qual é a diferença, e qual é a
cardinalidade de cada um. -/

/-! ### Exercício 2.3 (p. 17)

Verifique que o complemento do complemento de `A` é `A`.

Use `Set.ext`. Uma das duas direções precisa de raciocínio clássico: vale
`Classical.byContradiction`, `Classical.em` ou `Classical.byCases`.

**Não vale usar `compl_compl`** (nem `simp`, nem `tauto`, nem `grind`): a
Mathlib prova esse lema para qualquer álgebra de Boole, e conjuntos são uma.
Aqui o exercício é o argumento sobre elementos.
-/

theorem ex_2_3 (A : Set α) : Aᶜᶜ = A := sorry

/-! ✎ Em `RESPOSTAS.md`: qual das duas inclusões precisou do argumento
clássico, e por quê? -/

/-! ## §2.2 Relações

Uma relação binária entre `α` e `β` é, na Mathlib, `Rel α β` — abreviação de
`α → β → Prop`. As operações do capítulo têm nome:

| capítulo                  | Lean                        |
|---------------------------|-----------------------------|
| `R` é uma relação sobre `A` | `R : Rel α α`             |
| `R ⊆ S`                   | `R ≤ S`                     |
| `R = S`                   | `R = S` (via `le_antisymm`) |
| conversa `R˘`             | `flip R`                    |
| composição `R ∘ S`        | `Relation.Comp R S`         |
| `R` é transitiva          | `IsTrans α R`               |

Sobre a tabela:

* `R ≤ S` é a inclusão: desembrulhada, é `∀ x y, R x y → S x y`. Então
  `intro x y h` entra nela, e `h x y hxy` a usa.
* de `R ≤ S` e `S ≤ R` sai `R = S` por `le_antisymm` — é a dupla inclusão, e é
  onde a extensionalidade se esconde.
* transitividade **não** se escreve mais `Transitive R`: esse nome está
  deprecated na Mathlib desde 2026-02-20, em favor da classe `IsTrans α R`,
  cujo único campo é `trans : ∀ a b c, r a b → r b c → r a c`. Construa uma
  instância com `⟨fun x y z hxy hyz => ...⟩`, e use uma que já esteja no
  contexto com `_root_.trans hxy hyz`. Pelo mesmo motivo, `Reflexive` e
  `Symmetric` deram lugar a `Std.Refl` e `Std.Symm`.
* existe ainda `SetRel α β := Set (α × β)`, a relação como *conjunto de pares*
  — que é literalmente a definição do livro, com `⊆`, `○` (composição) e
  `.inv` (conversa). Não a usamos aqui porque `Equivalence` e `IsTrans` falam
  de `Rel`, mas vale abrir `Mathlib/Data/Rel.lean` e ver: o exercício 2.8
  aparece lá provado, com o nome `SetRel.isTrans_iff_comp_subset_self`.
-/

/-! ### Exercício 2.4 (p. 18)

Tome `A` como o conjunto {Kasparov, Karpov, Anand}. Encontre `A × A`.

Como `A` é finito, o produto cartesiano é finito e a Mathlib o calcula:
`Finset` é o tipo dos conjuntos finitos, `Fintype α` é a evidência de que `α`
tem finitos elementos (e dá `Finset.univ`, o conjunto de todos eles), e `s ×ˢ t`
é o produto cartesiano de dois `Finset`. Construa `A × A` e prove que tem nove
elementos.
-/

inductive Player where
  | kasparov | karpov | anand
deriving Repr, DecidableEq

/-- A evidência de que `Player` é finito: a lista dos seus elementos, mais a
prova de que não falta ninguém. (O normal seria `deriving Fintype`, mas o
gerador automático está quebrado nesta versão da Mathlib — então a instância
vai à mão, o que também mostra o que um `Fintype` é.) -/
instance : Fintype Player :=
  ⟨{.kasparov, .karpov, .anand}, fun x => by cases x <;> decide⟩

/-- Todos os pares de players, como conjunto finito. -/
def playerPairs : Finset (Player × Player) := sorry

theorem ex_2_4 : playerPairs.card = 9 := sorry

/-! ### Exercício 2.5 (p. 18)

Qual é a composição de `{(n, n + 2) | n ∈ ℕ}` com ela mesma?

Enuncie a resposta e prove.
-/

def plusTwo : Rel Nat Nat := fun a b => b = a + 2

theorem ex_2_5 (a c : Nat) : Relation.Comp plusTwo plusTwo a c ↔ c = a + 4 := sorry

/-! ### Exercício 2.6 (p. 18)

Mostre que de `R˘ ⊆ R` segue que `R = R˘`.

A Mathlib tem `Std.Symm.flip_eq : flip r = r` para relações simétricas. Usá-lo
é permitido — mas então o trabalho é seu de construir a instância `Std.Symm R`
a partir de `h`, que é o mesmo argumento. A prova direta é mais curta.
-/

theorem ex_2_6 (R : Rel α α) (h : flip R ≤ R) : R = flip R := sorry

/-! ### Exercício 2.7 (p. 19)

Quais das relações seguintes são transitivas?

1. {(1,2), (2,3), (3,4)}
2. {(1,2), (2,3), (3,4), (1,3), (2,4)}
3. {(1,2), (2,3), (3,4), (1,3), (2,4), (1,4)}
4. {(1,2), (2,1)}
5. {(1,1), (2,2)}

Estas relações são finitas, e por isso podem ser dadas como o `Finset` dos seus
pares — e aí a transitividade *se decide*: escreva-a como uma proposição sobre
os pares do `Finset` e o `decide` calcula a resposta.

Complete `isTransitive` e depois decida os cinco casos. É `abbrev`, e não `def`,
para que a instância `Decidable` seja encontrada através da definição — trocar
por `def` faz o `decide` falhar com `failed to synthesize Decidable
(isTransitive r3)`, porque a busca de instâncias não desdobra um `def`.
-/

abbrev isTransitive (r : Finset (Nat × Nat)) : Prop := sorry

def r1 : Finset (Nat × Nat) := {(1,2), (2,3), (3,4)}
def r2 : Finset (Nat × Nat) := {(1,2), (2,3), (3,4), (1,3), (2,4)}
def r3 : Finset (Nat × Nat) := {(1,2), (2,3), (3,4), (1,3), (2,4), (1,4)}
def r4 : Finset (Nat × Nat) := {(1,2), (2,1)}
def r5 : Finset (Nat × Nat) := {(1,1), (2,2)}

theorem ex_2_7_1 : ¬ isTransitive r1 := sorry
theorem ex_2_7_2 : ¬ isTransitive r2 := sorry
theorem ex_2_7_3 :   isTransitive r3 := sorry
theorem ex_2_7_4 : ¬ isTransitive r4 := sorry
theorem ex_2_7_5 :   isTransitive r5 := sorry

/-! ### Exercício 2.8 (p. 19)

Verifique que uma relação `R` é transitiva se e somente se `R ∘ R ⊆ R`.

**Não vale usar `SetRel.isTrans_iff_comp_subset_self`**, que é este enunciado
na versão "relação como conjunto de pares". Prove as duas direções.
-/

theorem ex_2_8 (R : Rel α α) : IsTrans α R ↔ Relation.Comp R R ≤ R := sorry

/-! ### Exercício 2.9 (p. 19)

Você pode dar um exemplo de relação transitiva `R` para a qual `R ∘ R = R`
não vale?

Exiba a testemunha completando `counterexample` e prove as duas coisas: que
ela é transitiva, e que a composição com ela mesma não lhe é igual.
-/

def counterexample : Rel Nat Nat := sorry

theorem ex_2_9_transitive : IsTrans Nat counterexample := sorry
theorem ex_2_9_different :
    Relation.Comp counterexample counterexample ≠ counterexample := sorry

/-! ## §2.3 Funções -/

/-! ### Exercício 2.10 (p. 21)

A função sucessor `s : ℕ → ℕ` é dada por `n ↦ n + 1`. Qual é a composição de
`s` com ela mesma?

`∘` é `Function.comp`, e duas funções são iguais quando concordam em todo
ponto — é o que `funext` diz.
-/

def s : Nat → Nat := fun n => n + 1

theorem ex_2_10 : s ∘ s = fun n => n + 2 := sorry

/-! ### Exercício 2.11 (p. 21)

`≤` é uma relação binária sobre os naturais. Qual é a função característica
correspondente?

Escreva a função e prove que ela é adequada — que responde `true` exatamente
quando a relação vale.

Aqui `Prop` e `Bool` se encontram: `m ≤ n` é uma proposição, `leChar m n` é um
cálculo. A ponte é `decide`, e os lemas que a atravessam são
`decide_eq_true_iff`, `of_decide_eq_true` e `decide_eq_true`.
-/

def leChar : Nat → Nat → Bool := sorry

theorem ex_2_11 (m n : Nat) : leChar m n = true ↔ m ≤ n := sorry

/-! ### Exercício 2.12 (p. 21)

Seja `f : A → B` uma função. Mostre que a relação `R` dada por `(x, y) ∈ R`
se e somente se `f x = f y` é uma relação de equivalência sobre `A`.

`Equivalence R` é a estrutura com os três campos `refl`, `symm` e `trans`;
`Setoid α` é a mesma coisa empacotada com a relação, e é o que a Mathlib usa
para quocientes.

**Não vale usar `Setoid.ker`**: é exatamente esta relação, já construída na
Mathlib com a prova de que é de equivalência. Prove os três campos.
-/

def kernel (f : α → β) : Rel α α := fun x y => f x = f y

theorem ex_2_12 (f : α → β) : Equivalence (kernel f) := sorry

/-- O mesmo fato, empacotado: um `Setoid` é uma relação mais a prova de que ela
é de equivalência. Reaproveite `ex_2_12`. -/
def kernelSetoid (f : α → β) : Setoid α := sorry

/-! ## §2.4 Cálculo lambda -/

/-! ### Exercício 2.13 (p. 26)

Outro exemplo de função de ordem superior é `λf λx ↦ f (f x)`, que aplica uma
função duas vezes a uma entrada dada. Ponha-a para trabalhar reduzindo:

    (λf λx ↦ f (f x)) (λy ↦ 1 + y)
-/

def twice (f : α → α) : α → α := sorry

/-- O resultado da redução. -/
theorem ex_2_13 : twice (fun y => 1 + y) = fun x => 2 + x := sorry

example : twice (fun y => 1 + y) 0 = 2 := sorry

/-! ### Exercício 2.14 (p. 26–27) ✎

Um aspecto do cálculo lambda é que reduções podem não terminar. Observe o
comportamento de redução de `(λx ↦ x x) (λx ↦ x x)`, e depois de
`(λx ↦ x x x) (λx ↦ x x x)`.

Este exercício **não se enuncia em Lean**, e a razão é o assunto da questão.
Responda em `RESPOSTAS.md`:

1. Reduza `(λx ↦ x x) (λx ↦ x x)` um passo. O que se obtém?
2. Descomente a linha abaixo e leia a mensagem de erro. O que o Lean está
   reclamando, e o que isso diz sobre por que o termo não pode existir aqui?
3. Qual é a relação entre "a redução não termina" e "o termo não tem tipo"?
-/

-- def omega := (fun x => x x) (fun x => x x)

/-! ## §2.5 Tipos na gramática e na computação -/

/-! ### Exercício 2.15 (p. 28)

Atribua tipos às expressões lambda do exemplo (2.6) da página 27:

    S  = Dorothy likes Toto
    NP = Dorothy
    VP = λy ↦ y likes Toto
    V  = λx λy ↦ y likes x
    NP = Toto

Os dois tipos básicos são `e`, das entidades, e `t`, dos valores de verdade.
Complete o léxico e as duas construções; ao compilar, o verificador de tipos
confirma a atribuição que o exercício pede.
-/

/-- O domínio de entidades deste fragmento: duas, as do exemplo. -/
inductive Entity where
  | dorothy | toto
deriving Repr, DecidableEq

abbrev e := Entity
abbrev t := Prop

def dorothy : e := .dorothy
def toto : e := .toto

/-- O predicado `likes` fica sem definição: o exercício é sobre tipos, e
qualquer definição serviria. `opaque` declara o nome com o tipo, sem corpo. -/
opaque likes : e → e → t

/-- `VP` — de tipo `e → t`: falta o sujeito. -/
def vp : e → t := sorry

/-- `S` — de tipo `t`: nada falta. -/
def sentence : t := sorry

/-! ✎ Em `RESPOSTAS.md`: escreva o tipo de cada um dos cinco nós (S, NP, VP,
V, NP) e diga qual operação leva do tipo de `V` ao tipo de `VP`. -/

/-! ### Exercício 2.16 (p. 28) ✎

E o termo `(λx ↦ x x) (λx ↦ x x)` do exercício 2.14? Você consegue achar um
tipo para ele?

Responda em `RESPOSTAS.md`. Atenção: a resposta é negativa, e uma resposta
completa explica *por que* nenhuma atribuição funciona — tente construir a
atribuição e mostre onde ela falha.
-/

/-! ### Exercício 2.17 (p. 30)

Adjetivos combinam com nomes para formar nomes complexos: *friendly* combina
com *wizard* para formar *friendly wizard*. Adjetivos são, portanto, de tipo
`N → N`.

Ache um tipo para o advérbio *very*, tal que se possa construir *very
friendly wizard* e *very very friendly wizard*. (Assuma que as expressões se
estruturam como `(very friendly) wizard` e `(very (very friendly)) wizard`.)
-/

abbrev N := String
abbrev Adj := N → N

def wizard : N := "wizard"
def friendly : Adj := fun n => "friendly " ++ n

/-! Descobrir o **tipo** de `very` é o exercício, então a assinatura não está
dada. Escreva a definição completa — nome, tipo e corpo — no lugar indicado, e
descomente as duas verificações abaixo. Elas só compilam se o tipo estiver
certo, e é isso que faz delas a resposta. -/

-- def very : ... := ...

-- example : very friendly wizard = "very friendly wizard" := by rfl
-- example : very (very friendly) wizard = "very very friendly wizard" := by rfl

/-! ✎ Em `RESPOSTAS.md`: escreva o tipo de `very` e explique por que ele
permite as duas construções acima. -/

end Exercises.Chapter03
