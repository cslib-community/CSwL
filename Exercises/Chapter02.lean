import Mathlib.Data.Set.Basic

/-
Exercícios do capítulo 2 — Programação funcional

Acompanha `CSwL/Chapter02.lean`, e não pressupõe nada além dele: cada seção
daqui exercita uma seção de lá, na mesma ordem.

Leitura de apoio, para quem quiser mais Lean do que o curso pede:
*Functional Programming in Lean*, capítulo 1,
https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/

Substitua cada `sorry` pela sua resposta. Nas provas, use só estas táticas:

    rfl        fecha um objetivo `a = b` quando os dois lados calculam o mesmo
    decide     fecha um objetivo decidível calculando a resposta
    intro h    introduz uma hipótese, para provar uma implicação
    exact e    fornece o termo que é a prova
    constructor  parte um ∧ ou um ↔ em dois objetivos
    simp       simplifica o objetivo
    simp [f]   idem, desdobrando também a definição `f`
    omega      resolve aritmética linear em Nat e Int

Duas notações de prova aparecem sem ser táticas: `⟨t, h⟩` monta um par (para
provar uma conjunção ou exibir a testemunha de um existencial), e `h.1`/`h.2`
desmontam um par que está numa hipótese.
-/

namespace Exercises.Chapter02

/-! ## 1. Avaliar e inspecionar

Duas ordens úteis: `#eval` calcula uma expressão, `#check` diz o tipo dela sem
calcular. No VS Code o resultado aparece no painel do Lean, à direita.
-/

#eval 2 + 3
#check 2 + 3

/-! `Nat` são os naturais — inteiros a partir de zero. Subtração em `Nat` não
desce abaixo de zero: `2 - 5` é `0`, não `-3`. Quem precisa de negativos usa
`Int`. -/

#eval (2 : Nat) - 5
#eval (2 : Int) - 5

/-- **E0.1.** Escreva uma expressão que calcule 42, usando ao menos uma
multiplicação e uma soma. -/
def fortyTwo : Nat := sorry

example : fortyTwo = 42 := sorry

/-! ## 2. Definir funções

`def nome (arg : Tipo) : TipoDoResultado := corpo`. O tipo do resultado vem
depois dos dois-pontos, e o corpo tem de produzir aquele tipo.
-/

def double (n : Nat) : Nat := 2 * n

#eval double 21

/-- **E0.2.** `triple n` devolve o triplo de `n`. -/
def triple (n : Nat) : Nat := sorry

example : triple 5 = 15 := sorry

/-- **E0.3.** `sumOfSquares m n` devolve `m² + n²`. -/
def sumOfSquares (m n : Nat) : Nat := sorry

example : sumOfSquares 3 4 = 25 := sorry

/-! ## 3. Condicionais e comparações

`if c then a else b` exige que `c` seja decidível — o que vale para as
comparações usuais. Note `==` para o teste que devolve `Bool`, distinto de `=`,
que é a afirmação de igualdade.
-/

def max' (m n : Nat) : Nat := if m ≥ n then m else n

#eval max' 3 7
#eval (3 == 3)
#check (3 = 3)

/-- **E0.4.** `isPositive n` responde se `n` é maior que zero. -/
def isPositive (n : Nat) : Bool := sorry

example : isPositive 5 = true := sorry
example : isPositive 0 = false := sorry

/-! ## 4. Casamento de padrão e recursão

Um `Nat` é ou `0` ou o sucessor de outro `Nat`. Uma função pode ser definida
tratando os dois casos separadamente — é o casamento de padrão:

O caso `n + 1` dá acesso a `n`, que é menor. Por isso a recursão termina, e
Lean aceita a definição: ele verifica que ela termina, e recusa se não vê como.
-/

def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5

/-- **E0.5.** `sumTo n` devolve `0 + 1 + ... + n`. -/
def sumTo : Nat → Nat
  | 0 => sorry
  | n + 1 => sorry

example : sumTo 4 = 10 := sorry

/-! ## 5. Listas

Uma lista é ou vazia, `[]`, ou um elemento seguido de uma lista, `x :: xs`.
Recursão sobre lista tem a mesma forma da recursão sobre `Nat`.
-/

def length' : List Nat → Nat
  | []      => 0
  | _ :: xs => 1 + length' xs

#eval length' [10, 20, 30]

/-- **E0.6.** `sumList` soma os elementos de uma lista. -/
def sumList : List Nat → Nat
  | []      => sorry
  | x :: xs => sorry

example : sumList [1, 2, 3, 4] = 10 := sorry

/-- **E0.7.** `countZeros` conta quantos zeros a lista tem. -/
def countZeros : List Nat → Nat
  | []      => sorry
  | x :: xs => sorry

example : countZeros [0, 1, 0, 2, 0] = 3 := sorry

/-! ## 6. Tipos próprios

`inductive` define um tipo novo listando as formas que seus valores podem ter.
Cada forma é um construtor. `deriving Repr` faz o `#eval` saber exibir valores
do tipo.
-/

inductive Color where
  | red | green | blue
deriving Repr, DecidableEq

def isWarm : Color → Bool
  | .red   => true
  | .green => false
  | .blue  => false

#eval isWarm .red

/-- **E0.8.** Complete o tipo com os três dias que faltam, e depois `isWeekend`,
que responde se o dia é sábado ou domingo. -/
inductive Day where
  | monday | tuesday | wednesday
deriving Repr, DecidableEq

def isWeekend : Day → Bool := sorry

/-! ## 7. Afirmar e provar

Até aqui, tudo foi cálculo. Agora o outro modo: `Prop` é o tipo das
afirmações, e provar uma afirmação é construir um termo do tipo dela.

`theorem nome : afirmação := prova`, ou `:= by tática`.

A tática `rfl` fecha um objetivo `a = b` quando os dois lados calculam o mesmo
valor. É a mesma ideia dos `example` que você já viu acima.
-/

theorem two_plus_two : 2 + 2 = 4 := by rfl

/-- `decide` fecha objetivos que a máquina pode resolver calculando. -/
theorem three_lt_five : 3 < 5 := by decide

/-- `omega` resolve aritmética linear, inclusive com variáveis. -/
theorem add_comm_two (n : Nat) : n + 2 = 2 + n := by omega

/-- **E0.9.** Prove, escolhendo a tática. -/
theorem seven_times_six : 7 * 6 = 42 := sorry

/-- **E0.10.** Prove. Uma variável aparece, então `rfl` não basta. -/
theorem double_eq (n : Nat) : double n = n + n := sorry

/-! ## 8. Implicação e conjunção

Provar `P → Q` é: suponha `P`, derive `Q`. A tática `intro h` faz a suposição e
chama `h` a prova de `P`; depois disso o objetivo passa a ser `Q`, e `h` está
disponível para usar com `exact`.

Provar `P ∧ Q` é provar as duas coisas: `constructor` divide em dois objetivos.
Da hipótese, `h.1` e `h.2` extraem cada lado.

Provar `P ∨ Q` é provar *um* dos dois, e dizer qual: `Or.inl` para o esquerdo,
`Or.inr` para o direito.
-/

theorem imp_example (P : Prop) : P → P := by
  intro h
  exact h

theorem and_example : 1 < 2 ∧ 2 < 3 := by
  constructor
  · decide
  · decide

/-- **E0.11.** Prove. Note que há duas hipóteses a introduzir. -/
theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := sorry

/-- **E0.12.** Prove. -/
theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := sorry

/-! ## 9. Existência

Provar `∃ x, P x` é exibir um `x` e mostrar que ele serve. A notação `⟨t, h⟩`
faz isso: `t` é a testemunha, `h` é a prova de que ela funciona.
-/

theorem exists_example : ∃ n : Nat, n * n = 49 := ⟨7, by rfl⟩

/-- **E0.13.** Prove exibindo a testemunha. -/
theorem exists_even : ∃ n : Nat, n + n = 10 := sorry

/-! ## 10. Funções como valores

Uma função pode ser escrita sem nome — `fun x => corpo` — e pode ser passada
como argumento para outra função. É o recurso que o curso mais vai usar.
-/

def applyTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

#eval applyTwice double 3
#eval applyTwice (fun n => n + 10) 5

/-- **E0.14.** `applyToAll` aplica `f` a cada elemento da lista.
(Existe uma função da biblioteca que faz isso; escreva a sua, por recursão.) -/
def applyToAll (f : Nat → Nat) : List Nat → List Nat
  | []      => sorry
  | x :: xs => sorry

example : applyToAll double [1, 2, 3] = [2, 4, 6] := sorry

/-! ## 11. Conjuntos

Um conjunto de elementos de `α` é dado pela função que, para cada elemento,
afirma se ele pertence. Isso não é analogia: é a definição em Lean.
-/

#print Set
-- def Set : Type u → Type u := fun α => α → Prop

/-! `Set` vem da Mathlib, e é por isso que este trabalho depende dela. Redefinir
`Set` à mão daria uma cópia sem a notação (`∈`, `⊆`, `∪`, `∩`, `∅`) e sem os
lemas já provados — e o hábito de procurar na biblioteca antes de escrever é
parte do que se aprende aqui.

Escrever `{n | n > 2}` constrói a função; escrever `x ∈ A` a aplica. -/

def bigger : Set Nat := {n | n > 2}

/-! Uma coisa a saber antes do primeiro exercício. `decide` **não** fecha
`3 ∈ bigger`, e a mensagem é `failed to synthesize Decidable (3 ∈ bigger)`. O
motivo é que `bigger` é um `def`, e `decide` não desdobra definições: para ele,
o objetivo é opaco.

A saída é pedir o desdobramento: `simp [bigger]` reduz o objetivo a `3 > 2`, e
fecha. Passar o nome de uma definição para o `simp` é o gesto mais útil deste
arquivo — vai ser preciso muitas vezes. -/

example : 3 ∈ bigger := by simp [bigger]

/-- **E0.15.** Prove que 5 pertence. -/
example : 5 ∈ bigger := sorry

/-- **E0.16.** Prove que 1 não pertence. `x ∉ A` é abreviação de `¬ (x ∈ A)`,
que por sua vez é `x ∈ A → False`. -/
example : 1 ∉ bigger := sorry

/-! Inclusão não é operação nova: `A ⊆ B` afirma que todo elemento de `A` está
em `B`. Provar começa com `intro`. -/

def bigger5 : Set Nat := {n | n > 5}

/-- **E0.17.** Prove a inclusão. Depois de `intro x h`, use
`simp [bigger, bigger5] at *` para desdobrar as duas definições, e então
`omega`. -/
example : bigger5 ⊆ bigger := sorry

/-! União e interseção são disjunção e conjunção elemento a elemento. As duas
inclusões abaixo valem para conjuntos quaisquer, e as provas não precisam saber
nada sobre eles. -/

/-- **E0.18.** Todo conjunto está contido na sua união com outro. Depois do
`intro`, `Or.inl` prova uma disjunção pelo lado esquerdo. -/
example (A B : Set Nat) : A ⊆ A ∪ B := sorry

/-- **E0.19.** E a interseção está contida em cada um dos dois. -/
example (A B : Set Nat) : A ∩ B ⊆ A := sorry

/-! A Mathlib tem esses dois lemas prontos, com os nomes `Set.subset_union_left`
e `Set.inter_subset_left`. O exercício é escrever a prova, não encontrá-los —
mas vale procurar depois, para ver como se chamam as coisas. -/

end Exercises.Chapter02
