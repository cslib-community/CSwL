/-
Exercícios do capítulo 1 — O estudo formal da língua natural

Acompanha `CSwL/Chapter01.lean`. As páginas citadas são as de van Eijck &
Unger, capítulo 1.

Substitua cada `sorry` pela sua resposta. Enquanto houver `sorry`, o Lean
avisa — é a sua lista do que falta. Não altere os enunciados dos teoremas.

As questões marcadas com ✎ são discursivas: responda em `Exercises/RESPOSTAS.md`.
-/

namespace Exercises.Chapter01

/-! ## Exercício 1.1 (p. 6)

A ignorância completa sobre a verdade ou falsidade de dois fatos se modela
como incerteza entre quatro possibilidades. Com dez fatos básicos, quantas
possibilidades? E no caso geral de `n` fatos?

Defina a contagem por recursão sobre `n` e prove que ela vale `2 ^ n`.
-/

def possibilities : Nat → Nat
  | 0 => sorry
  | n + 1 => sorry

/-- A prova é por indução: `induction n with | zero => ... | succ k ih => ...`.

No passo indutivo é preciso desdobrar a potência, e há dois lemas para isso.
`Nat.pow_succ'` diz que `m ^ (n + 1) = m * m ^ n`; `Nat.pow_succ` diz
`n ^ (m + 1) = n ^ m * n`, com os fatores na outra ordem — e então falta
`Nat.mul_comm`. Um dos dois dá uma prova mais curta.

`simp` sozinho não fecha este objetivo. -/
theorem possibilities_eq (n : Nat) : possibilities n = 2 ^ n := sorry

/-- Confira o caso do enunciado: dois fatos dão quatro possibilidades. -/
example : possibilities 2 = 4 := sorry

/-- E o caso pedido: dez fatos. -/
example : possibilities 10 = 1024 := sorry

/-! ## Exercício 1.2 (p. 8)

Pollard e Sag dão este exemplo de recursão que estende sentenças:

    Sentences can go on.
    Sentences can go on and on.
    Sentences can go on and on and on.
    Sentences can go on and on and on and on.
    ...

Dê uma descrição concisa do padrão de recursão — isto é, escreva o gerador.
`sentence n` deve produzir a sentença com `n` repetições de "and on".

Uma observação que economiza tempo: a recursão **não** cabe direto em
`sentence`, porque o ponto final tem de ficar sempre no fim. O que se repete é
o pedaço `" and on"`, e é ele que merece a função recursiva. Por isso o
esqueleto vem em duas partes.
-/

/-- `andOn n` são as `n` repetições de `" and on"`, sem mais nada. -/
def andOn : Nat → String
  | 0 => sorry
  | n + 1 => sorry

/-- E a sentença é o começo, mais as repetições, mais o ponto. -/
def sentence (n : Nat) : String := sorry

example : sentence 0 = "Sentences can go on." := sorry
example : sentence 2 = "Sentences can go on and on and on." := sorry

/-! ## Exercício 1.3 (p. 8)

Segue do exercício 1.2 que há infinitas sentenças em inglês? Ou segue que
sentenças em inglês podem ter comprimento infinito? Ou as duas coisas?

A primeira metade da pergunta se demonstra. Comece pelo caso concreto: exiba
uma sentença mais longa que uma cota dada. Este item sai por cálculo — a
máquina constrói a string e conta os caracteres.
-/

theorem sentence_10_long : (sentence 10).length > 50 := sorry

/-! ★ **Desafio, opcional.** O caso geral: não existe cota nenhuma.

Este é o item mais difícil do trabalho, e é o único opcional. Precisa de
indução para achar o comprimento de `andOn n`, de `String.length_append` para
somar os pedaços, e de `omega` no fim. Ninguém perde ponto por deixá-lo em
`sorry`. -/

theorem sentences_unbounded :
  ∀ n : Nat, ∃ m : Nat,  (sentence m).length > n := sorry

/-! ✎ **Exercício 1.3, segunda metade.** A outra pergunta — se as sentenças
podem ter comprimento *infinito* — não se enuncia em Lean: `String` é finita
por construção, então não há teorema a provar. Responda em `RESPOSTAS.md`:
qual das duas conclusões segue do exercício 1.2, e por que a outra não segue.
Comente a assimetria: um conjunto infinito cujos membros são todos finitos. -/

/-! ## Questões Complementares

As quatro seguintes não estão no livro. Elas cobrem as seções do capítulo 1
que não têm exercício.
-/

/-! ### Q1 — Denotação e computação (§1.2)

O capítulo observa que *seven plus five* e *two times six* denotam o mesmo
número por caminhos diferentes. Em Lean as duas expressões são iguais, e a
igualdade vale por cálculo.
-/

example : 7 + 5 = 2 * 6 := by rfl

/-- Escreva **outro** par de expressões `Nat` com estruturas diferentes e o
mesmo valor. Não use os números do exemplo acima, e não escreva o mesmo número
duas vezes: as duas expressões devem ter forma diferente. -/
def myFirst : Nat := sorry

/-- A segunda expressão do par. -/
def mySecond : Nat := sorry

/-- E a igualdade, que deve valer por `rfl`. -/
theorem q1_my_pair : myFirst = mySecond := sorry

/-! ✎ Em `RESPOSTAS.md`: se as duas expressões denotam o mesmo número, em que
sentido elas são diferentes? O que exatamente `rfl` verifica? -/

/-! ### Q2 — Composicionalidade (§1.4)

O princípio de Frege diz que o significado de uma expressão composta é
determinado pelos significados de suas partes e pelo modo como estão
combinadas. Em termos de programa: a interpretação é uma função recursiva
sobre a estrutura sintática.

Abaixo está a sintaxe de um fragmento minúsculo — expressões aritméticas.
Escreva a interpretação.
-/

inductive Expr where
  | num   (n : Nat)
  | plus  (a b : Expr)
  | times (a b : Expr)
deriving Repr

/-- A interpretação: um caso por construção da sintaxe, cada caso combinando
os resultados obtidos para as partes. -/
def eval : Expr → Nat := sorry

/-- *seven plus five* -/
def sevenPlusFive : Expr := .plus (.num 7) (.num 5)

/-- *two times six* -/
def twoTimesSix : Expr := .times (.num 2) (.num 6)

/-- Estruturas sintáticas diferentes, mesma denotação. -/
theorem q2_same_denotation : eval sevenPlusFive = eval twoTimesSix := sorry

/-! ✎ Em `RESPOSTAS.md`: identifique, na sua definição de `eval`, onde está o
"significado das partes" e onde está o "modo como estão combinadas". Por que
uma tabela de significados não serviria no lugar dessa definição? -/

/-! ### Q3 — Competência e desempenho (§1.1) ✎

Responda em `RESPOSTAS.md`, em um parágrafo cada:

1. Qual é a distinção entre competência e desempenho linguístico, e em que
   sentido uma gramática formal é um modelo da competência?
2. Um falante que produz uma sentença com erro de concordância viola a
   gramática da sua língua? Justifique usando a distinção acima.
-/

/-! ### Q4 — O que a semântica formal não é (§1.5, §1.6) ✎

Responda em `RESPOSTAS.md`, em um parágrafo cada:

1. O capítulo discute a objeção de que traduzir língua natural para lógica
   seria só "um exercício de tipografia" — trocar símbolos por outros
   símbolos, sem ganhar nada. Qual é a resposta a essa objeção?
2. Por que uma linguagem funcional, e não uma linguagem lógica como o Prolog?
   O que se ganha em separar a *construção* da representação de significado
   das *operações* sobre ela?
-/

end Exercises.Chapter01
