/-!
# 2. Funções, tipos e abstração

Analisar o significado de uma sentença é construir um objeto matemático a
partir de suas partes. Antes de fazer isso, é preciso ter o vocabulário:
função, aplicação, tipo, conjunto, relação.

Em Lean esse vocabulário não é notação auxiliar em torno da linguagem — é a
linguagem. Uma função é um valor que se pode nomear, passar adiante e aplicar
parcialmente. Um tipo é uma afirmação sobre o que um valor pode ser, e o
verificador de tipos a checa. Um conjunto pode ser dado pela função que
decide a pertinência.

Este capítulo fixa esses quatro conceitos na forma em que serão usados no
resto do texto.
-/

namespace Chapter02

/-! ## Funções são valores

Uma função pode ser escrita sem receber nome. `fun x => e` é a função que
leva `x` em `e`; essa notação é a abstração lambda, e é a operação básica
para construir funções.

`#check` mostra o tipo do que se escreveu, sem avaliar. `#eval` avalia.
-/

#check fun (x : Nat) => x * x
#eval (fun (x : Nat) => x * x) 4

/-- Dar nome a uma função é nomear esse valor. -/
def quadrado : Nat → Nat := fun x => x * x

/-- Escrever o argumento à esquerda dos dois-pontos é a mesma definição, em
forma mais curta. -/
def quadrado' (x : Nat) : Nat := x * x

/-- `rfl` prova uma igualdade que vale por cálculo: os dois lados reduzem ao
mesmo valor. -/
example : quadrado 4 = quadrado' 4 := rfl

/-! ## Aplicação parcial

Uma função de dois argumentos é uma função que, aplicada ao primeiro,
devolve uma função à espera do segundo. A seta em `Nat → Nat → Nat` associa
à direita: leia como `Nat → (Nat → Nat)`.

Aplicar só o primeiro argumento é legítimo, e o tipo do resultado registra o
que falta. Essa é a forma normal de escrever funções aqui, e a razão por que
a composição de significados vai funcionar tão bem adiante: um verbo
transitivo pode receber seu objeto e ficar esperando o sujeito.
-/

def soma (m n : Nat) : Nat := m + n

#check soma          -- Nat → Nat → Nat
#check soma 3        -- Nat → Nat
#eval  (soma 3) 4
#eval  soma 3 4      -- a aplicação também associa à esquerda

/-! ## Conjuntos como funções

Um conjunto de elementos de `α` pode ser apresentado pela sua função
característica: a função que, dado um elemento, responde se ele pertence.

Há duas maneiras de responder, e o texto vai usar as duas:

* `α → Bool` **calcula** a resposta. O resultado é `true` ou `false`, e
  pode-se rodar.
* `α → Prop` **enuncia** a resposta. O resultado é uma afirmação, que se
  pode provar.

A distinção parece pedante e não é: ela separa o que a máquina decide do que
se demonstra. O capítulo 6 volta a esse par com `Decidable`, que é a ponte
entre os dois — a evidência de que uma afirmação em particular _também_ pode
ser calculada.
-/

/-- Uma propriedade — relação unária — que se calcula. -/
def par (n : Nat) : Bool := n % 2 == 0

/-- A mesma propriedade, enunciada. -/
def Par (n : Nat) : Prop := n % 2 = 0

#eval par 4
example : Par 4 := rfl

/-! ## Relações

Uma relação binária sobre `α` é uma função de dois argumentos que responde
se o par está na relação. Aqui também valem as duas versões, `Bool` e `Prop`.
-/

def divide (m n : Nat) : Bool := n % m == 0

#eval divide 3 12
#eval divide 5 12

/-- Relações como `Prop` se combinam com os conectivos lógicos, e é assim que
propriedades de relações se enunciam. -/
def Reflexiva (R : α → α → Prop) : Prop := ∀ x, R x x

/-- A igualdade é reflexiva, e a prova é imediata. -/
example : Reflexiva (α := Nat) (· = ·) := fun _ => rfl

/-! ## Tipos como disciplina

O tipo de uma função diz o que ela aceita e o que devolve, e Lean recusa a
aplicação que não respeite isso — antes de rodar, ao escrever.

Essa recusa é o instrumento central do texto. As árvores sintáticas do
capítulo 4 serão tipos, e os significados do capítulo 7 também; a partir
daí, "esta combinação de palavras não é bem formada" e "este programa não
tipa" passam a ser a mesma frase.

Para ver a recusa acontecer, aplique `quadrado` a uma `String`:
`#eval quadrado "quatro"` não compila, e o erro aponta o argumento.
-/

end Chapter02
