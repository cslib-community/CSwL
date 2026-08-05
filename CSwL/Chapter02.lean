import Mathlib.Algebra.Group.Nat.Even

/-!
# 2. Funções, tipos e abstração

Construir o significado de uma sentença a partir do significado de suas
partes exige quatro noções: função, aplicação, tipo e relação. Em Lean elas
não são notação auxiliar em torno da linguagem — são a linguagem. Uma função
é um valor que se pode nomear, passar adiante e aplicar parcialmente. Um tipo
é uma afirmação sobre o que um valor pode ser, e o verificador de tipos a
checa. Um conjunto é a função que decide a pertinência.
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
def square : Nat → Nat := fun x => x * x

/-- Escrever o argumento à esquerda dos dois-pontos é a mesma definição, em
forma mais curta. -/
def square' (x : Nat) : Nat := x * x

/-- `rfl` prova uma igualdade que vale por cálculo: os dois lados reduzem ao
mesmo valor. -/
example : square 4 = square' 4 := rfl

/-! ## Aplicação parcial

Uma função de dois argumentos é uma função que, aplicada ao primeiro,
devolve uma função à espera do segundo. A seta em `Nat → Nat → Nat` associa
à direita: leia como `Nat → (Nat → Nat)`.

Aplicar só o primeiro argumento é legítimo, e o tipo do resultado registra o
que falta. É por isso que a composição de significados vai funcionar tão bem
adiante: um verbo transitivo recebe seu objeto e fica esperando o sujeito.
-/

def add (m n : Nat) : Nat := m + n

#check add          -- Nat → Nat → Nat
#check add 3        -- Nat → Nat
#eval  (add 3) 4
#eval  add 3 4      -- a aplicação também associa à esquerda

/-! ## Conjuntos como funções

Um conjunto de elementos de `α` se apresenta pela sua função característica:
a função que, dado um elemento, responde se ele pertence.

Há duas maneiras de responder, e as duas serão usadas:

* `α → Bool` **calcula** a resposta. O resultado é `true` ou `false`, e
  pode-se rodar.
* `α → Prop` **enuncia** a resposta. O resultado é uma afirmação, que se
  pode provar.
-/

/-- Ser par, na versão que se calcula. -/
def isEven (n : Nat) : Bool := n % 2 == 0

#eval isEven 4
#eval isEven 5

/-! A versão que se enuncia já existe na biblioteca: `Even n` afirma que `n`
é o dobro de algum número, sem dizer como encontrá-lo.

```
Even (a : α) : Prop := ∃ r, a = r + r
```

Aqui está a distinção em ato. `isEven` é um algoritmo — divide e compara o
resto. `Even` é uma condição de verdade — existe um `r` tal que `n = r + r`.
São conteúdos diferentes, e por isso vale a pena que sejam objetos
diferentes.
-/

example : Even 4 := ⟨2, rfl⟩

/-! ## `Decidable`, a ponte

As duas versões não são independentes: para os naturais, a afirmação `Even n`
_também_ pode ser calculada. Essa evidência é o que `Decidable` registra, e
`decide` a usa para transformar a afirmação num `Bool`.
-/

#eval decide (Even 4)
#eval decide (Even 5)

/-- Com `Decidable` disponível, a prova de uma afirmação concreta é uma
computação: `decide` reduz `Even 4` a `true`, e isso basta. -/
example : Even 4 := by decide

/-- E a ponte se enuncia como teorema: as duas versões concordam. Ele já está
provado na biblioteca, sob o nome `Nat.even_iff`. -/
example (n : Nat) : Even n ↔ n % 2 = 0 := Nat.even_iff

/-! O capítulo 6 é inteiro sobre esse mecanismo: verificar se uma sentença é
verdadeira num modelo será exibir a instância `Decidable` correspondente. -/

/-! ## Relações

Uma relação binária sobre `α` é uma função de dois argumentos que responde
se o par está na relação — de novo em duas versões. A divisibilidade tem as
duas prontas na biblioteca: `m ∣ n` enuncia, e `decide` calcula.
-/

#eval decide (3 ∣ 12)
#eval decide (5 ∣ 12)

/-- Uma relação em `Prop` se combina com quantificadores e conectivos, e é
assim que suas propriedades se enunciam. Reflexividade, por extenso: -/
example : ∀ n : Nat, n ∣ n := fun _ => Nat.dvd_refl _

/-- A biblioteca dá um nome a essa propriedade — `Std.Refl` é a classe das
relações reflexivas, e instanciá-la é dar a prova. -/
example : Std.Refl (α := Nat) (· ∣ ·) := ⟨fun _ => Nat.dvd_refl _⟩

/-! ## Tipos como disciplina

O tipo de uma função diz o que ela aceita e o que devolve, e Lean recusa a
aplicação que não respeite isso — ao escrever, antes de rodar.

Essa recusa é o instrumento central do texto. As árvores sintáticas do
capítulo 4 serão tipos, e os significados do capítulo 7 também; daí em
diante, "esta combinação de palavras não é bem formada" e "este programa não
tipa" passam a ser a mesma frase.

Para ver a recusa acontecer, aplique `square` a uma `String`:
`#eval square "quatro"` não compila, e o erro aponta o argumento.
-/

end Chapter02
