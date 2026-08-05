import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Set.Basic

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

/-! ## O cálculo lambda

A notação `fun x => e` não é invenção de linguagem de programação. Ela resolve
uma ambiguidade real, e vale ver qual.

A expressão `x² + y` não determina uma função. Ela pode ser lida como função de
`x`, com `y` fixo; como função de `y`, com `x` fixo; ou como função dos dois. O
que falta é dizer qual variável é o parâmetro — e o operador lambda é
exatamente o marcador que diz isso. Em `λx ↦ x² + y`, o `x` está **ligado** e o
`y` está **livre**.

O nome da variável ligada não importa: `λz ↦ z² + y` é a mesma função. E isso
não é convenção — em Lean as duas são o mesmo termo, e o `rfl` prova:
-/

example : (fun (x : Nat) => x * x) = (fun (z : Nat) => z * z) := rfl

/-! ### A gramática dos termos

O cálculo lambda tem três formas de construir expressão, e nada mais. Escritas
na notação usual para gramáticas — a Forma de Backus-Naur, ou BNF:

```
E ::= v | (E E) | (λv ↦ E)
```

Leia: uma expressão é uma variável, ou a justaposição de duas expressões
(aplicação), ou um lambda seguido de variável e expressão (abstração). A última
cláusula é implícita e importante: **nada além disso é expressão**.

Uma gramática BNF é uma definição indutiva, e uma definição indutiva é um tipo
`inductive`. As duas coisas são a mesma, escritas em notações diferentes:
-/

/-- A gramática acima, como tipo. Cada cláusula da BNF virou um construtor. -/
inductive Lam where
  | var (name : String)
  | app (fn arg : Lam)
  | lam (binder : String) (body : Lam)

/-! Essa correspondência é o motor do curso. Do capítulo 4 em diante, cada
fragmento da língua vai ser dado por uma gramática, e a gramática vai ser um
tipo `inductive` — o que torna "esta expressão é bem formada" a mesma coisa
que "este termo tem esse tipo".

Aqui, `Lam` fica como ilustração e não será usado: o cálculo lambda que
interessa é o próprio Lean, não uma cópia dele dentro de Lean.

### Redução

O que se faz com uma aplicação é substituir. A regra é uma só:

```
(λx ↦ E) A  →  E[x := A]
```

onde `E[x := A]` é `E` com toda ocorrência livre de `x` trocada por `A`. Isso é
a β-redução, e é o único mecanismo de cálculo do cálculo lambda inteiro.

Em Lean essa redução é o que o `#eval` executa e o que o `rfl` verifica:
-/

example : (fun (x : Nat) => x + 42) 5 = 5 + 42 := rfl

/-! ### Captura de variável

Substituir ingenuamente dá errado, e o exemplo clássico merece atenção porque
o erro é silencioso. Considere aplicar `λyλx ↦ x + y` ao argumento `x`.

Trocando `y` por `x` sem cuidado, obtém-se `λx ↦ x + x` — a função que soma um
número a si mesmo. Mas o resultado correto é a função que soma `x` a um número
dado: o `x` que veio de fora foi **capturado** pelo `λx` que já estava lá. Que
o resultado é outro se vê renomeando antes: `λyλz ↦ z + y` aplicado a `x` dá
`λz ↦ z + x`, que é o certo.

A saída é renomear a variável ligada quando houver risco de captura. Lean faz
isso sozinho — internamente as variáveis ligadas não têm nome, e o problema não
existe:
-/

example (x : Nat) : (fun y => fun z => z + y) x = (fun z => z + x) := rfl

/-! ### Funções são dados

Abstração e aplicação, como definidas, não distinguem dados de funções. Se
tudo é expressão, então uma função pode receber função, devolver função, e ser
aplicada a si mesma. Não há duas categorias de coisas.

É isso que permite escrever uma função que aplica outra a um argumento fixo: -/

def applyToDragon (f : String → String) : String := f "dragon"

def pluralize (w : String) : String := w ++ "s"

#eval applyToDragon pluralize

/-! ### Por que isso serve à semântica

Um verbo transitivo é uma função de dois lugares. *Likes* se escreve
`λxλy ↦ y likes x`, onde `likes` é a função característica da relação de
gostar: aplicada a duas entidades, responde se a primeira gosta da segunda.

Repare no que a notação **não** diz. Ela não diz o que *likes* significa no
mundo. Diz apenas com que outras expressões o verbo se combina e que papel
desempenha na expressão maior — e é justamente por dizer só isso que o cálculo
lambda serve à semântica composicional. A derivação do significado pode então
acompanhar, passo a passo, a estrutura sintática da sentença.

## Tipos

No cálculo lambda como está, toda expressão se aplica a toda expressão. Nada
impede escrever o número `4` aplicado a uma função, e o resultado não é falso —
é sem sentido. Tipos existem para excluir isso.

A gramática dos tipos também é uma BNF, com duas cláusulas:

```
τ ::= b | (τ → τ)
```

Há tipos básicos, e há tipos de função construídos a partir deles. Na
semântica, os dois básicos costumam ser `e`, das entidades, e `t`, dos valores
de verdade. Em Lean, `t` é `Prop`.

E a atribuição de tipos a expressões se dá por três regras:

* **variáveis** — para cada tipo há variáveis daquele tipo;
* **abstração** — se `x : δ` e `E : τ`, então `(λx ↦ E) : δ → τ`;
* **aplicação** — se `E₁ : δ → τ` e `E₂ : δ`, então `(E₁ E₂) : τ`.

Não há mais nada. O `#check` do Lean é essas três regras rodando:
-/

/-- O domínio de entidades. Duas bastam para os exemplos desta seção. -/
inductive Entity where
  | dorothy | toto
deriving DecidableEq

/-- `happy` é uma propriedade de entidades: aplicada a uma, dá uma afirmação.
`opaque` declara o nome com o tipo e sem corpo — aqui o assunto são os tipos,
e qualquer definição serviria. -/
opaque happy : Entity → Prop

section
variable (x : Entity)

-- regra da aplicação: `happy : Entity → Prop` e `x : Entity`, logo `happy x : Prop`
#check happy x

-- regra da abstração: `x : Entity` e `happy x : Prop`, logo o lambda é `Entity → Prop`
#check fun (y : Entity) => happy y

end

/-! ### Tipos e categorias sintáticas

Aqui está a observação que amarra as duas metades do assunto. Tipos, em
programação e no cálculo lambda, se comportam como **categorias sintáticas** em
gramática.

Categorias como NP correspondem a tipos básicos: expressões completas, que
carregam significado por si. Categorias como VP correspondem a tipos de função:
expressões incompletas, cujo significado consiste na contribuição que dão à
expressão em que aparecem.

Sob essa leitura, uma regra de reescrita como `S → NP VP` diz uma coisa sobre
tipos: se `a : NP` e `b : VP`, então a concatenação de `a` e `b` é um `S`. E se
o VP é o que combina com um NP para dar um S, então o próprio VP tem tipo
`NP → S` — a categoria deixa de ser um rótulo e passa a ser uma função.

Essa é a ideia da **gramática categorial**, que vem de Ajdukiewicz. Um verbo
transitivo, que combina com dois NPs, tem tipo `NP → (NP → S)`. A regra de
combinação é uma só: uma expressão de categoria `A` combina com uma de
categoria `A → B` e produz uma de categoria `B` — isto é, aplicação.

Em Lean isso se escreve diretamente, e o verificador de tipos passa a validar a
derivação:
-/

abbrev NP := Entity
abbrev S := Prop
abbrev VP := NP → S
abbrev TV := NP → VP

def dorothy : NP := .dorothy
def toto : NP := .toto

/-- O verbo, como função de dois lugares: recebe o objeto, depois o sujeito. -/
opaque likes : TV

/-- O VP: o verbo já recebeu o objeto e espera o sujeito. -/
def likesToto : VP := likes toto

/-- E a sentença, com o sujeito no lugar. -/
def dorothyLikesToto : S := likesToto dorothy

#check dorothyLikesToto

/-! A derivação da sentença é uma sequência de duas aplicações, e cada passo
é conferido pelos tipos. Uma combinação mal formada não chega a ser um termo.

### Lean como cálculo lambda

O que se descreveu acima é o cálculo lambda com tipos simples, e Lean o contém.
Abstração, aplicação, β-redução, tipos de função: tudo o que foi dito vale
literalmente, e os `#check` acima são as regras de tipagem sendo aplicadas.

Lean vai além disso em pontos que o curso vai usar:

* **tipos indutivos** — a BNF de uma gramática vira um tipo, com casamento de
  padrão e recursão garantidamente terminante;
* **tipos dependentes** — um tipo pode depender de um valor, o que permite
  exigir na assinatura condições que aqui teriam de ser verificadas à parte;
* **proposições como tipos** — `Prop` não é um tipo básico opaco: uma prova de
  `P` é um termo de tipo `P`, e é por isso que o mesmo verificador serve para
  checar programas e demonstrações;
* **universos** — `Type`, `Type 1`, e assim por diante, o que evita os paradoxos
  que apareceriam se houvesse um tipo de todos os tipos.

Para o que vem pela frente, a leitura útil é essa: o aparato da semântica de
Montague é um fragmento do que Lean oferece, e o excedente é o que vai permitir
demonstrar coisas sobre os significados, e não apenas calculá-los.

## Conjuntos como funções

Um conjunto de elementos de `α` se apresenta pela sua função característica:
a função que, dado um elemento, responde se ele pertence.

Há duas maneiras de responder, e as duas serão usadas:

* `α → Bool` **calcula** a resposta. O resultado é `true` ou `false`, e
  pode-se rodar.
* `α → Prop` **enuncia** a resposta. O resultado é uma afirmação, que se
  pode provar.

Isso não é uma analogia. A segunda versão é, literalmente, como conjunto se
define em Lean:
-/

#print Set
-- def Set : Type u → Type u := fun α => α → Prop

/-! Um `Set α` **é** uma função `α → Prop`, e nada mais. A notação de
conjunto que se escreve na prática é açúcar para construir essa função, e
pertencer é aplicá-la — as duas coisas são a mesma, e o `rfl` prova: -/

example : {n : Nat | n > 2} = Set.ofPred (fun n => n > 2) := rfl

example (p : Nat → Prop) (x : Nat) : (x ∈ {n | p n}) = p x := rfl

/-! Escrever `x ∈ A` em vez de `A x` é comodidade de leitura. Vale saber disso
porque, quando uma prova sobre conjuntos empacar, desdobrar a notação até a
aplicação costuma destravar. -/

example : (3 : Nat) ∈ {n : Nat | n > 2} := by decide

/-! ## Conjuntos e a escolha entre calcular e enunciar

Definido assim, um conjunto herda a escolha da seção anterior: `α → Prop`
enuncia a pertinência. Existe também `α → Bool`, que a calcula, e é o que se
usa quando o conjunto é finito e a resposta tem de sair rodando — é o caso do
capítulo 6, onde verificar uma sentença num modelo é percorrer um domínio
finito.
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

/-- Provar `Even 4` é exibir o `r` que a afirmação promete, junto com a
verificação de que ele serve. -/
example : Even 4 := ⟨2, rfl⟩

/-! ## As duas versões concordam

Nada obriga, a priori, uma afirmação e um algoritmo a dizerem a mesma coisa.
Que estes dois digam é um fato sobre os naturais, e como tal se enuncia e se
prova. A biblioteca já traz a prova, sob o nome `Nat.even_iff`:
-/

example (n : Nat) : Even n ↔ n % 2 = 0 := Nat.even_iff

/-! Provado isso, `Even n` passa a ser uma afirmação que se pode *calcular*
para um `n` dado — e o Lean faz isso sem que se peça nada: -/

#eval Even 4
#eval Even 5

/-! Vale reparar no que acabou de acontecer. `Even 4` é uma afirmação, não um
programa; ainda assim o `#eval` respondeu `true`. Há um mecanismo por trás
disso, que registra quais afirmações admitem esse cálculo e como fazê-lo. Ele
depende de classes de tipos, que aparecem no capítulo 3, e é o assunto do
capítulo 6 — onde verificar se uma sentença é verdadeira num modelo será
exatamente isso. -/

/-! ## Relações

Uma relação binária sobre `α` é uma função de dois argumentos que responde se
o par está na relação. Vale aqui a mesma escolha de antes, entre calcular e
enunciar.

A divisibilidade já vem na biblioteca, na versão que enuncia: `m ∣ n` afirma
que existe um fator que leva de `m` a `n`, e provar é exibi-lo.
-/

example : (3 : Nat) ∣ 12 := ⟨4, rfl⟩

#eval (3 ∣ 12 : Prop)
#eval (5 ∣ 12 : Prop)

/-- Relações em `Prop` se combinam com quantificadores e conectivos, e é assim
que suas propriedades se enunciam. Reflexividade, por extenso: -/
example : ∀ n : Nat, n ∣ n := fun _ => Nat.dvd_refl _

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
