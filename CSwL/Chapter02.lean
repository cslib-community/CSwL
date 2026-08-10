/-!
# 2. Programação funcional

_No livro: capítulo 3 (`FPH`)._

Um feixe de traços fonológicos e uma árvore sintática são o mesmo tipo de
objeto: dados com forma, definidos por casos, percorridos por recursão. Quem
sabe escrever o primeiro sabe escrever o segundo, e é por isso que os
exemplos daqui — plural do sueco, harmonia vocálica, quem escreveu o quê —
já são linguísticos, embora nenhuma teoria do significado tenha começado
ainda.

Este é o capítulo em que Lean entra. Nada aqui pressupõe a linguagem: `def`,
tipos, recursão e casamento de padrão se apresentam na hora. O capítulo 3
retoma o mesmo material por outro lado — o que é uma função, o que é um tipo,
o que é um conjunto — e é lá que o aparato ganha a leitura que a semântica
vai usar.
-/

namespace Chapter02

/-! ## Termos e tipos

Tudo em Lean é um _termo_, e todo termo tem um _tipo_. Um tipo é uma coleção de
termos; um termo é um elemento dela. `100` é um termo do tipo `Nat`, e
`"Chomsky"` é um termo do tipo `String`.

`def` dá nome a um termo. Os dois-pontos anunciam o tipo, e o `:=` dá o valor:
-/

def n : Nat := 100
def author : String := "Chomsky"

/-! Há dois comandos para interrogar o que se escreveu, e a diferença entre eles
organiza tudo o que vem depois. `#eval` **calcula** o valor; `#check` **pergunta
ou confirma o tipo**, sem calcular nada. -/

#eval  n
#check n

#eval  author
#check author

/-! O tipo não precisa ser declarado quando Lean consegue descobri-lo sozinho.
Escrever `def n := 100` funciona — mas escrever o tipo é conveniente e ajuda a
tornar o código mais legível.

Tipos também são termos, e portanto têm tipo. Perguntar pelo tipo sobe um
degrau: o tipo de `true` é `Bool`, o de `Bool` é `Type`, e o de `Type` é `Type
1`. -/

#check true
#check Bool
#check Nat
#check Type

/-! A escada não para: há `Type 1`, `Type 2`, e assim por diante. Ela existe
para que não exista um tipo de todos os tipos, o que produziria um paradoxo.
Nada no curso vai depender de subir mais que um degrau; basta saber que a
pergunta "qual o tipo disto?" tem sempre resposta.

### O tipo das funções

A seta `→` constrói um tipo novo a partir de dois. `Nat → String` é o tipo das
funções que recebem um `Nat` e devolvem uma `String` — e é um tipo como qualquer
outro, o que se confirma perguntando: -/

#check Nat → String

/-! Essa é a construção que o curso inteiro vai usar. No capítulo 3 ela
reaparece como a operação básica da semântica: um verbo intransitivo é uma
função de entidades em valores de verdade, e isso é literalmente um tipo com
uma seta.

## Uma primeira função

O tipo vem primeiro. `Int → Int` é uma promessa, e o corpo da definição tem
de cumpri-la; enquanto não cumprir, o arquivo não compila.

Na definição abaixo, `(x : Int)` declara o parâmetro e o `: Int` final declara
o resultado — juntos, dizem que `square` é uma função de `Int` em `Int`.

-/

def square (x : Int) : Int := x * x

#eval square 7
#eval square (-3)
#eval square (square 7)

/-! Perguntado sobre um nome que foi definido, o `#check` responde com a
assinatura, e não com o tipo na forma de seta. Envolver o nome em parênteses
força a segunda forma. As duas dizem o mesmo: -/

#check square
#check (square)


/-! ## Funções são valores

O nome é acessório. Uma função pode ser escrita sem receber nenhum: `fun x => e`
é a função que leva `x` em `e`, e essa notação — a abstração lambda — é a
operação básica para construir funções. O `def` acima apenas deu nome ao valor
que ela produz.

A seta `↦` e o `=>` são a mesma coisa, como `λ` e `fun`; a escolha é de gosto.
As duas linhas abaixo são, portanto, a mesma função: -/

#check (λ x ↦ x * x)
#check (fun x => x * x)

/-! A resposta dessas duas é estranha, e vale entender por quê. Sem dizer o
tipo de `x`, Lean não tem como saber em que `*` se está pensando — o de `Nat`,
o de `Int`, o de qualquer outro tipo com multiplicação. O que aparece no lugar
do tipo (`?m.7`, e coisas assim) é uma _metavariável_: um buraco que Lean
deixa em aberto à espera de informação que decida a questão.

Anotar o argumento resolve, e a resposta passa a ser o tipo esperado: -/

#check fun (x : Nat) => x * x

/-! O contexto também resolve, quando existe. Aplicada a `4`, a função não tem
mais o que decidir: -/

#eval (fun (x : Nat) => x * x) 4

/-! ### Funções que recebem e devolvem funções

Se função é valor, então nada impede que ela seja _argumento_ de outra função.
`g` recebe uma função de `Nat` em `Nat` e a aplica a um número: o primeiro
parâmetro tem tipo com seta, e é isso que o torna uma função de ordem
superior. -/

def g (f : Nat → Nat) (x : Nat) : Nat := f x

#eval g (λ x => x + 1) 10

/-! Nem que ela seja _resultado_. `h` recebe um número e devolve uma função,
como o tipo anuncia — o `(Nat → Nat)` à direita dos dois-pontos é o tipo do
resultado. Para obter um número, é preciso aplicar duas vezes: -/

def h (x : Nat) : (Nat → Nat) := fun y => x + y

#check h 10
#eval  (h 10) 10

/-! ## Tudo é expressão

Uma expressão tem valor e tipo; um comando faz algo e não devolve nada. Em
Lean não há a segunda categoria — o que em outras linguagens é comando aqui é
expressão, e portanto pode aparecer em qualquer lugar onde um valor cabe.

`let` nomeia um valor dentro de uma expressão, e a expressão inteira tem
valor: -/

def twenty : Nat := (let a := 10; a) + (let b := 10; b)

#eval twenty

/-! O `if`-`then`-`else` também é expressão, e não desvio de fluxo: os dois
ramos têm de ter o mesmo tipo, porque o `if` inteiro tem _um_ tipo. É por isso
que o resultado pode ser atribuído: -/

#eval
  let a := if 5 < 10 then 1 else 0
  a            -- 1

/-! ## Uma primeira prova

Que as duas grafias — o lambda e o argumento à esquerda dos dois-pontos — dão
a mesma função não é analogia. As duas definições abaixo são o mesmo termo: -/

def double : Nat → Nat := fun x => 2 * x
def double' (x : Nat) : Nat := 2 * x

/-! Afirmar isso é escrever uma igualdade, e uma igualdade é uma _proposição_:
algo que se pode enunciar e demonstrar. O `#check` confirma que `double =
double'` é uma proposição — note que perguntar pelo tipo não é o mesmo que
decidir se ela é verdadeira: -/

#check (double = double')

/-! Provar é dar um termo cujo tipo é a proposição. Para uma igualdade em que
os dois lados reduzem ao mesmo valor, o termo é `rfl` — de _reflexividade_,
que é o princípio de que tudo é igual a si mesmo. Escrito com `by`, `rfl` é
uma _tática_: uma instrução para construir a prova. -/

theorem doubleFive : double 5 = 10 := by rfl

/-! O que a tática construiu se pode inspecionar. `#print` mostra a prova como
termo, e o termo é `Eq.refl` — a reflexividade da igualdade, aplicada aqui: -/

#print doubleFive

/-! E a igualdade das duas funções, que era o ponto: -/

theorem doubleEqDouble : double = double' := rfl

/-! Este é todo o aparato de prova que o capítulo usa. Ele volta no capítulo 3,
com os tipos, e é assunto do capítulo 6, onde verificar se uma sentença é
verdadeira num modelo passa a ser exatamente essa questão — enunciar algo
versus calculá-lo.

Quem quiser praticar Lean por si, fora do curso, o _Natural Number Game_
(<https://adam.math.hhu.de/#/g/leanprover-community/nng4/>) é o caminho curto.
Nada do que vem depois depende dele.

## Aplicação parcial

Uma função de dois argumentos é, na verdade, uma função de um argumento que
devolve outra função. A seta associa à direita, e o tipo diz isso:
`Nat → Nat → Nat` lê-se `Nat → (Nat → Nat)`.

A consequência prática é que aplicar só o primeiro argumento é legítimo, e o
tipo do resultado registra o que ainda falta. -/

def add (m n : Nat) : Nat := m + n

#check (add)
#check add 3
#eval  (add 3) 4
#eval  add 3 4      -- a aplicação associa à esquerda

/-! Guardar uma aplicação parcial num nome é o uso comum disso: -/

def add3 : Nat → Nat := add 3

#eval add3 4

/-! ## Tipos definidos por casos

`inductive` declara um tipo listando as formas que seus valores podem ter.
Quando nenhuma forma carrega argumento, o tipo é uma enumeração; quando
carrega, é um registro variante; quando a forma se refere ao próprio tipo
sendo definido, é uma árvore. As três coisas são o mesmo mecanismo.

Essa é a construção mais importante do curso. O capítulo 3 mostra que uma
gramática escrita na notação usual — a Forma de Backus-Naur — é literalmente
um tipo `inductive`, e do capítulo 4 em diante todo fragmento da língua é
declarado assim.

A enumeração é o caso mais simples: cinco formas, nenhuma com argumento.
`deriving Repr, DecidableEq` pede que a exibição e o teste de igualdade sejam
gerados em vez de escritos à mão.
-/

/-- As cinco classes de declinação do plural em sueco. -/
inductive DeclClass where
  | One | Two | Three | Four | Five
deriving Repr, DecidableEq

#check DeclClass.Three
#eval  DeclClass.Three

/-! ### Os naturais são um tipo indutivo

Isso não vale só para os tipos que se declara: os que vêm com a linguagem são
declarados do mesmo modo, e `#print` mostra a declaração. `Bool` é a
enumeração de duas formas; `Nat` é o caso em que uma das formas se refere ao
próprio tipo que está sendo definido: -/

#print Bool
#print Nat

/-! Ou seja: um natural é `Nat.zero`, ou é `Nat.succ n` para algum natural
`n`, e nada mais. O `2` que se escreve é notação para `Nat.succ (Nat.succ
Nat.zero)` — o mesmo termo, como `rfl` verifica: -/

example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

/-! Duas consequências disso organizam a seção seguinte.

A primeira: _casar padrão_ é perguntar por qual das formas um valor foi
construído. Como as formas são conhecidas e são todas, Lean consegue conferir
se uma definição por casos tratou o tipo inteiro.

A segunda: como cada `Nat.succ n` guarda dentro de si um `n` menor, a recursão
sobre naturais tem por onde descer.

## Recursão

Uma definição recursiva precisa de dois cuidados: ter caso base, e chegar
nele. O segundo não é uma recomendação — é uma exigência que o compilador
verifica, e a definição é rejeitada se ele não conseguir ver que a recursão
termina.

Em `Nat`, os dois casos do tipo dão as duas coisas de uma vez. Casar por `0` e
`n + 1` — que é como se escreve `Nat.zero` e `Nat.succ n` — cobre o tipo
inteiro: o caso base é `0`, e a chamada recursiva recebe o `n` que estava
dentro do `succ`, necessariamente menor. Não há um terceiro caso a esquecer, e
não há argumento para o qual a função não responda.
-/

/-- O fatorial é o exemplo mínimo dessa forma: um caso base e um caso que
chama a si mesmo com um argumento menor. -/
def factorial : Nat → Nat
  | 0       => 1
  | .succ n => (n + 1) * factorial n

#eval factorial 5
#eval factorial 0

/-- A mesma função sem casar padrão, decidindo o caso base com um `if`. Funciona,
e serve de contraste: aqui o argumento da chamada recursiva é `x - 1`, e que ele
seja menor que `x` é um fato a ser verificado, não algo que a forma da definição
já garanta. Neste caso Lean verifica sozinho; em definições menos óbvias, não —
e aí a prova de terminação passa a ser trabalho do programador. Casar por `0` e
`n + 1` dispensa a questão, e é por isso que é a forma preferida no texto. -/
def factorial' (x : Nat) : Nat :=
  if x = 0 then 1
  else x * factorial' (x - 1)

def gen : Nat → String
  | 0     => "Sentences can go on"
  | n + 1 => gen n ++ " and on"

def genS (n : Nat) : String := gen n ++ "."

#eval genS 3

/-- Recursão que encaixa uma fala dentro da outra: o chefe dos canibais
repete, entre aspas, o discurso do chefe anterior. -/
def story : Nat → String
  | 0     => "Let's cook and eat that final missionary, and off to bed."
  | k + 1 =>
      "The night was pitch dark, mysterious and deep.\n"
    ++ "Ten cannibals were seated around a boiling cauldron.\n"
    ++ "Their leader got up and addressed them like this:\n'"
    ++ story k ++ "'"

#eval IO.println (story 2)

/-! ## Texto: `String` e `List Char`

`String` é uma sequência UTF-8 empacotada. Isso a torna eficiente para
guardar texto e inadequada para percorrer: não há padrão `c :: cs` para casar
diretamente numa `String`.

A divisão de trabalho é essa — `String` para armazenar, `List Char` para
computar. Converte-se com `.toList`, faz-se a recursão na lista, onde o
padrão existe, e volta-se com `String.ofList`.
-/

def hword : List Char → Bool
  | []      => false
  | c :: cs => c == 'h' || hword cs

#eval hword "shrimptoast".toList
#eval hword "antiquing".toList

def reversal : List Char → List Char
  | []     => []
  | c :: t => reversal t ++ [c]

#eval String.ofList (reversal "Chomsky".toList)

/-- Remove o último caractere. -/
def initS (s : String) : String := String.ofList s.toList.dropLast

#eval initS "flicka"

/-! ## O plural do sueco

Com o `inductive` e a recursão em texto, dá para escrever uma regra
morfológica de verdade. O sueco distribui os substantivos em cinco classes de
declinação, e a forma do plural depende da classe — `DeclClass`, declarada
acima, é exatamente esse tipo.
-/

-- Vogais fora do ASCII: 'ä' = 228, 'å' = 229, 'ö' = 246, 'ø' = 248.
def aUml   : Char := Char.ofNat 228
def aRing  : Char := Char.ofNat 229
def oUml   : Char := Char.ofNat 246
def oSlash : Char := Char.ofNat 248

def swedishVowels : List Char :=
  ['a','i','o','u','e','y', aUml, aRing, oUml, oSlash]

/-- A forma do plural é determinada pela classe de declinação. Na terceira
classe ela depende também de a palavra terminar ou não em vogal: uma regra
morfológica que consulta a forma fonológica. -/
def swedishPlural (noun : String) : DeclClass → String
  | .One   => initS noun ++ "or"
  | .Two   => initS noun ++ "ar"
  | .Three => if swedishVowels.contains noun.back then noun ++ "r"
              else noun ++ "er"
  | .Four  => noun ++ "n"
  | .Five  => noun

#eval swedishPlural "flicka" .One
#eval swedishPlural "pojke"  .Two
#eval swedishPlural "rad"    .Three
#eval swedishPlural "ko"     .Three
#eval swedishPlural "hus"    .Five


/-! ## Quando não há resposta

Uma função de tipo `List α → α` promete devolver um elemento para qualquer
lista que receba. Para a lista vazia não existe elemento nenhum, e a promessa
é impossível — não por falta de cuidado do programador, mas porque o tipo
afirma algo falso.

A correção é no tipo, não no corpo: `List α → Option α` promete devolver _ou_
um elemento (`some x`) _ou_ nada (`none`). Quem chama fica obrigado a tratar
os dois casos. O ganho é que o caso sem resposta deixa de ser invisível: ele
está na assinatura, e não há como esquecê-lo.
-/

def myLast {α : Type} : List α → Option α
  | []      => none
  | [x]     => some x
  | _ :: xs => myLast xs

#eval myLast [1,2,3]
#eval myLast ([] : List Nat)

def average (xs : List Int) : Option Rat :=
  if xs.isEmpty then none
  else some ((xs.sum : Rat) / (xs.length : Rat))

#eval average [1,2,3,4]
#eval average []

-- Nem toda função da biblioteca é honesta desse modo: algumas devolvem um
-- valor default no caso ruim, em vez de `Option`. `String.back` é uma delas,
-- e vale conhecer as que são assim.
#eval "rad".back
#eval "".back      -- não é erro, é o `Char` default


/-! ## Classes de tipos

`count` conta ocorrências em qualquer lista cujos elementos se possam
comparar. Essa exigência entra na assinatura entre colchetes, `[BEq α]`: uma
instância de igualdade para `α`, que Lean encontra sozinho no ponto de uso.

Duas noções de igualdade convivem, e vale separá-las desde já:

* `BEq α` devolve `Bool` e se escreve `==`. Serve para calcular.
* `DecidableEq α` devolve uma _prova_ de igualdade ou de desigualdade.
  Permite usar `=` num `if` e usar o resultado numa demonstração.

Essa diferença — entre calcular uma resposta e afirmar algo que se prova —
volta no capítulo 3 como a distinção entre `Bool` e `Prop`, e é o assunto do
capítulo 6, onde verificar uma sentença num modelo será exatamente calcular
o que em geral só se enunciaria.
-/

def count [BEq α] (x : α) : List α → Nat
  | []      => 0
  | y :: ys => if x == y then count x ys + 1 else count x ys

#eval count 'e' "temperate".toList
#eval count "thou" ["thou","art","thou"]

/-! ### Declarar sem definir

Com classes de tipos à mão, cabe explicar uma construção que o capítulo 3 vai
usar muito. Às vezes interessa dizer que uma função _existe_, com um certo tipo,
sem dizer qual função é. `opaque` faz isso: declara o nome com o tipo e não dá
corpo.

O uso tem conteúdo semântico. No capítulo 3, o verbo *likes* é declarado assim,
porque o tipo do verbo diz com que expressões ele se combina — e é só disso que
a sintaxe precisa. _Qual_ relação o verbo denota é assunto do modelo, e o
capítulo 6 é que vai fixá-la. `opaque` é essa divisão posta em código. -/

opaque triple : Int → Int

#check triple
#check triple 10

/-! O `#check` responde, porque conferir tipo não precisa do corpo. O `#eval`
não teria como calcular — e o que ele devolve merece atenção, porque não é erro
e não é o valor da função: -/

#eval triple 10

/-! `0` é o valor _default_ de `Int`. Para aceitar um `opaque`, Lean exige que o
tipo seja **habitado**: que exista pelo menos um valor nele, sem o quê a
declaração afirmaria que existe algo impossível. E é uma classe de tipos que
registra isso — `Inhabited α`, cuja instância fornece o valor default de `α`.
Declarar `opaque bad : T` para um `T` vazio é recusado com
`failed to synthesize 'Inhabited' or 'Nonempty' instance`; é a mesma busca de
instância do `[BEq α]` acima, falhando por não haver o que encontrar. Como o
corpo não existe, é esse valor default que o `#eval` acaba exibindo.

A regra prática: `opaque` serve para raciocinar sobre tipos, não para calcular.
Onde ele aparecer, `#eval` não é a pergunta certa — `#check` é. -/


/-! ## Um primeiro fragmento linguístico

Sujeito, predicado e sentença como tipos. A estrutura deixa de ser texto e
passa a ser um valor, e o verificador de tipos passa a recusar as combinações
que não são sentenças. Este é o embrião do capítulo 4.

`ToString` é a instância que diz como exibir um valor para leitores. É
distinta de `Repr`, que existe para depuração e mostra a estrutura interna.
-/

inductive Subject where
  | Chomsky | Montague
deriving Repr, DecidableEq

inductive Predicate where
  | Wrote (title : String)
deriving Repr

inductive Sentence where
  | S (subj : Subject) (pred : Predicate)

abbrev Sentences := List Sentence

instance : ToString Subject where
  toString
    | .Chomsky  => "Chomsky"
    | .Montague => "Montague"

instance : ToString Predicate where
  toString | .Wrote t => s!"wrote \"{t}\""

instance : ToString Sentence where
  toString | .S s p => s!"{s} {p}"

def makeP (title : String) : Predicate := .Wrote title
def makeS (s : Subject) (p : Predicate) : Sentence := .S s p

#eval toString (makeS .Chomsky (makeP "Syntactic Structures"))

/-! ## Fonemas como feixes de traços

Harmonia vocálica é o fenômeno em que as vogais de uma palavra têm de
concordar em algum traço — em turco e em finlandês, no traço de anterioridade.
Descrevê-la como substituição de letras erra o alvo: o processo não vê letras,
vê traços fonológicos, e a letra é só a realização de superfície.

Então o fonema não é um `Char`. É um conjunto de traços, e cada traço é um par
atributo/valor. Com essa representação, a harmonia vocálica é uma operação de
uma linha: forçar um traço a um valor.

Um `structure` diz melhor o que se quer aqui que um construtor com dois
argumentos posicionais — os campos ganham nome, e `f.attr` e `f.value` passam
a existir.
-/

inductive Attr where
  | Back | High | Round | Cons
deriving Repr, DecidableEq, BEq

inductive Value where
  | Plus | Minus
deriving Repr, DecidableEq, BEq

structure Feature where
  attr  : Attr
  value : Value
deriving Repr, DecidableEq, BEq

abbrev Phoneme := List Feature

section
open Attr Value

def i : Phoneme := [⟨Cons, Minus⟩, ⟨High, Plus⟩,  ⟨Round, Minus⟩, ⟨Back, Minus⟩]
def a : Phoneme := [⟨Cons, Minus⟩, ⟨High, Minus⟩, ⟨Round, Minus⟩, ⟨Back, Plus⟩]
def u : Phoneme := [⟨Cons, Minus⟩, ⟨High, Plus⟩,  ⟨Round, Plus⟩,  ⟨Back, Plus⟩]

end

/-- Consulta o valor de um traço no feixe. `Option` outra vez: o traço pode
não estar especificado. -/
def fValue (attr : Attr) : Phoneme → Option Value
  | []      => none
  | f :: fs => if f.attr == attr then some f.value else fValue attr fs

#eval fValue .High i
#eval fValue .High a
#eval fValue .Back ([] : Phoneme)

/-- Força um traço a um valor. É a operação da harmonia vocálica. -/
def fMatch (attr : Attr) (value : Value) (fs : Phoneme) : Phoneme :=
  fs.map fun f => if f.attr == attr then { f with value := value } else f

#eval fMatch .Back .Plus i

/-- A realização de superfície: qual letra corresponde a este feixe.

A função é total, e tem de ser: um feixe arbitrário pode não corresponder a
nenhuma vogal do inventário, e `none` é a resposta correta nesse caso. O
último exemplo mostra por que isso importa — forçar `Back` a `Plus` em `i`
produz um feixe que nenhuma das três vogais realiza. -/
def realize (x : Phoneme) : Option Char :=
  if x == i then some 'i'
  else if x == a then some 'a'
  else if x == u then some 'u'
  else none

#eval realize i
#eval realize (fMatch .Back .Plus i)

end Chapter02
