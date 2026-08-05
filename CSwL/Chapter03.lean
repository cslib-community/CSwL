/-!
# 3. Programação funcional

Um feixe de traços fonológicos e uma árvore sintática são o mesmo tipo de
objeto: dados com forma, definidos por casos, percorridos por recursão. Quem
sabe escrever o primeiro sabe escrever o segundo, e é por isso que os
exemplos daqui — plural do sueco, harmonia vocálica, quem escreveu o quê —
já são linguísticos, embora nenhuma teoria do significado tenha começado
ainda.
-/

namespace Chapter03

/-! ## Uma primeira função

O tipo vem primeiro. `Int → Int` é uma promessa, e o corpo da definição tem
de cumpri-la; enquanto não cumprir, o arquivo não compila.
-/

def square (x : Int) : Int := x * x

#eval square 7            -- 49
#eval square (-3)         -- 9
#eval square (square 7)   -- 2401

/-! ## Recursão

Uma definição recursiva precisa de dois cuidados: ter caso base, e chegar
nele. O segundo não é uma recomendação — é uma exigência que o compilador
verifica, e a definição é rejeitada se ele não conseguir ver que a recursão
termina.

Casar padrão em `Nat` pelos dois casos `0` e `n + 1` dá as duas coisas de
uma vez: o caso base é `0`, e a chamada recursiva recebe `n`, que é menor.
Não há um terceiro caso a esquecer, e não há argumento para o qual a função
não responda.
-/

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

#eval hword "shrimptoast".toList   -- true
#eval hword "antiquing".toList     -- false

def reversal : List Char → List Char
  | []     => []
  | c :: t => reversal t ++ [c]

#eval String.ofList (reversal "Chomsky".toList)   -- "yksmohC"

/-- Remove o último caractere. -/
def initS (s : String) : String := String.ofList s.toList.dropLast

#eval initS "flicka"   -- "flick"

/-! ## Tipos definidos por casos

`inductive` declara um tipo listando as formas que seus valores podem ter.
Quando nenhuma forma carrega argumento, o tipo é uma enumeração; quando
carrega, é um registro variante; quando a forma se refere ao próprio tipo
sendo definido, é uma árvore. As três coisas são o mesmo mecanismo, e o
capítulo 4 usa a terceira.

`deriving Repr, DecidableEq` pede que a exibição e o teste de igualdade sejam
gerados em vez de escritos à mão.
-/

/-- As cinco classes de declinação do plural em sueco. -/
inductive DeclClass where
  | One | Two | Three | Four | Five
deriving Repr, DecidableEq

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

#eval swedishPlural "flicka" .One    -- "flickor"
#eval swedishPlural "pojke"  .Two    -- "pojkar"
#eval swedishPlural "rad"    .Three  -- "rader"
#eval swedishPlural "ko"     .Three  -- "kor"
#eval swedishPlural "hus"    .Five   -- "hus"

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

#eval myLast [1,2,3]             -- some 3
#eval myLast ([] : List Nat)     -- none

def average (xs : List Int) : Option Rat :=
  if xs.isEmpty then none
  else some ((xs.sum : Rat) / (xs.length : Rat))

#eval average [1,2,3,4]   -- some (5/2)
#eval average []          -- none

-- Nem toda função da biblioteca é honesta desse modo: algumas devolvem um
-- valor default no caso ruim, em vez de `Option`. `String.back` é uma delas,
-- e vale conhecer as que são assim.
#eval "rad".back   -- 'd'
#eval "".back      -- 'A' — não é erro, é o `Char` default

/-! ## Classes de tipos

`count` conta ocorrências em qualquer lista cujos elementos se possam
comparar. Essa exigência entra na assinatura entre colchetes, `[BEq α]`: uma
instância de igualdade para `α`, que Lean encontra sozinho no ponto de uso.

Duas noções de igualdade convivem, e vale separá-las desde já:

* `BEq α` devolve `Bool` e se escreve `==`. Serve para calcular.
* `DecidableEq α` devolve uma _prova_ de igualdade ou de desigualdade.
  Permite usar `=` num `if` e usar o resultado numa demonstração.
-/

def count [BEq α] (x : α) : List α → Nat
  | []      => 0
  | y :: ys => if x == y then count x ys + 1 else count x ys

#eval count 'e' "temperate".toList          -- 3
#eval count "thou" ["thou","art","thou"]    -- 2

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

#eval fValue .High i               -- some Value.Plus
#eval fValue .High a               -- some Value.Minus
#eval fValue .Back ([] : Phoneme)  -- none

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

#eval realize i                       -- some 'i'
#eval realize (fMatch .Back .Plus i)  -- none

end Chapter03
