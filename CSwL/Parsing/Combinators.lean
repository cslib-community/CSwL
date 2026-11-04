import CSwLMeta
import Bib
import CSwL.Parsing.ParseTrees
import Mathlib.Data.List.Monad

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Parsers e combinadores de parsers" =>
%%%
tag := "parser-combinators"
file := "Combinators"
%%%

```lean
namespace Parsing
```

:::terse
- Objetivo: um método geral para analisar com qualquer gramática livre
  de contexto, em que o código do parser tem a forma das regras da
  gramática.
- Basta tratar três coisas: os símbolos terminais, a escolha `|` entre
  regras, e a sequência B₁ ⋯ Bₙ do lado direito de uma regra.
- Um parser lê um *prefixo* da entrada e devolve todos os pares
  (resultado, resto da entrada) que consegue construir. A lista vazia é
  a falha; mais de um par é ambiguidade.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, from the start to the type of a parser.
:::
::::

:::terse
- Em Lean, esse tipo já existe: `StateT (List α) List β`. O estado é o
  resto da entrada, e `List` dá as várias respostas.
- O `example` mostra que os dois tipos são o mesmo, por definição: um
  `Parser` é uma função, e pode ser escrito como tal.
- Usar `StateT` dá de graça as operações de que vamos precisar, com a
  notação que o Lean já tem para elas: `pure`, `failure`, `<|>`, `<$>` e
  `do`.
:::

```lean
abbrev Parser (α β : Type) := StateT (List α) List β

example {α β : Type} :
    Parser α β = (List α → List (β × List α)) := rfl
```

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, from "The parser uses the grammar rules…" to
Figure 9.1 and the paragraph after it.
:::
::::

:::terse
- Os dois parsers mais simples não leem nada. O parser `pure r` sempre
  dá certo, com o resultado `r`. O parser `failure` sempre falha.
- A expressão `p.run xs` aplica o parser `p` à entrada `xs`.
:::

```lean
#eval (pure 1 : Parser Char Nat).run "ab".toList
#eval (failure : Parser Char Nat).run "ab".toList
```

:::terse
- O parser `symbol c` reconhece o símbolo `c` no início da entrada;
  `token cs`, a lista de símbolos `cs`; `satisfy p`, um símbolo
  qualquer que tenha a propriedade `p`.
- Os três são escritos diretamente como funções sobre a entrada.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, from "Two very elementary parsers…" to the
definition of `digit`.
:::
::::

```lean
def symbol {α : Type} [BEq α] (c : α) : Parser α α
  | x :: xs => if x == c then [(x, xs)] else []
  | [] => []

def token {α : Type} [BEq α] (cs : List α)
  : Parser α (List α)
  | xs =>
    if cs == xs.take cs.length then
     [(cs, xs.drop cs.length)]
    else []

def satisfy {α : Type} (p : α → Bool) : Parser α α
  | x :: xs => if p x then [(x, xs)] else []
  | [] => []

def digit : Parser Char Char := satisfy Char.isDigit

#eval (symbol 'a').run "ab".toList
#eval (token "ab".toList).run "abc".toList
#eval digit.run "42".toList
```

::::exercise (rating := 1) (name := "symbol-satisfy")
Defina `symbol'`, que faz o mesmo que `symbol`, usando `satisfy`.

```lean
def symbol' {α : Type} [BEq α] (c : α) : Parser α α :=
  solution!(satisfy (· == c))

theorem symbol'_eq_symbol {α : Type} [BEq α] (c : α)
    (xs : List α) : symbol' c xs = symbol c xs := by
  solution!
   cases xs <;> rfl
```
::::

:::terse
- Os parsers elementares servem para os terminais. Com terminais
  `String`, a palavra *Alice* é `symbol "Alice"`; com terminais `Char`,
  é `token "Alice".toList`.
- Combinadores de parsers são funções que constroem parsers a partir de
  outros parsers.
- O combinador `just` filtra as análises: `just p` só aceita as de `p`
  que consomem a entrada toda.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, from "Now, these elementary parsers…" to the
definition of `just`.
:::
::::

```lean
def just {α β : Type} (p : Parser α β) : Parser α β
 | xs => (p xs).filter fun (_, ys) => ys.isEmpty
```

:::terse
- A escolha é `p <|> q`: todas as análises de `p`, seguidas de todas as
  de `q`. O `example` mostra que isso é a concatenação das listas.
- VP → smiled | laughed vira `symbol "smiled" <|> symbol "laughed"`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, from "For parsing one of our grammars…" to
the parser for VP.
:::
::::

```lean
example {α β : Type} (p q : Parser α β) (xs : List α) :
    (p <|> q) xs = p xs ++ q xs := rfl
```

:::terse
- A sequência é um bloco `do`. Em `let r₁ ← p`, o parser `p` lê o início
  da entrada e dá o resultado `r₁`; o parser da linha seguinte começa no
  resto que `p` deixou.
- Cada análise de `p` continua separadamente. O `example` mostra a
  operação por trás do `do`, `>>=`: um `flatMap` sobre as análises de
  `p`.
- Com isso, a gramática da figura vira uma definição por regra; aqui, o
  resultado é só a lista das palavras lidas.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, from "Next, what to do with rules like
S → NP VP?" to the definitions of `pS`, …, `pN` and the paragraph
after them.
:::
::::

```lean
example {α β γ : Type} (p : Parser α β) (q : β → Parser α γ)
    (xs : List α) :
    (p >>= q) xs =
      (p xs).flatMap fun (r, ys) => q r ys := rfl

def pD : Parser String String :=
  symbol "every" <|> symbol "some" <|> symbol "no"

def pN : Parser String String :=
  symbol "dwarf" <|> symbol "wizard"

def pVP : Parser String String :=
  symbol "smiled" <|> symbol "laughed"

def pNP : Parser String (List String) :=
  (do
    let w ← symbol "Alice" <|> symbol "Dorothy"
    return [w]) <|>
  (do
    let d ← pD
    let n ← pN
    return [d, n])

def pS : Parser String (List String) := do
  let np ← pNP
  let vp ← pVP
  return np ++ [vp]

#eval pS.run ["every", "wizard", "smiled"]
#eval pS.run ["Alice", "laughed", "loudly"]
```

:::terse
- O parser `f <$> p` aplica `f` ao resultado de cada análise de `p`,
  sem mexer no resto da entrada.
- O parser `digitize` lê um dígito e devolve o número que ele
  representa.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, from "However, we are not quite there
yet…" to the definition of `digitize`.
:::
::::

```lean
example {α β γ : Type} (f : β → γ) (p : Parser α β)
    (xs : List α) :
    (f <$> p) xs =
      (p xs).flatMap fun (r, ys) => [(f r, ys)] := rfl

def digitize : Parser Char Nat :=
  (fun c => c.toNat - '0'.toNat) <$> digit

#eval digitize.run "42".toList
```

:::terse
- Agora, parsers que constroem árvores: `Parser α (ParseTree α β)`,
  com terminais `α` nas folhas e não terminais `β` nos nós.
- O parser `epsilonT` não lê nada e dá a árvore vazia. O parser
  `symbolT s` lê o terminal `s` e dá uma folha.
- A função `collect` aplica uma lista de parsers um depois do outro e
  junta os resultados numa lista. A função `parseAs` faz disso um nó:
  `parseAs A ps` é a regra A → B₁ ⋯ Bₙ, com `ps` os parsers de B₁, …,
  Bₙ, e o nó tem rótulo `A`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, from "We will use <$> for constructing parse
trees." to the definition of `parseAs` and the paragraph after it.
:::
::::

```lean
def epsilonT {α β : Type} : Parser α (ParseTree α β) :=
  pure .ep

def symbolT {α β : Type} [BEq α] (s : α) :
    Parser α (ParseTree α β) :=
  .leaf <$> symbol s

def collect {α β : Type} :
    List (Parser α β) → Parser α (List β)
  | [] => pure []
  | p :: ps => do
    let r ← p
    let rs ← collect ps
    return r :: rs

def parseAs {α β : Type} (label : β)
    (ps : List (Parser α (ParseTree α β))) :
    Parser α (ParseTree α β) :=
  .branch label <$> collect ps
```

:::terse
- A gramática de novo, agora com árvores: um parser por categoria, uma
  linha por regra.
:::

```lean
def det : Parser String (ParseTree String Char) :=
  symbolT "every" <|> symbolT "some" <|> symbolT "no"

def cn : Parser String (ParseTree String Char) :=
  symbolT "man" <|> symbolT "woman"

def vp : Parser String (ParseTree String Char) :=
  symbolT "smiled" <|> symbolT "laughed"

def np : Parser String (ParseTree String Char) :=
  symbolT "Alice" <|> symbolT "Dorothy"
  <|> parseAs 'N' [det, cn]

def sent : Parser String (ParseTree String Char) :=
  parseAs 'S' [np, vp]

#eval (just sent).run ["every", "man", "laughed"] |>.map
  (toString ·.1)
```

:::terse
- Os palíndromos outra vez, agora uma linha por regra da gramática. Não
  há mais divisão da entrada: cada parser lê o que precisa e deixa o
  resto para o seguinte.
- O parser `palindrome` chama a si mesmo, mas sobre um resto da entrada
  que o Lean não vê: ele está escondido dentro do `StateT`. Por isso a
  definição é `partial def`. O Lean aceita a definição sem provar que
  ela termina, mas em troca não conhece a equação que a define: nada
  que dependa do que `palindrome` faz pode ser provado.
- Sem `just`, o parser também devolve as análises de prefixos da
  entrada, com o seu resto.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, the sentences introducing the two parsers
above and the palindrome parser.
:::
::::

```lean
partial def palindrome :
    Parser Char (ParseTree Char Char) :=
  epsilonT <|> symbolT 'a' <|> symbolT 'b' <|> symbolT 'c'
  <|> parseAs 'A' [symbolT 'a', palindrome, symbolT 'a']
  <|> parseAs 'A' [symbolT 'b', palindrome, symbolT 'b']
  <|> parseAs 'A' [symbolT 'c', palindrome, symbolT 'c']

#eval (just palindrome).run "abcba".toList |>.map
  (toString ·.1)
#eval palindrome.run "aba".toList |>.map fun (t, ys) =>
  (toString t, String.ofList ys)
```

:::terse
- O combinador `many` faz a repetição `{A}` das gramáticas em EBNF:
  `many p` aplica `p` quantas vezes for possível, inclusive nenhuma. A análise mais longa vem
  primeiro.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, the sentences introducing `many`.
:::
::::

```lean
partial def many {α β : Type} (p : Parser α β) :
    Parser α (List β) :=
  (do
    let r ← p
    let rs ← many p
    return r :: rs) <|> pure []

#eval (many (symbol 'a')).run "aab".toList
```

::::exercise (rating := 1) (name := "parse-many-as")
Para ter uma árvore, a repetição precisa ficar sob um rótulo. Defina
`parseManyAs l p`, que aplica `p` quantas vezes for possível e põe as
árvores obtidas sob um nó com rótulo `l`. Confira o resultado com
`adjectives`, uma sequência de adjetivos sob o rótulo `J`.

```lean
def parseManyAs {α β : Type} (l : β)
    (p : Parser α (ParseTree α β)) :
    Parser α (ParseTree α β) :=
  solution!(.branch l <$> many p)

def adjectives : Parser String (ParseTree String Char) :=
  parseManyAs 'J' (symbolT "happy" <|> symbolT "evil")

theorem adjectives_happy_evil :
    ((adjectives.run ["happy", "evil", "dwarf"]).map
      fun (t, ys) => (toString t, ys)) =
    [("[.J happy evil]", ["dwarf"]),
     ("[.J happy]", ["evil", "dwarf"]),
     ("[.J ]", ["happy", "evil", "dwarf"])] := by
  solution!
   native_decide
```
::::

:::terse
- Em resumo: um terminal t vira `symbolT t`, um não terminal A vira
  `parseAs A`, a escolha vira `<|>`, e o lado direito de uma regra vira a
  lista de parsers passada a `parseAs`.
- O método não serve para toda gramática livre de contexto. Numa regra
  recursiva à esquerda, A → A T, o parser de A chama a si mesmo antes de
  ler qualquer símbolo, sobre a mesma entrada, e nunca para.
- O parser `leftRec` abaixo é aceito, por ser `partial def`, mas não
  deve ser rodado: cada chamada abre outra, até esgotar a pilha, e o Lean para
  com um erro de recursão profunda.
- O reconhecedor por divisão não tinha esse problema, desde que as
  divisões com pedaço vazio fossem descartadas: aí cada chamada recebia
  um pedaço menor da entrada, e o Lean exigia uma prova disso.
- Há combinadores de parsers que garantem a terminação e aceitam
  recursão à esquerda; ver {citep Bib.danielsson2010}[].
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.3, the closing summary ("To sum up, …"),
without the sentence on `parseManyAs`.
:::
::::

```lean
partial def leftRec : Parser Char (ParseTree Char Char) :=
  parseAs 'A' [leftRec, symbolT 'a'] <|> symbolT 'b'
```

```lean
end Parsing
```
