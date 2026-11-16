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
- Objetivo: analisar uma lista de símbolos, caracteres ou palavras,
  segundo as regras de uma gramática livre de contexto.
- A gramática vira uma função, o *parser*, construída combinando
  funções menores e mais simples.
- Bastam três coisas: parsers para os terminais, a escolha `|` entre
  regras, e a sequência `B₁ ⋯ Bₙ` do lado direito de uma regra.
- O exemplo é a gramática abaixo, com a entrada
  `[every, wizard, smiled]`.
- *Descida recursiva*: a análise parte do símbolo inicial `S` e desce
  pelas regras até os terminais.
- Por isso um parser lê um *prefixo* da entrada e devolve todos os pares
  (resultado, resto da entrada) que consegue construir. A lista vazia é
  a falha. Duas árvores distintas com o mesmo resto indicam
  ambiguidade na análise daquele prefixo.
:::

::::full
Nesta seção, vamos construir parsers para gramáticas livres de contexto.
As regras têm a forma `A → B₁ ⋯ Bₙ`, em que cada `Bᵢ` pode ser um terminal
ou um não terminal. Regras com o mesmo símbolo à esquerda podem ser
reunidas com `|`, que indica escolha. Para transformar a gramática em
um parser, vamos partir de parsers básicos e combinadores de parsers.

Considere a entrada `[every, wizard, smiled]` e a gramática abaixo. Para
analisar a entrada como `S`, o parser usa a única regra `S → NP VP`. Ele
precisa primeiro analisar um prefixo da entrada como `NP`. A produção de `NP`
tem quatro alternativas, e o parser tenta todas. As duas primeiras
falham, porque a entrada não começa com `Alice` nem com `Dorothy`. A
terceira, `D N`, pede um `D` e depois um `N`. Entre as alternativas de
`D`, só `every` dá certo, e sobra `[wizard, smiled]`. Sobre esse resto,
a alternativa `dwarf` de `N` falha e `wizard` dá certo, e sobra
`[smiled]`. A quarta, `D ADJS N`, também lê `every`, mas falha em
seguida: `ADJS` pede pelo menos um `ADJ`, e `wizard` é alternativa de `N`. Assim
`NP` reconhece o prefixo `every wizard` e deixa `[smiled]` para o `VP`, que
reconhece `smiled` e não deixa resto algum. Essa estratégia, que parte
do símbolo inicial e desce pelas regras até os terminais, é chamada de
*descida recursiva*.
::::

```bnf
S    ::= NP VP ;
NP   ::= Alice | Dorothy | D N | D ADJS N ;
ADJS ::= ADJ "..." ADJ ;
VP   ::= smiled | laughed ;
D    ::= every | some | no ;
ADJ  ::= happy | evil ;
N    ::= dwarf | wizard ;
```

:::terse
Em vez de definir um novo tipo para nosso parser, reusamos
o {name}`StateT` do Lean.
:::

::::full
Em Lean, {lean}`StateT` é um construtor de tipos. Como mostra o `#print`
a seguir, ele recebe três parâmetros: o tipo `σ` do estado, um
construtor de tipos `m` e o tipo `α` do resultado. Então `StateT σ m α`
é o tipo das funções `σ → m (α × σ)`.
Cada função recebe um estado e devolve, dentro de `m`, um resultado e
um novo estado.

Para implementar um parser, usamos `List α` como estado, pois a lista
representa a parte da entrada que ainda falta analisar. Escolhemos
{lean}`List` para `m`, de modo que o parser possa devolver zero, uma
ou várias respostas.

Substituindo, `StateT (List α) List β` é `List α → List (β × List α)`,
como o `example` abaixo confirma. A vantagem de reusar {lean}`StateT` é que as
operações para combinar parsers, que veremos a seguir, já vêm prontas
com ele, e não precisamos defini-las.
::::

```lean
#print StateT

abbrev Parser (α β : Type) := StateT (List α) List β

example {α β : Type} :
    Parser α β = (List α → List (β × List α)) := rfl
```

::::full
Em `Parser α β`, `α` é o tipo dos símbolos da entrada e `β` é o tipo
do resultado, que pode ser uma árvore. Cada par devolvido pelo parser
contém um resultado e o resto da entrada correspondente. Quando o
parser produz duas árvores distintas com o mesmo resto, elas são duas
análises do mesmo prefixo.
::::

:::terse
- A expressão `p.run xs` aplica o parser `p` à entrada `xs`.
- Em `Parser α β`, o `α` é o tipo dos símbolos da entrada e o `β` o
  tipo do que o parser devolve. Vale acompanhar o `β` de cada parser
  a seguir.
- Os dois parsers mais simples não consomem nada da entrada. O parser `pure r`
  sempre dá certo, com o resultado `r`. O parser {name}`failure` sempre falha. Os
  dois servem para qualquer `β`.
:::

::::full
A expressão `p.run xs` aplica o parser `p` à entrada `xs`. Para
transformar um valor `r : β` em um parser, usamos `pure r`. Ao receber
`xs`, esse parser produz exatamente uma análise, `[(r, xs)]`. O
resultado é `r` e o resto é a própria entrada. No primeiro exemplo,
`pure 2` produz o número `2` e deixa os dois caracteres de `"ab"`
intactos.

Já {name}`failure` produz `[]` para qualquer entrada. A lista vazia indica
que não houve análise. Tanto {name}`pure` quanto {name}`failure` podem ser usados
para qualquer tipo de resultado `β`.
::::

```lean
#eval (pure 2 : Parser Char Nat).run "ab".toList
#eval (failure : Parser Char Nat).run "ab".toList
```

:::terse
- O parser `symbol c` reconhece o símbolo `c` no início da entrada e
  o devolve: é um `Parser α α`.
- O parser `token cs` reconhece a lista de símbolos `cs` e a devolve: é
  um `Parser α (List α)`. *Token*, aqui, é só isso, uma lista de
  símbolos da entrada.
- O parser `satisfy p` reconhece um símbolo qualquer que tenha a
  propriedade `p` e o devolve. Também um `Parser α α`.
- Os três são escritos diretamente como funções sobre a entrada.
:::

::::full
O parser `symbol c` reconhece um símbolo `c` no início da entrada. Se a
lista começa com `c`, ele devolve esse símbolo e deixa a cauda da lista
como resto. Se a lista é vazia ou começa com outro símbolo, a análise
falha.

Podemos generalizar esse parser para reconhecer uma lista inteira de
símbolos, chamada aqui de *token*. O parser `token cs` usa {name}`List.take` para
comparar `cs` com o prefixo da entrada de mesmo comprimento. Se forem
iguais, devolve `cs` e usa {name}`List.drop` para obter o resto. Assim, `symbol c`
devolve um símbolo e `token cs` devolve uma lista de símbolos.

O parser `satisfy p` reconhece o primeiro símbolo da entrada quando ele
satisfaz a propriedade `p`. Por exemplo, `digit` usa {name}`Char.isDigit`
para reconhecer um dígito no início de uma lista de caracteres.
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

#eval (symbol 'a').run "abc".toList
#eval (token "ab".toList).run "abcde".toList
#eval digit.run "42".toList
```

::::exercise (rating := 1) (name := "symbol-satisfy")
Defina `symbol'`, que faz o mesmo que {name}`symbol`, usando {name}`satisfy`.

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
- Os parsers elementares servem para os terminais, e a escolha do tipo
  da entrada decide qual usar.
- Se a entrada é uma lista de palavras, terminais {lean}`String`, a
  palavra `Alice` é um símbolo só: {lean}`symbol "Alice"`.
- Se é uma lista de caracteres, terminais {lean}`Char`, `Alice` é um
  token de cinco símbolos: {lean}`token "Alice".toList`.
:::

::::full
A escolha do tipo da entrada determina o que conta como um símbolo.
Se a entrada é uma lista de palavras, `Alice` é um único símbolo de
tipo {name}`String`. Se a entrada é uma lista de caracteres, `Alice`
é um token de cinco símbolos de tipo {name}`Char`.
::::

```lean
#eval
  let s : String := "Alice"
  let xs : List String := ["Alice", "laughed"]
  (symbol s).run xs
#eval
  let tk : List Char := "Alice".toList
  let xs : List Char := "Alice laughed".toList
  (token tk).run xs
```

:::terse
- Combinadores de parsers são funções que constroem parsers a partir de
  outros parsers.
- O combinador `just` filtra as análises: `just p` só aceita as de `p`
  que consomem a entrada toda.
:::

::::full
Com esses parsers elementares, podemos reconhecer os terminais da
gramática. Para analisar os não terminais, precisamos combinar
parsers, seja para reunir alternativas, seja para aplicá-los em
sequência.

Uma função que constrói um parser a partir de outros parsers é chamada
de *combinador de parsers*. Um primeiro exemplo é `just`. O parser
`just p` aplica `p` à entrada e mantém apenas os pares cujo resto é
vazio, isto é, as análises que consomem a entrada inteira.
::::

```lean
def just {α β : Type} (p : Parser α β) : Parser α β
 | xs => (p xs).filter fun (_, ys) => ys.isEmpty
```

:::terse
- A escolha é `p <|> q`: todas as análises de `p`, seguidas de todas as
  de `q`. O `example` mostra que isso é a concatenação das listas.
:::

::::full
Para representar a escolha entre duas alternativas, usamos `p <|> q`.
Os dois parsers recebem a mesma entrada, e o resultado é a concatenação
das listas de análises, com as de `p` primeiro. Se ambos tiverem
sucesso, as análises de ambos aparecem no resultado.

Por exemplo, para reconhecer `VP → smiled | laughed` em uma lista de
palavras, podemos usar `symbol "smiled" <|> symbol "laughed"`. O
`example` mostra a igualdade que caracteriza a escolha para parsers.
::::

```lean
example {α β : Type} (p q : Parser α β) (xs : List α) :
    (p <|> q) xs = p xs ++ q xs := rfl
```

:::terse
- O parser `f <$> p` aplica a função `f` ao resultado de cada análise
  de `p`, sem mexer no resto da entrada. Se `p : Parser α β` e
  `f : β → γ`, então `f <$> p : Parser α γ`. O primeiro `example`
  mostra que isso é um {name}`List.flatMap` sobre as análises de `p`.
- No exemplo `digitize`, a função à esquerda do operador `<$>` leva um caractere
  processado por {name}`digit` ao número que ele representa.
- A docstring de `<$>` diz "aplica uma função dentro de um funtor". Um
  construtor de tipos `m` com uma operação `<$>`, que leva
  `f : β → γ` a uma função de `m β` em `m γ` e obedece a certas leis,
  é chamado de *funtor*. Em {name}`List`, `f <$> xs` é `xs.map f`, como mostra
  o último `example`. Para parsers, "dentro" quer dizer no resultado.
:::

::::full
Até aqui, os parsers de terminais devolvem os símbolos reconhecidos.
Para obter uma árvore, precisamos transformar o resultado da análise.
A expressão `f <$> p` aplica a função `f` ao resultado de cada análise
de `p`, preservando o resto da entrada de cada uma. Se
`p : Parser α β` e `f : β → γ`, então `f <$> p : Parser α γ`.

Por exemplo, {name}`digit` devolve um caractere. O parser `digitize` usa
`<$>` para convertê-lo no número natural que ele representa. Na entrada
`"42".toList`, o resultado é `4` e o resto é `['2']`. Na entrada
`"x2".toList`, a análise falha já no primeiro caractere.

Um construtor de tipos `m` equipado com uma operação `<$>` que
transforma uma função de `β` em `γ` em uma função de `m β` em
`m γ`, e que obedece a certas leis, é chamado de *funtor*. Para
listas, `f <$> xs` é `xs.map f`. Para parsers, a transformação ocorre
nos resultados das análises.
::::

```lean
example {α β γ : Type} (f : β → γ) (p : Parser α β)
    (xs : List α) :
    (f <$> p) xs =
      (p xs).flatMap fun (r, ys) => [(f r, ys)] := rfl

def digitize : Parser Char Nat :=
  (fun c => c.toNat - '0'.toNat) <$> digit

#eval digitize.run "42".toList
#eval digitize.run "x2".toList

example : (· + 1) <$> [1, 2, 3] = [1, 2, 3].map (· + 1) :=
  by decide
```

:::terse
- Nosso uso principal de `<$>` será para construir árvores. Um parser que produz
  árvores tem tipo `Parser α (ParseTree α β)`, com terminais `α` nas
  folhas e não terminais `β` nos nós.
- O parser `symbolT s` lê o terminal `s` e, com `<$>`, faz dele uma
  folha.
- Cada alternativa dessas categorias tem um terminal à direita e
  produz um nó com uma folha: `det` aplica `fun t => .branch "D" [t]` à folha lida. Assim
  toda regra usada aparece na árvore.
- Os rótulos são {name}`String`, os nomes das categorias da gramática.
:::

::::full
Usaremos `<$>` para construir árvores sintáticas. Os parsers terão o
tipo `Parser α (ParseTree α β)`. Os terminais, de tipo `α`, aparecem
nas folhas. Os rótulos dos nós internos, de tipo `β`, identificam os
não terminais da gramática.

Para um terminal `s`, `symbolT s` aplica o construtor `.leaf`
ao resultado de `symbol s`. Uma regra como `D → every | some | no`
também deve aparecer na árvore. Por isso, `det` escolhe um dos três
parsers de terminais e põe a folha resultante sob um nó rotulado
`"D"`. O mesmo procedimento dá os parsers de `ADJ`, `N` e `VP`.
::::

```lean
def symbolT {α β : Type} [BEq α] (s : α)
  : Parser α (ParseTree α β) := .leaf <$> symbol s

def det : Parser String (ParseTree String String) :=
  (fun t => .branch "D" [t]) <$>
    (symbolT "every" <|> symbolT "some" <|> symbolT "no")

def adj : Parser String (ParseTree String String) :=
  (fun t => .branch "ADJ" [t]) <$>
    (symbolT "happy" <|> symbolT "evil")

def n : Parser String (ParseTree String String) :=
  (fun t => .branch "N" [t]) <$>
    (symbolT "dwarf" <|> symbolT "wizard")

def vp : Parser String (ParseTree String String) :=
  (fun t => .branch "VP" [t]) <$>
    (symbolT "smiled" <|> symbolT "laughed")

#eval det.run ["every", "wizard", "smiled"] |>.map
  fun (t, ys) => (toString t, ys)
```

:::terse
- Para `NP → D N` precisamos aplicar {name}`det`, depois {name}`n` sobre o resto que {name}`det`
  deixou, e juntar as duas árvores num nó `NP`.
- O operador `>>=` faz isso. Em `p >>= f`, o parser `p` é aplicado à
  entrada; para cada análise `(r, ys)` de `p`, a função `f`, ao receber
  o resultado de `p`, constrói um novo parser `f r`, que então é
  aplicado ao resto `ys`. O `example` mostra que isso é um {name}`List.flatMap`
  sobre as análises de `p`.
- No `#eval`, a primeira função recebe a árvore `td` de {name}`det`; a
  segunda, a árvore `tn` de {name}`n`; no fim, {name}`pure` devolve como resultado o nó `NP` com
  as duas árvores.
:::

::::full
Para analisar a regra `NP → D N`, primeiro aplicamos {name}`det` à entrada.
Para cada análise obtida, aplicamos {name}`n` ao resto.

Para encadear esses passos, usamos `>>=`. Em `p >>= f`, analisamos a
entrada com `p`. Para cada par `(r, ys)` devolvido, `f r` constrói o
parser que será aplicado ao resto `ys`. O {name}`List.flatMap` do primeiro
exemplo reúne em uma única lista todas as análises obtidas dessa
maneira. No segundo exemplo, o primeiro passo obtém a árvore de `D`, o
segundo obtém a de `N`, e {name}`pure` devolve o nó `NP` sem consumir mais
símbolos.
::::

```lean
example {α β γ : Type} (p : Parser α β) (f : β → Parser α γ)
    (xs : List α) :
    (p >>= f) xs =
      (p xs).flatMap fun (r, ys) => f r ys := rfl

#eval
  (det >>= fun td =>
    n >>= fun tn =>
      pure (ParseTree.branch "NP" [td, tn])).run
    ["every", "wizard", "smiled"] |>.map
  fun (t, ys) => (toString t, ys)
```

:::terse
- Encadear `>>=` torna a leitura difícil. A notação `do` é outra forma de
  escrever a mesma coisa, uma linha por passo: `let td ← det` aplica
  {name}`det` e chama de `td` a árvore lida; a linha seguinte começa no resto
  que {name}`det` deixou.
- Um construtor de tipos com {name}`pure` e `>>=`, que obedecem a certas
  leis, é chamado de *mônada*; a notação `do` funciona para qualquer
  mônada.
- O segundo `example` mostra que `f <$> p` é o mesmo que um bloco `do`
  que aplica `p` e devolve `f` aplicada ao resultado. Ou seja, `<$>`
  pode ser escrito só com `>>=` e {name}`pure`. Por isso toda mônada é também
  um funtor.
:::

::::full
A notação `do` permite escrever a sequência anterior com um passo
por linha. Em `let td ← det`, aplicamos {name}`det` e damos o nome `td` à
árvore obtida. O próximo passo aplica {name}`n` ao resto deixado por {name}`det`.
Na última linha desse bloco `do`, `return e` tem o mesmo efeito que
`pure e`. A expressão `e` constrói o nó `NP` com as árvores `td` e `tn`.
Para cada par de árvores obtido nos passos anteriores, esse último
passo devolve o nó e mantém o resto deixado por {name}`n`. O primeiro
`example` verifica a igualdade com a versão que usa `>>=` e {name}`pure`.

Um construtor de tipos com operações {name}`pure` e `>>=` que obedecem a
certas leis é chamado de *mônada*. A notação `do` funciona para
qualquer mônada. Essas operações também permitem definir `<$>`:
aplicamos o parser e devolvemos o resultado transformado com {name}`pure`.
O segundo `example` mostra essa igualdade para parsers.
::::

```lean
example :
    (det >>= fun td =>
       n >>= fun tn =>
         pure (ParseTree.branch "NP" [td, tn])) =
    (do
      let td ← det
      let tn ← n
      return ParseTree.branch "NP" [td, tn]) := rfl

example {α β γ : Type} (f : β → γ) (p : Parser α β) :
    (f <$> p) = (do
      let r ← p
      return f r) := rfl
```

:::terse
- Para uma regra `A → B₁ ⋯ Bₙ`, os parsers de `B₁, …, Bₙ` são aplicados
  um depois do outro, como o bloco `do` de `NP` fazia para dois.
- A função `collect ps` faz isso para uma lista `ps` de parsers, todos
  com resultado do mesmo tipo `β`, e devolve a lista dos resultados:
  `Parser α (List β)`.
- A definição é recursiva na lista. Sem parsers, nada é lido e o
  resultado é `[]`. Com `p :: ps`: `let r ← p` aplica o primeiro
  parser; `let rs ← collect ps` aplica os demais ao resto que `p`
  deixou; `return r :: rs` junta os resultados.
- O `#eval` mostra que `collect [det, n]` lê as mesmas duas árvores que
  o bloco `do` de `NP`.
- A função `parseAs` faz disso um nó: `parseAs A ps` é a regra
  `A → B₁ ⋯ Bₙ`, com `ps` os parsers de `B₁, …, Bₙ`, e o nó tem rótulo `A`.
- O `example` mostra que, com um só parser, `parseAs` constrói o mesmo
  nó que {name}`det` construía com `<$>`.
:::

::::full
O lado direito de uma regra pode ter qualquer número de terminais e
não terminais. Para aplicar seus parsers em sequência, usamos
`collect ps`. A função recebe uma lista de parsers com o mesmo tipo de
resultado e constrói um parser que devolve a lista dos resultados, na
mesma ordem.

Se a lista de parsers é vazia, `pure []` produz uma análise cujo
resultado é `[]` e cujo resto é a entrada inteira. Para `p :: ps`, aplicamos `p`, aplicamos
`collect ps` ao resto e acrescentamos o primeiro resultado à lista
dos demais. Por exemplo, `collect [det, n]` produz as duas árvores
que usamos para construir o nó `NP`.

Para obter a árvore da regra inteira, usamos `parseAs`. Para uma
regra `A → B₁ ⋯ Bₙ`, passamos o rótulo de `A` e a lista dos parsers de
`B₁, …, Bₙ`. A função aplica `collect` e, com `<$>`, reúne as árvores
obtidas sob um nó com o rótulo de `A`. Com um único parser, o
`example` mostra que isso dá a mesma construção que usamos em {name}`det`.
::::

```lean
def collect {α β : Type} :
    List (Parser α β) → Parser α (List β)
  | [] => pure []
  | p :: ps => do
    let r ← p
    let rs ← collect ps
    return r :: rs

#eval (collect [det, n]).run
    ["every", "wizard", "smiled"] |>.map
  fun (ts, ys) => (ts.map toString, ys)

def parseAs {α β : Type} (label : β)
  (ps : List (Parser α (ParseTree α β)))
  : Parser α (ParseTree α β) :=
  .branch label <$> collect ps

example {α β : Type} (l : β)
    (p : Parser α (ParseTree α β)) :
    parseAs l [p] = (fun t => .branch l [t]) <$> p := by
  funext xs
  simp [parseAs, collect]
```

:::terse
- Falta a regra de `ADJS`, que diz: um ou mais `ADJ`. Na gramática,
  `ADJ "..." ADJ` é uma sequência de `ADJ`, lado a lado.
- Um ou mais, e não zero ou mais: com zero, `every wizard` casaria
  tanto com `D N` quanto com `D ADJS N`, e o parser daria duas árvores
  para um `NP` sem ambiguidade.
- O combinador `many1 p` aplica `p` uma ou mais vezes e devolve a
  lista dos resultados. Tem a forma de uma regra recursiva: `p` seguido
  de mais, ou só um `p`. Com `symbol 'a'`, a análise mais longa vem primeiro.
- O combinador `many p` acrescenta o caso de nenhuma vez: é `many1 p`
  ou `pure []`, que sempre dá certo sem ler nada.
- O `many1` chama a si mesmo sobre o resto da entrada, que fica
  escondido dentro do {name}`StateT`. O Lean não vê que esse resto é menor, e
  não aceita a definição com `def`.
- Com `partial def`, o Lean aceita a definição sem prova de terminação.
  O corpo da definição fica opaco nas provas. Podemos examinar o
  comportamento do parser executando-o sobre entradas concretas.
- A execução termina se toda chamada recursiva vem depois de consumir
  parte da entrada. Na gramática: antes do não terminal recursivo vem
  um terminal, ou um não terminal que não gera `ε`, como `ADJ` em
  `ADJS ::= ADJ ADJS`. Em `many1 p`, se `p` sempre consome algo.
:::

::::full
A regra de `ADJS` pede uma sequência de um ou mais adjetivos. Se ela
aceitasse também a sequência vazia, `every wizard` teria duas análises
como `NP`, uma pela regra `D N` e outra pela regra `D ADJS N`.

O combinador `many1 p` aplica `p` uma ou mais vezes e devolve a lista
dos resultados. A primeira alternativa aplica `p` uma vez e continua
recursivamente. A segunda aplica `p` uma única vez. Com essa ordem,
no exemplo com `symbol 'a'`, a análise mais longa aparece primeiro.
O combinador `many p` acrescenta a possibilidade de zero ocorrências,
com `pure []`.

A chamada recursiva de `many1 p` usa o resto deixado por `p`. Como
esse resto fica dentro de {name}`StateT`, o Lean não consegue verificar a
diminuição da entrada nessa definição. Com `partial def`, podemos
definir o parser sem apresentar uma prova de terminação. Nas provas,
o corpo da definição fica opaco. Podemos examinar seu comportamento
executando-o sobre entradas concretas.

Se `p` sempre consome pelo menos um símbolo quando tem sucesso, cada
chamada recursiva recebe uma lista menor. Na regra
`ADJS ::= ADJ ADJS`, por exemplo, `ADJ` consome uma palavra antes da
chamada recursiva. Se `p` puder ter sucesso deixando a entrada intacta,
`many1 p` pode voltar a chamar a si mesmo sobre a mesma lista.
::::

```lean
partial def many1 {α β : Type} (p : Parser α β) :
    Parser α (List β) :=
  (do
    let r ← p
    let rs ← many1 p
    return r :: rs)
  <|> (do
    let r ← p
    return [r])

def many {α β : Type} (p : Parser α β) :
    Parser α (List β) :=
  many1 p <|> pure []

#eval (many1 (symbol 'a')).run "aab".toList
#eval (many (symbol 'a')).run "aab".toList
#eval (many1 (symbol 'a')).run "bab".toList
#eval (many (symbol 'a')).run "bab".toList
```

:::terse
- Faltam os parsers das categorias `ADJS`, `NP` e `S`.
- O parser `adjs` lê um ou mais {name}`adj`, com {name}`many1`, e põe as árvores
  lidas, lado a lado, sob um nó `ADJS`.
- `NP` e `S` usam {name}`parseAs`. Com {name}`det`, {name}`adj`, {name}`n` e {name}`vp`, a gramática
  inteira está escrita.
:::

::::full
Já temos parsers para os terminais e para as categorias `D`, `ADJ`, `N`
e `VP`. Para completar a gramática, `adjs` aplica `many1 adj` e põe
a lista de árvores resultante sob um nó `ADJS`. O parser `np` reúne as
alternativas de `NP` com `<|>`, e `sent` usa {name}`parseAs` com a sequência
`[np, vp]`. Nos exemplos, `just sent` mantém apenas as análises da
sentença inteira.
::::

```lean
def adjs : Parser String (ParseTree String String) :=
  .branch "ADJS" <$> many1 adj

def np : Parser String (ParseTree String String) :=
  parseAs "NP" [symbolT "Alice" <|> symbolT "Dorothy"]
  <|> parseAs "NP" [det, n]
  <|> parseAs "NP" [det, adjs, n]

def sent : Parser String (ParseTree String String) :=
  parseAs "S" [np, vp]

#eval (just sent).run ["every", "wizard", "smiled"] |>.map
  (toString ·.1)
#eval (just sent).run ["Alice", "laughed"] |>.map
  (toString ·.1)
#eval (just sent).run
    ["every", "happy", "evil", "wizard", "smiled"] |>.map
  (toString ·.1)
```

::::exercise (rating := 2) (name := "adjs-recursive")
A regra de `ADJS` também pode ser escrita sem `"..."`, de forma recursiva:

```bnf
ADJS ::= ADJ ADJS | ADJ ;
```

Defina `adjsRec`, o parser dessa regra, com {name}`parseAs` e uma linha por
alternativa. As duas regras geram as mesmas sequências de adjetivos,
mas as árvores são diferentes.

```lean
partial def adjsRec :
    Parser String (ParseTree String String) :=
  solution!(
    parseAs "ADJS" [adj, adjsRec]
    <|> parseAs "ADJS" [adj])

theorem adjsRec_happy_evil :
    ((just adjsRec).run ["happy", "evil"]).map
      (toString ·.1) =
    ["[.ADJS [.ADJ happy] [.ADJS [.ADJ evil]]]"] := by
  solution!
   native_decide
```

Agora troque a última alternativa por `ε`: defina `adjsEps`, o parser
de `ADJS ::= ADJ ADJS | ε`, e `npEps`, o parser das duas alternativas
`D N | D ADJS N` de `NP` com `adjsEps` no lugar de {name}`adjs`. O último
teorema mostra o que acontece com `every wizard`.

```lean
partial def adjsEps :
    Parser String (ParseTree String String) :=
  solution!(
    parseAs "ADJS" [adj, adjsEps]
    <|> parseAs "ADJS" [])

def npEps : Parser String (ParseTree String String) :=
  solution!(
    parseAs "NP" [det, n]
    <|> parseAs "NP" [det, adjsEps, n])

theorem npEps_every_wizard :
    ((just npEps).run ["every", "wizard"]).map
      (toString ·.1) =
    ["[.NP [.D every] [.N wizard]]",
     "[.NP [.D every] [.ADJS ] [.N wizard]]"] := by
  solution!
   native_decide
```
::::

:::terse
- O método não serve para toda gramática livre de contexto. Numa regra
  recursiva à esquerda, `A → A T`, o parser de `A` chama a si mesmo sem
  ter consumido nada da entrada, e nunca para. O mesmo acontece se antes
  de `A` vêm só símbolos que podem não consumir nada.
- O parser `leftRec` abaixo é aceito, por ser `partial def`, mas `leftRec` não deve
  ser executado: cada chamada abre outra, até esgotar a pilha de recursão.
- O reconhecedor por divisão não tinha esse problema, desde que as
  divisões com pedaço vazio fossem descartadas. Cada chamada recebia
  um pedaço menor da entrada, e o Lean exigia uma prova disso.
- Há combinadores de parsers que garantem a terminação e aceitam
  recursão à esquerda; ver {citep Bib.danielsson2010}[].
:::

::::full
A descida recursiva exige cuidado com a posição da chamada recursiva.
Em uma regra como `A → A a`, o parser de `A` chama a si mesmo sobre a
mesma entrada, antes de tentar reconhecer `a`. O parser `leftRec` ilustra o problema. Cada chamada
volta a executar o mesmo parser sem consumir a entrada. Isso também
pode ocorrer se os símbolos antes da chamada recursiva aceitarem a
entrada vazia.

No reconhecedor por divisão da seção
{ref "cf-recognition"}[Reconhecendo e analisando linguagens livres de contexto],
o descarte das divisões com pedaço vazio permitia provar que as
chamadas recursivas recebiam entradas menores. Existem combinadores de
parsers que garantem a terminação e aceitam recursão à esquerda
{citep Bib.danielsson2010}[].
::::

```lean
partial def leftRec : Parser Char (ParseTree Char Char) :=
  parseAs 'A' [leftRec, symbolT 'a']
  <|> parseAs 'A' [symbolT 'b']
```

:::details "Contornando a recursão à esquerda"
Toda gramática livre de contexto pode ser reescrita sem recursão à
esquerda, sem mudar a linguagem que ela gera. A gramática de `leftRec`,
`A → A a | b`, gera as palavras formadas por um `b` seguido de zero ou
mais `a`. A mesma linguagem é gerada por `A → b A'` e `A' → a A' | ε`,
com um novo não terminal `A'`. Agora toda chamada recursiva vem depois
de consumir um `b` ou um `a`, e o parser termina. O preço é que as
árvores mudam. Para `baa`, a gramática original dá
`[.A [.A [.A b] a] a]`, uma árvore que cresce para a esquerda; a nova
dá uma árvore que cresce para a direita, com os nós `A'`. Se a forma da
árvore importa, por exemplo para a interpretação semântica, é preciso
converter uma árvore na outra.

Há também algoritmos que analisam qualquer gramática livre de contexto,
inclusive com recursão à esquerda, como CKY e Earley. Em vez de descer
pelas regras, eles guardam numa tabela as análises já encontradas para
cada trecho da entrada. A seção
{ref "parsing-further-reading"}[Leituras adicionais] traz referências.
:::

::::exercise (rating := 2) (name := "palindrome-parser")
Defina `palindrome`, um parser para a gramática dos palíndromos sobre
`{a, b, c}`, com uma linha por regra. Cada regra usada vira um nó com
rótulo `A`, inclusive `A → ε` e as regras que só têm um terminal à
direita:

```bnf
A ::= ε | a | b | c | aAa | bAb | cAc ;
```

Como o parser é recursivo, a definição é `partial def`, e os testes
abaixo são verificados executando o parser, com {tactic}`native_decide`. O
segundo mostra que, sem {lean}`just`, o parser também devolve as análises de
prefixos da entrada, com o seu resto.

```lean
partial def palindrome :
    Parser Char (ParseTree Char Char) :=
  solution!(
    parseAs 'A' []
    <|> parseAs 'A' [symbolT 'a']
    <|> parseAs 'A' [symbolT 'b']
    <|> parseAs 'A' [symbolT 'c']
    <|> parseAs 'A' [symbolT 'a', palindrome, symbolT 'a']
    <|> parseAs 'A' [symbolT 'b', palindrome, symbolT 'b']
    <|> parseAs 'A' [symbolT 'c', palindrome, symbolT 'c'])

theorem palindrome_abcba :
    ((just palindrome).run "abcba".toList).map
      (toString ·.1) = ["[.A a [.A b [.A c] b] a]"] := by
  solution!
   native_decide

theorem palindrome_aba :
    (palindrome.run "aba".toList).map
      (fun (t, ys) => (toString t, String.ofList ys)) =
    [("[.A ]", "aba"),
     ("[.A a]", "ba"),
     ("[.A a [.A b] a]", "")] := by
  solution!
   native_decide
```
::::

:::terse
- Em resumo: um terminal `t` vira `symbolT t`, um não terminal `A` vira
  `parseAs A`, a escolha vira `<|>`, e o lado direito de uma regra vira a
  lista de parsers passada a {lean}`parseAs`.
- Uma regra com um só símbolo à direita pode usar `<$>` no lugar de
  {lean}`parseAs`, e a repetição `B "..." B` vira {name}`many1`.
:::

::::full
Em resumo, usamos {name}`symbolT` para obter a folha de um terminal
`t`. Para uma regra com não terminal `A` à esquerda, usamos {lean}`parseAs`
com o rótulo de `A` e a lista de parsers dos símbolos à direita, na
ordem em que aparecem. Quando há mais de uma alternativa, reunimos
os parsers correspondentes com `<|>`. Se a regra tem um só símbolo à
direita, podemos usar `<$>` para pôr o resultado do parser desse
símbolo sob um nó rotulado com `A`, como fizemos com as categorias
cujas regras só têm terminais. Para uma repetição como `ADJ "..." ADJ`, usamos {name}`many1` para
aplicar o parser de `ADJ` uma ou mais vezes.
::::

```lean
end Parsing
```
