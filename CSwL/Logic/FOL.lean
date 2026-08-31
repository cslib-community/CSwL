import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Lógica de predicados" =>
%%%
tag := "FOL"
%%%

```lean
namespace FOL
```

Frases como "Todo príncipe viu uma dama" não se relacionam em lógica
proposicional — ficariam como átomos `p`/`q` totalmente desconectados,
sem capturar que a mesma noção de "príncipe" e "viu" está em jogo nas
duas. Lógica de predicados acrescenta três ingredientes à
proposicional:

* uma proposição básica estruturada, um predicado `n`-ário seguido de
  `n` variáveis;
* uma fórmula universalmente quantificada, `∀` seguido de variável e
  fórmula;
* uma fórmula existencialmente quantificada, `∃` seguido de variável e
  fórmula.

Por isso o outro nome, "lógica de primeira ordem" — a quantificação é
sobre entidades, objetos de primeira ordem. O livro assume predicados
de aridade até 3 (relações unárias, binárias e ternárias — a última
para verbos como "dar", com sujeito, objeto e destinatário): "relações
com mais de três argumentos quase nunca são necessárias". A BNF
completa (usando primos para gerar infinitas variáveis e infinitos
predicados de cada aridade, como na lógica proposicional):

```
v    −→ x | y | z | v′
P    −→ P | P′
R    −→ R | R′
S    −→ S | S′
atom −→ P v | R v v | S v v v
F    −→ atom | (v = v) | ¬F | (F ∧ F) | (F ∨ F) | ∀v F | ∃v F
```

gerando fórmulas como `¬P′x`, `∀xRxx` ("tudo mantém a relação `R`
consigo mesmo") e `∀x∃x′Rxx′` ("para todo primeiro há algo que é
`R`-ado por ele").

# Ligação de variáveis

Numa fórmula `∀xF` (ou `∃xF`), o quantificador liga toda ocorrência de
`x` em `F` que não esteja já ligada por um `∀x`/`∃x` interno a `F`.
Uma fórmula é *aberta* se tem ao menos uma ocorrência livre de
variável, e *fechada* (também chamada *sentença*) caso contrário. Por
exemplo, `(Px ∧ ∃xRxx)` é aberta — o `x` de `Px` está fora do escopo
do `∃x` — mas `∃x(Px ∧ ∃xRxx)` é uma sentença.

Essa distinção é o que motiva a ambiguidade de escopo de _"Todo
príncipe viu uma dama"_: duas leituras, "para cada príncipe existe uma
dama (talvez diferente) que ele viu" contra "existe uma dama que todo
príncipe viu", formalizadas respectivamente como

```
∀x(Prince x → ∃y(Lady y ∧ Saw x y))
∃y(Lady y ∧ ∀x(Prince x → Saw x y))
```

— repare que a leitura universal usa `→` como conectivo principal, e
a existencial usa `∧`; vale a pena perguntar por quê — o assunto volta com a semântica. Já _"Algum príncipe viu uma dama bonita"_ não é
ambígua: `∃x∃y(Prince x ∧ Lady y ∧ Beautiful y ∧ Saw x y)`.

::::exercise (rating := 2) (name := "predicate-unique-readability")

Prove que as fórmulas desta língua têm a propriedade de leitura única.

:::solution
*Resposta.* Como no exercício correspondente da lógica proposicional:
em Lean, um termo de tipo
indutivo _é_ a árvore de análise — a prova é `injection` sobre os
construtores, não indução estrutural genuína sobre strings. Provar
leitura única para uma gramática dada como string exige mostrar que a
função string → árvore é bem definida (dá exatamente uma árvore, nunca
duas ou nenhuma); a versão Lean não tem essa função a definir, então a
"leitura única" vira a afirmação, quase vazia, de que construtores
diferentes (ou o mesmo construtor com argumentos diferentes) produzem
termos diferentes — exatamente o que `Form.noConfusion`/`injection`
dão de graça para qualquer `inductive`.
:::

::::

::::exercise (rating := 1) (name := "infinite-predicates-bnf")

Dê uma gramática BNF para uma língua de lógica de predicados com
infinitos símbolos de predicado para cada aridade finita. (Dica: use
`‴P`, `‴P′`, `‴P″`, ... para o conjunto de predicados de três lugares,
e assim por diante.)

:::solution
*Resposta.* A gramática de lógica de predicados acima, estendida com um
prefixo de primos por aridade:

```
P0 −→ P0 | P0′        (predicados de aridade 0)
P1 −→ P1 | P1′        (predicados de aridade 1)
P2 −→ P2 | P2′        (predicados de aridade 2)
P3 −→ ‴P | ‴P′         (predicados de aridade 3)
⋮
```

Em Lean, indexar por aridade é mais natural do que empilhar primos: um
`structure PredSymbol` com campos `name : String` e `arity : Nat` já
representa "infinitos predicados de cada aridade finita" sem precisar
de uma família de gramáticas, uma por aridade. Fica como observação —
`Formula` (abaixo) não adota `PredSymbol`, e limita a aridade por
construção (`atom`, `eq`, ...).
:::

::::

::::exercise (rating := 1) (name := "bound-occurrences")

Dê as ocorrências ligadas de `x` na fórmula seguinte.

```
∃x(Rxy ∨ Sxyz) ∧ Px
```

:::solution
*Resposta.* Duas: as duas ocorrências de `x` dentro do escopo do `∃x`
(em `Rxy` e em `Sxyz`). A terceira ocorrência de `x`, em `Px`, está
fora do escopo desse `∃x` — o parêntese fecha antes de `∧ Px` — e por
isso é *livre*, não ligada; a fórmula inteira é aberta. É o ponto fino
do exercício: uma mesma variável pode ter, na mesma fórmula,
ocorrências ligadas e uma ocorrência livre ao mesmo tempo, desde que
estejam em posições diferentes da árvore.
:::

::::

# Fórmulas de predicados em Lean

O "problema da aridade" (predicados de aridade 1, 2, 3, ... exigiriam
um `inductive` por aridade) se resolve como em linguagens como Prolog:
um predicado nomeado por `String`, aplicado a uma *lista* de termos —
o comprimento da lista já determina a aridade, sem precisar de um tipo
por aridade.

Uma variável carrega nome e um índice (lista de inteiros, para gerar
variáveis "frescas" a partir de uma dada — usadas quando a semântica
precisar renomear variáveis ligadas):

```lean
structure Variable where
  name : String
  index : List Nat
  deriving DecidableEq, Repr

def Variable.toStringImpl : Variable → String
  | ⟨name, []⟩ => name
  | ⟨name, [i]⟩ => name ++ toString i
  | ⟨name, is⟩ =>
    name ++ String.intercalate "_" (is.map toString)

instance : ToString Variable := ⟨Variable.toStringImpl⟩

def x : Variable := ⟨"x", []⟩
def y : Variable := ⟨"y", []⟩
def z : Variable := ⟨"z", []⟩
```

`Formula α` é parametrizado no tipo dos termos que preenchem os
predicados — por ora `α := Variable` (a seção sobre símbolos de função,
adiante, introduz `Term`, estruturado, e reaproveita `Formula` trocando o
parâmetro).

```lean
inductive Formula (α : Type) where
  | atom (name : String) (args : List α)
  | eq (t1 t2 : α)
  | neg (f : Formula α)
  | impl (f1 f2 : Formula α)
  | equi (f1 f2 : Formula α)
  | conj (fs : List (Formula α))
  | disj (fs : List (Formula α))
  | forall_ (v : Variable) (f : Formula α)
  | exists_ (v : Variable) (f : Formula α)
```

Por que `Formula` toma lista de fórmulas (`conj`/`disj`), diferente do
`Form` binário de {ref "PL"}[Lógica proposicional]? Porque a conjunção/disjunção vazia — `conj []`
como `"true"`, `disj []` como `"false"` — é a motivação para tomar
lista desde o início, não uma escolha de implementação a evitar.
`Form` binário funciona bem porque a lógica proposicional nunca precisa
de conjunções de tamanho variável; aqui, a conjunção/disjunção vazia como valor sensato
(ver `toStringImpl` abaixo, e a semântica adiante) depende da
lista vazia existir.

Diferente do fragmento de inglês, adiante — onde `NP`/`VP`/`RCN`/`INF`/
`Sent` são *mutuamente recursivos*, mas nenhum toma lista de si
mesmo, e por isso mantêm `induction` funcionando — `Formula` é
_nested_: a lista `List (Formula α)` dentro do próprio tipo tira
tanto `deriving DecidableEq` quanto `induction` automática. É a mesma
restrição que levou `Form` a ser binário lá; aqui a lista é
essencial, então o custo se paga, e as funções abaixo são recursão
explícita.

`ToString` — inclusive a escolha de mostrar `conj []` como `"true"` e
`disj []` como `"false"` (a razão fica clara na semântica, adiante:
são a base neutra de `∧`/`∨`, e como constantes independem de
qualquer atribuição de valores aos átomos):

```lean
def Formula.toStringImpl [ToString α] : Formula α → String
  | .atom name [] => name
  | .atom name args =>
    name ++ "[" ++
      String.intercalate "," (args.map toString) ++ "]"
  | .eq t1 t2 => s!"{t1}={t2}"
  | .neg f => s!"~{f.toStringImpl}"
  | .impl f1 f2 =>
    s!"({f1.toStringImpl}==>{f2.toStringImpl})"
  | .equi f1 f2 =>
    s!"({f1.toStringImpl}<=>{f2.toStringImpl})"
  | .conj [] => "true"
  | .conj fs =>
    "(" ++
      String.intercalate " & "
        (fs.map Formula.toStringImpl) ++ ")"
  | .disj [] => "false"
  | .disj fs =>
    "(" ++
      String.intercalate " | "
        (fs.map Formula.toStringImpl) ++ ")"
  | .forall_ v f => s!"A{v} {f.toStringImpl}"
  | .exists_ v f => s!"E{v} {f.toStringImpl}"

instance [ToString α] : ToString (Formula α) :=
  ⟨Formula.toStringImpl⟩

def formula0 : Formula Variable := .atom "R" [x, y]
```

A instância acima recebe outra entre colchetes: para imprimir uma
`Formula α` é preciso saber imprimir os `α` que a preenchem, e o
`[ToString α]` é essa exigência. Uma instância pode assim depender de
outras, e o Lean encadeia a busca — dado `ToString Variable`, ele monta
sozinho `ToString (Formula Variable)`.

```lean (name := c4eval7)
#eval toString formula0
```

```leanOutput c4eval7
"R[x,y]"
```

```lean
def formula1 : Formula Variable :=
  .forall_ x (.atom "R" [x, x])
```

```lean (name := c4eval8)
#eval toString formula1
```

```leanOutput c4eval8
"Ax R[x,x]"
```

reflexividade de R

```lean
def formula2 : Formula Variable :=
  .forall_ x (.forall_ y
    (.impl (.atom "R" [x, y]) (.atom "R" [y, x])))
```

```lean (name := c4eval9)
#eval toString formula2
```

```leanOutput c4eval9
"Ax Ay (R[x,y]==>R[y,x])"
```

simetria de R

::::exercise (rating := 2) (name := "closed-form")

Escreva uma função `closedForm : Formula Variable → Bool` que verifica
se uma fórmula é fechada. Comece por uma função que coleta a lista de
variáveis livres de uma fórmula: as fechadas são as que têm essa lista
vazia.

```lean
def freeVarsInFormula : Formula Variable → List Variable :=
  sorry

def closedForm (f : Formula Variable) : Bool :=
  solution!((freeVarsInFormula f).isEmpty)
```

::::

::::exercise (rating := 1) (name := "implication-as-abbrev")

Implicações e equivalências podem ser vistas como abreviações, pois se
definem a partir de negação e conjunção. Escreva uma função
`withoutIDs : Formula Variable → Formula Variable` que substitui cada
fórmula por uma equivalente sem ocorrências de `impl` ou `equi`.

```lean
def withoutIDs : Formula Variable → Formula Variable :=
  sorry
```

::::

::::exercise (rating := 2) (name := "negation-normal-form")

Toda fórmula de lógica de predicados é equivalente a uma fórmula em
*forma normal negativa*, onde negações só ocorrem diante de átomos. A
receita é "empurrar" as negações através dos quantificadores por
`¬∀xF ≡ ∃x¬F` e `¬∃xF ≡ ∀x¬F`, e através de disjunções e conjunções
pelas leis de De Morgan: `¬(F1 ∧ F2) ≡ ¬F1 ∨ ¬F2` e `¬(F1 ∨ F2) ≡ ¬F1
∧ ¬F2`. `¬¬F ≡ F` elimina dupla negação. Escreva uma função `nnf :
Formula Variable → Formula Variable` que transforma uma fórmula em
forma normal negativa. (Dica: use a função do exercício anterior para
eliminar `impl`/`equi` primeiro.)

*Cuidado ao implementar* (dica de verdade, não parte da nota de
rodapé): uma função `nnf`/`nnfNeg` mutuamente recursivas, com `nnfNeg`
chamando `nnfNeg (withoutIDs ...)` nos casos de `impl`/`equi`, não
termina por recursão estrutural — o Lean não consegue provar que
`withoutIDs f` é "menor" que `f` (em geral não é: `withoutIDs` pode
crescer o termo). Aplicar `withoutIDs` uma única vez, no início,
resolve — mas então as funções internas ainda precisam cobrir os
casos `impl`/`equi`, mesmo que nunca sejam de fato alcançados depois
desse passo.

```lean
def nnf : Formula Variable → Formula Variable := sorry
```

::::

# Símbolos de função

Lógica de predicados, como definida até aqui, não expressa equações
de aritmética escolar: um termo como `(5 + 3) × 4` é complexo, não uma
variável isolada. A solução é introduzir *constantes de função* para
operações arbitrárias — o mesmo movimento de nomear relações binárias
arbitrárias em vez de fixar "menor que" como primitivo.

Termos complexos, com símbolo de função e lista de argumentos — outro
`inductive` nested (a lista de `Term` dentro do próprio `Term`), então
sem `deriving DecidableEq`/`induction`, como `Form` teria sido se a
gramática da lógica proposicional não fosse binária:

```lean
inductive Term where
  | var (v : Variable)
  | struct (name : String) (args : List Term)

def Term.toStringImpl : Term → String
  | .var v => toString v
  | .struct name [] => name
  | .struct name args =>
    name ++ "[" ++
      String.intercalate ","
        (args.map Term.toStringImpl) ++ "]"

instance : ToString Term := ⟨Term.toStringImpl⟩

def tx : Term := .var x
def ty : Term := .var y
def tz : Term := .var z
```

Um termo *livre para* uma variável `v` numa fórmula `F` é um termo
que, substituído em toda ocorrência livre de `v` em `F`, não tem
nenhuma de suas próprias variáveis capturada por um quantificador de
`F`. Substituir sem essa cautela muda o significado: em `(∀yRxy →
∀xRxx)`, o `x` livre da premissa, substituído por `y`, produz
`(∀yRyy → ∀xRxx)` — o `y` do termo foi capturado pelo `∀y` que já
estava lá. Uma *variante alfabética* (a mesma fórmula, só renomeando
variáveis ligadas — aqui, `(∀zRxz → ∀xRxx)`) evita a captura.

Com `Term`, `Formula Term` são fórmulas com termos estruturados — o
semântica, daqui em diante, usa esse `Formula Term`, não mais `Formula
Variable`.

```lean
def isVar : Term → Bool
  | .var _ => true
  | .struct _ _ => false

mutual
def varsInTerm : Term → List Variable
  | .var v => [v]
  | .struct _ ts => varsInTerms ts

def varsInTerms : List Term → List Variable
  | [] => []
  | t :: ts => varsInTerm t ++ varsInTerms ts
end
```

O bloco `mutual` aparece aqui pela primeira vez. Ele agrupa definições
que se chamam umas às outras: `varsInTerm` chama `varsInTerms` na
segunda linha, e `varsInTerms` chama `varsInTerm` na sua. Definidas
separadamente, a primeira mencionaria um nome que ainda não existe.
Dentro de um `mutual`, o Lean elabora as duas ao mesmo tempo e verifica
juntas a terminação — a recursão diminui o termo a cada volta, mesmo
alternando entre as duas funções.

A necessidade vem da forma do dado: um `Term` carrega uma `List Term`,
então percorrer um termo é percorrer uma lista de termos, e vice-versa.
Onde os tipos se referem uns aos outros, as funções sobre eles também
se referem — e no fragmento de inglês, mais adiante no livro, gramáticas
inteiras serão declaradas assim.

::::exercise (rating := 1) (name := "term-parse-tree")

Dê uma árvore de análise para o termo `f″[f′[x, y], f‴[z, z, f[x]]]`.

:::solution
*Resposta.* A árvore _é_ o termo Lean correspondente — sem passo de
tradução a fazer:

```lean
def ex421Term : Term :=
  .struct "f2" [ .struct "f1" [tx, ty]
               , .struct "f3" [tz, tz, .struct "f" [tx]] ]
```

```lean (name := c4eval10)
#eval toString ex421Term
```

```leanOutput c4eval10
"f2[f1[x,y],f3[z,z,f[x]]]"
```

```
f2
├── f1
│   ├── x
│   └── y
└── f3
    ├── z
    ├── z
    └── f
        └── x
```
:::

::::

::::exercise (rating := 1) (name := "vars-in-formula")

Implemente uma função `varsInForm : Formula Term → List Variable` que
dá a lista de variáveis que ocorrem numa fórmula.

```lean
def varsInForm : Formula Term → List Variable := sorry
```

::::

::::exercise (rating := 2) (name := "open-form")

Implemente `freeVarsInForm : Formula Term → List Variable`, que dá a
lista de variáveis com ocorrências livres numa fórmula, e sobre ela
`openForm : Formula Term → Bool`, que verifica se uma fórmula é aberta
(ver a seção sobre ligação de variáveis).

```lean
def freeVarsInForm : Formula Term → List Variable := sorry

def openForm (f : Formula Term) : Bool :=
  solution!(!(freeVarsInForm f).isEmpty)
```

::::

```lean
end FOL
```
