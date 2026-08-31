import CSwLMeta
import Bib
import Mathlib.Tactic.Use

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

```bnf
v    ::= "x" | "y" | "z" | v "′" ;
P    ::= "P" | P "′" ;
R    ::= "R" | R "′" ;
S    ::= "S" | S "′" ;
atom ::= P v | R v v | S v v v ;
F    ::= atom
  | "(" v "=" v ")" ("identidade")
  | "¬" F ("negação")
  | "(" F "∧" F ")" ("conjunção")
  | "(" F "∨" F ")" ("disjunção")
  | "∀" v F ("quantificação universal")
  | "∃" v F ("quantificação existencial") ;
```

gerando fórmulas como `¬P′x`, `∀xRxx` ("tudo mantém a relação `R`
consigo mesmo") e `∀x∃x′Rxx′` ("para todo primeiro há algo que é
`R`-ado por ele").

# As regras dos quantificadores

Como no capítulo proposicional, duas leituras convivem aqui: os quantificadores
do próprio Lean, com que se enuncia e demonstra, e as fórmulas como dado, que é o
que `Formula` será. Esta seção é sobre os primeiros, e são duas regras novas —
uma para cada quantificador. O domínio dos exemplos é um tipo de três elementos,
`Node`, que a seção sobre semântica retoma como domínio de um modelo.

```lean
inductive Node where
  | one | two | three
  deriving DecidableEq, Repr
```

A introdução de `∀` diz: para provar que algo vale de todo `x`, tome um `x`
arbitrário e prove que vale dele. É `intro` de novo, agora sobre um objeto em vez
de uma hipótese.

```lean
example (P : Node → Prop) (h : ∀ x, P x) : ∀ y, P y := by
  intro y
  exact h y
```

A eliminação de `∀` é aplicação: de `∀x P x` e de um objeto `d`, sai `P d`. É o
`h y` da prova acima.

A introdução de `∃` exige exibir a testemunha. A tática `use` faz isso — ela
substitui a variável quantificada pelo objeto que se oferece, e deixa como
objetivo o que falta provar sobre ele.

```lean
example : ∃ x : Node, x = Node.two := by
  use Node.two
```

A eliminação de `∃` é a mais delicada, e pelo mesmo motivo que a de `∨`: de
`∃x P x` sabe-se que há uma testemunha, mas não qual. A tática `obtain` a
introduz com um nome, junto com a propriedade que ela satisfaz.

```lean
example (P Q : Node → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨d, hP, hQ⟩ := h
  exact ⟨d, hQ⟩
```

Com as duas regras, a validade que a seção anterior enunciou — que de `∀xF` segue
`∃xF` quando o domínio é não vazio — pode ser demonstrada, e não apenas afirmada.
A não vacuidade do domínio entra como a hipótese `d : Node`, isto é, como a
exibição de um habitante.

```lean
example (P : Node → Prop) (d : Node)
    (h : ∀ x, P x) : ∃ x, P x :=
  ⟨d, h d⟩
```

Repare que num domínio vazio a prova não existiria: não há testemunha a oferecer.
É a mesma exigência que o modelo faz, agora visível no tipo.

::::exercise (rating := 2) (name := "forall-exists-swap")

Uma das duas direções vale, a outra não. Prove a que vale.

```lean
example (R : Node → Node → Prop) (h : ∃ y, ∀ x, R x y) :
    ∀ x, ∃ y, R x y := solution!(by
  obtain ⟨d, hd⟩ := h
  intro x
  exact ⟨d, hd x⟩)
```

:::solution
A volta não vale. De `∀x∃yRxy` cada `x` pode ter a sua testemunha, e nada obriga
que seja a mesma para todos; é o mesmo contraexemplo do exercício anterior, com
`R` relacionando cada objeto apenas a si mesmo.
:::

::::

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

```bnf
P0 ::= "P0" | P0 "′" ("predicados de aridade 0") ;
P1 ::= "P1" | P1 "′" ("predicados de aridade 1") ;
P2 ::= "P2" | P2 "′" ("predicados de aridade 2") ;
P3 ::= "P3" | P3 "′" ("predicados de aridade 3") ;
```

e assim por diante, uma produção por aridade.

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
  | top
  | bot
  | neg (f : Formula α)
  | impl (f1 f2 : Formula α)
  | equi (f1 f2 : Formula α)
  | conj (f1 f2 : Formula α)
  | disj (f1 f2 : Formula α)
  | forall_ (v : Variable) (f : Formula α)
  | exists_ (v : Variable) (f : Formula α)
  deriving Repr
```

A conjunção e a disjunção são binárias, e `top` e `bot` são construtores
próprios — o mesmo desenho do tipo das fórmulas proposicionais, pelo mesmo
motivo: um construtor que guardasse uma lista de fórmulas dentro do próprio tipo
o tornaria um indutivo _nested_, e com isso se perderiam `induction` e
`deriving`. O `α` em `atom name (args : List α)` não cria esse problema, porque é
parâmetro, não o próprio tipo.

A notação n-ária se recupera com duas funções, como lá: uma conjunção vazia é
`top`, uma disjunção vazia é `bot`.

```lean
def Formula.conjs {α : Type} : List (Formula α) → Formula α
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Formula.conjs fs)

def Formula.disjs {α : Type} : List (Formula α) → Formula α
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Formula.disjs fs)
```

E a instância de `ToString`:

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
  | .top => "true"
  | .bot => "false"
  | .conj f1 f2 =>
    s!"({f1.toStringImpl}&{f2.toStringImpl})"
  | .disj f1 f2 =>
    s!"({f1.toStringImpl}|{f2.toStringImpl})"
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
def structuredTerm : Term :=
  .struct "f2" [ .struct "f1" [tx, ty]
               , .struct "f3" [tz, tz, .struct "f" [tx]] ]
```

```lean (name := c4eval10)
#eval toString structuredTerm
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

# Semântica da lógica de predicados

A semântica da lógica de predicados é estática de novo. Por conveniência, nos
limitamos a um fragmento de língua com apenas três letras de predicado: `P`, de
um lugar, `R`, de dois, e `S`, de três.

Como deve ser uma estrutura extralinguística para as constantes `P`, `R` e `S`?
Tal estrutura deve conter ao menos um domínio de discurso `D`, formado por
entidades individuais, com uma interpretação para `P`, para `R` e para `S`. Essas
interpretações são dadas por uma função `I`, que a cada nome de predicado e a
cada lista de elementos do domínio associa a afirmação de que a relação vale
entre eles.

```lean
abbrev Interp (D : Type) := String → List D → Prop
```

Um conjunto de símbolos de relação, com suas aridades, especifica uma linguagem
de lógica de predicados `L`. Uma estrutura `M = (D, I)`, formada por um domínio
não vazio `D` com uma função de interpretação para os símbolos de relação de `L`,
é chamada de *modelo* para `L`. Sempre suporemos que o domínio de um modelo é não
vazio.

Eis um modelo concreto, com domínio de três elementos. `P` vale de `1` e de `3`;
`R` relaciona `1` a `1` e a `2`, `2` a `2`, e `3` a `1` e a `2`.

```lean
def M : Interp Node
  | "P", [d] => d = .one ∨ d = .three
  | "R", [d, e] =>
      (d = .one ∧ (e = .one ∨ e = .two))
      ∨ (d = .two ∧ e = .two)
      ∨ (d = .three ∧ (e = .one ∨ e = .two))
  | _, _ => False
```

Dada uma estrutura com função de interpretação `M = (D, I)`, podemos definir uma
valoração para as fórmulas da lógica de predicados, desde que saibamos lidar com
os valores das variáveis individuais. Seja `V` o conjunto das variáveis da
linguagem. Uma função `g : V → D` é chamada de *atribuição de variáveis*, ou
valoração.

Escrevemos `g[v := d]` para a valoração que é como `g` exceto pelo fato de que
`v` recebe o valor `d` — onde `g` poderia ter atribuído um valor diferente.

```lean
def Assign (D : Type) := Variable → D

def Assign.update {D : Type} (g : Assign D)
    (v : Variable) (d : D) : Assign D :=
  fun w => if w = v then d else g w
```

Seja `M` um modelo para a linguagem `L`, seja `g` uma atribuição de variáveis
para `L` em `M`, e seja `F` uma fórmula de `L`. Estamos prontos para definir a
noção `M ⊨ᵍ F`, "F é verdadeira em M sob a atribuição g", ou: "g satisfaz F no
modelo M".

O que segue é uma definição recursiva de verdade para as fórmulas da lógica de
predicados. As cláusulas dos quantificadores são as que fazem a atribuição mudar:
`∀v F` vale quando `F` vale para toda escolha de valor de `v`, e `∃v F` quando
vale para ao menos uma.

```lean
def Formula.holds {D : Type} (I : Interp D)
    (g : Assign D) : Formula Variable → Prop
  | .atom name args => I name (args.map g)
  | .eq t1 t2 => g t1 = g t2
  | .top => True
  | .bot => False
  | .neg f => ¬ Formula.holds I g f
  | .impl f1 f2 =>
      Formula.holds I g f1 → Formula.holds I g f2
  | .equi f1 f2 =>
      Formula.holds I g f1 ↔ Formula.holds I g f2
  | .conj f1 f2 =>
      Formula.holds I g f1 ∧ Formula.holds I g f2
  | .disj f1 f2 =>
      Formula.holds I g f1 ∨ Formula.holds I g f2
  | .forall_ v f =>
      ∀ d : D, Formula.holds I (g.update v d) f
  | .exists_ v f =>
      ∃ d : D, Formula.holds I (g.update v d) f
```

Um caso por construtor, e cada caso troca o construtor pelo conectivo
correspondente do Lean — a mesma correspondência que o capítulo proposicional
enuncia como ponte entre as duas leituras.

Se avaliamos fórmulas fechadas, isto é, sem variáveis livres, a atribuição `g` se
torna irrelevante.

A definição de verdade faz uso essencial das atribuições e, ainda assim, nos
exercícios em que se olha apenas para fórmulas fechadas, a verdade ou a falsidade
não depende de qual atribuição se use. Poder-se-ia pensar, portanto, que é
possível dispensar as atribuições por completo, contanto que nos limitemos a
definir os valores de verdade das fórmulas fechadas da lógica de predicados.

O problema é que, ao aplicar a definição de verdade acima a uma sentença, por
exemplo a `∀x(Px → ∃yRxy)`, a cláusula que trata do quantificador universal faz
referência à noção de verdade para a fórmula `(Px → ∃yRxy)`, que é uma fórmula
aberta. Para determinar se ela é verdadeira temos de saber que objeto `x` denota.
A situação é inteiramente análoga à interpretação de sentenças de língua natural:

```
Todo mestre tem um aprendiz.
Ele tem um aprendiz.
```

Para determinar a verdade da segunda temos de saber quem é o referente do pronome
_ele_.

Uma sentença da lógica de predicados é *logicamente válida* se é verdadeira em
todo modelo; a notação é `⊨ F`. Da convenção de que os domínios de nossos modelos
são sempre não vazios segue que `⊨ ∀xF → ∃xF`, para toda `F` com no máximo a
variável `x` livre.

Uma sentença `C` *se segue logicamente* de uma sentença `P` (`P` de premissa, `C`
de conclusão; dizemos também que `P` implica logicamente `C`) se todo modelo que
torna `P` verdadeira também torna `C` verdadeira. A notação é `P ⊨ C`.

Como julgar afirmações da forma `P ⊨ C`? É claro como podemos refutá-la: achando
um contraexemplo. Um contraexemplo a `P ⊨ C` é um modelo `M` com `M ⊨ P` mas não
`M ⊨ C`.

::::exercise (rating := 2) (name := "quantifier-strength")

Mostre que `∀x(Ax ∧ Bx)` significa algo mais forte que "todo A é B", e que
`∃x(Ax → Bx)` significa algo mais fraco que "algum A é B".

:::solution
`∀x(Ax ∧ Bx)` diz que tudo no domínio é A e é B — não apenas que os A são B. Ela
é falsa em qualquer modelo que tenha um objeto fora de A, mesmo que todos os A
sejam B. A tradução correta de "todo A é B" é `∀x(Ax → Bx)`.

`∃x(Ax → Bx)` é verdadeira assim que houver um objeto que não seja A, porque a
implicação vale vacuamente para ele. Ela não afirma que existe um A que é B; a
tradução correta de "algum A é B" é `∃x(Ax ∧ Bx)`.
:::

::::

::::exercise (rating := 2) (name := "translate-quantified")

Traduza as sentenças a seguir para lógica de predicados, garantindo que as
condições de verdade sejam capturadas.

1. _Someone walks and someone talks._
2. _No wizard cast a spell or mixed a potion._
3. _Every ballad that is sung by a princess is beautiful._
4. _If a knight finds a dragon, he fights it._

```lean
def someoneWalksAndTalks : Formula Variable :=
  solution!(.conj
    (.exists_ x (.atom "Walk" [x]))
    (.exists_ y (.atom "Talk" [y])))

def noWizardCastOrMixed : Formula Variable :=
  solution!(.forall_ x
    (.impl (.atom "Wizard" [x])
      (.neg (.disj (.atom "CastSpell" [x])
                   (.atom "MixedPotion" [x])))))

def everyBalladBeautiful : Formula Variable :=
  solution!(.forall_ x
    (.impl
      (.conj (.atom "Ballad" [x])
        (.exists_ y (.conj (.atom "Princess" [y])
                           (.atom "Sung" [y, x]))))
      (.atom "Beautiful" [x])))

def knightFightsDragon : Formula Variable :=
  solution!(.forall_ x (.forall_ y
    (.impl
      (.conj (.atom "Knight" [x])
        (.conj (.atom "Dragon" [y])
               (.atom "Finds" [x, y])))
      (.atom "Fights" [x, y]))))
```

A fórmula é uma proposta; a verificação é mostrar que ela afirma o que se
queria. `Formula.holds` leva uma fórmula à proposição que ela afirma, dada uma
interpretação, então basta enunciar a condição de verdade pretendida com os
quantificadores do próprio Lean e exigir que as duas coincidam. Como `holds`
calcula, cada teorema fecha por `Iff.rfl`.

```lean
theorem someoneWalksAndTalks_means {D : Type}
    (I : Interp D) (g : Assign D) :
    Formula.holds I g someoneWalksAndTalks ↔
      ((∃ d : D, I "Walk" [d]) ∧ (∃ d : D, I "Talk" [d])) :=
  solution!(Iff.rfl)

theorem knightFightsDragon_means {D : Type}
    (I : Interp D) (g : Assign D) :
    Formula.holds I g knightFightsDragon ↔
      (∀ a : D, ∀ b : D,
        I "Knight" [a] ∧ I "Dragon" [b] ∧ I "Finds" [a, b] →
        I "Fights" [a, b]) :=
  solution!(Iff.rfl)
```

O segundo é o que torna a discussão abaixo verificável: a força universal dos
indefinidos não é uma opinião sobre a tradução, é o que o `∀` do lado direito
diz, e o `Iff.rfl` confirma que a fórmula proposta diz o mesmo.

:::solution
As duas primeiras são diretas, mas repare no escopo da negação em (2): _no
wizard cast a spell or mixed a potion_ nega a disjunção inteira, não cada
disjunto separadamente. Escrever `∀x(Wizard x → (¬CastSpell x ∨ ¬MixedPotion
x))` afirmaria algo mais fraco — que nenhum mago fez as duas coisas.

A terceira mostra por que a cláusula relativa entra como conjunto na
antecedente: _every ballad that is sung by a princess_ restringe o domínio da
quantificação, e a restrição é `Ballad x ∧ ∃y(Princess y ∧ Sung y x)`.

A quarta é a mais instrutiva. Os artigos indefinidos de _a knight_ e _a dragon_
parecem pedir `∃`, mas dentro do antecedente de uma condicional eles ganham
força universal: a sentença diz que *todo* par cavaleiro-dragão que se encontra
luta. Traduzir com `∃` daria `∃x∃y(Knight x ∧ Dragon y ∧ Finds x y → Fights x
y)`, que é quase trivialmente verdadeira — basta haver um par que não se
encontra. E os pronomes _he_ e _it_ retomam justamente as variáveis ligadas
pelos quantificadores, que é o que permite a tradução funcionar.
:::

::::

::::exercise (rating := 2) (name := "valid-consequence")

Quais das afirmações seguintes valem? Se uma vale, explique por quê; se não,
dê um contraexemplo.

1. `∀xPx ⊨ ∃xPx`
2. `∃x∃yRxy ⊨ ∃xRxx`
3. `∃y∀xRxy ⊨ ∀x∃yRxy`

:::solution
1. Vale, e é aqui que a exigência de domínio não vazio faz trabalho: tomando
   qualquer `d` do domínio, de `∀xPx` sai `Pd`, que testemunha `∃xPx`. Num
   domínio vazio a premissa seria vacuamente verdadeira e a conclusão falsa.
2. Não vale. Contraexemplo: domínio `{1, 2}` com `R` valendo apenas de `1` para
   `2`. A premissa é verdadeira, e nenhum objeto se relaciona consigo mesmo.
3. Vale. Se há um `d` tal que todo `x` se relaciona com `d`, então para cada `x`
   esse mesmo `d` testemunha `∃yRxy`.
:::

::::

```lean
end FOL
```
