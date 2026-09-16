import CSwLMeta
import Bib
import Mathlib.Tactic.Use
import CSwL.Logic.PL

open Verso.Genre Manual
open CSwLMeta

set_option verso.code.warnLineLength 100

#doc (Manual) "Lógica de Primeira Ordem" =>
%%%
tag := "FOL"
file := "FOL"
%%%

```lean
namespace FOL
```

# Introdução
%%%
tag := "fol-intro"
%%%

Se usarmos lógica proposicional para formalizar a frase "Toda maçã é vermelha", teremos uma letra proposicional, um átomo indivisível que não nos permitiria capturar a idéia do quantificador e da dependencia declarada entre as _coisas_ que são maçãs e a cor destas mesmas _coisas_. A Lógica de Predicados, também chamada Lógica de Primeira Ordem (FOL, "first order logic") acrescenta os seguintes ingredientes a sintaxe de Lógica Proposicional:

* termos para representar indivíduos de um domínio. Os termos poderão ser variáveis ou funções aplicadas sobre termos;
* proposições básicas serão predicados `n`-ários sobre termos;
* fórmulas universalmente quantificadas, `∀` seguido de variável e fórmula;
* fórmulas existencialmente quantificadas, `∃` seguido de variável e fórmula.


# Sintaxe de FOL
%%%
tag := "fol-syntax"
%%%

Nossa sintaxe terá dois elementos principais, termos e fórmulas.

Os _termos_ podem ser variáveis ou funções aplicadas a outros termos. Uma constante será uma função que não recebe argumentos. As _fórmulas_ usarão os mesmos conectivos da lógica proposicional, mas acrescentaremos os quantificadores existencial e universal. Podemos escrever `¬P x`, `∀ x R x x` e `∀ x ∃ y R x (f y)`, onde `P` e `R` são símbolos predicativos e `f` é um símbolo funcional.

O nome Lógica de Primeira Ordem (FOL, "first order logic") vem da idéia de que estamos quantificando sobre indivíduous de um domínio, objetos de primeira ordem. Como fizemos em {ref "pl-syntax"}[pl-syntax], nossa sintaxe será formalizada como tipos indutivos.

Uma variável carrega nome e um índice (lista de naturais usada para gerar "novas" variáveis a partir de uma dada variável):

```lean
structure Variable where
  name : String
  index : List Nat
  deriving DecidableEq

def Variable.format : Variable → Std.Format
  | ⟨name, []⟩ => name
  | ⟨name, [i]⟩ => name ++ toString i
  | ⟨name, is⟩ =>
    name ++ String.intercalate "_" (is.map toString)

instance : Repr Variable := ⟨fun v _ => v.format⟩

def x : Variable := ⟨"x", []⟩
def y : Variable := ⟨"y", []⟩
def z : Variable := ⟨"z", []⟩
```

Termos denotam objetos do domínio, e diferentes termos podem denotar um mesmo objeto como os termos `(5 + 3) × 4`, `8 × 4` e `32`. Para representar termos mais complexos que apenas variáveis, a solução é introduzir símbolos funcionais para as operações entre termos.

```lean
inductive Term where
  | var (v : Variable)
  | struct (name : String) (args : List Term)

def Term.format : Term → Std.Format
  | .var v => repr v
  | .struct name [] => name
  | .struct name args =>
    name ++ "[" ++
      Std.Format.joinSep
        (args.map Term.format) "," ++ "]"

instance : Repr Term := ⟨fun t _ => t.format⟩

def tx : Term := .var x
def ty : Term := .var y
def tz : Term := .var z
def tf : Term := .struct "f" [tx,.struct "g" [ty]]
```

Constantes podem ser representadas como funções com aridade zero, ou seja, com a lista de argumentos vazia, {lean}`Term.struct "c" []`

:::dev "Alexandre (arademaker)"
Em Lean, indexar por aridade é mais natural do que empilhar primos: um
`structure PredSymbol` com campos `name : String` e `arity : Nat` já
representa "infinitos predicados de cada aridade finita" sem precisar
de uma família de gramáticas, uma por aridade. Fica como observação,
`Formula` (abaixo) não adota `PredSymbol`.
:::

`Formula α` é parametrizado no tipo dos termos que preenchem os predicados. Se usarmos `Formula Variable` estamos permitindo apenas fórmulas cujos termos são apenas variáveis. Se usarmos `Formula Term` temos nossa sintaxe completa.

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
```

A conjunção e a disjunção são binárias, e `top` e `bot` são construtores próprios, o mesmo que fizemos para as fórmulas proposicionais.

Importante observar que o tipo {lean}`Formula` daqui é diferente do tipo {lean}`PL.Formula`. Observamos ainda que nossa linguagem FOL está sendo implementada em Lean, que aqui funciona como meta-linguagem. Em tipos dependentes, não fazemos a distinção entre termos e fórmulas. Como vimos em {ref "IntroL"}[IntroL], em Lean toda expressão é um termo e todo termo tem um tipo. Então quando falarmos em termos, ora estamos falando do termo Lean que pode representar uma {lean}`Formula` ou {lean}`Term` de FOL.

Também como fizemos para {lean}`PL.Formula`, a notação n-ária de {name}`Formula.conj` e {name}`Formula.disj` introduzimos com as funções abaixo. Uma conjunção vazia é `top`, uma disjunção vazia é `bot`.

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

Um termo (Lean) do tipo `Formula` não é muito legível, vamos implementar a instância de `Repr` para controlar a exibição destes termos. Note que ela demanda que o tipo `α` tenha também uma instância de `Repr`, que já implementamos para {name}`Variable` e {name}`Term`.

```lean
def Formula.format {α} [Repr α] : Formula α → Std.Format
  | .atom name [] => name
  | .atom name args =>
    name ++ "[" ++
      Std.Format.joinSep (args.map (repr ·)) ", " ++ "]"
  | .eq t1 t2 => f!"{repr t1} = {repr t2}"
  | .neg f => f!"~{f.format}"
  | .impl f1 f2 =>
    f!"({f1.format} ==> {f2.format})"
  | .equi f1 f2 =>
    f!"({f1.format} <=> {f2.format})"
  | .top => "true"
  | .bot => "false"
  | .conj f1 f2 =>
    f!"({f1.format} & {f2.format})"
  | .disj f1 f2 =>
    f!"({f1.format} | {f2.format})"
  | .forall_ v f => f!"∀{repr v} {f.format}"
  | .exists_ v f => f!"∃{repr v} {f.format}"

instance {α} [Repr α] : Repr (Formula α) :=
  ⟨fun f _ => f.format⟩
```

A seguir, `formula1` expressa que o predicado `R` é reflexivo enquanto `formula2` expressa que ele é simétrico. Note que para estes dois exemplos, não precisamos usar termos envolvendo funções, logo usamos apenas {lean}`Formula Variable`.

```lean
def formula1 : Formula Variable :=
  .forall_ x (.atom "R" [x, x])

def formula2 : Formula Variable :=
  .forall_ x (.forall_ y
    (.impl (.atom "R" [x, y]) (.atom "R" [y, x])))
```

Em uma fórmula `∀x F` (ou `∃x F`), o quantificador liga toda ocorrência de
`x` em `F` que não esteja já ligada por um `∀x` (ou `∃x`) interno a `F`. Uma fórmula é *aberta* se tem ao menos uma ocorrência livre de variável, e *fechada* (também chamada *sentença*) caso contrário. Por exemplo, `(P x ∧ ∃x, R x x)` é aberta, o `x` de `P x` está fora do escopo do `∃x`. Mas `∃x (P x ∧ ∃x R x x)` é uma sentença.

Coletar as variáveis livres de uma fórmula é uma operação recorrente. Abaixo, definimos a função freeVars que recebe como parâmetro uma função que extrai as variáveis de um termo. Para {lean}`formula1`, só precisamos de uma função que transforme uma variável em uma lista com ela mesma. Para fórmulas que podem conter termos complexos, {lean}`Formula Term`, nossa função terá que percorrer todo o termo coletando as variáveis. Nos quantificadores, `filter` remove todas as ocorrências da variável ligada.

```lean
def Formula.freeVars {α} (vars : α → List Variable) :
    Formula α → List Variable
  | .atom _ args => (args.map vars).flatten
  | .eq t1 t2 => vars t1 ++ vars t2
  | .top => []
  | .bot => []
  | .neg f => f.freeVars vars
  | .impl f1 f2 => f1.freeVars vars ++ f2.freeVars vars
  | .equi f1 f2 => f1.freeVars vars ++ f2.freeVars vars
  | .conj f1 f2 => f1.freeVars vars ++ f2.freeVars vars
  | .disj f1 f2 => f1.freeVars vars ++ f2.freeVars vars
  | .forall_ v f => (f.freeVars vars).filter (· != v)
  | .exists_ v f => (f.freeVars vars).filter (· != v)
```

::::exercise (rating := 2) (name := "closed-form")
Complete o código da função `closedForm` abaixo que verifica
se uma fórmula é fechada. Aqui cada termo é uma variável, então
extrair as variáveis de um termo é devolvê-lo numa lista de um
elemento.  As fórmulas fechadas são as que têm a lista de livres vazia.

```lean
def closedForm (f : Formula Variable) : Bool :=
  solution!((f.freeVars (fun x => [x])).isEmpty)
```
::::

::::exercise (rating := 1) (name := "implication-as-abbrev")
Implicações e equivalências podem ser vistas como abreviações, pois se
definem a partir de negação, conjunção e disjunção — as mesmas
equivalências usadas na lógica proposicional. Escreva uma função `withoutIDs` que substitui cada fórmula por uma equivalente sem ocorrências de `impl` ou `equi`. Note que a função não depende do tipo `α`.

```lean
def withoutIDs {α : Type} (frm : Formula α) : Formula α :=
  solution!(
    match frm with
    | .atom name as => .atom name as
    | .eq t1 t2 => .eq t1 t2
    | .top => .top
    | .bot => .bot
    | .neg f => .neg (withoutIDs f)
    | .impl f1 f2 =>
      .disj (.neg (withoutIDs f1)) (withoutIDs f2)
    | .equi f1 f2 =>
      let g1 := withoutIDs f1
      let g2 := withoutIDs f2
      .conj (.disj (.neg g1) g2) (.disj (.neg g2) g1)
    | .conj f1 f2 =>
      .conj (withoutIDs f1) (withoutIDs f2)
    | .disj f1 f2 =>
      .disj (withoutIDs f1) (withoutIDs f2)
    | .forall_ v f => .forall_ v (withoutIDs f)
    | .exists_ v f => .exists_ v (withoutIDs f))
```
::::

::::exercise (rating := 2) (name := "negation-normal-form")
Toda fórmula de lógica de predicados pode ser transformada em uma equivalente na *forma normal da negação* (NNF, "negation normal form"), onde negações só ocorrem diante de átomos. A receita é "empurrar" as negações através dos quantificadores por `¬ ∀x F ≡  ∃x ¬F` e `¬ ∃x F ≡ ∀x ¬F`, e através de disjunções e conjunções pelas leis de De Morgan: `¬(F1 ∧ F2) ≡ ¬F1 ∨ ¬F2` e `¬(F1 ∨ F2) ≡ ¬F1 ∧ ¬F2`. Finalmente, `¬¬F ≡ F` elimina dupla negação. Complete o código da função `nnf`.

Dica: a receita acima diz o que fazer com a negação diante de alguma subfórmula. Isso sugere duas funções, uma para cada situação em que uma subfórmula pode aparecer. As duas se chamam mutuamente, e por isso vão num bloco `mutual`.

- `nnfPos f` devolve a NNF de `f`;
- `nnfNeg f` devolve a NNF de `¬f`.

Trate `impl` e `equi` diretamente nas duas funções, sem passar por
`withoutIDs`. E novamente, observe que a função não depende do tipo `α`.

```lean
mutual
def nnfPos {α} (frm : Formula α) : Formula α :=
 solution!(
  match frm with
  | .atom n as => .atom n as
  | .eq t1 t2 => .eq t1 t2
  | .top => .top
  | .bot => .bot
  | .neg f => nnfNeg f
  | .impl f1 f2 => .disj (nnfNeg f1) (nnfPos f2)
  | .equi f1 f2 =>
    .conj (.disj (nnfNeg f1) (nnfPos f2))
          (.disj (nnfNeg f2) (nnfPos f1))
  | .conj f1 f2 => .conj (nnfPos f1) (nnfPos f2)
  | .disj f1 f2 => .disj (nnfPos f1) (nnfPos f2)
  | .forall_ v f => .forall_ v (nnfPos f)
  | .exists_ v f => .exists_ v (nnfPos f))

def nnfNeg {α} (frm : Formula α) : Formula α :=
 solution!(
  match frm with
  | .atom n as => .neg (.atom n as)
  | .eq t1 t2 => .neg (.eq t1 t2)
  | .top => .bot
  | .bot => .top
  | .neg f => nnfPos f
  | .impl f1 f2 => .conj (nnfPos f1) (nnfNeg f2)
  | .equi f1 f2 =>
    .disj (.conj (nnfPos f1) (nnfNeg f2))
          (.conj (nnfPos f2) (nnfNeg f1))
  | .conj f1 f2 => .disj (nnfNeg f1) (nnfNeg f2)
  | .disj f1 f2 => .conj (nnfNeg f1) (nnfNeg f2)
  | .forall_ v f => .exists_ v (nnfNeg f)
  | .exists_ v f => .forall_ v (nnfNeg f))
end

def Formula.nnf {α : Type} (f : Formula α) : Formula α :=
  solution!(nnfPos f)
```
::::

Um termo `t` é *livre para* a variável `v` na fórmula `F` se toda ocorrência livre de `v` em `F` pode ser substituída por `t` sem que nenhuma das variáveis de `t` fique ligada. Por exemplo, `y` é livre para `x` em `Px → ∀x Px`, mas o mesmo termo não é livre para `x` em `∀y R[x,y] → ∀x R[x,x]`. Da mesma forma, `g[x,y]` não é livre para `x` em `∀y R[x,y] → ∀x R[x,x]`.

Um termo livre para uma variável `v` pode ser substituído nas ocorrências livres de `v` sem uma mudança não intencional de significado. Considere a fórmula aberta `∀y R[x,y] → ∀x R[x,x]`. Se substituirmos a ocorrência livre de `x` nessa fórmula por `y`, obtemos uma fórmula fechada `∀y R[y,y] → ∀x R[x,x]`, uma variável acabou capturada.

Se `t` não é livre para `v` em `F`, podemos sempre renomear as variáveis ligadas de `F` para garantir que a substituição de `t` por `v` em `F` tenha o significado correto. Embora `g[y,c]` não seja livre para `x` em `∀y R[x,y] → ∀x R[x,x]`, o termo é livre para `x` em `∀z R[xz] → ∀x R[x,x]`, que é uma chamada *variante alfabética* (nomes diferentes para as variáveis ligadas) da fórmula original.

A função `isVar` verifica se um termo é uma variável. As funções `varsInTerm` e `varsInTerms` retornam as variáveis que ocorrem num termo ou numa lista de termos sem duplicatas.

```lean
def isVar : Term → Bool
  | .var _ => true
  | .struct _ _ => false

mutual
def varsInTerm : Term → List Variable
  | .var v => [v]
  | .struct _ ts => varsInTerms ts

def varsInTerms (ts : List Term) : List Variable :=
  ts.map varsInTerm |>.flatten |>.eraseDups
end
```

::::exercise (rating := 1) (name := "vars-in-formula")
Implemente uma função `varsInForm : Formula Term → List Variable` que
dá a lista de variáveis que ocorrem numa fórmula. Aqui não se trata de
ocorrências *livres*: conte todas, inclusive a variável que cada
quantificador liga. Mantenha a lista sem duplicatas, como fazem
`varsInTerm` e `varsInTerms`.

```lean
def Formula.varsInForm (frm : Formula Term) : List Variable :=
  solution!(
   let tmp :=
    match frm with
    | .atom _ args => varsInTerms args
    | .eq t1 t2 => varsInTerms [t1, t2]
    | .top => []
    | .bot => []
    | .neg f => f.varsInForm
    | .impl f1 f2 => f1.varsInForm ++ f2.varsInForm
    | .equi f1 f2 => f1.varsInForm ++ f2.varsInForm
    | .conj f1 f2 => f1.varsInForm ++ f2.varsInForm
    | .disj f1 f2 => f1.varsInForm ++ f2.varsInForm
    | .forall_ v f => v :: f.varsInForm
    | .exists_ v f => v :: f.varsInForm
   tmp.eraseDups)
```
::::


::::exercise (rating := 2) (name := "free-vars-in-formula")
Implemente `freeVarsInForm : Formula Term → List Variable`, que dá a
lista de variáveis com ocorrências livres numa fórmula.

```lean
def Formula.freeVarsInForm (f : Formula Term) : List Variable :=
  solution!(f.freeVars varsInTerm)
```
::::


::::exercise (rating := 2) (name := "open-form")
Usando a função `freeVarsInForm`, complete a função `openForm`, que verifica se uma fórmula é aberta. Reaproveite as funções anteriores.

```lean
def openForm (f : Formula Term) : Bool :=
  solution!(!f.freeVarsInForm.isEmpty)
```
::::


# Semântica de FOL
%%%
tag := "fol-semantics"
%%%

Por conveniência, nos limitamos a um fragmento de língua com apenas três letras de predicado: `P` (unário), `R` (binário), e `S` (ternário).

Como deve ser uma estrutura extralinguística para as constantes `P`, `R` e `S`? Tal estrutura deve conter ao menos um domínio de discurso `D`, formado por entidades individuais, com uma interpretação para `P`, para `R` e para `S`. Essas interpretações são dadas por uma função `Interp`, que a cada nome de predicado e a cada lista de elementos do domínio associa um valor de verdade.

```lean
abbrev Interp (D : Type) := String → List D → Bool
```

Um conjunto de símbolos de relação, com suas aridades, especifica uma linguagem
de lógica de predicados `L`. Uma estrutura `M = (D, I)`, formada por um domínio
não vazio `D` com uma função de interpretação para os símbolos de relação de `L`,
é chamada de *modelo* para `L`. Sempre suporemos que o domínio de um modelo é não
vazio.

Eis um modelo concreto: dez entidades de contos de fadas, nomeadas por letras.
Nada aqui depende da escolha das letras — o que importa é que o domínio seja
finito e que cada predicado diga, de cada entidade, se vale ou não.

```lean
inductive Entity where
  | A | B | D | E | G | M | R | S | T | Y
deriving Repr, DecidableEq, BEq

def entities : List Entity :=
  [.A, .B, .D, .E, .G, .M, .R, .S, .T, .Y]
```

`S` é Branca de Neve, `A` é Alice, `D` é Dorothy, `G` é Cachinhos Dourados,
`M` é o Pequeno Mook, `Y` é Atreyu, `E` é a princesa, `B` e `R` são os anões,
e `T` é o gigante.

Os predicados unários são a pertinência a uma lista, exatamente como no
original. Os binários se dão por enumeração dos pares, ou por uma regra.

```lean
def girl     : Entity → Bool := ([Entity.S, .A, .D, .G].contains ·)
def boy      : Entity → Bool := ([Entity.M, .Y].contains ·)
def princess : Entity → Bool := ([Entity.E].contains ·)
def dwarf    : Entity → Bool := ([Entity.B, .R].contains ·)
def giant    : Entity → Bool := ([Entity.T].contains ·)
def child    : Entity → Bool := fun x => girl x || boy x

def love (x y : Entity) : Bool :=
  [(.Y, .E), (.B, .S), (.R, .S)].contains (x, y)

def defeat (x y : Entity) : Bool :=
  dwarf x && giant y
```

A função de interpretação amarra os nomes de predicado ao modelo. Nomes fora
da lista, ou usados com o número errado de argumentos, recebem `false`.

```lean
def int0 : Interp Entity
  | "Girl",     [x]    => girl x
  | "Boy",      [x]    => boy x
  | "Princess", [x]    => princess x
  | "Dwarf",    [x]    => dwarf x
  | "Giant",    [x]    => giant x
  | "Child",    [x]    => child x
  | "Love",     [x, y] => love x y
  | "Defeat",   [x, y] => defeat x y
  | _, _ => false
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
predicados. Como em {ref "PL"}[lógica proposicional], a definição *calcula*: o
resultado é um `Bool`, e o valor de uma fórmula pode ser obtido com `#eval`. As
cláusulas dos quantificadores são as que fazem a atribuição mudar: `∀v F` vale
quando `F` vale para toda escolha de valor de `v`, e `∃v F` quando vale para ao
menos uma.

Aqui aparece a diferença em relação à lógica proposicional. Para decidir um
quantificador é preciso percorrer o domínio, e percorrer exige que o domínio
esteja disponível como uma lista. Por isso `eval` recebe um argumento a mais,
`dom`, e usa `List.all` e `List.any` — as versões computáveis de `∀` e `∃`.

```lean
def Formula.eval {D : Type} [DecidableEq D]
    (dom : List D) (I : Interp D)
    (g : Assign D) : Formula Variable → Bool
  | .atom name args => I name (args.map g)
  | .eq t1 t2 => g t1 == g t2
  | .top => true
  | .bot => false
  | .neg f => !(Formula.eval dom I g f)
  | .impl f1 f2 =>
    !(Formula.eval dom I g f1) || Formula.eval dom I g f2
  | .equi f1 f2 =>
    Formula.eval dom I g f1 == Formula.eval dom I g f2
  | .conj f1 f2 =>
    Formula.eval dom I g f1 && Formula.eval dom I g f2
  | .disj f1 f2 =>
    Formula.eval dom I g f1 || Formula.eval dom I g f2
  | .forall_ v f =>
    dom.all fun d => Formula.eval dom I (g.update v d) f
  | .exists_ v f =>
    dom.any fun d => Formula.eval dom I (g.update v d) f
```

Um caso por construtor, e cada caso troca o construtor pela operação
correspondente sobre `Bool`. Se avaliamos fórmulas fechadas, isto é, sem
variáveis livres, a atribuição `g` se torna irrelevante — mas ainda é preciso
fornecer alguma.

```lean
def g0 : Assign Entity := fun _ => .S

def someDwarfDefeatsSomeGiant : Formula Variable :=
  .exists_ x (.conj (.atom "Dwarf" [x])
    (.exists_ y (.conj (.atom "Giant" [y])
                       (.atom "Defeat" [x, y]))))

def everyChildIsGirlOrBoy : Formula Variable :=
  .forall_ x (.impl (.atom "Child" [x])
    (.disj (.atom "Girl" [x]) (.atom "Boy" [x])))

def everyDwarfLovesAPrincess : Formula Variable :=
  .forall_ x (.impl (.atom "Dwarf" [x])
    (.exists_ y (.conj (.atom "Princess" [y])
                       (.atom "Love" [x, y]))))

#eval (Formula.eval entities int0 g0 someDwarfDefeatsSomeGiant,
       Formula.eval entities int0 g0 everyChildIsGirlOrBoy,
       Formula.eval entities int0 g0 everyDwarfLovesAPrincess)
```

A terceira é falsa no modelo: os anões `B` e `R` amam `S`, que é Branca de
Neve, e Branca de Neve não é a princesa. Quem ama a princesa é `Y`, que não é
anão.

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

A fórmula é uma proposta; a verificação de que ela afirma o que se queria fica
para a seção seguinte, que dá o meio de enunciar a condição de verdade
pretendida com os quantificadores do próprio Lean e exigir que as duas
coincidam.

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

# Traduzindo `Formula` para `Prop`

Como em {ref "PL"}[lógica proposicional], fechamos o capítulo ligando as duas
leituras de uma fórmula. `Formula.eval` calcula um `Bool`; `Formula.denote`
produz a proposição que a fórmula afirma. A interpretação muda junto: onde
`Interp` devolvia um `Bool`, `Denot` devolve uma `Prop`.

```lean
abbrev Denot (D : Type) := String → List D → Prop

def Formula.denote {D : Type} (I : Denot D)
    (g : Assign D) : Formula Variable → Prop
  | .atom name args => I name (args.map g)
  | .eq t1 t2 => g t1 = g t2
  | .top => True
  | .bot => False
  | .neg f => ¬ Formula.denote I g f
  | .impl f1 f2 =>
    Formula.denote I g f1 → Formula.denote I g f2
  | .equi f1 f2 =>
    Formula.denote I g f1 ↔ Formula.denote I g f2
  | .conj f1 f2 =>
    Formula.denote I g f1 ∧ Formula.denote I g f2
  | .disj f1 f2 =>
    Formula.denote I g f1 ∨ Formula.denote I g f2
  | .forall_ v f =>
    ∀ d : D, Formula.denote I (g.update v d) f
  | .exists_ v f =>
    ∃ d : D, Formula.denote I (g.update v d) f
```

Cada caso troca um construtor de `Formula` pelo conectivo correspondente de
`Prop` — o `conj` do dado vira o `∧` da proposição, e o `forall_` vira o `∀`
do próprio Lean.

Com isso podemos voltar às traduções do exercício anterior e verificá-las.
Enunciamos a condição de verdade pretendida à direita, com os quantificadores
do Lean, e exigimos que coincida com o que a fórmula proposta afirma. Como
`denote` calcula, cada teorema fecha por `Iff.rfl`.

```lean
theorem someoneWalksAndTalks_means {D : Type}
    (I : Denot D) (g : Assign D) :
    Formula.denote I g someoneWalksAndTalks ↔
      ((∃ d : D, I "Walk" [d]) ∧ (∃ d : D, I "Talk" [d])) :=
  solution!(Iff.rfl)

theorem knightFightsDragon_means {D : Type}
    (I : Denot D) (g : Assign D) :
    Formula.denote I g knightFightsDragon ↔
      (∀ a : D, ∀ b : D,
        I "Knight" [a] ∧ I "Dragon" [b] ∧ I "Finds" [a, b] →
        I "Fights" [a, b]) :=
  solution!(Iff.rfl)
```

O segundo é o que torna verificável a discussão sobre os indefinidos: a força
universal de _a knight_ e _a dragon_ não é uma opinião sobre a tradução, é o
que o `∀` do lado direito diz, e o `Iff.rfl` confirma que a fórmula proposta
diz o mesmo.

Falta o teorema que diz que as duas leituras concordam. Ele precisa de uma
hipótese que não aparecia em lógica proposicional: `eval` decide um
quantificador percorrendo `dom`, então só podemos esperar que ele concorde com
o `∀` do Lean — que fala de *todo* elemento do tipo `D` — se `dom` de fato
listar todos eles. É isso que `hdom` exige.

```lean
theorem Formula.eval_iff_denote {D : Type} [DecidableEq D]
    (dom : List D) (hdom : ∀ d : D, d ∈ dom)
    (I : Interp D) (g : Assign D) (f : Formula Variable) :
    f.eval dom I g = true ↔
      f.denote (fun n as => I n as = true) g := by
  induction f generalizing g with
  | atom name args => simp [Formula.eval, Formula.denote]
  | eq t1 t2 => simp [Formula.eval, Formula.denote]
  | top => simp [Formula.eval, Formula.denote]
  | bot => simp [Formula.eval, Formula.denote]
  | neg f ih => simp [Formula.eval, Formula.denote, ← ih]
  | impl f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ← ih1, ← ih2]
      cases Formula.eval dom I g f1 <;> simp
  | equi f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ← ih1, ← ih2]
  | conj f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ih1, ih2]
  | disj f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ih1, ih2]
  | forall_ v f ih =>
      simp [Formula.eval, Formula.denote, ih]
      exact ⟨fun h d => h d (hdom d), fun h d _ => h d⟩
  | exists_ v f ih =>
      simp [Formula.eval, Formula.denote, ih]
      exact ⟨fun ⟨d, _, h⟩ => ⟨d, h⟩,
             fun ⟨d, h⟩ => ⟨d, hdom d, h⟩⟩
```

A hipótese `hdom` é a contrapartida formal de uma limitação real: só se pode
calcular o valor de uma fórmula quantificada quando o domínio é finito e
conhecido. Para domínios infinitos, `denote` continua dizendo o que a fórmula
afirma, mas nenhum `#eval` responde.

```lean
end FOL
```
