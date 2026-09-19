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

O nome Lógica de Primeira Ordem vem da idéia de que estamos quantificando sobre indivíduous de um domínio, objetos de primeira ordem. Como fizemos em {ref "pl-syntax"}[pl-syntax], nossa sintaxe será formalizada como tipos indutivos.

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
def tf : Term := .struct "f" [tx, .struct "g" [ty]]
```

Constantes podem ser representadas como funções com aridade zero, ou seja, com a lista de argumentos vazia, {lean}`Term.struct "c" []`

:::dev "Alexandre (arademaker)"
Nada proible que um mesmo símbolo seja usado com aridades diferentes dentro de uma mesma fórmula. Poderiamos definir uma estrututa PredSymbol com campos nome e aridade (natural).
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
  | .top => "⊤"
  | .bot => "⊥"
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

::::exercise (rating := 2) (name := "ex-fol-translate")
Considere a linguagem de primeira ordem com o vocabulário definido pelos símbolos abaixo.

- `R(x,y)` - `x` respeita `y`
- `M(x,y)` – `x` esta matriculado na disciplina `y`
- `P(x)` – x é um professor
- `A(x)` – `x` é um aluno
- `D(x)` – `x` é uma disciplina
- `Maria` - uma constante denotando a pessoa chamada Maria.

Vamos traduzir cada uma das sentenças a seguir para fórmulas em lógica de primeira ordem.

- (a) Maria respeita todos os professores.
- (b) Alguns professores respeitam Maria.
- (c) Maria respeita a si própria
- (d) Nenhum aluno esta matriculado em todas as disciplina
- (e) Não há disciplinas em que todos os alunos estejam nela matriculados
- (f) Não há disciplinas sem alunos matriculados

```lean
namespace ExSchool
def R (tx ty : Term) : Formula Term := .atom "R" [tx, ty]
def M (tx ty : Term) : Formula Term := .atom "M" [tx, ty]

def P (tx : Term) : Formula Term := .atom "P" [tx]
def A (tx : Term) : Formula Term := .atom "A" [tx]
def D (tx : Term) : Formula Term := .atom "D" [tx]

def Maria : Term := .struct "Maria" []

def Fa : Formula Term :=
  solution!( .forall_ x (.impl (P tx) (R Maria tx)) )

def Fb : Formula Term :=
  solution!( .exists_ x (.conj (P tx) (R tx Maria)) )

def Fc : Formula Term :=
  solution!(R Maria Maria)

def Fd : Formula Term :=
  solution!(
   .neg (.exists_ x (.conj (A tx)
    (.forall_ y (.impl (D ty) (M tx ty))))) )

def Fe : Formula Term :=
  solution!(
   .neg (.exists_ x (.conj (D tx)
    (.forall_ y (.impl (A ty) (M ty tx))))) )

def Ff : Formula Term :=
  solution!(
     .neg (.exists_ x (.conj (D tx)
      (.neg (.exists_ y (.conj (A ty) (M ty tx)))))) )

end ExSchool
```
::::


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

:::exercise (rating := 1) (name := "ex-fol-freevars")
Complete o enunciado do exemplo com o termo que torna possível provar o exemplo apenas usando a tática {tactic}`native_decide`.

```lean
def F : Formula Variable :=
  .exists_ x
    (.conj (.disj (.atom "R" [x, y]) (.atom "S" [x, y, z]))
           (.atom "P" [x]))

example : F.freeVars (fun x => [x]) = solution!([y, y, z]) :=
  solution!(by native_decide)
```
:::

:::exercise (rating := 1) (name := "ex-fol-closedform")
Complete o código da função `closedForm` abaixo que verifica
se uma fórmula é fechada. Aqui cada termo é uma variável, então
extrair as variáveis de um termo é devolvê-lo numa lista de um
elemento.  As fórmulas fechadas são as que têm a lista de livres vazia.

```lean
def closedForm (f : Formula Variable) : Bool :=
  solution!((f.freeVars (fun x => [x])).isEmpty)
```
:::

:::exercise (rating := 1) (name := "ex-fol-remove-impl_equiv")
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
:::

:::exercise (rating := 2) (name := "ex-fol-nnf")
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
:::

Um termo `t` é *livre para* a variável `v` na fórmula `F` se toda ocorrência livre de `v` em `F` pode ser substituída por `t` sem que nenhuma das variáveis de `t` fique ligada. Por exemplo, `y` é livre para `x` em `Px → ∀x Px`, mas o mesmo termo não é livre para `x` em `∀y R[x,y] → ∀x R[x,x]`. Da mesma forma, `g[x,y]` não é livre para `x` em `∀y R[x,y] → ∀x R[x,x]`.

Um termo livre para uma variável `v` pode ser substituído nas ocorrências livres de `v` sem uma mudança não intencional de significado. Considere a fórmula aberta `∀y R[x,y] → ∀x R[x,x]`. Se substituirmos a ocorrência livre de `x` nessa fórmula por `y`, obtemos uma fórmula fechada `∀y R[y,y] → ∀x R[x,x]`, uma variável acabou capturada.

Se `t` não é livre para `v` em `F`, podemos sempre renomear as variáveis ligadas de `F` para garantir que a substituição de `t` por `v` em `F` tenha o significado correto. Embora `g[y,c]` não seja livre para `x` em `∀y R[x,y] → ∀x R[x,x]`, o termo é livre para `x` em `∀z R[xz] → ∀x R[x,x]`, que é uma chamada *variante alfabética* (nomes diferentes para as variáveis ligadas) da fórmula original.

A função `isVar` verifica se um termo é uma variável. As funções `varsInTerm` e `varsInTerms` retornam a lista das variáveis que ocorrem num termo ou em uma lista de termos, sem duplicatas.

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

::::exercise (rating := 1) (name := "ex-fol-vars-in-formula")
Implemente a função `varsInForm` que retorna a lista de todas as variáveis que ocorrem em uma fórmula. Retorne a lista sem duplicatas, como em `varsInTerm` e `varsInTerms`.

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


::::exercise (rating := 2) (name := "ex-fol-free-vars-in-form")
Complete a definição de `freeVarsInForm`, que retorna a lista de variáveis com ocorrências livres em uma fórmula que contenha termos além de variáveis.

```lean
def Formula.freeVarsInForm (f : Formula Term) : List Variable :=
  solution!(f.freeVars varsInTerm)
```
::::


::::exercise (rating := 2) (name := "ex-fol-open-form")
Complete a função `openForm`, que verifica se uma fórmula é aberta. Reaproveite as funções anteriores.

```lean
def openForm (f : Formula Term) : Bool :=
  solution!(!f.freeVarsInForm.isEmpty)
```
::::


# Semântica de FOL
%%%
tag := "fol-semantics"
%%%

Em {ref "PL"}[PL], temos atribuições de valor de verdade para indicar o valor de verdade que deve ser atribuído a cada símbolos. Em FOL, uma _estrutura_ cumpre este papel. Uma estrutura é como um dicionário para traduzir a linguagem formal. Uma estrutura nos dirá duas coisas. Em primeiro lugar, sobre qual coleção de coisas o símbolo `∀` deve quantificar. Em segundo lugar, o que os símbolos predicativos e funcionais denotam.

Vamos considerar uma linguagem FOL com um único símbolo predicado binário, `E`. Chamaremos esta linguagem de `L₁`. Uma estrutura para `L₁` deve conter um domínio de discurso `D`, formado por entidades e uma interpretação para `E`.

Essa interpretação é dada por uma função `Interp`, que a cada nome de predicado e a cada lista de elementos do domínio associa um valor de verdade.

```lean
abbrev Interp (D : Type) := String → List D → Bool
```

Um conjunto de símbolos predicativos, com suas aridades, especifica uma linguagem de lógica de predicados. Uma estrutura `M = (D, I)`, formada por um domínio não vazio `D` com uma função de interpretação para os símbolos predicativos de `L`, é chamada de *modelo* para `L`. Sempre suporemos que o domínio de um modelo é não vazio.

Eis um modelo concreto, tomado de {citep Bib.enderton2001}[]. O domínio tem quatro objetos, e uma única relação binária para interpretar o símbolo `E` da linguagem `L`. Um domínio com um só predicado binário pode ser visto como um grafo dirigido: os objetos são os vértices, e `E x y` vale quando há uma aresta de `x` para `y`.

```lean
inductive Vertex where
  | a | b | c | d
deriving Repr, DecidableEq
```

O tipo indutivo diz *quais* são os objetos do domínio: apenas os quatro acima, e nenhum outro. Para avaliar uma fórmula quantificada, porém, será preciso percorrer o domínio, e para isso ele tem de estar disponível como uma lista. São duas coisas diferentes. O tipo indutivo declara o domínio, a lista o exibe na ordem em que será percorrido. Nada, até aqui, garante que a lista não tenha esquecido um vértice — e uma lista incompleta faria a avaliação correr num domínio menor que o pretendido, sem qualquer aviso. Mas isso é uma afirmação que podemos enunciar e provar:

```lean
def vertices : List Vertex := [.a, .b, .c, .d]

theorem mem_vertices (v : Vertex) : v ∈ vertices := by
  cases v
  all_goals decide
```

A tática `decide` fecha uma proposição decidível calculando-a. Combinada com `cases v`, que abre um caso por construtor, ela verifica os quatro casos um a um — e não há um quinto.

Definimos o domínio, agora precisamos definir a relação binária que será usada para interpretar o símbolo `E`.

```lean
def edge : Vertex → Vertex → Bool
  | .a, .b => true
  | .b, .a => true
  | .b, .c => true
  | .c, .c => true
  | _,  _  => false
```

Como dito acima, podemos mesmo representar este domínio e a relação binária como um grafo com nós e arestas.

:::diagramWithAlt
```diagram (cssWidth := "22em") (texWidth := "16em")
CSwLMeta.Diagrams.edgeGraph
```

```
             ┌───┐
             │   ↓
   a ⇄ b ──→ c ──┘    d

O grafo tem quatro vértices: a, b, c e d. Há uma aresta de a para b e outra
de b para a. Há uma aresta de b para c, e um laço de c para si mesmo. O
vértice d está isolado: dele não sai aresta alguma, e nenhuma chega nele.
```
:::

A função de interpretação amarra o nome de predicado a relação no modelo. Nomes fora da lista, ou usados com o número errado de argumentos, recebem `false`.

```lean
def intB : Interp Vertex
  | "E", [x, y] => edge x y
  | _, _ => false
```

Dada uma estrutura com função de interpretação `M = (D, I)`, podemos definir uma valoração para as fórmulas da lógica de predicados, desde que saibamos lidar com os valores das variáveis individuais. Seja `V` o conjunto das variáveis da linguagem. Uma função `g : V → D` é chamada de *atribuição de variáveis*, ou valoração. Escrevemos `g[v := d]` para a valoração que é como `g` exceto pelo fato de que `v` recebe o valor `d` — onde `g` poderia ter atribuído um valor diferente.

```lean
def Assign (D : Type) := Variable → D

def Assign.update {D : Type} (g : Assign D) (v : Variable) (d : D) : Assign D :=
  fun w => if w = v then d else g w
```

Seja `M` um modelo para a linguagem `L`, seja `g` uma atribuição de variáveis para `L` em `M`, e seja `F` uma fórmula de `L`. Estamos prontos para definir a noção `M ⊨ᵍ F`, `F` é verdadeira em `M` sob a atribuição `g` ou `g` satisfaz `F` no modelo `M`.

O que segue é uma definição recursiva de avaliação para as fórmulas da lógica de predicados. Como em {ref "PL"}[lógica proposicional], a definição calcula o resultado `Bool`, e o valor de uma fórmula pode ser obtido com `#eval`. As cláusulas dos quantificadores são as que alteram a atribuição de valores à variáveis. `∀v F` vale quando `F` vale para toda escolha de valor de `v`, e `∃v F` quando vale para ao menos uma.

Aqui aparece a diferença em relação à lógica proposicional. Para decidir um quantificador é preciso percorrer o domínio, e percorrer exige que o domínio seja enumerável e finito. Por isso `eval` recebe um argumento a mais, `dom`, e usa `List.all` e `List.any` — as versões computáveis de `∀` e `∃`.

Uma fórmula `Formula α` tem termos do tipo `α`, e para avaliar um átomo é preciso saber que elemento do domínio cada termo denota. Quando os termos são apenas variáveis, basta consultar `g`; quando forem termos estruturados, será preciso percorrê-los. Em vez de escrever duas funções de avaliação, passamos essa tarefa como um parâmetro `tval`, do mesmo modo que {name}`Formula.freeVars` recebeu a função que extrai as variáveis de um termo. Note que `tval` recebe a atribuição, e não só o termo: as cláusulas dos quantificadores mudam `g`, e a valoração dos termos tem de ver essa mudança.

```lean
def Formula.eval {D α : Type} [DecidableEq D]
    (dom : List D) (I : Interp D)
    (tval : Assign D → α → D)
    (g : Assign D) : Formula α → Bool
  | .atom name args => I name (args.map (tval g))
  | .eq t1 t2 => tval g t1 == tval g t2
  | .top => true
  | .bot => false
  | .neg f => !(Formula.eval dom I tval g f)
  | .impl f1 f2 =>
    !(Formula.eval dom I tval g f1) || Formula.eval dom I tval g f2
  | .equi f1 f2 =>
    Formula.eval dom I tval g f1 == Formula.eval dom I tval g f2
  | .conj f1 f2 =>
    Formula.eval dom I tval g f1 && Formula.eval dom I tval g f2
  | .disj f1 f2 =>
    Formula.eval dom I tval g f1 || Formula.eval dom I tval g f2
  | .forall_ v f =>
    dom.all fun d => Formula.eval dom I tval (g.update v d) f
  | .exists_ v f =>
    dom.any fun d => Formula.eval dom I tval (g.update v d) f
```

Um caso por construtor, e cada caso troca o construtor pela operação correspondente sobre `Bool`. Para `Formula Variable`, a valoração de um termo é a própria consulta a `g`:

```lean
def varVal {D : Type} (g : Assign D) (v : Variable) : D := g v
```

E finalmente podemos declarar algumas fórmulas para avaliarmos em nosso modelo `intB`.

```lean
def E (s t : Variable) : Formula Variable :=
  .atom "E" [s, t]

def someVertexUnreached : Formula Variable :=
  .exists_ x (.forall_ y (.neg (E y x)))

def everyVertexHasSuccessor : Formula Variable :=
  .forall_ x (.exists_ y (E x y))

def someVertexLoops : Formula Variable :=
  .exists_ x (E x x)

def edgeIsSymmetric : Formula Variable :=
  .forall_ x (.forall_ y (.impl (E x y) (E y x)))
```

Se avaliamos fórmulas fechadas, isto é, sem variáveis livres, a atribuição `g` se torna irrelevante — mas ainda é preciso fornecer alguma.

```lean
def g0 : Assign Vertex :=
  fun _ => .a

#eval (Formula.eval vertices intB varVal g0 someVertexUnreached,
       Formula.eval vertices intB varVal g0 everyVertexHasSuccessor,
       Formula.eval vertices intB varVal g0 someVertexLoops,
       Formula.eval vertices intB varVal g0 edgeIsSymmetric)
```

A primeira é a sentença `∃x ∀y ~E[y, x]` corresponde a afirmação de que existe um vértice para o qual nenhuma aresta aponta. É verdadeira, e a testemunha é `d`. A segunda é falsa pelo mesmo motivo — de `d` não sai aresta alguma. A terceira é verdadeira por causa do laço em `c`. A quarta é falsa: há aresta de `b` para `c`, mas não de `c` para `b`. Vale notar como a primeira soa em língua natural mais complicada do que a versão simbólica.


:::exercise (rating := 2) (name := "ex-fol-weak-strong")
Neste exercício, queremos mostrar que:

1. `∀ x, Ax ∧ Bx` significa algo mais forte que `∀ x, Ax → Bx` (todo A é B). O que valida a primeira afirmação necessariamente valida a segunda, mas não o inverso.
2. `∃ x, Ax → Bx` é mais fraco que `∃ x, Ax ∧ Bx` (alguns A são B). Neste caso, o que valida a segunda afirmação necessariamente valida a primeria, mas não o inverso.

Para confirmar (1), complete a definição de `int₁`. Para confirmar (2), complete `int₂`. Todos os exemplos deverão ser provados apenas com a tática {tactic}`native_decide`.  Note que nosso domínio só tem dois valores, você não deve alterar o domínio.

```lean
namespace ExWeakStrong

abbrev Values := Fin 2
def dom : List Values := [0, 1]

def int₁ (name : String) (as : List Values) : Bool :=
 solution!(
   match name, as with
   | "A", [x] => [0].contains x
   | "B", [x] => [0, 1].contains x
   | _  , _   => false)

def int₂ (name : String) (as : List Values) : Bool :=
 solution!(
   match name, as with
   | "A", [x] => false
   | "B", [x] => [1].contains x
   | _  , _   => false)

-- All x are A and B
def F₁ : Formula Variable :=
  .forall_ x (.conj (.atom "A" [x]) (.atom "B" [x]))

-- All A are B
def F₂ : Formula Variable :=
  .forall_ x (.impl (.atom "A" [x]) (.atom "B" [x]))

-- There is x such that, if x is A, then x is B
def F₃ : Formula Variable :=
  .exists_ x (.impl (.atom "A" [x]) (.atom "B" [x]))

-- Some A are B
def F₄ : Formula Variable :=
  .exists_ x (.conj (.atom "A" [x]) (.atom "B" [x]))

def g0 : Assign Values :=
  fun _ => 0

example : Formula.eval dom int₁ varVal g0 F₁ = false :=
  solution!(by native_decide)

example : Formula.eval dom int₁ varVal g0 F₂ :=
  solution!(by native_decide)

example : Formula.eval dom int₂ varVal g0 F₃ :=
  solution!(by native_decide)

example : Formula.eval dom int₂ varVal g0 F₄ = false :=
  solution!(by native_decide)

end ExWeakStrong
```
:::


## Termos estruturados
%%%
tag := "fol-terms"
%%%

Até aqui avaliamos apenas fórmulas de {lean}`Formula Variable`, cujos termos são
variáveis. Mas {name}`Term` permite termos estruturados, como {lean}`tf`, e para
avaliá-los falta dizer que elemento do domínio um símbolo funcional denota. Essa
é a contrapartida, para os símbolos funcionais, do que {name}`Interp` faz para os
símbolos predicativos. A cada nome e a cada lista de elementos do domínio, um
elemento do domínio.

```lean
abbrev FInterp (D : Type) := String → List D → D
```

Com {lean}`FInterp`, a valoração de um termo se define por recursão sobre a estrutura do termo. Uma variável se consulta em `g`; um termo estruturado avalia seus argumentos e entrega os resultados a `fint`.

::::exercise (rating := 1) (name := "lift-assign")
Complete `liftAssign`. Nossa recursão é parecida com {name}`varsInTerm`, avaliando cada argumento e combine os resultados e precisamos interpretar os símbolos funcionais.

```lean
def liftAssign {D : Type} (fint : FInterp D)
    (g : Assign D) : Term → D
  | .var v => g v
  | .struct name args =>
    solution!(fint name (args.map (liftAssign fint g)))
```
::::

`liftAssign fint` tem exatamente o tipo que o parâmetro `tval` de {name}`Formula.eval` pede, e é assim que fórmulas de {lean}`Formula Term` passam a ser avaliáveis. Para um exemplo, tomemos o domínio dos naturais. Precisamos de uma interpretação para os símbolos funcionais, uma para o símbolo de relação, e uma atribuição.

```lean
def finNat  : FInterp Nat
  | "zero",  []     => 0
  | "s",     [i]    => i + 1
  | "plus",  [i, j] => i + j
  | "times", [i, j] => i * j
  | _, _ => 0

def intR : Interp Nat
  | "R", [i, j] => i < j
  | _,    _     => false

def g₂ : Assign Nat
 | ⟨ "x", []⟩ => 1
 | ⟨ _  , _ ⟩ => 0

def zero : Term := .struct "zero" []
```

Uma constante é um símbolo funcional de aridade zero, como `zero` acima. Seguem dois exemplos do que `liftAssign` calcula. Os dois juntos mostram por que a valoração dos termos recebe a atribuição. O valor de `s[zero]` não depende de `g`, pois nenhuma variável ocorre nele, mas o de `plus[x, zero]` é `g x`, e muda com `g`. É essa dependência que o tipo de `tval` carrega.

```lean
theorem s_zero_is_one (g : Assign Nat) :
    liftAssign finNat g (.struct "s" [zero]) = 1 := by
  simp [liftAssign, finNat, zero]

theorem plus_x_zero_is_x (g : Assign Nat) :
    liftAssign finNat g (.struct "plus" [tx, zero]) = g x := by
  simp [liftAssign, finNat, zero, tx]
```

Note que os dois fecham por {tactic}`simp`, e não por {tactic}`rfl`. O casamento de strings não é processado por {tactic}`rfl`.

Finalmente, a avaliação de uma fórmula com termos estruturados, num domínio finito. A fórmula diz que existe um número maior que `0` no domínio `[0, 1, 2, 3, 4]`.

```lean (name := evalTerms)
#eval Formula.eval [0, 1, 2, 3, 4, 5] intR (liftAssign finNat) g₂
  (.exists_ x (.atom "R" [zero, tx]))
```

A definição de verdade faz uso essencial das atribuições e, ainda assim, para sentenças, a verdade ou a falsidade não depende da atribuição. Poder-se-ia pensar, portanto, que é possível dispensar as atribuições por completo, contanto que nos limitemos a definir os valores de verdade das sentenças da lógica de predicados.

O problema é que, ao aplicar a definição de verdade acima a uma sentença, por exemplo a `∀x (P[x] → ∃y R[x,y])`, a cláusula que trata do quantificador universal faz referência à noção de verdade para a fórmula `(P[x] → ∃y R[x,y])`, que é uma fórmula aberta. Para determinar se ela é verdadeira temos de saber que objeto `x` denota. A situação é análoga à interpretação da segunda  sentença em português abaixo temos de saber quem é o referente do pronome _ele_.

1. Todo mestre tem um aprendiz.
2. Ele tem um aprendiz.

Uma sentença da lógica de predicados é *logicamente válida* se é verdadeira em todo modelo; a notação é `⊨ F`. Da convenção de que os domínios de nossos modelos são sempre não vazios segue que `⊨ ∀x F → ∃x F`, para toda `F` com no máximo a variável `x` livre.

Uma sentença `C` *se segue logicamente* de uma sentença `P` (`P` de premissa, `C` de conclusão; dizemos também que `P` implica logicamente `C`) se todo modelo que torna `P` verdadeira também torna `C` verdadeira. A notação é `P ⊨ C`. Como julgar afirmações da forma `P ⊨ C`? É claro como podemos refutá-la: achando um contraexemplo. Um contraexemplo a `P ⊨ C` é um modelo `M` com `M ⊨ P` mas não `M ⊨ C`.


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

def Formula.denote {D α : Type} (I : Denot D)
    (tval : Assign D → α → D)
    (g : Assign D) : Formula α → Prop
  | .atom name args => I name (args.map (tval g))
  | .eq t1 t2 => tval g t1 = tval g t2
  | .top => True
  | .bot => False
  | .neg f => ¬ Formula.denote I tval g f
  | .impl f1 f2 =>
    Formula.denote I tval g f1 → Formula.denote I tval g f2
  | .equi f1 f2 =>
    Formula.denote I tval g f1 ↔ Formula.denote I tval g f2
  | .conj f1 f2 =>
    Formula.denote I tval g f1 ∧ Formula.denote I tval g f2
  | .disj f1 f2 =>
    Formula.denote I tval g f1 ∨ Formula.denote I tval g f2
  | .forall_ v f =>
    ∀ d : D, Formula.denote I tval (g.update v d) f
  | .exists_ v f =>
    ∃ d : D, Formula.denote I tval (g.update v d) f
```

Cada caso troca um construtor de `Formula` pelo conectivo correspondente de `Prop` — o `conj` do dado vira o `∧` da proposição, e o `forall_` vira o `∀` do próprio Lean. Com isso podemos voltar às traduções do exercício anterior e verificá-las. Enunciamos a condição de verdade pretendida à direita, com os quantificadores do Lean, e exigimos que coincida com o que a fórmula proposta afirma. Como `denote` calcula, o teorema fecha por `Iff.rfl`.

```lean
def knightFightsDragon : Formula Variable :=
  solution!(.forall_ x (.forall_ y
    (.impl
      (.conj (.atom "Knight" [x])
        (.conj (.atom "Dragon" [y])
               (.atom "Finds" [x, y])))
      (.atom "Fights" [x, y]))))

theorem knightFightsDragon_means {D : Type}
    (I : Denot D) (g : Assign D) :
    Formula.denote I varVal g knightFightsDragon ↔
      (∀ a b : D,
        I "Knight" [a] ∧ I "Dragon" [b] ∧ I "Finds" [a, b] →
        I "Fights" [a, b]) :=
  solution!(Iff.rfl)
```

Falta o teorema que nos diz que a denotação de uma fórmula conside com sua avaliação. Mas precisamos de uma hipótese que não aparecia em lógica proposicional. A função `eval` decide um quantificador percorrendo `dom`, então só podemos esperar que ele concorde com o `∀` do Lean, que fala de todo elemento do tipo `D` — se `dom` de fato listar todos eles. É isso que `hdom` exige.

```lean
theorem Formula.eval_iff_denote {D α : Type} [DecidableEq D]
    (dom : List D) (hdom : ∀ d : D, d ∈ dom)
    (I : Interp D) (tval : Assign D → α → D)
    (g : Assign D) (f : Formula α) :
    f.eval dom I tval g = true ↔
      f.denote (fun n as => I n as = true) tval g := by
  induction f generalizing g with
  | atom name args => simp [Formula.eval, Formula.denote]
  | eq t1 t2 => simp [Formula.eval, Formula.denote]
  | top => simp [Formula.eval, Formula.denote]
  | bot => simp [Formula.eval, Formula.denote]
  | neg f ih => simp [Formula.eval, Formula.denote, ← ih]
  | impl f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ← ih1, ← ih2]
      cases Formula.eval dom I tval g f1 <;> simp
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

No modelo de {ref "fol-semantics"}[Semântica de FOL], `mem_vertices` é exatamente a hipótese `hdom` que o teorema pede. As duas leituras de qualquer fórmula, portanto, concordam naquele modelo, e não sobra hipótese alguma aberta.

```lean
theorem eval_iff_denote_B (I : Interp Vertex) (g : Assign Vertex)
    (f : Formula Variable) :
    f.eval vertices I varVal g = true ↔
      f.denote (fun n as => I n as = true) varVal g :=
  Formula.eval_iff_denote vertices mem_vertices I varVal g f
```

## Domínios infinitos
%%%
tag := "fol-infinite"
%%%

A hipótese `hdom` é a contrapartida formal de uma limitação real: só se pode calcular o valor de uma fórmula quantificada quando o domínio é finito. Vale a pena ver o que ela exclui.

Considere o domínio dos naturais para interpretação da fórmula `∀x ∃y R[x,y]`, com `R` lido como a relação de menor. Fácil ver que a fórmula é verdadeira. Mas `eval` precisa de uma `List Nat` que contenha *todos* os naturais.

```lean
theorem le_foldr_max :
    ∀ (l : List Nat) (m : Nat), m ∈ l → m ≤ l.foldr max 0
  | [],      _, hm => absurd hm (by simp)
  | a :: as, m, hm => by
    cases hm with
    | head => exact Nat.le_max_left _ _
    | tail _ hm =>
      exact Nat.le_trans (le_foldr_max as m hm)
                         (Nat.le_max_right _ _)

theorem no_list_lists_Nat (dom : List Nat) :
    ∃ n : Nat, n ∉ dom := by
  refine ⟨dom.foldr max 0 + 1, fun h => ?_⟩
  have := le_foldr_max dom _ h
  omega
```

O lema auxiliar diz que todo elemento de uma lista de naturais é menor ou igual ao máximo da lista. Com ele, o candidato `dom.foldr max 0 + 1` não pode estar em `dom`: se estivesse, seria menor ou igual ao máximo, e é maior. Logo a hipótese `hdom` é insatisfazível quando `D` é `Nat`: não há domínio a fornecer, e a avaliação não tem como nem começar.

Já `denote` não depende de lista alguma. Ela traduz a fórmula numa proposição de Lean — e só isso: traduzir não é demonstrar. Mas, uma vez traduzida, a proposição fica ao alcance das táticas, e aí sim podemos demonstrá-la:

```lean
theorem forallExistsR_means (I : Denot Nat) (g : Assign Nat) :
    Formula.denote I (liftAssign finNat) g
      (.forall_ x (.exists_ y (.atom "R" [tx, ty]))) ↔
    (∀ a : Nat, ∃ b : Nat, I "R" [a, b]) := by
  simp [Formula.denote, liftAssign, Assign.update, tx, ty, x, y]

theorem forallExistsR_true (I : Denot Nat)
    (hI : ∀ i j, I "R" [i, j] ↔ i < j) (g : Assign Nat) :
    Formula.denote I (liftAssign finNat) g
      (.forall_ x (.exists_ y (.atom "R" [tx, ty]))) :=
  (forallExistsR_means I g).mpr
    fun a => ⟨a + 1, (hI a (a + 1)).mpr (by omega)⟩
```

Vale distinguir o que cada um dos dois faz. O primeiro é só tradução: ele diz que a fórmula, lida por `denote`, afirma `∀ a, ∃ b, I "R" [a, b]` e nada mais que isso. Por isso `simp` fecha o teorema, sem nenhuma aritmética. O segundo é que demonstra, e é ele que precisa de matemática: a hipótese `hI` fixa a leitura de `R` como `<`, a testemunha de `∃y` é `a + 1`, e `omega` verifica que `a < a + 1`.

Fica assim a divisão de trabalho entre as duas leituras. `eval` calcula, e por isso exige um domínio finito e dado. `denote` traduz para `Prop`. Traduzir, porém, é o que põe a afirmação ao alcance de uma demonstração — e uma demonstração alcança o que nenhum `#eval` alcançaria aqui, pois sobre os naturais não há lista a fornecer.

```lean
end FOL
```
