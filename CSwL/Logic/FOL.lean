import CSwLMeta
import Bib
import Mathlib.Tactic.Use
import CSwL.Logic.PL
import CSwLCompat

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

Se usarmos lógica proposicional para formalizar a frase "Toda maçã é vermelha", teremos uma letra proposicional, um átomo indivisível que não nos permitiria capturar a idéia do quantificador e da dependencia declarada entre as _coisas_ que são maçãs e a cor destas mesmas _coisas_. A lógica de predicados, também chamada lógica de primeira ordem (FOL, "first order logic") acrescenta os seguintes ingredientes a sintaxe da lógica proposicional:

* Termos para representar indivíduos de um domínio. Os termos poderão ser variáveis ou funções aplicadas sobre termos;
* Proposições básicas serão predicados `n`-ários sobre termos;
* Fórmulas universalmente quantificadas, `∀` seguido de variável e fórmula;
* Fórmulas existencialmente quantificadas, `∃` seguido de variável e fórmula.


# Sintaxe de FOL
%%%
tag := "fol-syntax"
%%%

Nossa sintaxe terá dois elementos principais, *termos* e *fórmulas*. Como fizemos em {ref "pl-syntax"}[pl-syntax], nossa sintaxe será formalizada como tipos indutivos.

Os _termos_ podem ser variáveis ou funções aplicadas a outros termos. Uma variável carrega nome e um índice (lista de naturais usada para gerar "novas" variáveis a partir de uma dada variável):

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
Nothing stopping us for using symbols with inconsistent arity, say `R[x,y]` and `R[x,y,z]` in the same formula. We could define a structure for holding the number and its arity (say `PredSymbol`) and implement a function for checking if a formula is well-formed.
:::

As *fórmulas* usarão os mesmos conectivos da lógica proposicional, mas acrescentaremos os quantificadores existencial e universal. O nome lógica de primeira ordem vem da idéia de que estamos quantificando sobre indivíduous de um domínio, objetos de primeira ordem. O tipo `Formula α` é parametrizado no tipo dos termos que preenchem os predicados. Se usarmos `Formula Variable` nossos termos são apenas variáveis. Se usarmos `Formula Term` temos nossa sintaxe completa com termos arbitrários.

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

Note que o tipo {lean}`Formula` é diferente do tipo {lean}`PL.Formula` definido em {ref "pl-syntax"}[pl-syntax], cada um em seu próprio `namespace`. Mais uma vez, estamos usando Lean como metalinguagem para implementar FOL.. Em tipos dependentes, não fazemos a distinção entre termos e fórmulas. Como vimos em {ref "IntroL"}[IntroL], em Lean toda expressão é um termo e todo termo tem um tipo. Então quando falarmos em termos, ora estamos falando do termo Lean que pode representar uma {lean}`Formula` ou {lean}`Term` de FOL.

Também como fizemos para {lean}`PL.Formula`, a notação n-ária de {name}`Formula.conj` e {name}`Formula.disj` introduzimos com as funções abaixo.

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

A seguir, `R_reflexive` expressa que o predicado `R` é reflexivo enquanto `R_simetric` expressa que ele é simétrico. Note que para estes dois exemplos, não precisamos usar termos envolvendo funções, logo usamos apenas {lean}`Formula Variable`.

```lean
def R_reflexive : Formula Variable :=
  .forall_ x (.atom "R" [x, x])

def R_simetric : Formula Variable :=
  .forall_ x (.forall_ y
    (.impl (.atom "R" [x, y]) (.atom "R" [y, x])))
```

Assim como definimos em {ref "pl-syntax"}[pl-syntax], chamamos de uma linguagem de primeira ordem o conjunto de todas as fórmulas que podem ser construídas a partir de um vocabulário de símbolos predicativos e funcionais.

::::exercise (rating := 2) (name := "ex-fol-translate")
Considere a linguagem de primeira ordem com o vocabulário definido pelos símbolos abaixo.

- `R(x,y)` - `x` respeita `y`
- `M(x,y)` – `x` esta matriculado na disciplina `y`
- `P(x)` – x é um professor
- `A(x)` – `x` é um aluno
- `D(x)` – `x` é uma disciplina
- `Maria` - uma constante denotando a pessoa chamada Maria.

Vamos traduzir cada uma das sentenças a seguir para fórmulas em lógica de primeira ordem.

- (`Fa`) Maria respeita todos os professores.
- (`Fb`) Alguns professores respeitam Maria.
- (`Fc`) Maria respeita a si própria
- (`Fd`) Nenhum aluno esta matriculado em todas as disciplina
- (`Fe`) Não há disciplinas em que todos os alunos estejam nela matriculados
- (`Ff`) Não há disciplinas sem alunos matriculados

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
`x` em `F` que não esteja já ligada por um `∀x` (ou `∃x`) interno a `F`. Uma fórmula é *aberta* se tem ao menos uma ocorrência livre de variável, e *fechada* (também chamada *sentença*) caso contrário. Por exemplo, `(P[x] ∧ ∃x, R[x,x])` é aberta, o `x` de `P[x]` está fora do escopo do `∃x`. Mas `∃y (P[y] ∧ ∃x R[x,x])` é uma sentença.

Coletar as variáveis livres de uma fórmula é uma operação recorrente. Abaixo, definimos a função freeVars que recebe como parâmetro uma função que extrai as variáveis de um termo. Para {lean}`R_reflexive`, só precisamos de uma função que transforme uma variável em uma lista com ela mesma. Para fórmulas que podem conter termos complexos, {lean}`Formula Term`, nossa função terá que percorrer todo o termo coletando as variáveis. Nos quantificadores, `filter` preserva apenas as variáveis diferentes da variável que o quantificador introduz.

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
Implicações e equivalências podem ser vistas como abreviações, pois se definem a partir de negação, conjunção e disjunção — as mesmas equivalências usadas na lógica proposicional. Escreva uma função `minimal` que substitui cada fórmula por uma equivalente sem ocorrências de `impl` ou `equi`. Note que a função não depende do tipo `α`.

```lean
def Formula.minimal {α : Type} (frm : Formula α) : Formula α :=
  solution!(
    match frm with
    | .atom name as => .atom name as
    | .eq t1 t2 => .eq t1 t2
    | .top => .top
    | .bot => .bot
    | .neg f => .neg (minimal f)
    | .impl f1 f2 =>
      .disj (.neg (minimal f1)) (minimal f2)
    | .equi f1 f2 =>
      let g1 := minimal f1
      let g2 := minimal f2
      .conj (.disj (.neg g1) g2) (.disj (.neg g2) g1)
    | .conj f1 f2 =>
      .conj (minimal f1) (minimal f2)
    | .disj f1 f2 =>
      .disj (minimal f1) (minimal f2)
    | .forall_ v f => .forall_ v (minimal f)
    | .exists_ v f => .exists_ v (minimal f))
```
:::

:::exercise (rating := 2) (name := "ex-fol-nnf")
Toda fórmula de lógica de predicados pode ser transformada em uma equivalente na *forma normal da negação* (NNF, "negation normal form"), onde negações só ocorrem diante de átomos. A receita é "empurrar" as negações através dos quantificadores por `¬ ∀x F ≡  ∃x ¬F` e `¬ ∃x F ≡ ∀x ¬F`, e através de disjunções e conjunções pelas leis de De Morgan: `¬(F1 ∧ F2) ≡ ¬F1 ∨ ¬F2` e `¬(F1 ∨ F2) ≡ ¬F1 ∧ ¬F2`. Finalmente, `¬¬F ≡ F` elimina dupla negação. Complete o código da função `nnf`.

Dica: a receita acima diz o que fazer com a negação diante de alguma subfórmula. Isso sugere duas funções, uma para cada situação em que uma subfórmula pode aparecer. As duas se chamam mutuamente, e por isso vão num bloco `mutual`.

- `nnfPos f` devolve a NNF de `f`;
- `nnfNeg f` devolve a NNF de `¬f`.

Trate `impl` e `equi` diretamente nas duas funções, sem passar por {name}`Formula.minimal`. E novamente, observe que a função não depende do tipo `α`.

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

Um termo `t` é *livre para* a variável `v` na fórmula `F` se toda ocorrência livre de `v` em `F` pode ser substituída por `t` sem que nenhuma das variáveis de `t` fique ligada. Por exemplo, `y` é livre para `x` em `P[x] → ∀x P[x]`, mas o mesmo termo não é livre para `x` em `∀y R[x,y] → ∀x R[x,x]`. Da mesma forma, `g[x,y]` não é livre para `x` em `∀y R[x,y] → ∀x R[x,x]`.

Um termo livre para uma variável `v` pode ser substituído nas ocorrências livres de `v` sem uma mudança não intencional de significado. Considere a fórmula aberta `∀y R[x,y] → ∀x R[x,x]`. Se substituirmos a ocorrência livre de `x` nessa fórmula por `y`, obtemos uma fórmula fechada `∀y R[y,y] → ∀x R[x,x]`, uma variável acabou capturada. Se `t` não é livre para `v` em `F`, podemos sempre renomear as variáveis ligadas de `F` para garantir que a substituição de `t` por `v` em `F` tenha o significado correto. Embora `g[y,c]` não seja livre para `x` em `∀y R[x,y] → ∀x R[x,x]`, o termo é livre para `x` em `∀z R[x,z] → ∀x R[x,x]`, que é uma chamada *variante alfabética* (nomes diferentes para as variáveis ligadas) da fórmula original.

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

::::exercise (rating := 2) (name := "ex-fol-vars-in-formula")
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


::::exercise (rating := 1) (name := "ex-fol-free-vars-in-form")
Complete a definição de `freeVarsInForm`, que retorna a lista de variáveis com ocorrências livres em uma fórmula que contenha termos além de variáveis.

```lean
def Formula.freeVarsInForm (f : Formula Term) : List Variable :=
  solution!(f.freeVars varsInTerm)
```
::::


::::exercise (rating := 1) (name := "ex-fol-open-form")
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

Em {ref "PL"}[PL], uma função de atribuição de valor de verdade para os símbolos proposicionais nos permite determinar o valor de verdade de uma fórmula. Em FOL, uma interpretação de um vocabulário é uma estrutura que atribui significado aos símbolos do vocabulário.

Uma estrutura `𝔸` é como um dicionário para traduzir a linguagem de primeira ordem `L`. Uma estrutura nos dirá sobre qual coleção de coisas os símbolos `∀` e `∃` quantificam, isto é, o conjunto `D`. A estrutura também associa os símbolos predicativos de `L` a relações no domínio e os símbolos funcionais a funções no domínio. Formalmente, a estrutura é o par, domínio e interpretação.

Mas nossos termos podem ser conter variáveis então também precisamos interpretar variávei em elementos do domínio. O tipo `Assign` mapea variávies em elementos do domínio. A função `Assign.update` atualiza um mapeamento de variáveis em elementos do domínio associando a variável `v` e um novo elemento `d`, normalmente escrevemos `g[v := d]` para representar esta idéia de que `g`

```lean
def Assign (D : Type) := Variable → D

def Assign.update {D : Type}
  (g : Assign D) (v : Variable) (d : D) : Assign D :=
  fun w => if w = v then d else g w
```

A idéia é demostrada nos exemplos a seguir. Em um domínio dos naturais, a partir de um mapeamento inicial onde qualquer variável é mapeada no `0`, podemos atualizar indicando que se a variável `x` for passada, ela deve agora estar associada ao valor `1`.

```lean
def g0 : Assign Nat  := λ x ↦ 0
def g1 : Assign Nat  := g0.update x 1

#eval [g0 x, g0 y, g1 x, g1 y]
```

Definido o mapeamento de variáveis, definimos agora o tipo `FInterp` para a interpretação de termos em elementos de um domínio `D`.

```lean
abbrev FInterp (D : Type) := String → List D → D
```

A partir de {lean}`FInterp`, definimos a interpretação de um termo na função `liftAssign`, recursiva sobre a estrutura do termo. Nossa recursão é parecida com {name}`varsInTerm`, avaliando cada argumento e combinando os resultados para interpretar os símbolos funcionais. Note que `fint name` tem tipo `List D → D` e `(args.map (liftAssign fint g))` irá retornar um termo do tipo `List D`.

```lean
def liftAssign {D : Type} (fint : FInterp D) (g : Assign D) : Term → D
  | .var v => g v
  | .struct name args => fint name (args.map (liftAssign fint g))
```

Agora podemos definir quando uma fórmula `α` é verdadeira em uma estrutura `𝔸`. Vamos usar a notação `𝔸 ⊧ α [g]` ou `⊧ α [𝔸,g]` para indicar que esta relação de consequência depende da interpretação dos símbolos em `α` dada por `𝔸` e da atribuição de variáveis a elementos do domínio dada por `g`. A segunda notação é mais precisa, preservando a idéia de que consequência lógica é uma relação entre fórmulas `β ⊧ α` ou entre uma listas de fórmulas e uma fórmula `Δ ⊧ α`.

O tipo `Interp` define o que é a interpretação de símbolos predicativos e seus argumentos para um valor boleano.

```lean
abbrev Interp (D : Type) := String → List D → Bool
```

Em seguida definimos como avaliar fórmulas. Como em {ref "PL"}[lógica proposicional], a definição calcula o resultado `Bool`. As cláusulas dos quantificadores são as que alteram a atribuição de valores à variáveis. `∀v F` vale quando `F` vale para toda escolha de valor de `v`, e `∃v F` quando vale para ao menos uma.

Aqui aparece a diferença em relação à lógica proposicional. Em nossa implementação, para avaliar uma fórmula com quantificador é preciso percorrer o domínio, e percorrer exige que o domínio seja enumerável e finito. Por isso `eval` recebe um argumento a mais, `dom`, e usa `List.all` e `List.any`, versões computáveis de `∀` e `∃`. Em FOL, domínios não precisam ser finitos, mas não existe processo de decisão para avaliação de fórmulas em domínios infinitos e não enumeráveis.

Uma fórmula `Formula α` tem termos do tipo `α`, que pode ser `Variable` ou `Term`. Quando os termos são apenas variáveis, basta consultar `g`; quando forem termos estruturados, será necessário promover, com `liftAssign`, um mapeamento de variáveis no domínio para um mapemanto de termos no domínio. Em vez de escrever duas funções de avaliação, passamos essa tarefa como um parâmetro `tval`, do mesmo modo que {name}`Formula.freeVars` recebeu a função que extrai as variáveis de um termo.

```lean
def Formula.eval {D α : Type} [DecidableEq D]
    (f : Formula α)
    (dom : List D) (I : Interp D)
    (g : Assign D) (tval : Assign D → α → D) : Bool :=
  match f with
  | .atom name args => I name (args.map (tval g))
  | .eq t1 t2 => tval g t1 == tval g t2
  | .top => true
  | .bot => false
  | .neg f => !(f.eval dom I g tval)
  | .impl f1 f2 =>
    !(f1.eval dom I g tval) || f2.eval dom I g tval
  | .equi f1 f2 =>
    f1.eval dom I g tval == f2.eval dom I g tval
  | .conj f1 f2 =>
    f1.eval dom I g tval && f2.eval dom I g tval
  | .disj f1 f2 =>
    f1.eval dom I g tval || f2.eval dom I g tval
  | .forall_ v f =>
    dom.all fun d => f.eval dom I (g.update v d) tval
  | .exists_ v f =>
    dom.any fun d => f.eval dom I (g.update v d) tval
```

Para `Formula Variable`, a interpretação de `Variable` é a própria `g`.

```lean
def varVal {D : Type} (g : Assign D) (v : Variable) : D := g v
```

Vamos considerar uma linguagem FOL, tomado de {citep Bib.enderton2001}[], com um único símbolo predicado binário, `E`. Chamaremos esta linguagem de `L₁`. Uma estrutura para `L₁` deve conter um domínio de discurso `D`, formado por entidades e uma interpretação para `E`. O domínio tem quatro objetos, e uma única relação binária para interpretar o símbolo `E` da linguagem `L₁`.

```lean
inductive Vertex where
  | a | b | c | d
deriving Repr, DecidableEq

def edge : Vertex → Vertex → Bool
  | .a, .b => true
  | .b, .a => true
  | .b, .c => true
  | .c, .c => true
  | _,  _  => false
```

O tipo indutivo {name}`Vertex` determinar quais são os objetos do nosso domínio. Para avaliar uma fórmula quantificada, porém, será preciso percorrer o domínio, e para isso ele tem de estar disponível em uma coleção que possa ser percorrida, vamos usar uma lista. Então o tipo indutivo declara o domínio, a lista o exibe na ordem em que será percorrido.

```lean
def vertices : List Vertex := [.a, .b, .c, .d]

theorem mem_vertices (v : Vertex) : v ∈ vertices := by
  cases v <;> decide
```

O teorema {name}`mem_vertices` nos garante que na lista estão todos os elementos do tipo `Vertex`. A tática `decide` é combinada com `cases v`, que abre um caso por construtor, ela verifica os quatro casos um a um.

Um domínio com um só predicado binário pode ser visto como um grafo direcionado: os objetos são os vértices, e `E x y` vale quando há uma aresta de `x` para `y`.

:::diagramWithAlt
```diagram (cssWidth := "22em") (texWidth := "16em")
CSwLMeta.Diagrams.edgeGraph
```

```
             ┌───┐
             │   ↓
   a ⇄ b ──→ c ──┘    d

O grafo tem quatro vértices: a, b, c e d. Há uma aresta de a para b e outra de b para a. Há uma aresta de b para c, e um laço de c para si mesmo. O vértice d está isolado: dele não sai aresta alguma, e nenhuma chega nele.
```
:::

A seguir `intB` interpreta o predicado de `E` à relação no modelo {name}`edge`.

```lean
def intB : Interp Vertex
  | "E", [x, y] => edge x y
  | _, _ => false
```

Uma importante observação é que nomes fora da lista, ou usados com o número errado de argumentos, recebem {lean}`false`. Isto quer dizer que fórmulas mal formadas, como por exemplo `∃ x E[x]` com o predicado `E` sendo usado com um único argumento, serão silenciosamente avaliadas como {lean}`false`.

Finalmente podemos declarar algumas fórmulas para avaliarmos em nossa estrutura.

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

A primeira é a sentença corresponde a afirmação de que existe um vértice para o qual nenhuma aresta aponta. É verdadeira, e a testemunha é o nó `d`. A segunda é falsa pelo mesmo motivo, de `d` não sai aresta alguma. A terceira é verdadeira por causa do laço em `c`. A quarta é falsa: há aresta de `b` para `c`, mas não de `c` para `b`. Vale notar como a primeira soa em língua natural mais complicada do que a versão simbólica.

Quando avaliamos fórmulas fechadas, sem variáveis livres, a atribuição `g` é irrelevante, mas ainda é preciso fornecer alguma para {name}`Formula.eval`.

```lean
def g : Assign Vertex :=
  fun _ => .a

#eval (someVertexUnreached.eval vertices intB g varVal,
       everyVertexHasSuccessor.eval vertices intB g varVal,
       someVertexLoops.eval vertices intB g varVal,
       edgeIsSymmetric.eval vertices intB g varVal)
```

A seguir, vamos usar o tipo {lean}`Fin` que constrói um tipo dos números naturais menores que um limite superior. O {lean}`Fin 2` corresponde aos naturais menores que `2`. Quando escrevemos {lean}`(1 : Fin 2)`, a instância {lean}`OfNat (Fin 2) 1` normaliza o literal armazenando o resto da divisão {lean}`1 % 2`.

```lean
example : (3 : Fin 2) = 1 := rfl
example : ⟨0, by omega⟩ = (0 : Fin 2) := rfl
example : Fin.mk 0 (by omega) = (0 : Fin 2) := rfl
```

Usando o construtor `Fin.mk n` (ou o construtor anônimo `⟨...⟩`), temos que passar uma prova de que o número informado é menor que o limite do tipo. Não conseguimos abaixo construir uma prova de que `3 < 2`.

```lean +error
example : ⟨3, by omega⟩ = (3 : Fin 2) := rfl
```

:::exercise (rating := 1) (name := "ex-fol-model")
Complete a definição das interpretações `int₁` e `int₂` que permitam os exemplos serem provados com a tática {tactic}`native_decide`. Note que nosso domínio contém apenas 3 valores, isto não deve ser alterado.

```lean
namespace ExModel

abbrev Values := Fin 3
def dom : List Values := [0, 1, 2]

def int₁ (name : String) (as : List Values) : Bool :=
 solution!(
   match name, as with
   | "P", [x]   => [1].contains x
   | "R", [x,y] => [(0,0),(1,0)].contains (x,y)
   | _  , _     => false)

def int₂ (name : String) (as : List Values) : Bool :=
 solution!(
   match name, as with
   | "P", [x]   => [0,1].contains x
   | "R", [x,y] => [(0,0),(1,0)].contains (x,y)
   | _  , _     => false)

def P (x : Variable) : Formula Variable :=
  .atom "P" [x]

def R (x y : Variable) : Formula Variable :=
  .atom "R" [x, y]

def α₁ : Formula Variable :=
  .exists_ x (.conj (P x) (R x x))

def α₂ : Formula Variable :=
  .forall_ x (.impl (P x) (.exists_ y (R x y)))

def α₃ : Formula Variable :=
  .forall_ x (.impl (.exists_ y (R y x)) (R x x))

def g0 : Assign Values :=
  fun _ => 0

example : α₁.eval dom int₁ g0 varVal = false :=
  solution!(by native_decide)

example : α₂.eval dom int₂ g0 varVal :=
  solution!(by native_decide)

example : α₃.eval dom int₁ g0 varVal :=
  solution!(by native_decide)

end ExModel
```
:::

:::exercise (rating := 2) (name := "ex-fol-weak-strong")
Neste exercício, queremos mostrar que:

1. `∀ x, Ax ∧ Bx` significa algo mais forte que `∀ x, Ax → Bx` (todo A é B).
2. `∃ x, Ax → Bx` é mais fraco que `∃ x, Ax ∧ Bx` (alguns A são B).

Para confirmar (1), complete a definição de `int₁` construíndo uma interpretação onde `∀ x, Ax → Bx` é verdadeira mas `∀ x, Ax ∧ Bx` é falsa. Isto é, seja `M = (dom, int₁)` é um modelo que não satisfaz a restrição mais forte `∀ x, Ax ∧ Bx`. Para confirmar (2), complete `int₂` com uma interpretação onde `∃ x, Ax → Bx` é verdadeira mas `∃ x, Ax ∧ Bx` é falsa.

Todos os exemplos deverão ser provados apenas com a tática {tactic}`native_decide`.  Note que nosso domínio é definido sobre os únicos dois possíveis valore de {lean}`Fin 2` e isso não deve ser alterado.

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

example : F₁.eval dom int₁ g0 varVal = false :=
  solution!(by native_decide)

example : F₂.eval dom int₁ g0 varVal :=
  solution!(by native_decide)

example : F₃.eval dom int₂ g0 varVal :=
  solution!(by native_decide)

example : F₄.eval dom int₂ g0 varVal = false :=
  solution!(by native_decide)

end ExWeakStrong
```
:::

Como segundo exemplo, vamos considerar uma linguagem `L₂` com interpretação também sobre os naturais. Precisamos de uma interpretação para os símbolos funcionais, uma para o símbolo de relação, e uma atribuição.

```lean
def intFNat : FInterp Nat
  | "zero",  []     => 0
  | "s",     [i]    => i + 1
  | "plus",  [i, j] => i + j
  | "times", [i, j] => i * j
  | _, _ => 0

def intNat : Interp Nat
  | "R", [i, j] => i < j
  | _,    _     => false

def g3 : Assign Nat
 | ⟨ "x", []⟩ => 1
 | ⟨ _  , _ ⟩ => 0

def zero : Term := .struct "zero" []
```

Uma constante é um símbolo funcional de aridade zero, como {name}`zero` acima. Seguem dois exemplos do que {name}`liftAssign` calcula. O valor de `s[zero]` não depende de `g`, pois nenhuma variável ocorre nele, mas o de `plus[x, zero]` é `g x`, e muda com `g`. Note que os dois fecham por {tactic}`simp`, e não por {tactic}`rfl`. O casamento de strings não é processado por {tactic}`rfl`.

```lean
theorem s_zero_is_one (g : Assign Nat) :
    liftAssign intFNat g (.struct "s" [zero]) = 1 := by
  simp [liftAssign, intFNat, zero]

theorem plus_x_zero_is_x (g : Assign Nat) :
    liftAssign intFNat g (.struct "plus" [tx, zero]) = g x := by
  simp [liftAssign, intFNat, zero, tx]
```

Segue um exemplo de avaliação de uma fórmula de `L₂` no domínio `[0, 1, 2, 3, 4]`. A fórmula diz que existe um número maior que `0`.

```lean
def frm₁ : Formula Term := .exists_ x (.atom "R" [zero, tx])
def frm₂ : Formula Term := .forall_ x (.exists_ y (.atom "R" [tx, ty]))

#eval
  let dom : List Nat := [0, 1, 2, 3, 4]
  (frm₁.eval dom intNat g3 (liftAssign intFNat),
   frm₂.eval dom intNat g3 (liftAssign intFNat))
```

Vale destacar os limites de nossa implemenação. Em FOL, `frm₂` sob o domínio dos naturais é verdadeira. Nossa implementação, no entanto, para ser decidível, processa apenas domínios finitos, listas.

A definição de verdade faz uso essencial das atribuições e, ainda assim, para sentenças, a verdade ou a falsidade não depende da atribuição. O problema é que, ao aplicar a definição de verdade acima a uma sentença, por exemplo a `∀x (P[x] → ∃y R[x,y])`, a cláusula que trata do quantificador universal faz referência à noção de verdade para a fórmula `(P[x] → ∃y R[x,y])`, que é uma fórmula aberta. Para determinar se ela é verdadeira temos de saber qual elemento do domínio associar a `x`. A situação é análoga à interpretação de pronomes nas linguas naturais.

1. Todo mestre tem um aprendiz.
2. Ele tem um aprendiz.

Assim como definimos em {ref "PL"}[PL]. Uma sentença `α` em FOL é *válida*, `⊨ α`, se é verdadeira em toda possível interpretação para a linguagem de `α`. Uma sentença `C` é consequência lógica de uma sentença `P` (`P` de premissa, `C` de conclusão) se todo modelo que torna `P` verdadeira também torna `C` verdadeira. A notação é `P ⊨ C`.

Mas como julgar afirmações da forma `P ⊨ C`? Em FOL não temos a função {name}`PL.Formula.allVals`, que enumera todas as possíveis valorações. Logo não podemos decidir `P ⊧ C`. Podemos refutar a afirmação achando um contraexemplo. Um contraexemplo para `P ⊨ C` é uma interpretação `I` com `I ⊨ P` mas `I ⊭ C`.


# Traduzindo `Formula` para `Prop`

Como fizemos em {ref "PL"}[PL], agora podemos mapear termos do tipo `Formula` em `Prop`. Temos {name}`Formula.eval` que calcula o valor verdade de uma fórmula para uma dada interpretação em {name}`Bool`; `Formula.denote` produz a proposição que a fórmula afirma. O tipo para interpretaçõa também precisa mudar, {name}`Interp` devolvia um `Bool`, `Denot` devolve uma `Prop`.

```lean
abbrev Denot (D : Type) := String → List D → Prop

def Formula.denote {D α : Type}
    (f : Formula α) (I : Denot D)
    (g : Assign D) (tval : Assign D → α → D) : Prop :=
  match f with
  | .atom name args => I name (args.map (tval g))
  | .eq t1 t2 => tval g t1 = tval g t2
  | .top => True
  | .bot => False
  | .neg f => ¬ f.denote I g tval
  | .impl f1 f2 => f1.denote I g tval → f2.denote I g tval
  | .equi f1 f2 => f1.denote I g tval ↔ f2.denote I g tval
  | .conj f1 f2 => f1.denote I g tval ∧ f2.denote I g tval
  | .disj f1 f2 => f1.denote I g tval ∨ f2.denote I g tval
  | .forall_ v f => ∀ d : D, f.denote I (g.update v d) tval
  | .exists_ v f => ∃ d : D, f.denote I (g.update v d) tval
```

Cada caso troca um construtor de `Formula` pelo conectivo correspondente de `Prop` — o `conj` do dado vira o `∧` da proposição, e o `forall_` vira o `∀` do próprio Lean.

O teorema a seguir nos diz que a denotação de uma fórmula conside com sua avaliação. Mas precisamos de uma hipótese que não aparecia em lógica proposicional. A função `eval` decide um quantificador percorrendo `dom`, então só podemos esperar que ele concorde com o `∀` do Lean, que fala de todo elemento do tipo `D` — se `dom` de fato listar todos eles. É isso que `hdom` exige.

```lean
theorem Formula.eval_iff_denote {D α : Type} [DecidableEq D]
    (dom : List D) (hdom : ∀ d : D, d ∈ dom)
    (I : Interp D) (tval : Assign D → α → D)
    (g : Assign D) (f : Formula α) :
    f.eval dom I g tval = true ↔ f.denote (λ n as ↦ I n as = true) g tval := by
  induction f generalizing g with
  | atom name args => simp [Formula.eval, Formula.denote]
  | eq t1 t2 => simp [Formula.eval, Formula.denote]
  | top => simp [Formula.eval, Formula.denote]
  | bot => simp [Formula.eval, Formula.denote]
  | neg f ih => simp [Formula.eval, Formula.denote, ← ih]
  | impl f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ← ih1, ← ih2]
      cases f1.eval dom I g tval <;> simp
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

O teorema {name}`mem_vertices` é exatamente a hipótese `hdom` que o teorema {name}`Formula.eval_iff_denote` pede. As duas leituras de qualquer fórmula, portanto, concordam naquele modelo, e não sobra hipótese alguma aberta.

```lean
theorem eval_iff_denote_B (I : Interp Vertex) (g : Assign Vertex)
    (f : Formula Variable) :
    f.eval vertices I g varVal = true ↔
      f.denote (fun n as => I n as = true) g varVal :=
  Formula.eval_iff_denote vertices mem_vertices I varVal g f
```

A hipótese `hdom` é a contrapartida formal de uma limitação real de que só podemos calcular o valor de uma fórmula quantificada quando o domínio é finito.

::::details  "Interpretação nos Naturais não é decidível"
Considere o domínio dos naturais para interpretação da fórmula `∀x ∃y R[x,y]` que vimos acima. Fácil ver que a fórmula é verdadeira. Mas {name}`Formula.eval` precisa de uma {lean}`List Nat` que contenha *todos* os naturais. É fácil aceitar que não teríamos como provar que {lean}`∀ d : ℕ, d ∈ [0, 1, 2, 3, 4]`, justificando porque a avaliação de `∀x ∃y R[x,y]` não corresponde a denotação desta fórmula em `Prop`. Mas podemos provar esta afirmação.

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
::::

Mas `denote` não depende de nenhuma lista. Ela traduz a fórmula numa proposição de Lean. Uma vez traduzida, a proposição pode ser provada sem recorrermos a noção de consequência lógica e construção de uma interpretação.

```lean
theorem frm₂_is_valid_aux (I : Denot Nat) (g : Assign Nat)
  : frm₂.denote I g (liftAssign intFNat) ↔ (∀ a, ∃ b, I "R" [a, b]) := by
  simp [frm₂, Formula.denote, liftAssign, Assign.update, tx, ty, x, y]

theorem frm₂_is_valid (I : Denot Nat)
    (hI : ∀ i j, I "R" [i, j] ↔ i < j) (g : Assign Nat)
    : frm₂.denote I g (liftAssign intFNat) := by
  apply (frm₂_is_valid_aux I g).mpr
  intro a
  exact ⟨a + 1, (hI a (a + 1)).mpr (by omega)⟩
```

O teorema {name}`frm₂_is_valid_aux` é só tradução. Por isso `simp` fecha o teorema, sem nenhuma aritmética. O teorema {name}`frm₂_is_valid` é que demonstra, e é ele que precisa de matemática. A hipótese `hI` interpreta `R` como `<` em `Prop`, a testemunha de `∃y` é `a + 1`, e `omega` verifica que `a < a + 1`. Com isso, temos {name}`Formula.eval` que calcula, e por isso exige um domínio finito e dado. E {name}`Formula.denote` traduz para `Prop`.

A função {name}`Formula.denote` nos permite definir em `Prop` o que são fórmulas válidas, satisfatíveis e quando existe uma consequência lógica entre duas fórmulas.

```lean
/-- A formula is valid when it is true in every model. -/
def Formula.Valid (f : Formula Variable) : Prop :=
  ∀ (D : Type) (I : Denot D) (g : Assign D), f.denote I g varVal

/-- A formula is satisfiable when some model makes it true. -/
def Formula.Satisfiable (f : Formula Variable) : Prop :=
  ∃ (D : Type) (I : Denot D) (g : Assign D), f.denote I g varVal

/-- `f ⊨ g` holds exactly when `f → g` is valid. -/
def Formula.Implies (f g : Formula Variable) : Prop :=
  (Formula.impl f g).Valid
```

::::exercise (rating := 2) (name := "ex-fol-valid")
Complete as provas dos exemplos abaixo. Note que uma das afirmações não é válida: para ela, vamos precisar da interpretação `intR` como testemunha onde a relação `R` é interpretada como o conjunto unitário `{(0,0)}`.

```lean
namespace ExValid

def P (x : Variable) : Formula Variable := .atom "P" [x]
def R (x y : Variable) : Formula Variable := .atom "R" [x, y]

def intR : Denot Nat
  | "R", [i, j] => i = 0 ∧ j = 0
  | _, _ => False

def g : Assign Nat := fun _ => 0

example :
  (Formula.disj (.forall_ x (P x))
    (.exists_ x (.neg (P x)))).Valid := by
  solution!
   intro D I g
   simp [Formula.denote, P, Assign.update, x, varVal]
   by_contra hc
   apply hc
   left
   intro d
   by_contra hd
   exact hc (Or.inr ⟨d, hd⟩)

example :
  (Formula.impl (.exists_ x (.exists_ y (R x y)))
     (.exists_ x (.exists_ y (R y x)))).Valid := by
  solution!
   intro D I g
   simp [Formula.denote, R, Assign.update, x, y, varVal]
   intro a b hab
   exact ⟨b, a, hab⟩

example :
  (Formula.impl (.forall_ x (R x x))
     (.forall_ x (.exists_ y (R x y)))).Valid := by
  solution!
   intro D I g
   simp [Formula.denote, R, Assign.update, x, y, varVal]
   intro h a
   exact ⟨a, h a⟩

example :
  ¬ (Formula.impl (.exists_ x (R x x))
       (.forall_ x (.exists_ y (R x y)))).Valid := by
  solution!
   intro h
   have h₁ := h Nat intR g
   simp [Formula.denote, R, Assign.update, x, y, varVal, intR] at h₁
   have := h₁ 1
   omega

end ExValid
```
::::

::::exercise (rating := 2) (name := "ex-fol-consequence")
Complete as provas dos exemplos abaixo. Note que uma das consequências lógicas não é válida. Apeans para este exemplo vamos precisar da interpretação `intR`.

```lean
namespace ExEntailsOnlyVars

def P (x : Variable) : Formula Variable := .atom "P" [x]
def R (x y : Variable) : Formula Variable := .atom "R" [x, y]

def intR : Denot Nat
  | "R", [i, j] => i < j
  | _, _ => False

def g : Assign Nat := fun _ => 0

example : (Formula.forall_ x (P x)).Implies (.exists_ x (P x)) := by
  solution!
   intro D I g
   simp [Formula.denote, P]
   intro hh
   exact ⟨g x, hh (g x)⟩

example :
  ¬ (Formula.exists_ x (.exists_ y (R x y))).Implies
      (Formula.exists_ x (R x x)) := by
  solution!
   intro h
   have h₁ := h Nat intR g
   simp [Formula.denote, R, Assign.update, x, y, varVal, intR] at h₁
   have := h₁ 0 1
   omega

example :
  (Formula.exists_ y (.forall_ x (R x y))).Implies
    (.forall_ x (.exists_ y (R x y))) := by
  solution!
   intro D I g
   simp [Formula.denote, R, Assign.update, x, y, varVal]
   intro b hb a
   exact ⟨b, hb a⟩

end ExEntailsOnlyVars
```
::::

Definimos {name}`Formula.Valid` para {lean}`Formula Variable`, onde os argumentos dos predicados são apenas variáveis. Em {lean}`Formula Variable`, uma estrutura é o par `(D, I)`, o domínio e a interpretação dos símbolos predicativos. Quando há símbolos funcionais, a estrutura passa a ser a tripla`(D, I, F)` onde `F` que diz qual elemento do domínio cada símbolo funcional nomeia. A definição abaixo torna isso explícito: ela quantifica também sobre {name}`FInterp`, e usa {name}`liftAssign` no lugar de {name}`varVal` para avaliar os termos.

```lean
/-- A formula with terms is valid when it is true in every
structure `(D, I, F)` and under every assignment. -/
def Formula.ValidT (f : Formula Term) : Prop :=
  ∀ (D : Type) (I : Denot D) (F : FInterp D) (g : Assign D),
    f.denote I g (liftAssign F)
```

Até aqui, nossa noção de consequência lógica relaciona *duas* fórmulas. Mas o argumento mais comum tem várias premissas: dizemos que `C` é consequência de `P₁, …, Pₙ` quando todo modelo que torna todas as premissas verdadeiras também torna `C` verdadeira. Assim como fizemos em {ref "PL"}[PL], no próximo exercício vamos definir a consequência lógica de um conjunto de premissas em uma conclusão.

::::exercise (rating := 2) (name := "ex-fol-implies-from-list")
Assim como {name}`PL.Formula.impliesL` fez em {ref "PL"}[PL], complete a definição abaixo para que possamos falar de `Δ ⊧ α`, a consequência lógica de uma lista de fórmulas. Use {name}`Formula.ValidT` e {name}`Formula.conjs`.

```lean
def Formula.ImpliesL (hs : List (Formula Term)) (c : Formula Term) : Prop :=
  solution!(Formula.ValidT (.impl (Formula.conjs hs) c))
```
::::

::::exercise (rating := 2) (name := "ex-fol-entails")
Complete os exemplos a seguir que envolvem provar a consequência lógica a partir de uma lista de premissas que envolvem fórmulas com termos. A segunda não vale, e para mostrar isso basta exibir um modelo que satisfaça as duas premissas e refute a conclusão.

```lean
namespace ExEntailsTerms

def R (t u : Term) : Formula Term := .atom "R" [t, u]

def ta : Term := .struct "a" []
def tb : Term := .struct "b" []

def symmR : Formula Term :=
  .forall_ x (.forall_ y (.impl (R tx ty) (R ty tx)))

def intNe : Denot Nat
  | "R", [i, j] => i ≠ j
  | _, _ => False

def fab : FInterp Nat
  | "a", [] => 0
  | "b", [] => 1
  | _, _ => 0

def g : Assign Nat := fun _ => 0

example : Formula.ImpliesL [symmR, R ta tb] (R tb ta) := by
  solution!
   intro D I F g
   simp [Formula.conjs, Formula.denote, symmR, R, liftAssign,
         Assign.update, tx, ty, x, y]
   intro hsym hab
   exact hsym _ _ hab

example : ¬ Formula.ImpliesL [symmR, R ta tb] (R ta ta) := by
  solution!
   intro h
   have h₁ := h Nat intNe fab g
   simp [Formula.conjs, Formula.denote, symmR, R, ta, tb, liftAssign,
         fab, Assign.update, tx, ty, x, y, intNe] at h₁

end ExEntailsTerms
```
::::

```lean
end FOL
```
