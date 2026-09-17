import CSwLMeta
import Bib
import Mathlib.Tactic.ByContra
import CSwLCompat

open Verso.Genre Manual
open CSwLMeta

set_option verso.code.warnLineLength 100

#doc (Manual) "Lógica proposicional" =>
%%%
tag := "PL"
file := "PL"
%%%

```lean
namespace PL
```

# Introdução
%%%
tag := "pl-intro"
%%%

Em {ref "Proof"}["Proof"] as fórmulas proposicionais foram escritas diretamente como termos do tipo `Prop`, e usando táticas construimos provas de proposições `α` a partir de um conjunto de hipóteses `Γ`. Isto é, mostramos como derivar `α` a partir de `Γ`, isto é `Γ ⊢ α`.

Mas em Lean, `Prop` é um tipo e proposições particulares também são tipos. A variável `h` abaixo pode ser entendida como um identificador para uma "prova qualquer" da proposição `p ∧ q`. E Lean adota o princípio da "irrelevância da prova", ou seja, Lean não distingue diferentes provas de uma proposição. Como consequência, o tipo `Prop` não é computável, não é um "dado" que pode ser manipulado. Por exemplo, não conseguimos extrair os componentes de uma conjunção `a ∧ b`. Lean sabe que todas as provas de `a ∧ b` são irrelevantes e iguais, então ele não permite que você use uma prova para tomar decisões no mundo dos dados programáveis (`Type`). Em outras palavras, não podemos realizar casamento de padrões em `h` abaixo.

```lean +error
section
variable (p q : Prop)

variable (h : p ∧ q)
#check p ∧ q
#check h

def doesNotWork (h : p ∧ q) : Type :=
  match h with
  | And.intro ha hb => ha

end
```

Nesta seção, queremos manipular fórmulas e decidir quando uma fórmula `α` é consequência lógica de `β`, isto é `β ⊧ α `. A noção de consequência lógica é semântica. Para toda possível escolha de valores verdade para os símbolos proposicionais em `α` e `β`, sempre que `β` for verdade, `α` deve ser verdade. Para _computar_ o valor verdade de uma fórmula, vamos precisar manipula a formula como dado, e calcular seu valor verdade a partir do mapeamento de variáveis proposicionais em valores verdade. Em tempo, a relação dentre duas fórmulas pode ser naturalmente estendida para uma relação entre um conjunto de fórmulas `Γ` e uma fórmula, `Γ ⊧ α`.

Em um problema com um número finito de proposições, e os números costumam ser pequenos o suficiente para que a análise sistemática de todas as combinações de valores verdade seja viável na prática. Para demonstrar que todo número par maior que dois pode ser escrito como uma soma de dois números primos esta estratégia não seria válida.


# Sintaxe de Lógica Proposicional
%%%
tag := "pl-syntax"
%%%

Para construir fórmulas como dados, não poderemos mais usar a notação de Lean disponível para os termos do tipo `Prop`. Quando escrevemos `p ∧ q`, o símbolo `∧` é um operador infixado (aparece no meio dos argumentos) e representa o construtor {lean}`And.intro` do tipo {lean}`And`. Os operadores, para serem usados de forma infixada, precisam ter um mecanismo de precedência para permitir que possamos escrever termos ambiguos como `p ∧ q ∧ r` que terão sua leitura associada a `p ∧ (q ∧ r)` e não `(p ∧ q) ∧ r`. Nada disso estará ao nosso dispor.

Nossas fórmulas serão representadas por termos do tipo indutivo `Formula`. Um átomo é identificado por um nome, e o nome é uma {lean}`String`. Isso dá o inventário ilimitado que a gramática pede sem precisar enumerar símbolo por símbolo.

```lean
inductive Formula where
  | atom (name : String)
  | top
  | bot
  | neg (f : Formula)
  | conj (f g : Formula)
  | disj (f g : Formula)
  deriving DecidableEq, Repr
```

Os contrutores {name}`Formula.top` e {name}`Formula.bot` representam as proposições "sempre verdadeira" e "sempre falsa". São objetos sintáticos que serão sempre interpretados como os valores verdade {lean}`true` e {lean}`false` na semântica. Com este tipo, podemos representar fórmulas arbitrariamente complexas.

```lean
#eval
  let p  : Formula := .atom "p"
  let q  : Formula := .atom "q"
  let f₁ : Formula := .neg (.neg p)
  let f₂ : Formula := .disj (.neg p) q
  Formula.conj f₁ f₂
```

Como não temos símbolos infixados, não temos ambiguidade. As duas possíveis interpretações para a sentença ambigua em português "Maira é jovem e bonita ou triste" seriam:

```lean
namespace Maria

def j : Formula := .atom "MJ"
def b : Formula := .atom "MB"
def t : Formula := .atom "MT"

#eval Formula.conj j (.disj b t)
#eval Formula.disj (.conj j b) t

end Maria
```

Vale observar que a biblioteca `cslib` define o tipo `Cslib.Logic.PL.Proposition` que poderia ser usado nesta seção, mas isto introduziria uma complexidade desnecessária.

Nem todos os conectivos precisam ser definidos como "primitivos". Como vimos na seção {ref "pl-lean"}[pl-lean] a implicação pode ser definida como uma dijunção. E a dupla implicação como uma conjunção de implicações.

```lean
def Formula.impl (f g : Formula) : Formula := .disj (.neg f) g
def Formula.iff (f g : Formula) : Formula :=
  .conj (Formula.impl f g) (Formula.impl g f)
```

A conjunção e a disjunção são binárias. Poderiam receber uma lista de fórmulas `conj (fs : List Formula)`, mas um construtor que guarda uma `List Form` dentro do próprio tipo o torna um indutivo _nested_, mais complicado de manipular em Lean. Mas podemos definir funções que recebem listas de fórmulas e constrem conjunções e disjunções. Abaixo `top`/`bot` são a base da recursão de `conjs`/`disjs`.

```lean
def Formula.conjs : List Formula → Formula
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Formula.conjs fs)

def Formula.disjs : List Formula → Formula
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Formula.disjs fs)
```

Note que {name}`Formula.bot` é o elemento neutro da dijunção, `bot ∨ a`. E {name}`Formula.top` é o elemento neutro da conjunção, `top ∧ a`. Uma conjunção vazia é sempre verdadeira, uma disjunção vazia é sempre falsa. O que sugere as implementações alternativas a seguir.

```lean
def Formula.conjs₁ (fs : List Formula) : Formula :=
  fs.foldl .conj .top

def Formula.disjs₁ (fs : List Formula) : Formula :=
  fs.foldl .disj .bot
```

:::exercise (rating := 1) (name := "bangu-form")
Três pessoas são suspeitas de torcer pelo Bangu F.C. Aparecido entrevistou os três, para tentar descobrir, e obteve os seguintes depoimentos:

- Auro: Joaquim não torce pelo BFC e Cláudia torce pelo BFC.
- Joaquim: Se Auro não torce pelo BFC, Cláudia também não torce pelo BFC.
- Cláudia: Eu torço pelo BFC, mas pelo menos um dos outros não torce pelo BFC.

Termine a formalização dos depoimentos construindo uma expressão no tipo {name}`Formula`.

```lean
namespace Bangu

def A : Formula := .atom "Auro"
def J : Formula := .atom "Joaquim"
def C : Formula := .atom "Claudia"

def depo1 : Formula := solution!(.conj (.neg J) C)
def depo2 : Formula := solution!(.impl (.neg A) (.neg C))
def depo3 : Formula := solution!(.conj C (.disj (.neg A) (.neg J)))

end Bangu
```
:::

:::exercise (rating := 1) (name := "exclusive-or")
A expressão `p ∨ q` é verdadeira mesmo quando `p` e `q` são ambos verdadeiros. Em português, "ou" costuma ser exclusivo, como em "Você pode ficar com o sorvete ou com o algodão-doce, mas não com os dois." Defina um conectivo `xor` para "ou exclusivo", usando os conectivos já definidos.

```lean
def Formula.xor (f g : Formula) : Formula :=
  solution!(.disj (.conj f (.neg g)) (.conj (.neg f) g))
```
:::

Um termo do tipo {lean}`Formula` é um dado. Nenhum dos exercícios abaixo seriam possíveis em `Prop`. Não há como perguntar "quantos `∧` tem esta proposição" a um valor de tipo `Prop`, porque `Prop` não guarda a fórmula que o provou.  Vamos definir duas fórmulas para usar nos exercícios seguintes.

```lean
def form1 : Formula :=
  .conj (.atom "p") (.neg (.atom "p"))

def form2 : Formula :=
  .disjs [.atom "p1", .atom "p2", .atom "p3", .atom "p4"]

def form3 : Formula :=
  let p : Formula := .atom "p"
  let q : Formula := .atom "q"
  .iff (.impl p q ) (.disj (.neg p) q)
```

:::exercise (rating := 1) (name := "count-operators")
Implemente uma função `opsNr` para contar o número de operadores de uma fórmula. a tática {tactic}`decide` é como pedir ao Lean para executar a decisão de uma proposição booleana e, se o resultado for true, transformar esse resultado em uma prova.

```lean
def Formula.opsNr : Formula → Nat :=
  solution!(fun
    | .atom _ => 0
    | .top => 0
    | .bot => 0
    | .neg f => 1 + f.opsNr
    | .conj f g => 1 + f.opsNr + g.opsNr
    | .disj f g => 1 + f.opsNr + g.opsNr)

example : form2.opsNr = 3 := by decide
```
:::

:::exercise (rating := 1) (name := "formula-depth")
Implemente uma função `depth` para calcular a profundidade da árvore de análise de uma fórmula.

```lean
def Formula.depth : Formula → Nat :=
  solution!(fun
    | .atom _ => 0
    | .top => 0
    | .bot => 0
    | .neg f => 1 + f.depth
    | .conj f g => 1 + max f.depth g.depth
    | .disj f g => 1 + max f.depth g.depth)

example : form2.depth = 3 := by decide
```
:::

:::exercise (rating := 2) (name := "collect-atoms")
Implemente `propNames` para coletar a lista de nomes de átomos proposicionais que ocorrem numa fórmula. A lista resultante deve estar ordenada e sem repetições. O exemplo pode ser provado com {tactic}`native_decide`.

```lean
def Formula.propNamesRaw (f : Formula) : List String :=  solution!(
  match f with
  | .atom name => [name]
  | .top => []
  | .bot => []
  | .neg f => f.propNamesRaw
  | .conj f g => f.propNamesRaw ++ g.propNamesRaw
  | .disj f g => f.propNamesRaw ++ g.propNamesRaw)

def Formula.propNames (f : Formula) : List String :=
  solution!(f.propNamesRaw.eraseDups.mergeSort (· ≤ ·))

example : form1.propNames == ["p"] := solution!(by native_decide)
```
:::


# Semântica de Lógica Proposicional
%%%
tag := "pl-semantics"
%%%

Todas as regras de derivação que usamos em {ref "Proof"}["Proof"] são justificadas por uma noção semântica de *consequência lógica*. Entendemos que `P` deve ser verdade sempre que `P ∧ Q` for verdade, para qualquer possível tradução de `P` e `Q` de volta para expressões em uma linguagem natural, por isso aceitamos `P ∧ Q ⊧ P`.  Para formalizar esta noção de "todas as possíveis traduções", vamos precisar de um processo para avaliar fórmulas lógicas em valores verdade.

Vamos chamar de *valorações* um mapeamento de símbolos proposicionais no conjunto dos booleanos, que em Lean correspondem aos valores `True` e `False` do tipo `Bool`.

Podemos representar uma valoração como uma lista de pares, e um átomo ausente da lista conta como falso.

```lean
abbrev Valuation := List (String × Bool)
```

Se `V` é uma valoração, ela se estende a uma função que mapea qualquer fórmula para um valor de verdade. A extensão é definida por recursão sobre a estrutura da fórmula, um caso por construtor. Os construtores {name}`Formula.top` e {name}`Formula.bot` são constantes, nenhuma valoração os afeta. Se um átomo ocorrer mais de uma vez, vamos assumir que seu valor verdade é a primeira ocorrência dele na lista, isto corresponde ao comportamento da função {name}`List.lookup`.

```lean
/-- The evaluation of a formula `f` in a valuation `v`. -/
def Formula.eval (f : Formula) (v : Valuation) : Bool :=
  match f with
  | .atom name => (v.lookup name).getD false
  | .top => true
  | .bot => false
  | .neg g => !g.eval v
  | .conj g h => g.eval v && h.eval v
  | .disj g h => g.eval v || h.eval v
```

Chamamos as fórmulas que são sempre verdade para qualquer valoração de suas variáveis proposicionais de *tautologias*, ou, simplesmente, fórmulas *válidas*. Se `α` é uma tautologia, significa que `⊨ α`, não depende de nenhuma hipótese para ser verdade. As fórmulas que são sempre falsas para toda valoração são chamadas de *contradições* (ou insatisfatíveis). Uma fórmula é *satisfatível* se há pelo menos uma valoração que a torna verdadeira. Uma fórmula é *contingente* se existe pelo menos uma valoração que torna a fórmula verdadeira e pelo menos uma que a torna falsa. Podemos concluir que se `α` é uma contradição, então `⊨ ¬ α` (sua negação é válida). Toda tautologia é satisfatível, mas nem toda fórmula satisfatível é uma tautologia.

:::exercise (rating := 1) (name := "valuations")
Construa as valorações `vs1` e `vs2` de tal forma que os exemplos possam ser provados com a tática {tactic}`decide`.

```lean
namespace TestVals

def p : Formula := .atom "p"
def q : Formula := .atom "p"
def r : Formula := .atom "r"

def form3 : Formula := .disj p (.conj q r)

def form4 : Formula := .neg (.conj p (.neg q))

def form5 : Formula :=
  .conj (.atom "a") (.impl (.neg (.atom "b")) (.atom "c"))

def vs1 : List (String × Bool) := solution!([("p", true),("q", true)])
def vs2 : List (String × Bool) := solution!([("a", true),("b", true)])

example : form3.eval vs1 = true := solution!(by decide)
example : form4.eval vs1 = true := solution!(by decide)
example : form5.eval vs2 = true := solution!(by decide)

end TestVals
```
:::

A função a seguir gera a lista de todas as valorações sobre o conjunto dos nomes de átomos presentes em um termo do tipo {name}`Formula`.

```lean
def genVals : List String → List Valuation
  | [] => [[]]
  | n :: ns =>
    let vs := (genVals ns)
    vs.map ((n, true) :: ·) ++ vs.map ((n, false) :: ·)

/-- return all possible valuations for `f`. -/
def Formula.allVals (f : Formula) : List Valuation :=
  genVals f.propNames
```

Com estas funções, podemos construir a tabela verdade de uma fórmula.

```lean
#eval List.zip form1.allVals (form2.allVals.map (form2.eval ·))
```

Para decidir se uma fórmula é tautologia, satisfatível ou contradição, podemos percorrer todas as valorações possíveis, que são finitas, porque uma fórmula tem finitos átomos.

```lean
def Formula.tautology (f : Formula) : Bool :=
  f.allVals.all (fun v => f.eval v)

def Formula.satisfiable (f : Formula) : Bool :=
  f.allVals.any (fun v => f.eval v)

def Formula.contradiction (f : Formula) : Bool :=
  !f.satisfiable

#eval form1.contradiction
#eval (Formula.neg form1).tautology
#eval form1.satisfiable
```

E como já sabemos da seção {ref "pl-lean"}[pl-lean], podemos mostrar que {name}`form3` é uma tautologia.

```lean
#eval form3.tautology
```

:::exercise (rating := 1) (name := "def-contingente")
Complete a definição de fórmula contingente. Para provar o exemplo, use {tactic}`native_decide`.

```lean
def Formula.contingent (f : Formula) : Bool :=
  solution!(f.satisfiable && !f.tautology)

example : (Formula.atom "q").satisfiable = true := by
  solution!(native_decide)
```
:::

A seguir, escrevemos implies para a relação de consequência lógica, chamando atenção para a relação entre `P ⊨ Q` e `⊨ P → Q`. Uma proposição `Q` é consequência lógica de `P` se, e somente se, a implicação `P → Q` é uma tautologia. Se `P → Q ≡ ¬ P ∨ Q ≡ ¬ (P ∧ ¬ Q)` então podemos também dizer que `P ⊧ Q` se e somente se `⊨ ¬ (P ∧ ¬ Q)`.

Podemos estender para uma consequência lógica de fórmulas `{P₁, …, Pₙ} ⊧ α`, indicando que toda valoração que torna as fórmulas `P₁, …, Pₙ` verdadeiras também torna `α` verdadeira. O que equivale afirmar que a implicação da conjunção das premissas na conclusão é válida `⊧ (P₁ ∧ … ∧ Pₙ) → α`.

Duas fórmulas `α` e `β` são *logicamente equivalentes*, escrevemos `α ≡ β`, se têm o mesmo valor de verdade para toda valoração possível. Segue da definição que todas as tautologias são logicamente equivalentes entre si, e o mesmo vale para as contradições.

```lean
def Formula.implies (f g : Formula) : Bool :=
  (Formula.conj f (.neg g)).contradiction

def Formula.equivalent (f g : Formula) : Bool :=
  f.implies g && g.implies f
```

Podemos mostrar que toda tautologia é equivalente a {name}`Formula.top`, consequência das definições acima. Note que provamos em Lean (como meta-linguagem) uma equivalência sobre definições de nossa linguagem de PL.

```lean
open Formula in

theorem top_equiv_taut (f : Formula)
 : f.tautology ↔ f.equivalent top := by
  have hv : (conj top (neg f)).allVals = f.allVals := rfl
  simp only [equivalent, implies,
    contradiction, satisfiable, tautology, hv, eval]
  simp [List.all_eq_true]
```

:::exercise (rating := 2) (name := "pl-equivalent")
Complete a definição de `Feq2` com uma fómula equivalente mas sintaticamente diferente de `Feq1` e feche o exemplo com {tactic}`native_decide`.

```lean
namespace Eqs
def p : Formula := .atom "p"
def q : Formula := .atom "q"

def F0 : Formula := .neg (.neg p)
def F1 : Formula := solution!(p)
def F2 : Formula := .neg (.iff p q)
def F3 : Formula := solution!(.disj (.conj (.neg p) q) (.conj (.neg q) p))

example : F0.equivalent F1 = true :=
  solution!(by native_decide)

example : F2.equivalent F3 = true :=
  solution!(by native_decide)
end Eqs
```
:::

A semântica da lógica proposicional também pode ser dada em formato de *atualização*. Fixe primeiro um conjunto de valorações como estado corrente e depois defina uma função de atualização que deixa apenas as valorações que satisfazem uma dada fórmula.

```lean
def update (vals : List Valuation) (f : Formula) : List Valuation :=
  vals.filter (fun v => f.eval v)
```

Atualizar o estado de todas as valorações com uma contradição não deixa nada; atualizar com uma tautologia não tira nada. Atualizar com uma fórmula contingente tira alguma coisa, e atualizar com sua negação tira o complemento.

```lean
#eval form1.allVals
#eval (update form1.allVals form1)
#eval (update form1.allVals (.neg form1))
#eval (update form2.allVals (.neg form2))
```

::::exercise (rating := 2) (name := "implies-list")
Estenda a checagem de implicação proposicional para o caso de uma lista de premissas. O tipo é `Form.impliesL : List Form → Form → Bool`.

```lean
def Formula.impliesL (ps : List Formula) (c : Formula) : Bool :=
  solution!((Formula.conjs ps).implies c)
```
::::

:::exercise (rating := 1) (name := "bangu-proof")
Complete a definição de `banguSolution` para que a fórmula represente a solução do problema dos torcedores do Bangu F.C. assumindo que os 3 depoimentos foram verdadeiros. A prova do exemplo é completada com {tactic}`native_decide`.

```lean
namespace Bangu

def banguSolution : Formula := solution!(.conjs [A, (.neg J), C])

example : Formula.impliesL [depo1, depo2, depo3] banguSolution = true :=
  solution!(by native_decide)

end Bangu
```
:::


# Traduzindo `Formula` para `Prop`
%%%
tag := "pl-to-prop"
%%%

O mapeamento de {lean}`Formula` em `Prop` pode ser definido como uma função que interpreta cada fórmula como a proposição que ela afirma, dada uma valoração.

```lean
def Formula.denote (f : Formula) (v : Valuation) : Prop :=
  match f with
  | .atom name => (v.lookup name).getD false = true
  | .top => True
  | .bot => False
  | .neg g => ¬ g.denote v
  | .conj g h => g.denote v ∧ h.denote v
  | .disj g h => g.denote v ∨ h.denote v
```

Repare no que cada caso faz: ele troca um construtor de {lean}`Formula` pelo conectivo correspondente de `Prop`. O {lean}`Formula.conj` do dado vira o `∧` da proposição, o {name}`Formula.neg` vira o `¬`. O teorema que fecha o capítulo diz que as duas leituras concordam. Dada uma valoração, computar o valor verdade de uma fórmula resulta em `true` exatamente quando a proposição resultande da fórmula para a mesma valoração tem prova.

```lean
open Formula in

theorem Formula.eval_iff_denote (f : Formula) (v : Valuation) :
    f.eval v = true ↔ f.denote v := by
  induction f with
  | atom name => simp [eval, denote]
  | top => simp [eval, denote]
  | bot => simp [eval, denote]
  | neg g ih =>
      simp only [eval, denote]
      rw [← ih]
      simp
  | conj g h ihg ihh => simp [eval, denote, ihg, ihh]
  | disj g h ihg ihh => simp [eval, denote, ihg, ihh]
```

```lean
end PL
```
