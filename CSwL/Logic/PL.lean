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
%%%

```lean
namespace PL
```

# Introdução

A lógica proposicional (PL, "Propositional Logic") trata de fórmulas construídas a partir de variáveis proposicionais usando os conectivos `¬`, `∧`, `∨`, `→` e `↔`. Intuitivamente, uma variável proposicional `p` representa uma sentença ou proposição que pode ser verdadeira ou falsa. Podemos usar lógica proposicional para fugir das impressões das línguas naturais. Queremos tornar precisa a noção de que uma proposição `α` decorre de outra proposição `β`.

Como primeiro exemplo, adaptado de {citet Bib.enderton2001}[], a sentença "traços de potássio foram observados" pode ser traduzida para a linguagem formal como o símbolo `K`. Já para a sentença relacionada "traços de potássio não foram observados", podemos usar `¬ K`. Aqui `¬` é o nosso símbolo de negação, lido como "não". Poderíamos também pensar em traduzir "traços de potássio não foram observados" por algum símbolo novo `J`, mas preferimos decompor sentenças em suas partes atômicas tanto quanto possível. Para uma sentença não relacionada, "a amostra continha cloro" escolhemos o símbolo `C`. Assim, as seguintes sentenças compostas podem ser formalizadas.

- A sentença "Se traços de potássio foram observados, então a amostra não continha cloro." é formalizada como `(K → (¬C))` com símbolo `→` significando "se ... então ...".
- A sentença "A amostra continha cloro, e traços de potássio foram observados." é formalizada como `(C ∧ K)` com símbolo `∧` significando a conjunção "e".
- A sentença "Ou traços de potássio não foram observados, ou a amostra não continha cloro." formalizamos como `((¬K) ∨ (¬C))` com símbolo `∨` significando a disjunção "ou".
- E a sentença "Nem a amostra continha cloro, nem traços de potássio foram observados." é formalizada como `(¬(C ∨ K))` ou `((¬C) ∧ (¬K))`, são *equivalentes*.

Sempre que nos é dada a verdade ou falsidade das partes atômicas de uma sentença, podemos  calcular a verdade ou falsidade da sentença. Suponha, por exemplo, que um químico saia do laboratório e anuncie que observou traços de potássio, mas que a amostra não continha cloro. A partir destas afirmações, podemos então determinar quais das sentenças acima são verdadeiras ou falsas. De fato, podemos construir uma tabela analisando os valores das sentenças para cada possível combinação possível dos valores verdade das proposições atômicas.

:::table +header (align := center)
*
  * `K`
  * `C`
  * `(¬(C ∨ K))`
  * `((¬C) ∧ (¬K))`
*
  * F
  * F
  * T
  * T
*
  * F
  * T
  * F
  * F
*
  * T
  * F
  * F
  * F
*
  * T
  * T
  * F
  * F
:::

::::quiz
Três irmãs - Ana, Maria e Cláudia — foram a uma festa com vestidos de cores
diferentes. Uma vestiu azul, a outra branco, e a terceira, preto.

Chegando à festa, o anfitrião perguntou quem era cada uma delas.

- A de azul respondeu: "Ana é a que está de branco";
- A de branco disse: "Eu sou Maria";
- A de preto respondeu: "Cláudia é quem está de branco".

O anfitrião foi capaz de identificar cada irmã considerando que:

- Ana sempre diz a verdade;
- Maria às vezes diz a verdade;
- Cláudia nunca diz a verdade.

:::quizSolution
Ana é quem veste preto, Cláudia quem veste branco e Maria quem veste azul.
:::

::::

Podemos formalizar o problema anterior em LP.  Uma das motivações é tornar a argumentação  precisa e convincente e, se possível, mecânica.

Para isso, primeiro precisamos identificar as proposições mais elementares do problema e associar cada proposição a um símbolo. Em seguida, precisamos formalizar cada afirmação (ou enunciado) do problema como uma fórmula em LP. Vamos chamar de `Γ` o conjunto destas fórmulas. Também precisamos formalizar a resposta em uma fórmula em LP, vamos chamar de `α`.

Finalmente, precisamos de um método para definir se a fórmula `α` é *consequência lógica* das premissas `Γ`. Um dos métodos possíveis é semântico. Quando para toda possível escolha de valores verdade para os símbolos proposicionais, sempre que todas as premissas forem *verdade* a conclusão deve ser *verdade*. Usamos a notação `Γ ⊧ α` para indicar que `α` é consequência lógica  das premissas.

No problema dos vestidos, o número de personagens e atributos é finito, portanto há apenas um número finito de possíveis proposições. Os números também são pequenos o suficiente para que análise sistemática de todas as combinações de valores verdade seja viável na prática. Para demonstrar que todo número par maior que dois pode ser escrito como uma soma de dois números primos esta estratégia não seria válida.

# Sintaxe

Em Lean, `Prop` é um tipo e proposições particulares também são tipos. A variável `h` abaixo pode ser entendida como um identificador para uma "prova qualquer" da proposição `p ∨ q`.

```lean
section
variable (p q : Prop)

#check p ∨ q
variable (h : p ∨ q)
```

Mas Lean adota o princípio da "irrelevância da prova", ou seja, Lean não distingue diferentes provas de uma proposição. Como consequência, o tipo `Prop` não é computável, não é um "dado" que pode ser manipulado. Por exemplo, não conseguimos extrair os componentes de uma conjunção `a ∧ b`, para fora do tipo `Prop`. Lean proíbe a extração de `Prop` para `Type`, ele sabe que todas as provas de `a ∧ b` são irrelevantes e iguais, então ele não permite que você use uma prova para tomar decisões no mundo dos dados programáveis (`Type`).

```lean +error
variable (a b : Prop)

def cannotExtractLeft (h : a ∧ b) : Type :=
  match h with
  | And.intro ha hb => ha
```

```lean
end
```

Como vamos precisar manipular fórmulas lógicas, teremos que definir um tipo de dado para representar fórmulas proposicionais.

Formalmente, a sintaxe da LP é definida pela BNF abaixo. As variáveis proposicionais (ou símbolos sentenciais) são os `atom`. O uso do sufixo `'` no não-terminal `atom` é uma forma conveniente de expressar que podemos gerar quantos átomos forem necessários.

```bnf
atom ::= "p" | "q" | "r" | atom"'" ;
F    ::= atom
  | "¬" F ("negação")
  | "(" F "∧" F ")" ("conjunção")
  | "(" F "∨" F ")" ("disjunção")
  | "(" F "→" F ")" ("implicação")
  | "(" F "↔" F ")" ("se-somente-se") ;
```

Com esta gramática, podemos gerar fórmulas como `¬¬¬p'''`, `((p ∨ p') ∧ p')`, `(p ∧ (p' ∧ p'''))`. Sem parênteses a gramática pode gerar strings ambíguas: `p ∧ p′ ∨ p″` lê-se tanto como `(p ∧ p′) ∨ p″` quanto como `p ∧ (p′ ∨ p″)`, e a ambiguidade estrutural afeta o significado, como na sentença "era jovem e bonita ou triste". Nem todos os conectivos precisam ser definidos como "primitivos". Em algumas apresentações, o conectivo `→` é definido como uma abreviação para `p → q ≃ ¬ p ∨ q`.

Como anteriormente, iremos formalizar a gramática acima como um tipo indutivo. Um átomo é identificado por um nome, e o nome é uma `String`. Isso dá o inventário ilimitado que a gramática pede sem precisar enumerar símbolo por símbolo.

```lean
inductive Form where
  | atom (name : String)
  | top
  | bot
  | neg (f : Form)
  | conj (f g : Form)
  | disj (f g : Form)
  deriving DecidableEq
```

Vale observar que a biblioteca `cslib` define o tipo `Cslib.Logic.PL.Proposition` que poderia ser usado nesta seção, mas isto introduziria uma complexidade desnecessária. Acima escolhemos não declarar os símbolos `→` e `↔` como construtores do tipo, eles serão funções que criam `Form` a partir de `Form`.

```lean
def Form.impl (f g : Form) : Form := .disj (.neg f) g
def Form.equi (f g : Form) : Form :=
  .conj (Form.impl f g) (Form.impl g f)
```

A conjunção e a disjunção são binárias. Poderiam receber uma lista de fórmulas `conj (fs : List Form)`, mas um construtor que guarda uma `List Form` dentro do próprio tipo o torna um indutivo _nested_, mais complicado em Lean. Mas podemos definir funções que recebem listas de fórmulas e constrem conjunções e disjunções. Abaixo `top`/`bot` são a base da recursão de `conjs`/`disjs`. Uma conjunção vazia é sempre verdadeira, uma disjunção vazia é sempre falsa.

```lean
def Form.conjs : List Form → Form
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Form.conjs fs)

def Form.disjs : List Form → Form
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Form.disjs fs)
```

::::exercise (rating := 1) (name := "bangu-form")
Três pessoas são suspeitas de torcer pelo Bangu F.C. Aparecido entrevistou os três, para tentar descobrir, e obteve os seguintes depoimentos:

- Auro: Joaquim não torce pelo BFC e Cláudia torce pelo BFC.
- Joaquim: Se Auro não torce pelo BFC, Cláudia também não torce pelo BFC.
- Cláudia: Eu torço pelo BFC, mas pelo menos um dos outros não torce pelo BFC.

Termine a formalização dos depoimentos construindo uma expressão no tipo `Form`.

```lean
def A : Form := Form.atom "Auro"
def J : Form := Form.atom "Joaquim"
def C : Form := Form.atom "Claudia"

def depo1 : Form := solution!(.conj (.neg J) C)
def depo2 : Form := solution!(.impl (.neg A) (.neg C))
def depo3 : Form := solution!(.conj C (.disj (.neg A) (.neg J)))
```
::::


::::exercise (rating := 1) (name := "exclusive-or")

A expressão `p ∨ q` é verdadeira mesmo quando `p` e `q` são ambos verdadeiros. Em português, "ou" costuma ser exclusivo, como em "Você pode ficar com o sorvete ou com o algodão-doce, mas não com os dois." Defina um conectivo `xor` para "ou exclusivo", usando os conectivos já definidos.

```lean
def Form.xor (f g : Form) : Form :=
  solution!(.disj (.conj f (.neg g)) (.conj (.neg f) g))
```
::::

O tipo `Form` é um `inductive`. Um valor de `Form` é dado. Nenhum dos exercícios abaixo seriam possíveis em `Prop`. Não há como perguntar "quantos `∧` tem esta proposição" a um valor de tipo `Prop`, porque `Prop` não guarda a fórmula que o provou.  Vamos definir duas fórmulas para usar nos exercícios seguintes.

```lean
def form1 : Form :=
  .conj (.atom "p") (.neg (.atom "p"))

def form2 : Form :=
  Form.disjs [.atom "p1", .atom "p2", .atom "p3", .atom "p4"]

#eval form2
```

::::exercise (rating := 1) (name := "count-operators")
Implemente uma função `opsNr` para contar o número de operadores de uma fórmula.

```lean
def Form.opsNr : Form → Nat :=
  solution!(fun
    | .atom _ => 0
    | .top => 0
    | .bot => 0
    | .neg f => 1 + f.opsNr
    | .conj f g => 1 + f.opsNr + g.opsNr
    | .disj f g => 1 + f.opsNr + g.opsNr)

theorem opsNr_test : form1.opsNr = 2 := solution!(by decide)
```
::::

::::exercise (rating := 1) (name := "formula-depth")
Implemente uma função `depth` para calcular a profundidade da árvore de análise de uma fórmula.

```lean
def Form.depth : Form → Nat :=
  solution!(fun
    | .atom _ => 0
    | .top => 0
    | .bot => 0
    | .neg f => 1 + f.depth
    | .conj f g => 1 + max f.depth g.depth
    | .disj f g => 1 + max f.depth g.depth)

theorem depth_test : form1.depth = 2 := solution!(by decide)
```
::::

::::exercise (rating := 2) (name := "collect-atoms")

Implemente `propNames` para coletar a lista de nomes de átomos proposicionais que ocorrem numa fórmula. A lista resultante deve estar ordenada e sem repetições.

```lean
private def Form.propNamesRaw : Form → List String :=
  solution!(fun
    | .atom name => [name]
    | .top => []
    | .bot => []
    | .neg f => f.propNamesRaw
    | .conj f g => f.propNamesRaw ++ g.propNamesRaw
    | .disj f g => f.propNamesRaw ++ g.propNamesRaw)

def Form.propNames (f : Form) : List String :=
  solution!(f.propNamesRaw.eraseDups.mergeSort (· ≤ ·))
```
::::

# Semântica

Vimos que a noção de "derivação" é diretamente implementada no Lean. Isto é, dizemos que `P ∧ Q ⊢ P` porque conseguimos construir uma prova de `P` a partir da existência de uma prova de `P ∧ Q`.

Mas as regras de derivação que usamos correspondem a (ou são justificadas por) uma noção semântica de *consequência lógica*, `P ∧ Q ⊧ P`. Entendemos que `P` deve ser verdade sempre que `P ∧ Q` for verdade, para qualquer possível tradução de `P` e `Q` de volta para expressões em uma linguagem natural. Para formalizar esta noção de "todas as possíveis traduções", vamos precisar de um processo para avaliar fórmulas lógicas em valores verdade.

Vamos chamar de *valorações* um mapeamento de símbolos proposicionais no conjunto dos booleanos, que em Lean correspondem aos valores `True` e `False` do tipo `Bool`.

Uma valoração é uma lista de pares, e um átomo ausente da lista conta como
falso.

```lean
abbrev Valuation := List (String × Bool)
```

Se `V` é uma valoração, ela se estende a uma função que mapea qualquer fórmula para um valor de verdade. A extensão é definida por recursão sobre a estrutura da fórmula, um caso por construtor. Os construtores `top` e `bot` são constantes, nenhuma valoração os afeta.

```lean
def Form.eval (f : Form) (v : Valuation) : Bool :=
  match f with
  | .atom name => (v.lookup name).getD false
  | .top => true
  | .bot => false
  | .neg g => !g.eval v
  | .conj g h => g.eval v && h.eval v
  | .disj g h => g.eval v || h.eval v
```

Chamamos de *tautologias* (válidas) as fórmulas que são sempre verdade, independente da valoração. A notação usual para "`α` é uma tautologia" é `⊨ α`. As fórmulas que são sempre falsas para toda valoração são chamadas de *contradições* (ou insatisfatíveis) e podemos concluir que se `α` é uma contradição, então `⊨ ¬ α` (sua negação é válida). Uma fórmula é *satisfatível* se há ao menos uma valoração que a torna verdadeira. Uma fórmula é *contingente* se é satisfatível mas não é uma tautologia. Toda tautologia é satisfatível, mas nem toda fórmula satisfatível é uma tautologia.

```lean
def taut  : Form :=  (.disj (.atom "p") (.neg (.atom "p")))
def unsat : Form :=  (.conj (.atom "p") (.neg (.atom "p")))

#eval taut.eval [("p1", True)]
#eval taut.eval [("p1", False)]
#eval unsat.eval [("p", False)]
#eval unsat.eval [("p", True)]
```

A função a seguir gera a lista de todas as valorações sobre o conjunto dos nomes de átomos presentes em um termo do tipo `Form`. Com estas funções, podemos construir a tabela verdade de uma fórmula.

```lean
def genVals : List String → List Valuation
  | [] => [[]]
  | name :: names =>
      (genVals names).map ((name, true) :: ·)
      ++ (genVals names).map ((name, false) :: ·)

def Form.allVals (f : Form) : List Valuation :=
  genVals f.propNames

#eval List.zip form2.allVals (form2.allVals.map (form2.eval ·))
```

Para decidir se uma fórmula é tautologia, satisfatível ou contradição, podemos percorrer todas as valorações relevantes, que são finitas, porque uma fórmula tem finitos átomos.

```lean
def Form.tautology (f : Form) : Bool :=
  f.allVals.all (fun v => f.eval v)

def Form.satisfiable (f : Form) : Bool :=
  f.allVals.any (fun v => f.eval v)

def Form.contradiction (f : Form) : Bool :=
  !f.satisfiable

#eval (form1.contradiction,
       (Form.neg form1).tautology,
       form2.satisfiable)
```

A seguir, escrevemos implies para a relação de consequência lógica, chamando atenção para a relação entre `P ⊨ Q` e `⊨ P → Q`. Uma proposição `Q` é consequência lógica de `P` se, e somente se, a implicação `P → Q` é uma tautologia. Se `P → Q ≡ ¬ P ∨ Q ≡ ¬ (P ∧ ¬ Q)` então podemos também dizer que `P ⊧ Q` se e somente se `⊨ ¬ (P ∧ ¬ Q)`.

Podemos estender para uma consequência lógica de fórmulas `{P₁, …, Pₙ} ⊧ α`, indicando que toda valoração que torna as fórmulas `P₁, …, Pₙ` verdadeiras também torna `α` verdadeira. O que equivale afirmar que a implicação da conjunção das premissas na conclusão é válida `⊧ (P₁ ∧ … ∧ Pₙ) → α`.

Duas fórmulas `α` e `β` são *logicamente equivalentes*, escrevemos `α ≡ β`, se têm o mesmo valor de verdade para toda valoração possível. Segue da definição que todas as tautologias são logicamente equivalentes entre si, e o mesmo vale para as contradições.

```lean
def Form.implies (f g : Form) : Bool :=
  (Form.conj f (.neg g)).contradiction

def Form.equivalent (f g : Form) : Bool :=
  f.implies g && g.implies f
```

A nossa definição de `Form.impl` acima pode ser justificada pelas equivalência abaixo. A relação de equivalência entre fórmulas é transitiva.

```lean
#eval
  let p := (.atom "p")
  let q := (.atom "q")

  let α := (Form.impl p q)
  let β := Form.disj (.neg p) q
  let γ := Form.neg $ .conj p (.neg q)

  let r1 := [Form.equivalent α β, Form.equivalent β γ, Form.equivalent α γ]
  let r2 := [Form.implies p (.disj p q), (Form.impl p (.disj p q)).tautology]
  let r3 := [Form.implies (.disj p q) p, (Form.impl (.disj p q) p).tautology]
  let r4 := [Form.implies (Form.conj p (.neg p)) q]
  (r1, r2, r3, r4)
```

A semântica da lógica proposicional também pode ser dada em formato de
*atualização*. Fixe primeiro um conjunto de valorações relevantes como
estado corrente e depois defina uma função de atualização que deixa apenas as
valorações que satisfazem uma dada fórmula.

```lean
def update (vals : List Valuation) (f : Form) : List Valuation :=
  vals.filter (fun v => f.eval v)
```

Atualizar o estado de todas as valorações relevantes com uma contradição não deixa nada; atualizar com uma tautologia não tira nada. Atualizar com uma fórmula contingente tira alguma coisa, e atualizar com sua negação tira o complemento.

```lean
#eval (update form1.allVals form1)
#eval (update form1.allVals (.neg form1))
#eval (form2.allVals.length,
       (update form2.allVals form2).length,
       (update form2.allVals (.neg form2)))
```

::::exercise (rating := 1) (name := "valuation-table")
Seja `V` dada por `p ↦ 0`, `q ↦ 1`, `r ↦ 1`. Dê os valores das fórmulas
seguintes: `¬p ∨ p`, `p ∧ ¬p`, `¬¬(p ∨ ¬r)`, `¬(p ∧ ¬r)`, `p ∨ (q ∧ r)`.

```lean
namespace ValuationTableEx

def p := Form.atom "p"
def q := Form.atom "q"
def r := Form.atom "r"

def vs : Valuation :=
  [("p", false), ("q", true), ("r", true)]

example :
 (Form.disj (.neg p) p).eval vs = solution!(true) :=
 by decide

example :
 (Form.neg (.neg (.conj p (.neg r)))).eval vs = solution!(false) :=
 by decide

example :
 (Form.neg (.conj p (.neg r))).eval vs = solution!(true) :=
 by decide

example :
 (Form.disj p (.conj q r)).eval vs = solution!(true) :=
 by decide

end ValuationTableEx
```
::::

::::exercise (rating := 1) (name := "negated-tautology")
Explique por que a negação de uma tautologia é sempre uma contradição, e vice-versa.

:::solution
Uma fórmula `F` é tautologia quando `F.eval v = true` para toda `v`. Como `(Form.neg F).eval v = !(F.eval v)`, isso vale exatamente quando `(Form.neg F).eval v = false` para toda `v`, que é a definição de contradição. O argumento se lê igual nas duas direções.
:::
::::

::::exercise (rating := 2) (name := "implies-list")
Estenda a checagem de implicação proposicional para o caso de uma lista de premissas. O tipo é `Form.impliesL : List Form → Form → Bool`.

```lean
def Form.impliesL (ps : List Form) (c : Form) : Bool :=
  solution!((Form.conjs ps).implies c)
```
::::

::::exercise (rating := 1) (name := "bangu-proof")
Como podemos identificar os torcedores do Bangu e os não torcedores, supondo que todos os depoimentos são verdadeiros?

:::solution
```lean
#eval Form.impliesL [depo1, depo2, depo3] A
#eval Form.impliesL [depo1, depo2, depo3] J
#eval Form.impliesL [depo1, depo2, depo3] C
```
:::
::::


# Traduzindo `Form` para `Prop`

O capítulo começou distinguindo raciocinar em lógica proposicional de raciocinar sobre fórmulas dela. Temos que `p ∧ q` é uma proposição, do tipo `Prop` e `Form.conj p q` é um termo (dado) do tipo `Form`. A ligação é uma função que interpreta cada fórmula como a proposição que ela afirma, dada uma valoração.

```lean
def Form.denote (f : Form) (v : Valuation) : Prop :=
  match f with
  | .atom name => (v.lookup name).getD false = true
  | .top => True
  | .bot => False
  | .neg g => ¬ g.denote v
  | .conj g h => g.denote v ∧ h.denote v
  | .disj g h => g.denote v ∨ h.denote v
```

Repare no que cada caso faz: ele troca um construtor de `Form` pelo conectivo correspondente de `Prop`. O `conj` do dado vira o `∧` da proposição, o `neg` vira o `¬`. O teorema que fecha o capítulo diz que as duas leituras concordam: computar dá `true` exatamente quando a proposição vale.

```lean
theorem Form.eval_iff_denote (f : Form) (v : Valuation) :
    f.eval v = true ↔ f.denote v := by
  induction f with
  | atom name => simp [Form.eval, Form.denote]
  | top => simp [Form.eval, Form.denote]
  | bot => simp [Form.eval, Form.denote]
  | neg g ih =>
      simp only [Form.eval, Form.denote]
      rw [← ih]
      simp
  | conj g h ihg ihh =>
      simp [Form.eval, Form.denote, ihg, ihh]
  | disj g h ihg ihh =>
      simp [Form.eval, Form.denote, ihg, ihh]
```

```lean
end PL
```
