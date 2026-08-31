import CSwLMeta
import Bib
import Mathlib.Tactic.ByContra

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Lógica proposicional" =>
%%%
tag := "PL"
%%%

```lean
namespace PL
```

A lógica proposicional (LP) ou cálculo sentencial, é um sistema formal no qual as fórmulas representam proposições que podem ser formadas pela combinação de proposições atômicas usando conectivos lógicos e um sistema de regras de derivação, que permite que certas fórmulas sejam estabelecidas como teoremas do sistema formal.

Há duas maneiras de tratar disso em Lean, e é preciso não confundi-las. Uma é
*raciocinar em* lógica proposicional: usar os conectivos para enunciar e
demonstrar coisas, como já vínhamos fazendo. A outra é *raciocinar sobre* ela:
tomar as fórmulas como dado, sobre o qual se computa. Este capítulo faz as duas,
nessa ordem, e a primeira seção é a primeira.

# Regras de dedução, e as táticas que são elas

Cada conectivo vem com dois tipos de regra: as de *introdução*, que dizem como
construir uma prova cuja conclusão usa o conectivo, e as de *eliminação*, que
dizem como usar uma prova cuja hipótese o usa. É a organização da dedução
natural, e as táticas do Lean são exatamente essas regras — cada uma tem nome
próprio na tradição lógica, e vale saber qual é.

Nesta seção `P`, `Q` e `R` são proposições quaisquer.

```lean
variable (P Q R : Prop)
```

## Implicação

A regra de introdução de `→` diz: para provar `P → Q`, suponha `P` e derive `Q`.
É o que `intro` faz — ele move o antecedente para as hipóteses.

```lean
example : P → (Q → P) := by
  intro hP _
  exact hP
```

A regra de eliminação é o *modus ponens*: de `P → Q` e de `P`, conclua `Q`. Em
Lean isso é aplicação — `h hP` já é a prova de `Q`. A tática `apply` faz o mesmo
de trás para frente: ela transforma o objetivo `Q` no objetivo `P`.

```lean
example (h : P → Q) (hP : P) : Q := h hP

example (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  intro hP
  apply h₂
  apply h₁
  exact hP
```

## Conjunção

Introdução de `∧`: para provar `P ∧ Q`, prove `P` e prove `Q`. A tática
`constructor` parte o objetivo em dois; o construtor anônimo `⟨_, _⟩` faz o
mesmo em forma de termo.

```lean
example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ
```

Eliminação de `∧`: de `P ∧ Q` conclua `P`, e conclua `Q`. São duas regras, e em
Lean são as projeções `.1` e `.2`. A tática `obtain` desmonta a hipótese de uma
vez, dando nome às duas partes.

```lean
example (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩

example (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩
```

## Disjunção

Introdução de `∨`: para provar `P ∨ Q` basta provar um dos dois lados. São duas
regras, e as táticas `left` e `right` escolhem qual.

```lean
example (hP : P) : P ∨ Q := by
  left
  exact hP
```

Eliminação de `∨` é a regra que dá mais trabalho, e por um bom motivo: de
`P ∨ Q` não se sabe qual dos dois vale. Para concluir `R` a partir dela é preciso
concluir `R` nos dois casos. A tática `cases` abre exatamente esses dois
objetivos.

```lean
example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => right; exact hP
  | inr hQ => left; exact hQ
```

## Negação e o absurdo

Não há um conectivo primitivo para a negação: `¬P` é notação para `P → False`,
onde `False` é a proposição sem nenhuma prova. Isso já entrega as duas regras.

A introdução de `¬` é a introdução de `→`: para provar `¬P`, suponha `P` e
derive `False`.

```lean
example (h : P → Q) : ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (h hP)
```

A eliminação é a eliminação de `→`: de `¬P` e de `P` sai `False`. E de `False`
sai qualquer coisa — é a regra que a tradição chama de *ex falso quodlibet*,
`False.elim` em Lean. As duas juntas são `absurd`.

```lean
example (hP : P) (hn : ¬P) : False := hn hP

example (h : False) : P := False.elim h

example (hP : P) (hn : ¬P) : Q := absurd hP hn
```

## Bi-implicação

`P ↔ Q` é a conjunção das duas implicações, e as regras seguem disso:
`constructor` parte o objetivo nas duas direções, e `.mp` e `.mpr` são as
eliminações — de `P` para `Q` e de `Q` para `P`.

```lean
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩

example (h : P ↔ Q) (hP : P) : Q := h.mp hP
```

## O que as regras acima não dão

Repare que em nenhum momento se usou "ou `P` vale, ou não vale". Todas as regras
até aqui são *construtivas*: uma prova de `P ∨ Q` traz consigo qual dos dois
lados vale, e uma prova de `P` é uma construção de `P`. Nessa leitura, `P ∨ ¬P`
não é um princípio disponível — afirmá-lo seria dizer que, para toda proposição,
sabemos decidir de que lado ela cai.

O raciocínio *clássico* acrescenta esse princípio, chamado de terceiro excluído.
Em Lean ele existe, e tem nome:

```lean
example : P ∨ ¬P := Classical.em P
```

Dele saem as duas táticas que o capítulo vai usar. `by_cases` parte a prova em
dois casos, supondo `P` num e `¬P` no outro:

```lean
example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exact absurd hP h
```

E `by_contra` prova `P` supondo `¬P` e derivando `False` — a redução ao absurdo:

```lean
example (h : ¬¬P) : P := by
  by_contra hn
  exact h hn
```

A distinção volta a importar mais adiante, quando cada fórmula receber um valor
entre dois: uma valoração que só admite verdadeiro e falso é, por construção,
clássica.

::::exercise (rating := 1) (name := "contrapositive")

Prove a contrapositiva, e depois a volta. Só uma das duas direções precisa de
raciocínio clássico — descubra qual.

```lean
example : (P → Q) → (¬Q → ¬P) := solution!(by
  intro h hnQ hP
  exact hnQ (h hP))

example : (¬Q → ¬P) → (P → Q) := solution!(by
  intro h hP
  by_contra hnQ
  exact h hnQ hP)
```

::::

::::exercise (rating := 2) (name := "de-morgan")

Uma das leis de De Morgan vale construtivamente; a outra precisa do terceiro
excluído.

```lean
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := solution!(by
  constructor
  · intro h
    exact ⟨fun hP => h (Or.inl hP), fun hQ => h (Or.inr hQ)⟩
  · intro h hor
    cases hor with
    | inl hP => exact h.1 hP
    | inr hQ => exact h.2 hQ)

example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := solution!(by
  constructor
  · intro h
    by_cases hP : P
    · right; intro hQ; exact h ⟨hP, hQ⟩
    · left; exact hP
  · intro h hand
    cases h with
    | inl hnP => exact hnP hand.1
    | inr hnQ => exact hnQ hand.2)
```

::::

# Sintaxe

:::terse
A gramática de LP é definida de forma recursiva. Note que o `atom` também abaixo
é definido de forma recursiva para permitir um inventário infinito mas enumerável de átomos.
:::

Na BNF a seguir, as letras proposicionais são os `atom`, podemos predefinir um certo conjunto de letras como válidas ou um processo de geração de âtomos válidos com o sufixo `'`.

```bnf
atom ::= "p" | "q" | "r" | atom"'" ;
F    ::= atom
  | "¬" F ("negação")
  | "(" F "∧" F ")" ("conjunção")
  | "(" F "∨" F ")" ("disjunção") ;
```

gerando fórmulas como `¬¬¬p'''`, `((p ∨ p') ∧ p')`, `(p ∧ (p' ∧ p'''))`. Sem parênteses a gramática é ambígua — `p ∧ p′ ∨ p″` lê-se tanto como `(p ∧ p′) ∨ p″` quanto como `p ∧ (p′ ∨ p″)`, e a ambiguidade estrutural afeta o significado, como na sentença em português "era jovem e bonita ou triste".

Um átomo é identificado por um nome, e o nome é uma `String`. Isso dá o inventário ilimitado que a gramática pede sem precisar enumerar símbolo por símbolo: `p`, `q`, `p'` e `chove` são todos átomos, e nada impede inventar mais um.

A conjunção e a disjunção são binárias. Poderiam receber uma lista de fórmulas de uma vez — `conj (fs : List Form)` —, mas um construtor que guarda uma `List Form` dentro do próprio tipo o torna um indutivo _nested_, e isso custa caro em Lean: perdem-se `deriving DecidableEq` e a tática `induction`, os dois necessários mais adiante. Com dois argumentos, uma conjunção de três fórmulas é `conj f (conj g h)`, e tudo continua funcionando.

```lean
inductive Form where
  | atom (name : String)
  | top
  | bot
  | neg (f : Form)
  | conj (f g : Form)
  | disj (f g : Form)
  deriving DecidableEq, Repr
```

`top`/`bot` são a base da recursão de `conjs`/`disjs` abaixo — uma
conjunção vazia é sempre verdadeira, uma disjunção vazia é sempre
falsa. Diferente de um átomo de nome `"⊤"` (que a valoração, adiante
neste capítulo, `(String → Bool) → Form → Bool`, poderia mandar para
`false`, dependendo da atribuição de átomos), `top`/`bot` são
construtores próprios: a valoração vai tratá-los como constantes,
sempre `true`/`false`, sem depender de nenhuma atribuição — por isso a
conjunção vazia imprime `"true"` e a disjunção vazia `"false"` (ver
`toStringPolish` abaixo).

Notação n-ária recuperada por duas funções, para a valoração e para os
fragmentos de língua que virão (uma conjunção/disjunção quase sempre de
dois elementos, e uma única vez com mais — o `lfDET The` da verificação
de modelos):

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

`ToString` em notação polonesa (prefixa):

```lean
def Form.toStringPolish : Form → String
  | .atom name => name
  | .top => "true"
  | .bot => "false"
  | .neg f => "-" ++ f.toStringPolish
  | .conj f g =>
    "&[" ++ f.toStringPolish ++ "," ++
      g.toStringPolish ++ "]"
  | .disj f g =>
    "v[" ++ f.toStringPolish ++ "," ++
      g.toStringPolish ++ "]"

instance : ToString Form := ⟨Form.toStringPolish⟩

def form1 : Form := .conj (.atom "p") (.neg (.atom "p"))

def form2 : Form :=
  .disj (.atom "p1")
    (.disj (.atom "p2") (.disj (.atom "p3") (.atom "p4")))
```


`form2` não é `v[p1,p2,p3,p4]` — sendo `Form` binário, quatro disjuntos
exigem três `disj` encadeados, não uma lista achatada. É exatamente o
preço da escolha binária, e a razão de existir `Form.disjs`: `disjs`
_constrói_ esses `disj` encadeados, não achata a saída — o mesmo
`form2` de novo, desta vez a partir da lista:

```lean
example :
    Form.disjs
      [.atom "p1", .atom "p2", .atom "p3", .atom "p4"] =
      form2 :=
  rfl

-- Simétrico para `conjs`, com a mesma forma de `form2` só
-- troca `∨` por `∧`:
def form2' : Form :=
  .conj (.atom "p1")
    (.conj (.atom "p2") (.conj (.atom "p3") (.atom "p4")))

example :
    Form.conjs
      [.atom "p1", .atom "p2", .atom "p3", .atom "p4"] =
      form2' :=
  rfl
```

Duas abreviações usuais: `F1 → F2` para `¬(F1 ∧ ¬F2)` ("implicação"), e
`F1 ↔ F2` para `(F1 → F2) ∧ (F2 → F1)` ("equivalência").

```lean
def Form.impl (f g : Form) : Form := .neg (.conj f (.neg g))
def Form.equi (f g : Form) : Form :=
  .conj (Form.impl f g) (Form.impl g f)
```

::::exercise (rating := 1) (name := "translate-sentences")

Traduza as sentenças a seguir para lógica proposicional, garantindo que
as condições de verdade sejam capturadas. Que limitações você encontra?

1. _The wizard polishes his wand and learns a new spell, or he is
   lazy._
2. _The peasant will deal with the devil only if he has a plan to
   outwit him._
3. _If neither unicorns nor dragons exist, then neither do goblins._

Use `p` para "o mago pole a varinha", `q` para "aprende um feitiço novo",
`r` para "está com preguiça"; `s` para "o camponês faz o trato", `t` para
"tem um plano"; `u`, `v` e `w` para a existência de unicórnios, dragões e
duendes.

```lean
def wizardOrLazy : Form :=
  solution!(.disj (.conj (.atom "p") (.atom "q"))
    (.atom "r"))
def peasantOnlyIf : Form :=
  solution!(.neg (.conj (.atom "s") (.neg (.atom "t"))))
def noUnicornsNoGoblins : Form :=
  solution!(.neg (.conj (.neg (.atom "u"))
    (.conj (.neg (.atom "v")) (.atom "w"))))
```

::::

::::exercise (rating := 1) (name := "exclusive-or")

O conectivo `∨` é inclusivo: `p ∨ q` é verdadeiro mesmo quando `p` e
`q` são ambos verdadeiros. Em português, "ou" costuma ser exclusivo,
como em "Você pode ficar com o sorvete ou com o algodão-doce, mas não
com os dois." Defina um conectivo `⊕` para "ou exclusivo", usando os
conectivos já definidos.

```lean
def Form.xor (f g : Form) : Form :=
  solution!(.disj (.conj f (.neg g)) (.conj (.neg f) g))
```

::::

::::exercise (rating := 2) (name := "unique-readability")

Use o princípio de indução estrutural para provar que as fórmulas de
lógica proposicional em notação prefixa são de leitura única.

```lean
theorem neg_inj (f g : Form) (h : Form.neg f = Form.neg g) :
    f = g :=
  solution!(by injection h)

theorem conj_inj (f1 f2 g1 g2 : Form)
    (h : Form.conj f1 f2 = Form.conj g1 g2) :
    f1 = g1 ∧ f2 = g2 := solution!(by
  injection h with h1 h2
  exact ⟨h1, h2⟩)
```

:::gradeTheorem "1" neg_inj conj_inj
:::
::::

Em Lean, essas duas provas são `injection`, sem indução — um termo de
tipo indutivo _é_ a árvore, e o Lean já sabe, para todo `inductive`,
que construtores diferentes produzem valores diferentes, e que um
mesmo construtor com argumentos diferentes produz valores diferentes.
É a mesma observação de "Indução estrutural", abaixo — não à toa a
versão Lean deste exercício é quase vazia: provar leitura única para
uma gramática dada como _string_ exige indução estrutural genuína;
aqui não há string a analisar, o termo Lean já é a árvore.

# Sintaxe e proposição são coisas diferentes

`Prop` é o tipo das proposições, e uma proposição não tem estrutura
interna que se possa inspecionar: ela é verdadeira ou falsa, e mais nada
se pergunta a ela. `Form`, acima, é um `inductive` de *sintaxe*: um valor
de `Form` é dado, no sentido de {ref "IntroL"}[Programação Funcional no
Lean] — casa padrão, conta operadores, mede profundidade, coleta os
átomos que ocorrem nele — é o que pedem os exercícios `count-operators`,
`formula-depth` e `collect-atoms`, mais abaixo. Nada
disso é possível sobre um `Prop`: não há como perguntar "quantos `∧`
tem esta proposição" a um valor de tipo `Prop`, porque `Prop` não
guarda a fórmula que o provou, só se ela é verdadeira. A valoração
`Form → Bool` — que dá sentido a `Form` como lógica, e não só como
árvore — chega adiante, neste mesmo capítulo.

Uma fórmula pode ainda ser tomada como objeto de um sistema de prova, e
não de uma valoração: em vez de perguntar que valor ela recebe, pergunta-se
o que se deriva dela. A biblioteca `cslib` faz isso, em
`Cslib.Logic.PL.Proposition`, com dedução natural completa — leitura
para quem quiser seguir por esse caminho.

# Indução estrutural

O Princípio da Indução Estrutural diz: para provar algo de toda fórmula,
basta provar da base (átomos) e do passo indutivo (que a propriedade
passa por `¬`, `∧`, `∨`). Onde se raciocina sobre fórmulas como
_strings_, ele precisa ser enunciado como teorema à parte; em Lean não é
um teorema a enunciar — é o recursor que `inductive Form` já gera de
graça:

```lean (name := c4check1)
#check @Form.rec
```

```leanOutput c4check1
@Form.rec : {motive : Form → Sort u_1} →
  ((name : String) → motive (Form.atom name)) →
    motive Form.top →
      motive Form.bot →
        ((f : Form) → motive f → motive f.neg) →
          ((f g : Form) → motive f → motive g → motive (f.conj g)) →
            ((f g : Form) → motive f → motive g → motive (f.disj g)) → (t : Form) → motive t
```

`Form.rec` — e a tática `induction`, construída sobre ele — já *são* o
princípio de indução estrutural, sem que o capítulo precise declará-lo.
Duas afirmações que noutro contexto seriam proposições a demonstrar — que
toda fórmula tem o mesmo número de parênteses à esquerda e à direita, e a
leitura única, que é o exercício acima — viram, aqui, só `induction`:

```lean
def Form.leftParens : Form → Nat
  | .atom _ => 0
  | .top => 0
  | .bot => 0
  | .neg f => f.leftParens
  | .conj f g => 1 + f.leftParens + g.leftParens
  | .disj f g => 1 + f.leftParens + g.leftParens

def Form.rightParens : Form → Nat
  | .atom _ => 0
  | .top => 0
  | .bot => 0
  | .neg f => f.rightParens
  | .conj f g => 1 + f.rightParens + g.rightParens
  | .disj f g => 1 + f.rightParens + g.rightParens

theorem Form.leftParens_eq_rightParens (f : Form) :
    f.leftParens = f.rightParens := by
  induction f with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | neg _ ih => exact ih
  | conj _ _ ih1 ih2 =>
    simp [Form.leftParens, Form.rightParens, ih1, ih2]
  | disj _ _ ih1 ih2 =>
    simp [Form.leftParens, Form.rightParens, ih1, ih2]
```

Vale notar o que a prova de fato estabelece: `Form` binário já garante
um parêntese de abertura por `conj`/`disj`, contado igualmente nas duas
funções por construção, de modo que a demonstração formaliza essa
contagem em vez de descobrir algo novo sobre a gramática.

A leitura única é o caso extremo dessa observação. Provar leitura única
para uma gramática dada como _string_ exige indução estrutural genuína;
em Lean, um termo de `Form` já é a árvore, não uma string a analisar —
não há uma segunda leitura possível a excluir, e o exercício
`unique-readability`, acima, se reduz a `injection`.

::::exercise (rating := 1) (name := "count-operators")

Implemente uma função `opsNr` para contar o número de operadores de
uma fórmula. O tipo é `opsNr : Form → Nat`. A chamada `opsNr form1`
deve dar `2`.

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

:::gradeTheorem "1" opsNr_test
:::
::::

::::exercise (rating := 1) (name := "formula-depth")

Implemente uma função `depth` para calcular a profundidade da árvore
de análise de uma fórmula. O tipo é `depth : Form → Nat`. A chamada
`depth form1` deve dar `2`.

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

:::gradeTheorem "1" depth_test
:::
::::

::::exercise (rating := 2) (name := "collect-atoms")

Implemente `propNames : Form → List String` para coletar a lista de
nomes de átomos proposicionais que ocorrem numa fórmula. A lista
resultante deve estar ordenada e sem repetições.

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

```lean (name := c4eval5)
#eval form1.propNames
```

```leanOutput c4eval5
["p"]
```

```lean (name := c4eval6)
#eval form2.propNames
```

```leanOutput c4eval6
["p1", "p2", "p3", "p4"]
```


# Semântica

A primeira questão a enfrentar na semântica da lógica proposicional é: quais são
as estruturas extralinguísticas de que as fórmulas da lógica proposicional
tratam? Nossa resposta é: informação sobre a verdade ou falsidade das proposições
atômicas. Essa resposta é codificada nas chamadas *valorações*, funções do
conjunto dos átomos para o conjunto `{0, 1}` dos valores de verdade.

Aqui uma valoração é uma lista de pares, e um átomo ausente da lista conta como
falso.

```lean
abbrev Valuation := List (String × Bool)
```

Se `V` é uma valoração, ela se estende a uma função de todas as fórmulas para os
valores de verdade. A extensão é definida por recursão sobre a estrutura da
fórmula, um caso por construtor:

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

Os construtores `top` e `bot` são constantes: nenhuma valoração os afeta.

```lean (name := c5eval1)
#eval form1.eval [("p", true)]
```

```leanOutput c5eval1
false
```

Outra maneira de apresentar a semântica dos conectivos proposicionais é por meio
de *tabelas de verdade*, que especificam como o valor de verdade de uma fórmula
complexa é calculado a partir dos valores de verdade de seus componentes.

```
F₁  F₂    ¬F₁    F₁ ∧ F₂    F₁ ∨ F₂    F₁ → F₂    F₁ ↔ F₂
1   1      0        1          1          1          1
1   0      0        0          1          0          0
0   1      1        0          1          1          0
0   0      1        0          0          1          1
```

Não é difícil ver que há fórmulas cujo valor não depende da valoração. As
fórmulas que valem 1 para toda valoração são chamadas de *tautologias*; a notação
usual para "F é uma tautologia" é `⊨ F`. As fórmulas que valem 0 para toda
valoração são chamadas de *contradições*.

Uma fórmula é *satisfatível* se há ao menos uma valoração que a torna verdadeira,
e é *contingente* se é satisfatível mas não é uma tautologia. Toda tautologia é
satisfatível, mas nem toda fórmula satisfatível é uma tautologia.

Para decidir isso basta percorrer todas as valorações relevantes — e são finitas,
porque uma fórmula tem finitos átomos. A função a seguir gera a lista de todas as
valorações sobre um conjunto de nomes.

```lean
def genVals : List String → List Valuation
  | [] => [[]]
  | name :: names =>
      (genVals names).map ((name, true) :: ·)
      ++ (genVals names).map ((name, false) :: ·)

def Form.allVals (f : Form) : List Valuation :=
  genVals f.propNames
```

```lean (name := c5eval2)
#eval form1.allVals
```

```leanOutput c5eval2
[[("p", true)], [("p", false)]]
```

Com isso, as três noções são imediatas.

```lean
def Form.tautology (f : Form) : Bool :=
  f.allVals.all (fun v => f.eval v)

def Form.satisfiable (f : Form) : Bool :=
  f.allVals.any (fun v => f.eval v)

def Form.contradiction (f : Form) : Bool :=
  !f.satisfiable
```

```lean (name := c5eval3)
#eval (form1.contradiction,
       (Form.neg form1).tautology,
       form2.satisfiable)
```

```leanOutput c5eval3
(true, true, true)
```

Duas fórmulas `F₁` e `F₂` são *logicamente equivalentes* se têm o mesmo valor sob
toda valoração; a notação é `F₁ ≡ F₂`. Segue da definição que todas as
tautologias são logicamente equivalentes entre si, e o mesmo vale para as
contradições.

Fórmulas `P₁, …, Pₙ` *implicam logicamente* a fórmula `C` (`P` de premissa, `C`
de conclusão) se toda valoração que torna verdadeiros todos os membros de
`P₁, …, Pₙ` também torna `C` verdadeira. A notação é `P₁, …, Pₙ ⊨ C`.

Disso sai uma caracterização que dispensa quantificar sobre valorações duas
vezes: `F₁` implica `F₂` se e somente se `F₁ ∧ ¬F₂` é uma contradição.

```lean
def Form.implies (f g : Form) : Bool :=
  (Form.conj f (.neg g)).contradiction

def Form.equivalent (f g : Form) : Bool :=
  f.implies g && g.implies f
```

```lean (name := c5eval4)
#eval (Form.implies (.atom "p")
         (.disj (.atom "p") (.atom "q")),
       Form.equivalent
         (.neg (.neg (.atom "p"))) (.atom "p"))
```

```leanOutput c5eval4
(true, true)
```

A semântica da lógica proposicional também pode ser dada em formato de
*atualização*. Fixe primeiro um conjunto de valorações relevantes: esse é o
estado corrente. Depois defina uma função de atualização que deixa apenas as
valorações que satisfazem uma dada fórmula.

```lean
def update (vals : List Valuation) (f : Form) :
    List Valuation :=
  vals.filter (fun v => f.eval v)
```

Atualizar o estado de todas as valorações relevantes com uma contradição não
deixa nada; atualizar com uma tautologia não tira nada.

```lean (name := c5eval5)
#eval (update form1.allVals form1).length
```

```leanOutput c5eval5
0
```

```lean (name := c5eval6)
#eval (update form1.allVals (.neg form1)).length
```

```leanOutput c5eval6
2
```

Atualizar com uma fórmula contingente tira alguma coisa, e atualizar com sua
negação tira o complemento.

```lean (name := c5eval7)
#eval (form2.allVals.length,
       (update form2.allVals form2).length,
       (update form2.allVals (.neg form2)).length)
```

```leanOutput c5eval7
(16, 15, 1)
```

Essa é a imagem do conhecimento que cresce por eliminação de possibilidades, que
já apareceu no primeiro capítulo: cada afirmação aceita corta o estado.

::::exercise (rating := 1) (name := "valuation-table")

Seja `V` dada por `p ↦ 0`, `q ↦ 1`, `r ↦ 1`. Dê os valores das fórmulas
seguintes: `¬p ∨ p`, `p ∧ ¬p`, `¬¬(p ∨ ¬r)`, `¬(p ∧ ¬r)`, `p ∨ (q ∧ r)`.

```lean
def vpqr : Valuation :=
  [("p", false), ("q", true), ("r", true)]

example :
    (Form.disj (.neg (.atom "p")) (.atom "p")).eval vpqr
      = true :=
  solution!(by decide)

example :
    (Form.conj (.atom "p") (.neg (.atom "p"))).eval vpqr
      = false :=
  solution!(by decide)
```

::::

::::exercise (rating := 1) (name := "negated-tautology")

Explique por que a negação de uma tautologia é sempre uma contradição, e
vice-versa.

:::solution
Uma fórmula `F` é tautologia quando `F.eval v = true` para toda `v`. Como
`(Form.neg F).eval v = !(F.eval v)`, isso vale exatamente quando
`(Form.neg F).eval v = false` para toda `v`, que é a definição de contradição.
O argumento se lê igual nas duas direções, porque `!` é uma bijeção sobre os
booleanos.
:::

::::

::::exercise (rating := 2) (name := "implies-list")

Estenda a checagem de implicação proposicional para o caso de uma lista de
premissas. O tipo é `Form.impliesL : List Form → Form → Bool`.

```lean
def Form.impliesL (ps : List Form) (c : Form) :
    Bool :=
  solution!((Form.conjs ps).implies c)
```

::::

# A ponte entre as duas leituras

O capítulo começou distinguindo raciocinar *em* lógica proposicional de raciocinar
*sobre* ela. As duas leituras convivem desde então: `p ∧ q` é uma proposição, do
tipo `Prop`, e `Form.conj p q` é um dado, do tipo `Form`. Nada, até aqui, as
liga.

A ligação é uma função que interpreta cada fórmula como a proposição que ela
afirma, dada uma valoração.

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

Repare no que cada caso faz: ele troca um construtor de `Form` pelo conectivo
correspondente de `Prop`. O `conj` do dado vira o `∧` da proposição, o `neg` vira
o `¬`. É a mesma correspondência que a seção sobre sintaxe e proposição pediu
para não confundir — e é só aqui, com uma função explícita entre as duas, que ela
pode ser enunciada sem confusão.

O teorema que fecha o capítulo diz que as duas leituras concordam: computar dá
`true` exatamente quando a proposição vale.

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

A ponte também dá o que faltava para o exercício de tradução do começo do
capítulo. Traduzir bem é algo que se pode *conferir*: basta enunciar em Lean a
condição de verdade pretendida e exigir que a denotação da fórmula coincida com
ela. O teorema fecha por `Iff.rfl` — a denotação calcula, e o que sobra dos dois
lados é o mesmo termo.

```lean
theorem wizardOrLazy_means (v : Valuation) :
    wizardOrLazy.denote v ↔
      ((v.lookup "p").getD false = true
        ∧ (v.lookup "q").getD false = true)
      ∨ (v.lookup "r").getD false = true :=
  Iff.rfl
```

É esse teorema, e não a fórmula sozinha, que responde à pergunta "as condições
de verdade foram capturadas?" — a fórmula é uma proposta, e o teorema é a
verificação.

A prova é indução estrutural sobre a fórmula, com um caso por construtor — a
mesma indução que o recursor de `Form` já dava. Em cada caso a hipótese de
indução vale para as subfórmulas, e o que resta é conferir que o conectivo
booleano e o conectivo proposicional concordam.

Vale notar onde a lógica clássica entra. A valoração devolve `Bool`, que tem
exatamente dois habitantes; a denotação devolve `Prop`, onde a decidibilidade não
é dada. O teorema acima diz que, para as fórmulas desta linguagem, as duas
coincidem — ou seja, a semântica de dois valores é clássica por construção, e é
por isso que a discussão sobre o terceiro excluído, no começo do capítulo, não
reaparece aqui.

```lean
end PL
```
