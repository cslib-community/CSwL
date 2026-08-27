import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Lógica proposicional" =>
%%%
tag := "PL"
%%%

```lean
namespace PL
```

A lógica proposicional ou cálculo sentencial, é um sistema formal no qual as fórmulas representam proposições que podem ser formadas pela combinação de proposições atômicas usando conectivos lógicos e um sistema de regras de derivação, que permite que certas fórmulas sejam estabelecidas como teoremas do sistema formal.

# Sintaxe

Mas vamos começar como antes, definindo a gramática que nos permite especificar o que é a linguagem da lógica proposicional.

```bnf
atom ::= "p" | "q" | "r" | atom"'" ;
F    ::= atom
  | "¬" F ("negação")
  | "(" F "∧" F ")" ("conjunção")
  | "(" F "∨" F ")" ("dijunção") ;
```

gerando fórmulas como `¬¬¬p'''`, `((p ∨ p') ∧ p')`, `(p ∧ (p' ∧ p'''))`. Sem parênteses a gramática é ambígua — `p ∧ p′ ∨ p″` lê-se tanto como `(p ∧ p′) ∨ p″` quanto como `p ∧ (p′ ∨ p″)`, e a ambiguidade estrutural afeta o significado, como na sentença em português "era jovem e bonita ou triste".

A lista infinita de átomos (`p, q, r, p', q', ...`) se traduz melhor em Lean como um átomo com nome (`String`), não como uma enumeração de símbolos. Então ao invés de infinitas letras proposicionais usamos qualquer string como um átomo.

Mantemos a cojunção e dijunção na forma binária ao pé da letra porque, em Lean, uma lista custa caro. Um `inductive` com `List Form` dentro de si mesmo (`Cnj (fs : List Form)`) é _nested_, e perde tanto `deriving DecidableEq` quanto a tática `induction` (que os Exercícios 4.11/4.15 pedem, mais adiante).

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
falsa. Diferente de um átomo de nome `"⊤"` (que a valoração do
capítulo 5, `(String → Bool) → Form → Bool`, poderia mandar para
`false`, dependendo da atribuição de átomos), `top`/`bot` são
construtores próprios: a valoração vai tratá-los como constantes,
sempre `true`/`false`, sem depender de nenhuma atribuição — por isso a
conjunção vazia imprime `"true"` e a disjunção vazia `"false"` (ver
`toStringPolish` abaixo).

Notação n-ária recuperada por duas funções, para os capítulos 5–7 (uma
conjunção/disjunção quase sempre de dois elementos, e uma única vez com
mais — `lfDET The`, no capítulo 8):

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
```

```lean (name := c4eval3)
#eval toString form1
```

```leanOutput c4eval3
"&[p,-p]"
```

```lean
def form2 : Form :=
  .disj (.atom "p1")
    (.disj (.atom "p2") (.disj (.atom "p3") (.atom "p4")))
```

```lean (name := c4eval4)
#eval toString form2
```

```leanOutput c4eval4
"v[p1,v[p2,v[p3,p4]]]"
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

::::exercise (rating := 1) (name := "4.9")

Ref. CSwFP/4, exercício 4.9 (p. 74).

Traduza as sentenças a seguir para lógica proposicional, garantindo que
as condições de verdade sejam capturadas. Que limitações você encontra?

1. _The wizard polishes his wand and learns a new spell, or he is
   lazy._
2. _The peasant will deal with the devil only if he has a plan to
   outwit him._
3. _If neither unicorns nor dragons exist, then neither do goblins._

```lean
def ex49_1 : Form :=
  solution!(.disj (.conj (.atom "p") (.atom "q"))
    (.atom "r"))
def ex49_2 : Form :=
  solution!(.neg (.conj (.atom "s") (.neg (.atom "t"))))
def ex49_3 : Form :=
  solution!(.neg (.conj (.neg (.atom "u"))
    (.conj (.neg (.atom "v")) (.atom "w"))))
```

::::

::::exercise (rating := 1) (name := "4.10")

Ref. CSwFP/4, exercício 4.10 (p. 74).

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

::::exercise (rating := 2) (name := "4.11")

Ref. CSwFP/4, exercício 4.11 (p. 74).

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

O capítulo 3 definiu `abbrev S := Prop` — uma proposição semântica, sem
estrutura interna que se possa inspecionar. `Form`, acima, é um segundo
`inductive` de *sintaxe*: um valor de `Form` é dado, no sentido do
capítulo 2 — casa padrão, conta operadores, mede profundidade, coleta
os átomos que ocorrem nele (Exercícios 4.12–4.14, mais abaixo). Nada
disso é possível sobre um `Prop`: não há como perguntar "quantos `∧`
tem esta proposição" a um valor de tipo `Prop`, porque `Prop` não
guarda a fórmula que o provou, só se ela é verdadeira. A valoração
`Form → Bool` — que dá sentido a `Form` como lógica, e não só como
árvore — chega no capítulo 5.

Há um terceiro objeto que responde à mesma pergunta ("o que é uma
fórmula?") de um jeito diferente: `Cslib.Logic.PL.Proposition`
(biblioteca `cslib`, já dependência deste projeto). Também é sintaxe —
um `inductive` de fórmulas —, mas o que se faz com ela é dedução
natural (`Γ ⊢ A`), não valoração. Três respostas, três pontos de
vista: `Prop` é a proposição em si, sem estrutura; `Proposition` do
`cslib` é sintaxe mais um sistema de prova; `Form` daqui é sintaxe mais
uma função `Form → Bool`. Este capítulo e o capítulo 5 seguem a
terceira.

`Proposition` fica como leitura complementar, não como base do
capítulo, por um motivo de vocabulário: a BNF acima tem `¬`/`∧`/`∨`
primitivos e introduz `→` só depois, como abreviação; `Proposition`
faz o caminho inverso — `imp` é primitivo, `neg` deriva de `imp ·⊥`,
exigindo uma instância `[Bot Atom]` no tipo dos átomos que não tem
motivação linguística, só satisfaz a typeclass. Adotar `Proposition`
obrigaria `opsNr`/`depth` (Exercícios 4.12–4.13) a passar primeiro por
essa tradução de vocabulário, antes de bater com os números esperados.
Quem quiser ver como um curso de teoria da prova trataria fórmulas
proposicionais em Lean, com dedução natural completa, encontra em
`Cslib.Logic.PL.Proposition`.

# Indução estrutural

O Princípio da Indução Estrutural (Teorema 4.1 de CSwFP) diz: para
provar algo de toda fórmula, basta provar da base (átomos) e do passo
indutivo (que a propriedade passa por `¬`, `∧`, `∨`). Isso é necessário
enunciar como teorema separado quando se raciocina sobre fórmulas como
_strings_; em Lean não é um teorema a enunciar — é o recursor que
`inductive Form` já gera de graça:

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
A Proposição 4.2 de CSwFP (número igual de parênteses em toda fórmula)
e a Proposição 4.3 (leitura única — o Exercício 4.11 acima é essa
prova) viram, aqui, só `induction`:

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

Essa é a Proposição 4.2 traduzida — mas com uma ressalva: `Form`
binário já garante um parêntese de abertura por `conj`/`disj`, contado
igualmente nas duas funções por construção; a prova formaliza essa
contagem, não descobre nada de novo sobre a gramática. A Proposição 4.3
e os Exercícios 4.11/4.15 (leitura única) são o caso mais extremo dessa
observação: provar leitura única para uma gramática dada como _string_
exige indução estrutural genuína; em Lean, um termo de `Form` já é a
árvore, não uma string a analisar — não há uma segunda leitura possível
a excluir, e a prova (Exercício 4.11 acima) se reduz a `injection`.

::::exercise (rating := 1) (name := "4.12")

Ref. CSwFP/4, exercício 4.12 (p. 75).

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

::::exercise (rating := 1) (name := "4.13")

Ref. CSwFP/4, exercício 4.13 (p. 75).

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

::::exercise (rating := 2) (name := "4.14")

Ref. CSwFP/4, exercício 4.14 (p. 75).

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


```lean
end PL
```
