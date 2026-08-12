/-!
# 4. Sintaxe Formal de Fragmentos

Ref. CSwFP/4 (`FSynF`). Formal Syntax for Fragments.
-/

namespace Chapter04

/-! ## 4.1 Gramáticas de jogos

O capítulo trata de como definir uma língua — no sentido amplo: um conjunto
de strings bem formadas — por meio de uma gramática. O primeiro exemplo é um
jogo, a Batalha Naval: um tabuleiro 10×10 (colunas `A` a `J`, linhas `1` a
`10`) e uma frota de navios. O livro dá a gramática em BNF:

```
column   −→ A | B | C | D | E | F | G | H | I | J
row      −→ 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10
attack   −→ column row
ship     −→ battleship | frigate | submarine | destroyer
reaction −→ missed | hit ship | sunk ship | lost battle
turn     −→ attack reaction
```

Cada regra reescreve um símbolo não-terminal (à esquerda) numa sequência de
símbolos (à direita); repetindo o processo a partir de `turn` até só restarem
terminais, obtém-se uma jogada válida, como `B 2 missed`. O livro chama esse
passo de reescrita de `⇒`, e sua repetição de `⇒*` — `turn ⇒* B 2 missed`.

Em Lean, um `inductive` já é essa gramática: cada construtor é uma regra de
produção, e um valor do tipo já é uma sequência de reescritas aplicada até o
fim — não há passo intermediário a formalizar, o termo *é* o resultado do
processo.
-/

inductive Column where
  | A | B | C | D | E | F | G | H | I | J
  deriving DecidableEq, Repr

inductive Ship where
  | battleship | frigate | submarine | destroyer
  deriving DecidableEq, Repr

structure Attack where
  column : Column
  row : Fin 10
  deriving DecidableEq, Repr

inductive Reaction where
  | missed
  | hit (s : Ship)
  | sunk (s : Ship)
  | lostBattle
  deriving DecidableEq, Repr

structure Turn where
  attack : Attack
  reaction : Reaction
  deriving DecidableEq, Repr

/-!
Como no capítulo 2 (`Attack` como `structure`, não como par posicional): os
campos nomeados dizem o que cada componente significa, o par `Column × Fin
10` não diria.

**Ressalva sobre `Fin 10`.** O livro numera as linhas de `1` a `10`; `Fin
10` numera de `0` a `9` — um desvio de representação, não só de notação: a
linha `1` do livro é `Row` `0` aqui, e a linha `10` do livro é `Row` `9`.
Quem digitar `(10 : Fin 10)` não erra de tipo, recebe de volta `0` (`10 %
10`, via `OfNat`) — a linha 10 do livro "some" nesse literal, reaparecendo
só como `9`. O erro de tipo aparece apenas na construção explícita e
verificada, `⟨n, by omega⟩` com `n ≥ 10`; um literal solto não passa por
ali. Os exemplos abaixo, por segurança, sempre nomeiam a linha do livro na
prosa e escrevem o índice `Fin 10` já convertido (`linha 2` do livro é
`⟨1, by omega⟩`).
-/

example : (Attack.mk .B ⟨1, by omega⟩).row = 1 := rfl
-- ⟨1, ...⟩ é a linha *2* do tabuleiro do livro (linha do livro − 1).

/-!
Depois do primeiro exercício, o livro estende a gramática para o jogo
completo, permitindo repetir jogadas:

```
game −→ turn | turn game
```

E comenta: exigir explicitamente que o jogo termine quando um lado é
derrotado é uma decisão semântica que se refletiu na sintaxe — a gramática
por si só (a definição acima) não impede jogadas depois do fim do jogo.
-/

abbrev Game := List Turn

/-! ### Exercício\* — Fim de jogo

Revise `Reaction`/`Game` de modo que um jogo termine (a lista de `Turn`
pare de crescer) quando `lostBattle` ocorrer. Uma abordagem: um tipo
`GameEnd` separado de `Reaction`, e `Game := List Turn × Option GameEnd`.

Em `## 4.1`–`## 4.3`, cada `def ... : Type := sorry` é um placeholder de
gramática: a tarefa é apagar o `def` e escrever no lugar o `inductive`
(ou `structure`/`abbrev`) que a gramática pedida exige — não substituir
só o `sorry`. Já em `## 4.4` em diante, o `sorry` marca uma função a
implementar com o tipo já dado (`def opsNr : Form → Nat := sorry`) —
aí a tarefa é só a definição, o tipo já está certo.
-/

def GameEnd : Type := sorry

def Game' : Type := sorry

/-! ### Exercício 4.1 (p. 65)

Revise a gramática de modo que fique explícito, nas próprias regras, que o
jogo termina quando um dos jogadores é derrotado.
-/

def SeaBattleReaction : Type := sorry

def SeaBattleGame : Type := sorry

/-! ### Exercício 4.2 (p. 67)

Revise a gramática para garantir que um jogo tenha no máximo quatro
jogadas.
-/

def SeaBattleGameMax4 : Type := sorry

/-! ### Exercício 4.3 (p. 67)

Escreva suas próprias gramáticas para xadrez e para bingo.
-/

def ChessGame : Type := sorry

def BingoGame : Type := sorry

/-! ### Exercício 4.4 (p. 67)

Confira: todas essas gramáticas geram línguas infinitas. Em seguida, altere
a definição de `reaction` no Exercício 4.2 de modo que a gramática revisada
gere uma língua finita.
-/

def SeaBattleReactionFinite : Type := sorry

/-! ### Exercício 4.5 (p. 68)

Dê uma gramática para strings que também gera a string vazia. Use `ε` como
símbolo para a string vazia.
-/

def StringWithEmpty : Type := sorry

/-! ### Mastermind

Segundo exemplo do livro: no Mastermind, um jogador esconde uma sequência
de 4 pinos coloridos e o outro tenta adivinhá-la, recebendo como resposta
uma contagem de acertos (pino certo na posição certa) e presenças (cor
certa, posição errada) — sem dizer quais posições. Gramática em EBNF (`{ }`
para repetição zero-ou-mais):

```
colour   −→ red | yellow | blue | green | orange
answer   −→ black | white
guess    −→ colour colour colour colour
reaction −→ { answer }
turn     −→ guess reaction
game     −→ turn | turn game
```
-/

inductive Colour where
  | red | yellow | blue | green | orange
  deriving DecidableEq, Repr

def Colour.all : List Colour := [.red, .yellow, .blue, .green, .orange]

inductive Answer where
  | black | white
  deriving DecidableEq, Repr

abbrev Pattern := Colour × Colour × Colour × Colour

abbrev Feedback := List Answer

/-!
`Colour.all` substitui o `deriving (Bounded, Enum)` do Haskell do livro —
não há equivalente no núcleo do Lean, mas a lista explícita cumpre o mesmo
papel (enumerar todos os valores) e será usada quando o jogo precisar
gerar ou percorrer todas as cores.
-/

/-! ## 4.2 Um fragmento do inglês

O terceiro exemplo do capítulo — e o que interessa ao curso — é uma
gramática para um fragmento do inglês. O livro dá primeiro a BNF:

```
S    −→ NP VP
NP   −→ Snow White | Alice | Dorothy | Goldilocks | Little Mook | Atreyu
            | DET CN | DET RCN
DET  −→ the | every | some | no
CN   −→ girl | boy | princess | dwarf | giant | wizard | sword | dagger
RCN  −→ CN that VP | CN that NP TV
VP   −→ laughed | cheered | shuddered
            | TV NP | DV NP NP
TV   −→ loved | admired | helped | defeated | caught
DV   −→ gave
```

com a ressalva de que é "muito básica e grosseira demais", mas serve para
dar uma ideia do formato. Depois estende essa BNF para uma implementação
que soma catorze tipos de dado — os oito não-terminais da BNF mais seis
tipos auxiliares (`Sent`, `ADJ`, `That`, `AV`, `INF`, `TINF`, `To`) que
existem só na versão Haskell, introduzidos para ilustrar intensionalidade
mais adiante (§8.3 do livro).

A tradução para Lean é direta: cada categoria sintática é um construtor de
um `inductive` mutuamente recursivo — a árvore de análise de uma sentença
*é* um termo desse tipo, sem passo de tradução string→árvore a definir.
-/

inductive DET where
  | the | every | some | no | most
  deriving DecidableEq, Repr

instance : ToString DET :=
  ⟨fun | .the => "the" | .every => "every" | .some => "some"
       | .no => "no" | .most => "most"⟩

inductive CN where
  | girl | boy | princess | dwarf | giant | wizard | sword | dagger
  deriving DecidableEq, Repr

instance : ToString CN :=
  ⟨fun | .girl => "girl" | .boy => "boy" | .princess => "princess"
       | .dwarf => "dwarf" | .giant => "giant" | .wizard => "wizard"
       | .sword => "sword" | .dagger => "dagger"⟩

inductive ADJ where
  | fake
  deriving DecidableEq, Repr

instance : ToString ADJ := ⟨fun | .fake => "fake"⟩

inductive That where
  | that
  deriving DecidableEq, Repr

inductive TV where
  | loved | admired | helped | defeated | caught
  deriving DecidableEq, Repr

instance : ToString TV :=
  ⟨fun | .loved => "loved" | .admired => "admired" | .helped => "helped"
       | .defeated => "defeated" | .caught => "caught"⟩

inductive DV where
  | gave
  deriving DecidableEq, Repr

instance : ToString DV := ⟨fun | .gave => "gave"⟩

inductive AV where
  | hoped | wanted
  deriving DecidableEq, Repr

instance : ToString AV := ⟨fun | .hoped => "hoped" | .wanted => "wanted"⟩

inductive TINF where
  | love | admire | help | defeat | catch
  deriving DecidableEq, Repr

instance : ToString TINF :=
  ⟨fun | .love => "love" | .admire => "admire" | .help => "help"
       | .defeat => "defeat" | .catch => "catch"⟩

inductive To where
  | to
  deriving DecidableEq, Repr

/-!
Estes nove tipos não se referem uns aos outros nem a `NP`/`VP`/`RCN`/`INF`/
`Sent` — cada um é um enum simples ou tem campos só desses enums, então não
precisam entrar no bloco `mutual` abaixo. Isolá-los deixa visível qual é a
recursão real do fragmento: só `NP`, `RCN`, `VP` e `INF` se chamam entre si
(e a `Sent` que os fecha).
-/

mutual
  inductive Sent where
    | sent (np : NP) (vp : VP)

  inductive NP where
    | snowWhite | alice | dorothy | goldilocks | littleMook | atreyu
    | everyone | someone
    | np1 (det : DET) (cn : CN)
    | np2 (det : DET) (rcn : RCN)

  inductive RCN where
    | rcn1 (cn : CN) (compl : That) (vp : VP)
    | rcn2 (cn : CN) (compl : That) (np : NP) (tv : TV)
    | rcn3 (adj : ADJ) (cn : CN)

  inductive VP where
    | laughed | cheered | shuddered
    | vp1 (tv : TV) (np : NP)
    | vp2 (dv : DV) (np1 np2 : NP)
    | vp3 (av : AV) (marker : To) (inf : INF)

  inductive INF where
    | laugh | cheer | shudder
    | inf1 (tinf : TINF) (np : NP)
end

deriving instance Repr for Sent, NP, RCN, VP, INF

mutual
def Sent.toStringImpl : Sent → String
  | .sent np vp => s!"{np.toStringImpl} {vp.toStringImpl}"

def NP.toStringImpl : NP → String
  | .snowWhite => "Snow White" | .alice => "Alice" | .dorothy => "Dorothy"
  | .goldilocks => "Goldilocks" | .littleMook => "Little Mook"
  | .atreyu => "Atreyu" | .everyone => "everyone" | .someone => "someone"
  | .np1 det cn => s!"{det} {cn}"
  | .np2 det rcn => s!"{det} {rcn.toStringImpl}"

def RCN.toStringImpl : RCN → String
  | .rcn1 cn _ vp => s!"{cn} that {vp.toStringImpl}"
  | .rcn2 cn _ np tv => s!"{cn} that {np.toStringImpl} {tv}"
  | .rcn3 adj cn => s!"{adj} {cn}"

def VP.toStringImpl : VP → String
  | .laughed => "laughed" | .cheered => "cheered" | .shuddered => "shuddered"
  | .vp1 tv np => s!"{tv} {np.toStringImpl}"
  | .vp2 dv np1 np2 => s!"{dv} {np1.toStringImpl} {np2.toStringImpl}"
  | .vp3 av _ inf => s!"{av} to {inf.toStringImpl}"

def INF.toStringImpl : INF → String
  | .laugh => "laugh" | .cheer => "cheer" | .shudder => "shudder"
  | .inf1 tinf np => s!"{tinf} {np.toStringImpl}"
end

instance : ToString Sent := ⟨Sent.toStringImpl⟩

/-!
`That` e `To` são tipos com um único construtor, sem informação nenhuma —
existem porque o capítulo 9 (parsing) os quer como palavras da gramática,
não como marcadores internos. `catch` colide com a palavra reservada do
Lean para captura de exceções; o construtor de `TINF` fica `catch` mesmo
assim, dentro do namespace `TINF`, sem conflito (o Lean resolve pelo
namespace, `TINF.catch` não é `catch` do núcleo).

A Figura 4.1 do livro mostra a árvore de análise de *"The dwarf that Snow
White helped admired every princess"*:

```
S
├── NP
│   ├── DET — the
│   └── RCN
│       ├── CN — dwarf
│       ├── That — that
│       ├── NP — Snow White
│       └── TV — helped
└── VP
    ├── TV — admired
    └── NP
        ├── DET — every
        └── CN — princess
```

pareada com o termo Lean correspondente — a árvore acima não é uma
estrutura auxiliar, é a *notação* deste termo. Três coisas coincidem: a
árvore, o termo Lean que a constrói, e a sentença em inglês que ele
denota sintaticamente — `Repr` imprime o termo (a árvore, por extenso);
`ToString`, definido abaixo, faz o caminho inverso do parsing (assunto do
capítulo 9): devolve, a partir do termo, a sentença de superfície.
-/

def figure4_1 : Sent :=
  .sent (.np2 .the (.rcn2 .dwarf .that .snowWhite .helped))
        (.vp1 .admired (.np1 .every .princess))

#eval figure4_1          -- o termo — a árvore, por extenso
#eval toString figure4_1  -- a sentença que o termo denota

/-!
### Uma categoria, duas leituras

`NP`, `VP` e (aqui) `Sent` reaparecem em `Chapter03.lean` como
`abbrev NP := Entity`, `abbrev VP := NP → S` e `abbrev S := Prop`
(`Chapter03.lean:793-796`) — mas ali são tipos **semânticos**: a categoria
lida como o tipo do significado, na leitura categorial de Ajdukiewicz que
o capítulo 3 estabeleceu. Aqui `NP`/`VP`/`Sent` são construtores de um
`inductive` **sintático**: a categoria lida como nó de uma árvore.

Não é coincidência de nome nem confusão a evitar — é o próprio ponto de
Montague. Uma categoria sintática determina um tipo semântico: `NP`-nó da
árvore e `NP`-tipo do significado são as duas faces da mesma categoria,
ligadas pela leitura categorial. Os capítulos 5 a 7 vão definir a função
que lê um termo como o de `figure4_1` (sintaxe) e devolve um valor do tipo
semântico correspondente (`S`, `VP`, ...) — essa função é a semântica
composicional do fragmento.
-/

/-! ### Exercício 4.6 (p. 69)

Estenda este fragmento com os adjetivos `happy` e `evil`.
-/

def CNWithAdjectives : Type := sorry

/-! ### Exercício 4.7 (p. 69)

Estenda o fragmento com sintagmas preposicionais, de modo que a sentença
*A dwarf defeated a giant with a sword* seja gerada de duas formas
estruturalmente diferentes, enquanto *A dwarf defeated Little Mook with a
sword* só tenha uma forma de ser gerada.
-/

def NPWithPP : Type := sorry

def VPWithPP : Type := sorry

/-! ### Exercício 4.8 (p. 69)

Estenda o fragmento com orações relativas complexas, em que a oração
relativa pode ser uma conjunção de sentenças. O fragmento deve gerar,
entre outras, a sentença *The dwarf that Snow White helped and Goldilocks
admired cheered.* Que problemas você encontra?
-/

def RCNWithCoordination : Type := sorry

/-! ## 4.3 Uma língua para falar de classes

O livro não dá código Haskell nesta seção — adia a implementação para o
motor de inferência do capítulo 5. A gramática é um fragmento minúsculo
para perguntar e afirmar coisas sobre classes:

```
Q ::= Are all PN PN?
    | Are no PN PN?
    | Are any PN PN?
    | Are any PN not PN?
    | What about PN?

S ::= All PN are PN.
    | No PN are PN.
    | Some PN are PN.
    | Some PN are not PN.
```

onde `PN` (plural noun) fica deliberadamente sem gramática própria. A
tradução para Lean é barata e o capítulo 5 a reaproveita — uma base de
conhecimento consultável por essas perguntas e afirmações.
-/

abbrev PN := String

inductive Statement where
  | allAre (a b : PN)
  | noneAre (a b : PN)
  | someAre (a b : PN)
  | someAreNot (a b : PN)
  deriving DecidableEq, Repr

inductive Query where
  | areAllPNPN (a b : PN)
  | areNoPNPN (a b : PN)
  | areAnyPNPN (a b : PN)
  | areAnyPNNotPN (a b : PN)
  | whatAbout (a : PN)
  deriving DecidableEq, Repr

/-! ## 4.4 Lógica proposicional

A gramática de lógica proposicional do livro usa primos para gerar
infinitos átomos:

```
atom −→ p | q | r | atom′
F    −→ atom | ¬F | (F ∧ F) | (F ∨ F)
```

gerando fórmulas como `¬¬¬p‴`, `((p ∨ p′) ∧ p‴)`, `(p ∧ (p′ ∧ p‴))`. Sem
parênteses a gramática é ambígua — `p ∧ p′ ∨ p″` lê-se tanto como
`(p ∧ p′) ∨ p″` quanto como `p ∧ (p′ ∨ p″)`, e a ambiguidade estrutural
afeta o significado, como na sentença em português "era jovem e bonita ou
depravada".

Como no capítulo 2, a lista infinita de átomos (`p, q, r, p′, q′, ...`) se
traduz melhor em Lean como um átomo com nome (`String`), não como uma
enumeração de primos — o "infinitas letras proposicionais" do livro é só
"qualquer string serve de átomo".

Diferente do fragmento de inglês (§4.2), aqui a BNF do próprio livro já é
**binária**: `(F ∧ F)`, não uma lista de conjunctos. A implementação
Haskell troca para `Cnj [Form]`/`Dsj [Form]` — o livro justifica: "listas
Haskell permitem uma solução elegante". Em Lean a lista custa caro: um
`inductive` com `List Form` dentro de si mesmo (`Cnj (fs : List Form)`) é
*nested*, e perde tanto `deriving DecidableEq` quanto a tática `induction`
(que os Exercícios 4.11/4.15 do próprio livro pedem, mais adiante). Fica-se
com a BNF binária do livro, ao pé da letra:
-/

inductive Form where
  | atom (name : String)
  | top
  | bot
  | neg (f : Form)
  | conj (f g : Form)
  | disj (f g : Form)
  deriving DecidableEq, Repr

/-!
`top`/`bot` são a base da recursão de `conjs`/`disjs` abaixo — uma
conjunção vazia é sempre verdadeira, uma disjunção vazia é sempre falsa.
Diferente de um átomo de nome `"⊤"` (que a valoração do capítulo 5,
`(String → Bool) → Form → Bool`, poderia mandar para `false`, dependendo
da atribuição de átomos), `top`/`bot` são construtores próprios: a
valoração vai tratá-los como constantes, sempre `true`/`false`, sem
depender de nenhuma atribuição — é a mesma razão pela qual o livro mostra
`Conj []` como `"true"` e `Disj []` como `"false"` (comentário do livro em
§4.6, p. 81).

Notação n-ária recuperada por duas funções, para os capítulos 5–7 (que
usam `Cnj`/`Dsj` do livro quase sempre com dois elementos, e uma única vez
com mais — `lfDET The`, no capítulo 8):
-/

def Form.conjs : List Form → Form
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Form.conjs fs)

def Form.disjs : List Form → Form
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Form.disjs fs)

/-!
`ToString` em notação polonesa (prefixa), como o livro:
-/

def Form.toStringPolish : Form → String
  | .atom name => name
  | .top => "true"
  | .bot => "false"
  | .neg f => "-" ++ f.toStringPolish
  | .conj f g => "&[" ++ f.toStringPolish ++ "," ++ g.toStringPolish ++ "]"
  | .disj f g => "v[" ++ f.toStringPolish ++ "," ++ g.toStringPolish ++ "]"

instance : ToString Form := ⟨Form.toStringPolish⟩

def form1 : Form := .conj (.atom "p") (.neg (.atom "p"))
#eval toString form1  -- &[p,-p]

def form2 : Form := .disj (.atom "p1") (.disj (.atom "p2") (.disj (.atom "p3") (.atom "p4")))
#eval toString form2  -- v[p1,v[p2,v[p3,p4]]]

/-!
`form2` não é `v[p1,p2,p3,p4]` como no livro — lá `Dsj` toma uma lista de
uma vez; aqui, binário, quatro disjuntos exigem três `disj` encadeados. É
exatamente o preço da escolha binária, e a razão de existir `Form.disjs`:
`disjs` *constrói* esses `disj` encadeados, não achata a saída — o mesmo
`form2` de novo, desta vez a partir da lista:
-/

example :
    Form.disjs [.atom "p1", .atom "p2", .atom "p3", .atom "p4"] = form2 := rfl

-- Simétrico para `conjs`, com a mesma forma de `form2` só troca `∨` por `∧`:
def form2' : Form := .conj (.atom "p1") (.conj (.atom "p2") (.conj (.atom "p3") (.atom "p4")))

example :
    Form.conjs [.atom "p1", .atom "p2", .atom "p3", .atom "p4"] = form2' := rfl

/-!
Abreviações do livro: `F1 → F2` para `¬(F1 ∧ ¬F2)` ("implicação"), e
`F1 ↔ F2` para `(F1 → F2) ∧ (F2 → F1)` ("equivalência").
-/

def Form.impl (f g : Form) : Form := .neg (.conj f (.neg g))
def Form.equi (f g : Form) : Form := .conj (Form.impl f g) (Form.impl g f)

/-! ### Exercício 4.9 (p. 74)

Traduza as sentenças a seguir para lógica proposicional, garantindo que as
condições de verdade sejam capturadas. Que limitações você encontra?

1. *The wizard polishes his wand and learns a new spell, or he is lazy.*
2. *The peasant will deal with the devil only if he has a plan to outwit
   him.*
3. *If neither unicorns nor dragons exist, then neither do goblins.*
-/

def ex49_1 : Form := sorry
def ex49_2 : Form := sorry
def ex49_3 : Form := sorry

/-! ### Exercício 4.10 (p. 74)

O conectivo `∨` é inclusivo: `p ∨ q` é verdadeiro mesmo quando `p` e `q`
são ambos verdadeiros. Em português, "ou" costuma ser exclusivo, como em
"Você pode ficar com o sorvete ou com o algodão-doce, mas não com os
dois." Defina um conectivo `⊕` para "ou exclusivo", usando os conectivos
já definidos.
-/

def Form.xor (f g : Form) : Form := sorry

/-! ### Exercício 4.11 (p. 74)

Use o princípio de indução estrutural para provar que as fórmulas de
lógica proposicional em notação prefixa são de leitura única.
-/

example (f g : Form) (h : Form.neg f = Form.neg g) : f = g := sorry

example (f1 f2 g1 g2 : Form) (h : Form.conj f1 f2 = Form.conj g1 g2) :
    f1 = g1 ∧ f2 = g2 := sorry

/-!
Em Lean, essas duas provas são `injection`, sem indução — um termo de tipo
indutivo *é* a árvore, e o Lean já sabe, para todo `inductive`, que
construtores diferentes produzem valores diferentes, e que um mesmo
construtor com argumentos diferentes produz valores diferentes. É a mesma
observação de "Indução estrutural", abaixo — não à toa a versão Lean deste
exercício é quase vazia: o livro precisa da indução porque define fórmula
como *string* e prova que a árvore de análise é única. Aqui não há string
a analisar: o termo Lean é a árvore.
-/

/-! ### Sintaxe e proposição são coisas diferentes

Um contraste que o livro não precisa fazer, mas Lean exige. O capítulo 3
definiu `abbrev S := Prop` — uma proposição semântica, sem estrutura
interna que se possa inspecionar. `Form`, acima, é um segundo `inductive`
de **sintaxe**: um valor de `Form` é dado, no sentido do capítulo 2 — casa
padrão, conta operadores, mede profundidade, coleta os átomos que
ocorrem nele (Exercícios 4.12–4.14, mais abaixo). Nada disso é possível
sobre um `Prop`: não há como perguntar "quantos `∧` tem esta proposição"
a um valor de tipo `Prop`, porque `Prop` não guarda a fórmula que o
provou, só se ela é verdadeira. A valoração `Form → Bool` — que dá
sentido a `Form` como lógica, e não só como árvore — chega no capítulo 5.

Há um terceiro objeto que responde à mesma pergunta ("o que é uma
fórmula?") de um jeito diferente: `Cslib.Logic.PL.Proposition` (biblioteca
`cslib`, já dependência deste projeto). Também é sintaxe — um `inductive`
de fórmulas —, mas o que se faz com ela é dedução natural (`Γ ⊢ A`), não
valoração. Três respostas, três pontos de vista: `Prop` é a proposição em
si, sem estrutura; `Proposition` do `cslib` é sintaxe mais um sistema de
prova; `Form` daqui é sintaxe mais uma função `Form → Bool`. O capítulo 5
segue a terceira, porque é a que o livro segue.

`Proposition` fica como leitura complementar, não como base do capítulo,
por um motivo de vocabulário: a BNF de §4.4 tem `¬`/`∧`/`∨` primitivos e
introduz `→` só depois, como abreviação; `Proposition` faz o caminho
inverso — `imp` é primitivo, `neg` deriva de `imp · ⊥`, exigindo uma
instância `[Bot Atom]` no tipo dos átomos que não tem motivação
linguística, só satisfaz a typeclass. Adotar `Proposition` obrigaria
`opsNr`/`depth` (Exercícios 4.12–4.13) a passar primeiro por essa
tradução de vocabulário, antes de bater com os números que o livro dá.
Quem quiser ver como um curso de teoria da prova trataria fórmulas
proposicionais em Lean, com dedução natural completa, encontra em
`Cslib.Logic.PL.Proposition`.
-/

/-! ### Indução estrutural

O livro precisa enunciar o Teorema 4.1 (Princípio da Indução Estrutural)
porque raciocina sobre fórmulas como *strings*: para provar algo de toda
fórmula, basta provar da base (átomos) e do passo indutivo (que a
propriedade passa por `¬`, `∧`, `∨`). Em Lean isso não é um teorema a
enunciar — é o recursor que `inductive Form` já gera de graça:
-/

#check @Form.rec

/-!
`Form.rec` — e a tática `induction`, construída sobre ele — já *são* o
princípio de indução estrutural, sem que o capítulo precise declará-lo.
Onde o livro prova a Proposição 4.2 (número igual de parênteses em toda
fórmula) e a Proposição 4.3 (leitura única — o Exercício 4.11 acima é
essa prova), a versão Lean só precisa de `induction`:
-/

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
  | conj _ _ ih1 ih2 => simp [Form.leftParens, Form.rightParens, ih1, ih2]
  | disj _ _ ih1 ih2 => simp [Form.leftParens, Form.rightParens, ih1, ih2]

/-!
Essa é a Proposição 4.2 traduzida — mas com uma ressalva: `Form` binário
já garante um parêntese de abertura por `conj`/`disj`, contado igualmente
nas duas funções por construção; a prova formaliza essa contagem, não
descobre nada de novo sobre a gramática. Já as Proposições 4.3 e os
Exercícios 4.11/4.15 (leitura única) são o caso mais extremo dessa
observação: no livro, precisam de indução estrutural genuína, porque
provam algo sobre *strings* que a gramática gera; em Lean, um termo de
`Form` já é a árvore, não uma string a analisar — não há uma segunda
leitura possível a excluir, e a prova (Exercício 4.11 acima) se reduz a
`injection`.
-/

/-! ### Exercício 4.12 (p. 75)

Implemente uma função `opsNr` para contar o número de operadores de uma
fórmula. O tipo é `opsNr : Form → Nat`. A chamada `opsNr form1` deve dar
`2`.
-/

def Form.opsNr : Form → Nat := sorry

/-! ### Exercício 4.13 (p. 75)

Implemente uma função `depth` para calcular a profundidade da árvore de
análise de uma fórmula. O tipo é `depth : Form → Nat`. A chamada
`depth form1` deve dar `2`.
-/

def Form.depth : Form → Nat := sorry

/-! ### Exercício 4.14 (p. 75)

Implemente `propNames : Form → List String` para coletar a lista de
nomes de átomos proposicionais que ocorrem numa fórmula. A lista
resultante deve estar ordenada e sem repetições.
-/

def Form.propNames : Form → List String := sorry

/-! ## 4.5 Lógica de predicados

Frases como "Todo príncipe viu uma dama" não se relacionam em lógica
proposicional — ficariam como átomos `p`/`q` totalmente desconectados, sem
capturar que a mesma noção de "príncipe" e "viu" está em jogo nas duas.
Lógica de predicados acrescenta três ingredientes à proposicional:

* uma proposição básica estruturada, um predicado `n`-ário seguido de `n`
  variáveis;
* uma fórmula universalmente quantificada, `∀` seguido de variável e
  fórmula;
* uma fórmula existencialmente quantificada, `∃` seguido de variável e
  fórmula.

Por isso o outro nome, "lógica de primeira ordem" — a quantificação é
sobre entidades, objetos de primeira ordem. O livro assume predicados de
aridade até 3 (relações unárias, binárias e ternárias — a última para
verbos como "dar", com sujeito, objeto e destinatário): "relações com mais
de três argumentos quase nunca são necessárias". A BNF completa (usando
primos para gerar infinitas variáveis e infinitos predicados de cada
aridade, como em §4.4):

```
v    −→ x | y | z | v′
P    −→ P | P′
R    −→ R | R′
S    −→ S | S′
atom −→ P v | R v v | S v v v
F    −→ atom | (v = v) | ¬F | (F ∧ F) | (F ∨ F) | ∀v F | ∃v F
```

gerando fórmulas como `¬P′x`, `∀xRxx` ("tudo mantém a relação `R` consigo
mesmo") e `∀x∃x′Rxx′` ("para todo primeiro há algo que é `R`-ado por
ele").

### Ligação de variáveis

Numa fórmula `∀xF` (ou `∃xF`), o quantificador liga toda ocorrência de `x`
em `F` que não esteja já ligada por um `∀x`/`∃x` interno a `F`. Uma
fórmula é **aberta** se tem ao menos uma ocorrência livre de variável, e
**fechada** (também chamada **sentença**) caso contrário. Por exemplo,
`(Px ∧ ∃xRxx)` é aberta — o `x` de `Px` está fora do escopo do `∃x` — mas
`∃x(Px ∧ ∃xRxx)` é uma sentença.

Essa distinção é o que motiva a ambiguidade de escopo de *"Todo príncipe
viu uma dama"*: duas leituras, "para cada príncipe existe uma dama (talvez
diferente) que ele viu" contra "existe uma dama que todo príncipe viu",
formalizadas respectivamente como

```
∀x(Prince x → ∃y(Lady y ∧ Saw x y))
∃y(Lady y ∧ ∀x(Prince x → Saw x y))
```

— repare que a leitura universal usa `→` como conectivo principal, e a
existencial usa `∧`; vale a pena perguntar por quê (o livro retoma isso no
Exercício 5.17). Já *"Algum príncipe viu uma dama bonita"* não é ambígua:
`∃x∃y(Prince x ∧ Lady y ∧ Beautiful y ∧ Saw x y)`.
-/

/-! ### Exercício 4.15 (p. 77) ✎

Prove que as fórmulas desta língua têm a propriedade de leitura única.

**Resposta.** Como no Exercício 4.11 (§4.4): em Lean, um termo de tipo
indutivo *é* a árvore de análise — a prova é `injection` sobre os
construtores, não indução estrutural genuína sobre strings. O livro
precisa da indução porque define fórmula como string e prova que a função
string → árvore é bem definida (dá exatamente uma árvore, nunca duas ou
nenhuma); a versão Lean não tem essa função a definir, então a "leitura
única" vira a afirmação, quase vazia, de que construtores diferentes (ou
o mesmo construtor com argumentos diferentes) produzem termos diferentes
— exatamente o que `Form.noConfusion`/`injection` dão de graça para
qualquer `inductive`.
-/

/-! ### Exercício 4.16 (p. 77) ✎

Dê uma gramática BNF para uma língua de lógica de predicados com
infinitos símbolos de predicado para cada aridade finita. (Dica: use
`‴P`, `‴P′`, `‴P″`, ... para o conjunto de predicados de três lugares, e
assim por diante.)

**Resposta.** A gramática do livro, estendida com um prefixo de primos
por aridade:

```
P0 −→ P0 | P0′        (predicados de aridade 0)
P1 −→ P1 | P1′        (predicados de aridade 1)
P2 −→ P2 | P2′        (predicados de aridade 2)
P3 −→ ‴P | ‴P′         (predicados de aridade 3)
⋮
```

Em Lean, indexar por aridade é mais natural do que empilhar primos: um
`structure PredSymbol` com campos `name : String` e `arity : Nat` já
representa "infinitos predicados de cada aridade finita" sem precisar de
uma família de gramáticas, uma por aridade. Fica como observação — o
capítulo não adota `PredSymbol` como base de `Formula` (abaixo), que segue
o livro e limita a aridade por construção.
-/

/-! ### Exercício 4.17 (p. 78) ✎

Dê as ocorrências ligadas de `x` na fórmula seguinte.

```
∃x(Rxy ∨ Sxyz) ∧ Px
```

**Resposta.** Duas: as duas ocorrências de `x` dentro do escopo do `∃x`
(em `Rxy` e em `Sxyz`). A terceira ocorrência de `x`, em `Px`, está fora
do escopo desse `∃x` — o parêntese fecha antes de `∧ Px` — e por isso é
**livre**, não ligada; a fórmula inteira é aberta. É o ponto fino do
exercício: uma mesma variável pode ter, na mesma fórmula, ocorrências
ligadas e uma ocorrência livre ao mesmo tempo, desde que estejam em
posições diferentes da árvore.
-/

/-! ## 4.6 Fórmulas de predicados em Lean

O "problema da aridade" (predicados de aridade 1, 2, 3, ... exigiriam um
`inductive` por aridade) se resolve como em linguagens como Prolog: um
predicado nomeado por `String`, aplicado a uma **lista** de termos — o
comprimento da lista já determina a aridade, sem precisar de um tipo por
aridade.

Uma variável carrega nome e um índice (lista de inteiros, para gerar
variáveis "frescas" a partir de uma dada — usado a partir do capítulo 6):
-/

structure Variable where
  name : String
  index : List Nat
  deriving DecidableEq, Repr

def Variable.toStringImpl : Variable → String
  | ⟨name, []⟩ => name
  | ⟨name, [i]⟩ => name ++ toString i
  | ⟨name, is⟩ => name ++ String.intercalate "_" (is.map toString)

instance : ToString Variable := ⟨Variable.toStringImpl⟩

def x : Variable := ⟨"x", []⟩
def y : Variable := ⟨"y", []⟩
def z : Variable := ⟨"z", []⟩

/-!
`Formula α` é parametrizado no tipo dos termos que preenchem os
predicados — por ora `α := Variable` (o capítulo 4.7 introduz `Term`,
estruturado, e reaproveita `Formula` trocando o parâmetro).
-/

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

/-!
Por que `Formula` toma lista de fórmulas (`conj`/`disj`), diferente do
`Form` binário de §4.4? Porque, aqui, o livro mostra `Conj []` como
`"true"` e `Disj []` como `"false"` — a conjunção/disjunção vazia é a
motivação para tomar lista desde o início, não uma escolha de
implementação a evitar. `Form` binário funciona bem porque o capítulo 4.4
nunca precisa de conjunções de tamanho variável; aqui, o próprio ponto do
livro (§4.6, no comentário sobre `Show (Formula a)`, p. 81) depende da
lista vazia existir.

Diferente do fragmento de inglês (§4.2) — onde `NP`/`VP`/`RCN`/`INF`/
`Sent` são **mutuamente recursivos**, mas nenhum toma lista de si mesmo,
e por isso mantêm `induction` funcionando — `Formula` é *nested*: a lista
`List (Formula α)` dentro do próprio tipo tira tanto `deriving
DecidableEq` quanto `induction` automática. É a mesma restrição que levou
`Form` a ser binário em §4.4; aqui a lista é essencial ao ponto do livro,
então o custo se paga, e as funções abaixo são recursão explícita.
-/

/-!
`ToString`, como o livro — inclusive a escolha de mostrar `conj []` como
`"true"` e `disj []` como `"false"` (a razão fica clara na semântica do
capítulo 5: são a base neutra de `∧`/`∨`, e como constantes independem de
qualquer atribuição de valores aos átomos):
-/

def Formula.toStringImpl [ToString α] : Formula α → String
  | .atom name [] => name
  | .atom name args => name ++ "[" ++ String.intercalate "," (args.map toString) ++ "]"
  | .eq t1 t2 => s!"{t1}={t2}"
  | .neg f => s!"~{f.toStringImpl}"
  | .impl f1 f2 => s!"({f1.toStringImpl}==>{f2.toStringImpl})"
  | .equi f1 f2 => s!"({f1.toStringImpl}<=>{f2.toStringImpl})"
  | .conj [] => "true"
  | .conj fs => "(" ++ String.intercalate " & " (fs.map Formula.toStringImpl) ++ ")"
  | .disj [] => "false"
  | .disj fs => "(" ++ String.intercalate " | " (fs.map Formula.toStringImpl) ++ ")"
  | .forall_ v f => s!"A{v} {f.toStringImpl}"
  | .exists_ v f => s!"E{v} {f.toStringImpl}"

instance [ToString α] : ToString (Formula α) := ⟨Formula.toStringImpl⟩

def formula0 : Formula Variable := .atom "R" [x, y]
#eval toString formula0  -- R[x,y]

def formula1 : Formula Variable := .forall_ x (.atom "R" [x, x])
#eval toString formula1  -- Ax R[x,x] — reflexividade de R

def formula2 : Formula Variable :=
  .forall_ x (.forall_ y (.impl (.atom "R" [x, y]) (.atom "R" [y, x])))
#eval toString formula2  -- Ax Ay (R[x,y]==>R[y,x]) — simetria de R

/-! ### Exercício 4.18 (p. 81)

Escreva uma função `closedForm : Formula Variable → Bool` que verifica se
uma fórmula é fechada. (Dica: primeiro escreva uma função que coleta a
lista de variáveis livres de uma fórmula. As fórmulas fechadas são as que
têm lista de variáveis livres vazia.)
-/

def freeVarsInFormula : Formula Variable → List Variable := sorry

def closedForm : Formula Variable → Bool := sorry

/-! ### Exercício 4.19 (p. 82)

Implicações e equivalências podem ser vistas como abreviações, pois se
definem a partir de negação e conjunção. Escreva uma função
`withoutIDs : Formula Variable → Formula Variable` que substitui cada
fórmula por uma equivalente sem ocorrências de `impl` ou `equi`.
-/

def withoutIDs : Formula Variable → Formula Variable := sorry

/-! ### Exercício 4.20 (p. 82)

Toda fórmula de lógica de predicados é equivalente a uma fórmula em
**forma normal negativa**, onde negações só ocorrem diante de átomos. A
receita é "empurrar" as negações através dos quantificadores por
`¬∀xF ≡ ∃x¬F` e `¬∃xF ≡ ∀x¬F`, e através de disjunções e conjunções pelas
leis de De Morgan: `¬(F1 ∧ F2) ≡ ¬F1 ∨ ¬F2` e `¬(F1 ∨ F2) ≡ ¬F1 ∧ ¬F2`.
`¬¬F ≡ F` elimina dupla negação. Escreva uma função
`nnf : Formula Variable → Formula Variable` que transforma uma fórmula em
forma normal negativa. (Dica: use a função do exercício anterior para
eliminar `impl`/`equi` primeiro.)

**Cuidado ao implementar** (dica de verdade, não parte da nota de rodapé):
uma função `nnf`/`nnfNeg` mutuamente recursivas, com `nnfNeg` chamando
`nnfNeg (withoutIDs ...)` nos casos de `impl`/`equi`, não termina por
recursão estrutural — o Lean não consegue provar que `withoutIDs f` é
"menor" que `f` (em geral não é: `withoutIDs` pode crescer o termo).
Aplicar `withoutIDs` uma única vez, no início, resolve — mas então as
funções internas ainda precisam cobrir os casos `impl`/`equi`, mesmo que
nunca sejam de fato alcançados depois desse passo.
-/

def nnf : Formula Variable → Formula Variable := sorry

/-! ## 4.7 Símbolos de função

Lógica de predicados, como definida até aqui, não expressa equações de
aritmética escolar: um termo como `(5 + 3) × 4` é complexo, não uma
variável isolada. A solução é introduzir **constantes de função** para
operações arbitrárias — o mesmo movimento de nomear relações binárias
arbitrárias em vez de fixar "menor que" como primitivo.

Termos complexos, com símbolo de função e lista de argumentos — outro
`inductive` nested (a lista de `Term` dentro do próprio `Term`), então
sem `deriving DecidableEq`/`induction`, como `Form` teria sido se a
gramática do livro não fosse binária em §4.4:
-/

inductive Term where
  | var (v : Variable)
  | struct (name : String) (args : List Term)

def Term.toStringImpl : Term → String
  | .var v => toString v
  | .struct name [] => name
  | .struct name args => name ++ "[" ++ String.intercalate "," (args.map Term.toStringImpl) ++ "]"

instance : ToString Term := ⟨Term.toStringImpl⟩

def tx : Term := .var x
def ty : Term := .var y
def tz : Term := .var z

/-!
Um termo **livre para** uma variável `v` numa fórmula `F` é um termo que,
substituído em toda ocorrência livre de `v` em `F`, não tem nenhuma de
suas próprias variáveis capturada por um quantificador de `F`. Substituir
sem essa cautela muda o significado: em `(∀yRxy → ∀xRxx)`, o `x` livre da
premissa, substituído por `y`, produz `(∀yRyy → ∀xRxx)` — o `y` do termo
foi capturado pelo `∀y` que já estava lá. Uma **variante alfabética** (a
mesma fórmula, só renomeando variáveis ligadas — aqui, `(∀zRxz → ∀xRxx)`)
evita a captura.

Com `Term`, `Formula Term` são fórmulas com termos estruturados — o
capítulo 5 em diante usa esse `Formula Term`, não mais `Formula
Variable`.
-/

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

/-! ### Exercício 4.21 (p. 83) ✎

Dê uma árvore de análise para o termo `f″[f′[x, y], f‴[z, z, f[x]]]`.

**Resposta.** A árvore *é* o termo Lean correspondente — sem passo de
tradução a fazer:
-/

def ex421Term : Term :=
  .struct "f2" [ .struct "f1" [tx, ty]
               , .struct "f3" [tz, tz, .struct "f" [tx]] ]

#eval toString ex421Term  -- f2[f1[x,y],f3[z,z,f[x]]]

/-!
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
-/

/-! ### Exercício 4.22 (p. 84)

Implemente uma função `varsInForm : Formula Term → List Variable` que dá
a lista de variáveis que ocorrem numa fórmula.
-/

def varsInForm : Formula Term → List Variable := sorry

/-! ### Exercício 4.23 (p. 84)

Implemente
```
freeVarsInForm : Formula Term → List Variable
```
que dá a lista de variáveis com ocorrências livres numa fórmula.
-/

def freeVarsInForm : Formula Term → List Variable := sorry

/-! ### Exercício 4.24 (p. 84)

Implemente `openForm : Formula Term → Bool` que verifica se uma fórmula
é aberta (ver §4.5).
-/

def openForm : Formula Term → Bool := sorry

end Chapter04
