import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Sintaxe Formal de Fragmentos" =>
%%%
tag := "Chapter04"
htmlSplit := .never
file := "Chapter04"
%%%

Ref. CSwFP/4 (`FSynF`). Formal Syntax for Fragments.

Neste capítulo apresentamos definições de algumas linguagens simples para jogos, linguagens lógicas, fragmentos de linguagens de programação e fragmentos de inglês. Quando passarmos à semântica de fragmentos de inglês, usaremos a lógica de predicados como ferramenta básica. Como preparação para isso, introduzimos a lógica proposicional e a lógica de predicados, observamos como elas podem ser usadas para representar o significado de sentenças em linguagem natural, e mostramos como implementar sua sintaxe em Lean.

```lean
namespace Chapter04
```

# Gramáticas para jogos

## Batalha Naval

Vamos considerar o jogo _Batalha Naval_ e como representa-lo como uma linguagem.

Batalha naval é um jogo de tabuleiro de dois jogadores, no qual os jogadores têm de adivinhar em que quadrados estão os navios do oponente.

Cada jogador tem dois tabuleiros, `10×10` (colunas `A..J`, linhas `0..9`). Um tabuleiro representa a disposição dos navios do jogador e onde ele irá registrar os 'tiros' do seu oponente, o outro representa a tabuleiro do seu oponente, onde ele marca os 'tiros' que realizou, que podem acertar ou erras parte dos navios do oponente. O objetivo de cada jogador é revelar o tabuleiro do oponente, afundando todos os navios a frota adversária.

Modelar o jogo como uma linguagem `L` significa determinarmos quais são as sentenças válidas de nossa linguagem. Como o jogo é jogado em turnos, cada participante faz um ataque, marca a reação do oponente e depois recebe um ataque, indicando a consequência. Desta forma, a sentença `A 10` representa um ataque na posição `A × 10` do tabuleiro adversário. A sentença `hit frigate` representa uma reação a um 'tiro' indicando ele ter atingido parte de uma fragata. A gramática a seguir captura esta idéia.

:::dev "Alexandre Rademaker" (year := 2026)
CSwFP numera as linhas do tabuleiro `1..10` mas na implementação Haskell usar `Int`, o que não corresponde os valores possíveis como esperado. Usamos `0..9` para corresponder os valores possíveis para o tipo `Fin 10` que melhor captura a idéia dos naturais menores que 10.
:::

```bnf
column   ::= "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" ;
row      ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
attack   ::= column row ;
ship     ::= "battleship" | "frigate" | "submarine" | "destroyer" ;
reaction ::= "missed" | "hit" ship | "sunk" ship | "lost_battle" ;
turn     ::= attack reaction ;
```

A imlementação desta gramática é mostrada a seguir, cada construtor é uma regra de produção.

```lean
namespace Battleship

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
  | lost
  deriving DecidableEq, Repr

structure Turn where
  attack : Attack
  reaction : Reaction
  deriving DecidableEq, Repr

end Battleship
```

O tipo `Fin 10` corresponde os números naturais menores que 10. O termo `(10 : Fin 10)` corresponde ao `0` (`10 % 10`, via `OfNat`), mas isso só vale para o literal `10` interpretado nesse tipo. A instância `OfNat (Fin 10) 10` (usada ao escrever `10 : Fin 10`) normaliza o literal por `% 10` antes de guardá-lo. O construtor `⟨n, prova⟩` (`Fin.mk`) exige uma prova de `n < 10` como dado — para `n = 10` essa prova não existe (`10 < 10` é falso), então `⟨10, by omega⟩` sequer elabora. Ou seja, `(10 : Fin 10)` sempre existe via módulo, e `(⟨10, _⟩ : Fin 10)` só existe para `n` de fato menor que `10`.

```lean
#eval (10 : Fin 10)
#eval (11 : Fin 10)

example : (11 : Fin 10) = 1 := rfl
example : ⟨0, by omega⟩ = (0 : Fin 10) := rfl
```

Cada regra reescreve um símbolo não-terminal (à esquerda) numa sequência
de símbolos (à direita); repetindo o processo a partir de `turn` (símbolo inicial)
até só restarem terminais, obtém-se uma jogada válida, como `B 2 missed`.

Chamamos cada passo de reescrita de `⇒` e nele temos os vários estados intermediários para geração de uma sentença válida:

```
 turn ⇒ attack reaction ⇒ attack missed ⇒ ... ⇒ B 2 missed
```

 A repetição de passos é o feixo transitivo e reflexivo que representamos por `⇒*`:

```
turn ⇒* B 2 missed
```

Uma possível extensão de nossa gramática seria representar como sentença um jogo completo entre dois jogadores.

```bnf
game ::= turn | turn game ;
```

Uma forma conveniente de formalizar em Lean esta extensão seria usar o tipo parametrizado `List`. E naturalmente temos uma sequencia de `Turn` de qualquer comprimento.

```lean
namespace Battleship

abbrev Game := List Turn

def game1 : Game :=
  [⟨⟨.B, 2⟩, .missed⟩,
   ⟨⟨.B, 3⟩, .hit .battleship⟩,
   ⟨⟨.B, 4⟩, .sunk .battleship⟩
  ]

end Battleship
```

Note que `game1` não representa um jogo completo. A expressão `B 2 missed` pode ou não ser verdade para um determinado tabuleiro. Ou seja, só temos a _sintaxe_, não temos a _semântica_ do jogo. Existir que o jogo termine quando um dos jogadores é derrotado é também uma questão semântica. Uma regra para "não atacar duas vezes a mesma posição" vai para além da sintaxe ou semântica, refere-se a pragmática do jogo. Até aqui temos uma forma de representar o jogo, não nada falamos sobre o funcionamento do jogo ou como ele deve ser jogado.

## Mastermind (Jogo Senha)

Outra linguagem bem simples é a do Mastermind (Jogo Senha). O Mastermind é um jogo de dois jogadores em que um deles tenta descobrir o código escolhido pelo outro. Um dos jogadores decide uma sequência de quatro pinos coloridos, com as cores escolhidas dentro de um conjunto fixo. O outro jogador (quem tenta decifrar) tenta adivinhar o padrão de cores. Depois de cada palpite, quem propôs o código dá uma resposta indicando sua correção. Essa resposta consiste numa sequência de pinos pretos e brancos: um pino preto para cada pino da cor certa na posição certa, e um pino branco para cada pino adicional da cor certa, mas na posição errada. Se o código secreto é vermelho, azul, verde, amarelo, e o palpite é verde, azul, vermelho, laranja, a resposta é um preto (o azul está na posição certa) e dois brancos (verde e vermelho aparecem no palpite, mas nas posições erradas). Os palpites e as respostas se alternam até que o padrão seja descoberto. O desafio é adivinhar o padrão no menor número de tentativas.

```bnf
colour ::= "red" | "yellow" | "blue" | "green" | "orange" ;
answer ::= "black" | "white" ;
guess ::= colour colour colour colour ;
reaction ::= answer
  | answer answer
  | answer answer answer
  | answer answer answer answer ;
turn ::= guess reaction ;
game ::= turn | turn game ;
```

Note que os pinos pretos e brancos são colocados em qualquer ordem, não correspondem a uma sinalização por posição. Uma desvantagem da implementação a seguir é que dois diferentes termos do tipo `Reaction` poderiam representar a mesma _resposta_  para uma tentativa. Sobre a definição de `Subtypes`, ver {citep Bib.love2026}[Seção 12.4].

```lean
namespace Mastermind

inductive Colour where
  | red | yellow | blue | green | orange
  deriving DecidableEq, Repr

inductive Answer where
  | black | white
  deriving DecidableEq, Repr

abbrev Guess := Vector Colour 4

/-- uma alternativa `Vector (Option Answer) 4` -/
abbrev Reaction := { r : List Answer // r.length ≤ 4 }

structure Turn where
  guess : Guess
  reaction : Reaction
  deriving DecidableEq, Repr

abbrev Game := List Turn

def turn1 : Turn :=
  ⟨#v[.green, .blue, .red, .orange],
   (⟨[.black, .white], by simp⟩ : Reaction) ⟩

end Mastermind
```

::::exercise (rating := 1) (name := "mastermind-4-passos")

Revise a gramática para garantir que um jogo tenha no máximo quatro
jogadas.

```lean
namespace Mastermind

abbrev Game₄ := solution!(Vector Turn 4)

end Mastermind
```
::::


::::exercise (rating := 1) (name := "chess-grammar")

Escreva suas próprias gramáticas para o xadrez e em seguida sua implementação no Lean.

```bnf
figure ::= "King" | "Queen" | "Knight"
  | "Rook" | "Bishop" | "Pawn" ;
row    ::= "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" ;
column ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" ;
move   ::= figure row column ;
turn   ::= move move ;
game   ::= turn | turn game ;
```

```lean
namespace Chess

inductive Figure where
  | king | queen | knight | rook | bishop | pawn
  deriving DecidableEq, Repr

inductive Row where
  | a | b | c | d | e | f | g | h
  deriving DecidableEq, Repr

structure Move where
  figure : Figure
  row : Row
  column : Fin 8
  deriving DecidableEq, Repr

structure Turn where
  white : Move
  black : Move
  deriving DecidableEq, Repr

abbrev Game := List Turn

end Chess
```
::::

::::quiz
Todas as gramáticas que discutimos geram linguagens infinitas?

:::quizSolution
O sinal claro de uma linguagem livre de contexto infinita é uma regra de produção da forma `A → W A V`, em que `W` e `V` não são ambos vazios. Um exemplo é a regra `game → turn game`. Isso é chamado de uso recursivo de um não-terminal. A recursão também pode ser indireta, passando por um ou mais outros não-terminais: `A → W B V`, `B → Y A Z`. Basta procurar esse tipo de recursão nas gramáticas para identificar quais delas geram linguagens infinitas.
:::
::::

A partir das discussões acima, poderíamos sugerir uma primeira gramática para um fragmennto do inglês talvez um tanto quanto permissiva. Qualquer sequencia de caracteres ASCII.

```bnf
 character ::= _ascii ;
 string ::= character | character string ;
```

# Um fragmento do inglês

Em seguida, vamos implementar um fragmento um pouco mais realistico do inglês.  Ela é deliberadamente básica e grosseira, queremos capturar a sintaxe de sentenças como:

1. The girl laughed.
2. No dwarf admired some princess that shuddered.
3. Every girl that some boy loved cheered.
4. The wizard that helped Snow White defeated the giant.

Então o que precisamos é uma regra para uma sentença sujeito-predicado. Uma regra para a estrutura interna de um sintagma nominal. Uma regra para substantivos com ou sem clausulas relativas. Nossa gramática poderia ser:

```bnf
S    ::= NP VP ;
NP   ::= "Snow White" | "Alice" | "Dorothy" | "Goldilocks" | "Little Mook" | "Atreyu"
      | DET CN | DET RCN ;
DET  ::= "the" | "a" | "every" | "some" | "no" | "most" ;
CN   ::= "girl" | "boy" | "princess" | "dwarf" | "giant" | "wizard" | "sword" | "dagger" ;
RCN  ::= CN "that" VP | CN "that" NP TV ;
VP   ::= "laughed" | "cheered" | "shuddered" | TV NP | DV NP NP ;
TV   ::= "loved" | "admired" | "helped" | "defeated" | "caught" ;
DV   ::= "gave" ;
```

A implementação abaixo acrescenta tipos auxiliares aos oito não-terminais da BNF, introduzidos para ilustrar intensionalidade mais adiante.

A tradução para Lean é direta: cada categoria sintática é um construtor de um `inductive` mutuamente recursivo — a árvore de análise de uma sentença é um termo desse tipo, sem passo de tradução string→árvore a definir.

```lean
inductive DET where
  | a | the | every | some | no | most
  deriving Repr

instance : ToString DET :=
  ⟨fun | .a => "a" | .the => "the"
       | .every => "every" | .some => "some"
       | .no => "no" | .most => "most"⟩

inductive CN where
  | girl | boy | princess | dwarf | giant | wizard | sword
  | dagger
  deriving Repr

instance : ToString CN :=
  ⟨fun | .girl => "girl" | .boy => "boy"
       | .princess => "princess" | .dwarf => "dwarf"
       | .giant => "giant" | .wizard => "wizard"
       | .sword => "sword" | .dagger => "dagger"⟩

inductive ADJ where
  | fake
  deriving Repr

instance : ToString ADJ := ⟨fun | .fake => "fake"⟩

inductive That where
  | that
  deriving Repr

inductive TV where
  | loved | admired | helped | defeated | caught
  deriving Repr

instance : ToString TV :=
  ⟨fun | .loved => "loved" | .admired => "admired"
       | .helped => "helped" | .defeated => "defeated"
       | .caught => "caught"⟩

inductive DV where
  | gave
  deriving Repr

instance : ToString DV := ⟨fun | .gave => "gave"⟩

inductive AV where
  | hoped | wanted
  deriving Repr

instance : ToString AV :=
  ⟨fun | .hoped => "hoped" | .wanted => "wanted"⟩

inductive TINF where
  | love | admire | help | defeat | catch
  deriving Repr

instance : ToString TINF :=
  ⟨fun | .love => "love" | .admire => "admire"
       | .help => "help" | .defeat => "defeat"
       | .catch => "catch"⟩

inductive To where
  | to
  deriving Repr
```

Estes nove tipos não se referem uns aos outros nem a
`NP`/`VP`/`RCN`/`INF`/`Sent` — cada um é um enum simples ou tem campos
só desses enums, então não precisam entrar no bloco `mutual` abaixo.
Isolá-los deixa visível qual é a recursão real do fragmento: só `NP`,
`RCN`, `VP` e `INF` se referenciam (e a `Sent` que os fecha).

```lean
mutual
  inductive Sent where
    | sent (np : NP) (vp : VP)
  deriving Repr

  inductive NP where
    | snowWhite | alice | dorothy | goldilocks | littleMook
    | atreyu
    | everyone | someone
    | np1 (det : DET) (cn : CN)
    | np2 (det : DET) (rcn : RCN)
  deriving Repr

  inductive RCN where
    | rcn1 (cn : CN) (compl : That) (vp : VP)
    | rcn2 (cn : CN) (compl : That) (np : NP) (tv : TV)
    | rcn3 (adj : ADJ) (cn : CN)
  deriving Repr

  inductive VP where
    | laughed | cheered | shuddered
    | vp1 (tv : TV) (np : NP)
    | vp2 (dv : DV) (np1 np2 : NP)
    | vp3 (av : AV) (marker : To) (inf : INF)
  deriving Repr

  inductive INF where
    | laugh | cheer | shudder
    | inf1 (tinf : TINF) (np : NP)
  deriving Repr
end
mutual

def Sent.toStringImpl : Sent → String
  | .sent np vp => s!"{np.toStringImpl} {vp.toStringImpl}"

def NP.toStringImpl : NP → String
  | .snowWhite => "Snow White" | .alice => "Alice"
  | .dorothy => "Dorothy" | .goldilocks => "Goldilocks"
  | .littleMook => "Little Mook" | .atreyu => "Atreyu"
  | .everyone => "everyone" | .someone => "someone"
  | .np1 det cn => s!"{det} {cn}"
  | .np2 det rcn => s!"{det} {rcn.toStringImpl}"

def RCN.toStringImpl : RCN → String
  | .rcn1 cn _ vp => s!"{cn} that {vp.toStringImpl}"
  | .rcn2 cn _ np tv => s!"{cn} that {np.toStringImpl} {tv}"
  | .rcn3 adj cn => s!"{adj} {cn}"

def VP.toStringImpl : VP → String
  | .laughed => "laughed" | .cheered => "cheered"
  | .shuddered => "shuddered"
  | .vp1 tv np => s!"{tv} {np.toStringImpl}"
  | .vp2 dv np1 np2 =>
    s!"{dv} {np1.toStringImpl} {np2.toStringImpl}"
  | .vp3 av _ inf => s!"{av} to {inf.toStringImpl}"

def INF.toStringImpl : INF → String
  | .laugh => "laugh" | .cheer => "cheer"
  | .shudder => "shudder"
  | .inf1 tinf np => s!"{tinf} {np.toStringImpl}"
end

instance : ToString Sent := ⟨Sent.toStringImpl⟩
```

`That` e `To` são tipos com um único construtor. `catch` colide com a palavra reservada do Lean para captura de exceções; o construtor de `TINF` fica `catch` mesmo assim, dentro do namespace `TINF`, sem conflito (o Lean resolve pelo namespace, `TINF.catch` não é `catch` do núcleo).

A árvore de análise de "The dwarf that Snow White helped admired every
princess" é como segue, construir esta árvore a partir da string é o que chamamos de _parsing_.

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

O termo Lean correspondente segue. Note que a sentença em inglês é uma sequencia de caracteres em um alfabeto, uma string no computador. A árvore é a representação abstrata da estrutura da sentença, o termo Lean é a formalização desta representação. `Repr` imprime o termo; `ToString` faz o caminho inverso do _parsing_, devolve, a partir do termo, a sentença de superfície.

```lean
def snowWhile : Sent :=
  .sent (.np2 .the (.rcn2 .dwarf .that .snowWhite .helped))
        (.vp1 .admired (.np1 .every .princess))

#eval snowWhile
#eval toString snowWhile
```

::::exercise (rating := 1) (name := "preposition-phrase")

Estenda o fragmento com sintagmas preposicionais, de modo que a
sentença "A dwarf defeated a giant with a sword" seja gerada de duas
formas estruturalmente diferentes, enquanto "A dwarf defeated Little
Mook with a sword" só tenha uma forma de ser gerada.

Primeiro acrescentamos duas regras para construir PPs a partir de uma
preposição e um NP. Em seguida estendemos a regra de NPs, para gerar NPs
como a giant with a sword. Note que não simplesmente acrescentamos uma
produção recursiva `NP → NP PP`. Se fizéssemos isso, não só permitiríamos
um número arbitrário de PPs como modificadores de NP, mas também
geraríamos NPs como "Little Mook with a sword" (o que queremos excluir).
Por fim, também estendemos a regra de VP para construir VPs com sintagmas
preposicionais.

```bnf
P   ::= "with" ;
PP  ::= P NP ;
NP  ::= _NP | DET CN PP ;
VP  ::= _VP | TV NP PP ;
```

Como `inductive` em Lean é fechado — não dá para acrescentar construtores a um tipo já definido —, a extensão exige redefinir todo o agrupamento mutuamente recursivo (`Sent`, `NP`, `RCN`, `VP`, `INF`), acrescentando `PP` a ele, em vez de simplesmente estender `NP`/`VP` originais. Isolamos o restante num namespace próprio, para não afetar o fragmento original de `NP`/`VP` sem PPs.

```lean
namespace WithPP

inductive P where
  | «with»
  deriving Repr

instance : ToString P := ⟨fun | .with => "with"⟩

mutual
  inductive Sent where
    | sent (np : NP) (vp : VP)
  deriving Repr

  inductive NP where
    | snowWhite | alice | dorothy | goldilocks | littleMook
    | atreyu
    | everyone | someone
    | np1 (det : DET) (cn : CN)
    | np2 (det : DET) (rcn : RCN)
    | np3 (det : DET) (cn : CN) (pp : PP)
  deriving Repr

  inductive RCN where
    | rcn1 (cn : CN) (compl : That) (vp : VP)
    | rcn2 (cn : CN) (compl : That) (np : NP) (tv : TV)
    | rcn3 (adj : ADJ) (cn : CN)
  deriving Repr

  inductive VP where
    | laughed | cheered | shuddered
    | vp1 (tv : TV) (np : NP)
    | vp2 (dv : DV) (np1 np2 : NP)
    | vp3 (av : AV) (marker : To) (inf : INF)
    | vp4 (tv : TV) (np : NP) (pp : PP)
  deriving Repr

  inductive INF where
    | laugh | cheer | shudder
    | inf1 (tinf : TINF) (np : NP)
  deriving Repr

  inductive PP where
    | pp1 (p : P) (np : NP)
  deriving Repr
end

mutual

def Sent.toStringImpl : Sent → String
  | .sent np vp => s!"{np.toStringImpl} {vp.toStringImpl}"

def NP.toStringImpl : NP → String
  | .snowWhite => "Snow White"
  | .alice => "Alice"
  | .dorothy => "Dorothy"
  | .goldilocks => "Goldilocks"
  | .littleMook => "Little Mook"
  | .atreyu => "Atreyu"
  | .everyone => "everyone" | .someone => "someone"
  | .np1 det cn => s!"{det} {cn}"
  | .np2 det rcn => s!"{det} {rcn.toStringImpl}"
  | .np3 det cn pp => s!"{det} {cn} {pp.toStringImpl}"

def RCN.toStringImpl : RCN → String
  | .rcn1 cn _ vp => s!"{cn} that {vp.toStringImpl}"
  | .rcn2 cn _ np tv => s!"{cn} that {np.toStringImpl} {tv}"
  | .rcn3 adj cn => s!"{adj} {cn}"

def VP.toStringImpl : VP → String
  | .laughed => "laughed" | .cheered => "cheered"
  | .shuddered => "shuddered"
  | .vp1 tv np => s!"{tv} {np.toStringImpl}"
  | .vp2 dv np1 np2 =>
    s!"{dv} {np1.toStringImpl} {np2.toStringImpl}"
  | .vp3 av _ inf => s!"{av} to {inf.toStringImpl}"
  | .vp4 tv np pp =>
    s!"{tv} {np.toStringImpl} {pp.toStringImpl}"

def INF.toStringImpl : INF → String
  | .laugh => "laugh" | .cheer => "cheer"
  | .shudder => "shudder"
  | .inf1 tinf np => s!"{tinf} {np.toStringImpl}"

def PP.toStringImpl : PP → String
  | .pp1 p np => s!"{p} {np.toStringImpl}"

end

instance : ToString Sent := ⟨Sent.toStringImpl⟩
```

A ambiguidade pedida está em `giantWithSword1`/`giantWithSword2`: o PP
`with a sword` pode se ligar dentro do NP (modificando `a giant`) ou
direto na VP (modificando o evento de derrotar); as duas árvores são
diferentes, mas produzem a mesma sentença de superfície. Já
`mookWithSword` só admite a segunda leitura, porque `NP ::= DET CN PP`
exige um determinante e `CN`, e "Little Mook" é um nome próprio sem
determinante — não há como formar `Little Mook with a sword` como um
único NP.

```lean
-- PP dentro do NP objeto ("a giant with a sword" é um NP).
def giantWithSword1 : Sent :=
  .sent (.np1 .a .dwarf)
    (.vp1 .defeated
      (.np3 .a .giant (.pp1 .with (.np1 .a .sword))))

-- mesma sentença, PP ligado à VP em vez do NP.
def giantWithSword2 : Sent :=
  .sent (.np1 .a .dwarf)
    (.vp4 .defeated (.np1 .a .giant)
      (.pp1 .with (.np1 .a .sword)))

-- única leitura possível
def mookWithSword : Sent :=
  .sent (.np1 .a .dwarf)
    (.vp4 .defeated .littleMook
      (.pp1 .with (.np1 .a .sword)))

end WithPP
```

```lean (name := c4evalPP1)
#eval toString WithPP.giantWithSword1
#eval toString WithPP.giantWithSword2
#eval toString WithPP.mookWithSword
```

As duas árvores diferentes imprimem a mesma sentença de superfície,
a ambiguidade pedida.
::::

::::exercise (rating := 1) (name := "complex-relative-clauses")

Estenda o fragmento com orações relativas complexas, em que a oração relativa coordena duas VPs paralelas ou dois pares NP-TV paralelos (não sentenças completas). O fragmento deve gerar, entre outras, a sentença "The dwarf that Snow White helped and Goldilocks admired cheered". Que problemas você encontra?

Acrescentamos `COORD` e duas regras para `RCN`, cada uma coordenando
duas ocorrências da mesma forma — ou duas VPs, ou dois pares NP-TV:

```bnf
COORD ::= "and" ;
RCN   ::= _RCN | CN "that" VP COORD VP
               | CN "that" NP TV COORD NP TV ;
```

Como antes, `inductive` fechado obriga a redefinir todo o agrupamento
mutual só para acrescentar construtores a `RCN`.

```lean
namespace WithCoord

inductive COORD where
  | and
  deriving Repr

instance : ToString COORD := ⟨fun | .and => "and"⟩

mutual
  inductive Sent where
    | sent (np : NP) (vp : VP)
  deriving Repr

  inductive NP where
    | snowWhite | alice | dorothy | goldilocks | littleMook
    | atreyu
    | everyone | someone
    | np1 (det : DET) (cn : CN)
    | np2 (det : DET) (rcn : RCN)
  deriving Repr

  inductive RCN where
    | rcn1 (cn : CN) (compl : That) (vp : VP)
    | rcn2 (cn : CN) (compl : That) (np : NP) (tv : TV)
    | rcn3 (adj : ADJ) (cn : CN)
    | rcn4 (cn : CN) (compl : That)
        (vp1 : VP) (coord : COORD) (vp2 : VP)
    | rcn5 (cn : CN) (compl : That)
        (np1 : NP) (tv1 : TV) (coord : COORD)
        (np2 : NP) (tv2 : TV)
  deriving Repr

  inductive VP where
    | laughed | cheered | shuddered
    | vp1 (tv : TV) (np : NP)
    | vp2 (dv : DV) (np1 np2 : NP)
    | vp3 (av : AV) (marker : To) (inf : INF)
  deriving Repr

  inductive INF where
    | laugh | cheer | shudder
    | inf1 (tinf : TINF) (np : NP)
  deriving Repr
end

mutual

def Sent.toStringImpl : Sent → String
  | .sent np vp => s!"{np.toStringImpl} {vp.toStringImpl}"

def NP.toStringImpl : NP → String
  | .snowWhite => "Snow White" | .alice => "Alice"
  | .dorothy => "Dorothy" | .goldilocks => "Goldilocks"
  | .littleMook => "Little Mook" | .atreyu => "Atreyu"
  | .everyone => "everyone" | .someone => "someone"
  | .np1 det cn => s!"{det} {cn}"
  | .np2 det rcn => s!"{det} {rcn.toStringImpl}"

def RCN.toStringImpl : RCN → String
  | .rcn1 cn _ vp => s!"{cn} that {vp.toStringImpl}"
  | .rcn2 cn _ np tv => s!"{cn} that {np.toStringImpl} {tv}"
  | .rcn3 adj cn => s!"{adj} {cn}"
  | .rcn4 cn _ vp1 coord vp2 =>
    s!"{cn} that {vp1.toStringImpl} {coord} " ++
      s!"{vp2.toStringImpl}"
  | .rcn5 cn _ np1 tv1 coord np2 tv2 =>
    s!"{cn} that {np1.toStringImpl} {tv1} {coord} " ++
      s!"{np2.toStringImpl} {tv2}"

def VP.toStringImpl : VP → String
  | .laughed => "laughed" | .cheered => "cheered"
  | .shuddered => "shuddered"
  | .vp1 tv np => s!"{tv} {np.toStringImpl}"
  | .vp2 dv np1 np2 =>
    s!"{dv} {np1.toStringImpl} {np2.toStringImpl}"
  | .vp3 av _ inf => s!"{av} to {inf.toStringImpl}"

def INF.toStringImpl : INF → String
  | .laugh => "laugh" | .cheer => "cheer"
  | .shudder => "shudder"
  | .inf1 tinf np => s!"{tinf} {np.toStringImpl}"

end

instance : ToString Sent := ⟨Sent.toStringImpl⟩

end WithCoord
```

Dois exemplos: a sentença do enunciado usa `rcn5` (coordenação de
pares NP-TV, a RCN é sobre o objeto em ambos os ramos); a outra usa
`rcn4` (coordenação de VPs, a RCN é sobre o sujeito em ambos os ramos).

```lean (name := c4evalCoord1)
#eval toString (WithCoord.Sent.sent
  (.np2 .the  (.rcn5 .dwarf .that .snowWhite .helped
     .and .goldilocks .admired))
  .cheered)
```

```lean (name := c4evalCoord2)
#eval toString (WithCoord.Sent.sent
  (.np2 .the (.rcn4 .dwarf .that
    (.vp1 .helped .goldilocks) .and
    (.vp1 .admired .snowWhite)))
  .laughed)
```

`rcn4` e `rcn5` só coordenam formas paralelas (VP com VP, ou NP-TV com NP-TV), exatamente porque são regras separadas; misturá-las produziria "the dwarf that Goldilocks helped and admired Snow White", que é agramatical: na primeira RCN o vazio (_gap_) está no objeto ("Goldilocks helped ␣"), na segunda está no sujeito ("␣ admired Snow White"), e não há como coordenar as duas leituras numa só sentença. Coordenar `Sent` inteiras em vez de VPs/pares NP-TV geraria justamente essa mistura, por isso o fragmento não faz isso.

O _gap_ é a posição, dentro da `RCN`, onde entraria o `CN` que ela modifica — em `rcn1` (`CN "that" VP`) o gap é o sujeito da VP; em `rcn2` (`CN "that" NP TV`) é o objeto do TV. `rcn4` sempre coordena dois gaps-sujeito e `rcn5` dois gaps-objeto; nenhuma das duas mistura um tipo de gap com o outro.

O problema é que `rcn4`/`rcn5` não são recursivas: cada uma coordena exatamente duas ocorrências. Não é possível gerar "the dwarf that helped Goldilocks and admired the princess that shuddered and laughed" sem acrescentar mais uma regra para RCNs de três coordenadas, depois quatro, e assim por diante — o fragmento não captura a generalização "coordenação de qualquer número de VPs paralelas".
::::


# Uma língua para falar de classes

O livro não dá código Haskell nesta seção — adia a implementação para
o motor de inferência do capítulo 5. A gramática é um fragmento
minúsculo para perguntar e afirmar coisas sobre classes:

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

```lean
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
```

# Lógica proposicional

Uma gramática de lógica proposicional usa primos para gerar infinitos
átomos:

```
atom −→ p | q | r | atom′
F    −→ atom | ¬F | (F ∧ F) | (F ∨ F)
```

gerando fórmulas como `¬¬¬p‴`, `((p ∨ p′) ∧ p‴)`, `(p ∧ (p′ ∧ p‴))`.
Sem parênteses a gramática é ambígua — `p ∧ p′ ∨ p″` lê-se tanto como
`(p ∧ p′) ∨ p″` quanto como `p ∧ (p′ ∨ p″)`, e a ambiguidade estrutural
afeta o significado, como na sentença em português "era jovem e
bonita ou depravada".

Como no capítulo 2, a lista infinita de átomos (`p, q, r, p′, q′, ...`)
se traduz melhor em Lean como um átomo com nome (`String`), não como
uma enumeração de primos: "infinitas letras proposicionais" vira só
"qualquer string serve de átomo".

A gramática é *binária*: `(F ∧ F)`, não uma lista de conjunctos.
Mantemos essa forma binária ao pé da letra porque, em Lean, uma lista
custa caro aqui: um `inductive` com `List Form` dentro de si mesmo
(`Cnj (fs : List Form)`) é _nested_, e perde tanto `deriving
DecidableEq` quanto a tática `induction` (que os Exercícios 4.11/4.15
pedem, mais adiante).

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

## Sintaxe e proposição são coisas diferentes

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

## Indução estrutural

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

# Lógica de predicados

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
predicados de cada aridade, como em §4.4):

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

## Ligação de variáveis

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
a existencial usa `∧`; vale a pena perguntar por quê (retomamos isso no
Exercício 5.17). Já _"Algum príncipe viu uma dama bonita"_ não é
ambígua: `∃x∃y(Prince x ∧ Lady y ∧ Beautiful y ∧ Saw x y)`.

## Exercício 4.15 (p. 77) ✎

Prove que as fórmulas desta língua têm a propriedade de leitura única.

*Resposta.* Como no Exercício 4.11 (§4.4): em Lean, um termo de tipo
indutivo _é_ a árvore de análise — a prova é `injection` sobre os
construtores, não indução estrutural genuína sobre strings. Provar
leitura única para uma gramática dada como string exige mostrar que a
função string → árvore é bem definida (dá exatamente uma árvore, nunca
duas ou nenhuma); a versão Lean não tem essa função a definir, então a
"leitura única" vira a afirmação, quase vazia, de que construtores
diferentes (ou o mesmo construtor com argumentos diferentes) produzem
termos diferentes — exatamente o que `Form.noConfusion`/`injection`
dão de graça para qualquer `inductive`.

## Exercício 4.16 (p. 77) ✎

Dê uma gramática BNF para uma língua de lógica de predicados com
infinitos símbolos de predicado para cada aridade finita. (Dica: use
`‴P`, `‴P′`, `‴P″`, ... para o conjunto de predicados de três lugares,
e assim por diante.)

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

## Exercício 4.17 (p. 78) ✎

Dê as ocorrências ligadas de `x` na fórmula seguinte.

```
∃x(Rxy ∨ Sxyz) ∧ Px
```

*Resposta.* Duas: as duas ocorrências de `x` dentro do escopo do `∃x`
(em `Rxy` e em `Sxyz`). A terceira ocorrência de `x`, em `Px`, está
fora do escopo desse `∃x` — o parêntese fecha antes de `∧ Px` — e por
isso é *livre*, não ligada; a fórmula inteira é aberta. É o ponto fino
do exercício: uma mesma variável pode ter, na mesma fórmula,
ocorrências ligadas e uma ocorrência livre ao mesmo tempo, desde que
estejam em posições diferentes da árvore.

# Fórmulas de predicados em Lean

O "problema da aridade" (predicados de aridade 1, 2, 3, ... exigiriam
um `inductive` por aridade) se resolve como em linguagens como Prolog:
um predicado nomeado por `String`, aplicado a uma *lista* de termos —
o comprimento da lista já determina a aridade, sem precisar de um tipo
por aridade.

Uma variável carrega nome e um índice (lista de inteiros, para gerar
variáveis "frescas" a partir de uma dada — usado a partir do capítulo
6):

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
predicados — por ora `α := Variable` (o capítulo 4.7 introduz `Term`,
estruturado, e reaproveita `Formula` trocando o parâmetro).

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
`Form` binário de §4.4? Porque a conjunção/disjunção vazia — `conj []`
como `"true"`, `disj []` como `"false"` — é a motivação para tomar
lista desde o início, não uma escolha de implementação a evitar.
`Form` binário funciona bem porque §4.4 nunca precisa de conjunções de
tamanho variável; aqui, a conjunção/disjunção vazia como valor sensato
(ver `toStringImpl` abaixo, e a semântica do capítulo 5) depende da
lista vazia existir.

Diferente do fragmento de inglês (§4.2) — onde `NP`/`VP`/`RCN`/`INF`/
`Sent` são *mutuamente recursivos*, mas nenhum toma lista de si
mesmo, e por isso mantêm `induction` funcionando — `Formula` é
_nested_: a lista `List (Formula α)` dentro do próprio tipo tira
tanto `deriving DecidableEq` quanto `induction` automática. É a mesma
restrição que levou `Form` a ser binário em §4.4; aqui a lista é
essencial, então o custo se paga, e as funções abaixo são recursão
explícita.

`ToString` — inclusive a escolha de mostrar `conj []` como `"true"` e
`disj []` como `"false"` (a razão fica clara na semântica do capítulo
5: são a base neutra de `∧`/`∨`, e como constantes independem de
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

## Exercício 4.18 (p. 81)

Escreva uma função `closedForm : Formula Variable → Bool` que verifica
se uma fórmula é fechada. (Dica: primeiro escreva uma função que
coleta a lista de variáveis livres de uma fórmula. As fórmulas
fechadas são as que têm lista de variáveis livres vazia.)

```lean
def freeVarsInFormula : Formula Variable → List Variable :=
  sorry
```

::::exercise (rating := 1) (name := "4.18-closedForm")

A definição de `closedForm`, a partir de `freeVarsInFormula` acima
(que fica como exercício aberto).

```lean
def closedForm (f : Formula Variable) : Bool :=
  solution!((freeVarsInFormula f).isEmpty)
```

::::

## Exercício 4.19 (p. 82)

Implicações e equivalências podem ser vistas como abreviações, pois se
definem a partir de negação e conjunção. Escreva uma função
`withoutIDs : Formula Variable → Formula Variable` que substitui cada
fórmula por uma equivalente sem ocorrências de `impl` ou `equi`.

```lean
def withoutIDs : Formula Variable → Formula Variable :=
  sorry
```

## Exercício 4.20 (p. 82)

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

# Símbolos de função

Lógica de predicados, como definida até aqui, não expressa equações
de aritmética escolar: um termo como `(5 + 3) × 4` é complexo, não uma
variável isolada. A solução é introduzir *constantes de função* para
operações arbitrárias — o mesmo movimento de nomear relações binárias
arbitrárias em vez de fixar "menor que" como primitivo.

Termos complexos, com símbolo de função e lista de argumentos — outro
`inductive` nested (a lista de `Term` dentro do próprio `Term`), então
sem `deriving DecidableEq`/`induction`, como `Form` teria sido se a
gramática de §4.4 não fosse binária:

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
capítulo 5 em diante usa esse `Formula Term`, não mais `Formula
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

## Exercício 4.21 (p. 83) ✎

Dê uma árvore de análise para o termo `f″[f′[x, y], f‴[z, z, f[x]]]`.

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

## Exercício 4.22 (p. 84)

Implemente uma função `varsInForm : Formula Term → List Variable` que
dá a lista de variáveis que ocorrem numa fórmula.

```lean
def varsInForm : Formula Term → List Variable := sorry
```

## Exercício 4.23 (p. 84)

Implemente

```
freeVarsInForm : Formula Term → List Variable
```

que dá a lista de variáveis com ocorrências livres numa fórmula.

```lean
def freeVarsInForm : Formula Term → List Variable := sorry
```

::::exercise (rating := 1) (name := "4.24")

Ref. CSwFP/4, exercício 4.24 (p. 84).

Implemente `openForm : Formula Term → Bool` que verifica se uma
fórmula é aberta (ver seção de ligação de variáveis).

A definição de `openForm`, a partir de `freeVarsInForm` acima (que
fica como exercício aberto).

```lean
def openForm (f : Formula Term) : Bool :=
  solution!(!(freeVarsInForm f).isEmpty)
```

::::

```lean
end Chapter04
```
