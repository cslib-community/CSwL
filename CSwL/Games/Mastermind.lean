import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Mastermind (Jogo Senha)" =>
%%%
tag := "Mastermind"
%%%

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
