import CSwLMeta
import Bib
import CSwL.ModelChecking

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "A composição do significado na língua natural" =>
%%%
tag := "Composition"
htmlSplit := .never
file := "Composition"
%%%

```lean
namespace Composition
```

:::full
Em {ref "ModelChecking"}[Verificação de modelos com lógica de primeira ordem] demos uma interpretação indireta para o nosso fragmento do inglês. Traduzimos sentenças para formas lógicas e depois avaliamos essas formas lógicas em relação a um modelo. As formas lógicas eram fórmulas da lógica de predicados, construídas a partir de expressões da lógica tipada.
Usamos o Lean como implementação do cálculo lambda para esse procedimento de construção. Isso funcionou muito bem, mas tem a desvantagem de que o Lean esconde os detalhes de como as expressões da lógica tipada são simplificadas.

Neste capítulo, vamos demonstrar que a composição do significado pode ser realizada sem uma linguagem de formas lógicas como nível intermediário de representação. Daremos instruções diretas para ligar expressões da língua natural ao "mundo" fora da língua (representado por um modelo). Mostraremos como modelos da lógica de predicados podem ser estendidos a modelos da lógica tipada, e como a lógica tipada fornece representações de significado apropriadas para os itens lexicais de fragmentos de língua natural e oferece os meios para construir significados de modo composicional. Mas antes de nos dedicarmos a isso, precisamos nos concentrar num ingrediente-chave da semântica da língua natural: os quantificadores.
:::

:::dev NOW
Skeleton: the headings follow CSwFP/7.1–7.7 (7.8, further reading, is
omitted). Each section is to be translated into `:::full` blocks, with a
`:::terse` cue before each `lean` block (see `STYLE-CODE.md`).
:::

# As regras do jogo
%%%
tag := "comp-rules"
%%%

:::suppressPreviousHeaderWhenTerse
:::

:::full
Pedir a alguém que traduza para uma lógica as sentenças de um fragmento de uma linguagem natural como o inglês, definido por um conjunto de regras gramaticais, pressupõe duas coisas: (i) que essa pessoa compreenda o significado das fórmulas da linguagem lógica, e (ii) que compreenda o significado das sentenças do fragmento do inglês. O primeiro tipo de conhecimento pode ser formulado de modo totalmente explícito; essa é justamente a função das definições semânticas de verdade das linguagens lógicas. Aliás, os exercícios de tradução desse tipo, comuns nos livros de lógica, servem para mostrar ao leitor o poder expressivo da linguagem de representação, ao pedir que ele exprima nesse novo meio uma mensagem que (intuitivamente) já compreende bem. Como essas traduções pressupõem que a
mensagem original já foi compreendida, elas não podem contar como uma explicação do conceito de significado para a língua natural.

Como vimos em {ref "english-lf"}[FOL como linguagem de representação], é
possível tornar plenamente explícito o conhecimento do significado de um
fragmento de língua natural. O que demos lá é um procedimento de tradução da
língua natural para a lógica de predicados que pode contar como uma explicação
do conceito de significado para a língua natural. O procedimento não pressupõe
o conhecimento do significado de sentenças completas da língua natural. Em vez
disso, ele especifica como os significados das sentenças são derivados dos
significados de blocos de construção menores. Os significados de expressões
complexas são construídos de maneira sistemática a partir dos significados dos
menores blocos de construção que ocorrem nessas expressões. O significado
desses menores blocos de construção é tomado como dado. Supomos que eles são
dados por instruções que ligam palavras individuais à realidade fora da
língua. No nosso exemplo, essas ligações são feitas pelas instruções de
interpretação dos símbolos de relação e de função num modelo da lógica de
predicados. A semântica computacional tem pouco ou nada a dizer sobre a
interpretação dos átomos semânticos. Tem bastante a dizer, no entanto, sobre o
processo de compor significados complexos de maneira sistemática a partir dos
significados dos componentes. A intuição de que isso é sempre possível pode ser
enunciada de modo um pouco mais preciso; ela se chama Princípio da
Composicionalidade, que já encontramos em {ref "IntroCS"}[O estudo formal da
língua natural]:

> O significado de uma expressão é uma função dos significados de seus
> componentes sintáticos imediatos e de seu modo sintático de composição.

O princípio da composicionalidade está implícito na obra de Frege sobre a
filosofia da linguagem, e foi tornado plenamente explícito na abordagem de
Richard Montague à semântica da língua natural. Outro elemento-chave na
semântica ao estilo de Montague é o tratamento dos quantificadores.
:::

# Quantificação
%%%
tag := "comp-quantification"
%%%

# A linguagem da lógica tipada e sua semântica
%%%
tag := "comp-typed-logic"
%%%

# Redução de expressões da lógica tipada
%%%
tag := "comp-reduction"
%%%

# Significados tipados para a língua natural
%%%
tag := "comp-typed-meanings"
%%%

# Implementando a interpretação semântica
%%%
tag := "comp-interpretation"
%%%

# Tratando a ambiguidade
%%%
tag := "comp-ambiguity"
%%%

```lean
end Composition
```
