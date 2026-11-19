import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "As Regras do Jogo" =>
%%%
tag := "comp-rules"
file := "Rules"
%%%

:::terse
- Traduzir sentenças para uma lógica pressupõe entender as fórmulas e as
  sentenças. Por isso a tradução não explica o significado das sentenças.
- O procedimento de {ref "english-lf"}[FOL como linguagem de representação]
  explica: o significado do todo é construído a partir dos significados das
  partes. Os significados das palavras vêm do modelo.
- A semântica computacional tem pouco ou nada a dizer sobre a interpretação dos
  átomos semânticos (a interpretação dos átomos no modelo de primeira ordem);
  tem muito a dizer sobre o processo de compor sistematicamente significados
  complexos a partir dos significados dos componentes.
- Princípio da Composicionalidade, já visto em
  {ref "IntroCS"}[O estudo formal da língua natural]: o significado de uma
  expressão é uma função dos significados de seus componentes imediatos e do
  modo de composição.
- Frege, depois Montague. Em Montague, outro ingrediente-chave: os
  quantificadores.
:::

::::full
Um exercício de tradução de uma sentença para uma linguagem lógica pressupõe
que entendemos tanto a sentença quanto as fórmulas dessa linguagem. O
significado das fórmulas pode ser explicitado pelas definições de verdade da
lógica. O exercício pede então que expressemos nessa linguagem uma mensagem
que já compreendemos. Isso ajuda a explorar o poder expressivo da lógica, mas
pressupõe justamente a compreensão da sentença cujo significado queremos
explicar.

O procedimento de interpretação apresentado em
{ref "english-lf"}[FOL como linguagem de representação] permite explicar como
o significado de uma sentença é construído. Para aplicá-lo, precisamos conhecer
os significados dos componentes básicos e as regras que os combinam. Cada
expressão complexa recebe uma interpretação construída a partir das
interpretações de suas partes, seguindo sua estrutura sintática. Os
significados das palavras são dados pelo modelo, que associa nomes a entidades
e predicados a propriedades e relações. Tomamos essas associações como dadas e
estudamos como compô-las para interpretar expressões maiores.

O Princípio da Composicionalidade, apresentado em
{ref "IntroCS"}[O estudo formal da língua natural], afirma que o significado de
uma expressão é uma função dos significados de seus componentes sintáticos
imediatos e do modo como eles se combinam. A semântica computacional estuda como
realizar sistematicamente essa construção. O princípio está presente no trabalho
de Frege e foi explicitado na abordagem de Montague para a semântica da língua
natural. O tratamento dos quantificadores é outro ingrediente central dessa
abordagem e será o ponto de partida para as nossas regras.
::::
