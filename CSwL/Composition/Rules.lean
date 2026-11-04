import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "As regras do jogo" =>
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
  átomos semânticos (a interpretação dos átomos no modelo de primeira ordem); tem muito a dizer sobre o processo de compor sistematicamente significados complexos a partir dos significados dos componentes.
- Princípio da Composicionalidade, já visto em {ref "IntroCS"}[O estudo formal
  da língua natural]: o significado de uma expressão é uma função dos
  significados de seus componentes imediatos e do modo de composição.
- Frege, depois Montague. Em Montague, outro ingrediente-chave: os
  quantificadores.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/7.1.
:::
::::
