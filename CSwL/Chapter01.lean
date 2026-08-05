/-!
# 1. O estudo formal da língua natural

*Every student passed* descreve um estado de coisas. Dizer o que a sentença
significa é dizer em que situações ela é verdadeira: numa turma em que todos
passaram, sim; numa em que alguém repetiu, não. O significado, então, é
aquilo que decide entre as situações — e é isso que se vai construir.

## Sintaxe, semântica, pragmática

Três perguntas diferentes cabem sobre a mesma expressão:

* é bem formada, e que estrutura tem?
* o que significa, em que situações é verdadeira?
* o que o falante quis fazer ao dizê-la, aqui e agora?

A segunda é o objeto central, e a primeira entra na medida em que a segunda
depende dela — não se calcula o significado de uma sentença sem antes saber
como ela se divide em partes. A terceira reaparece no capítulo 13, quando o
assunto for conhecimento comum entre interlocutores.

Tratar a segunda pergunta computacionalmente tem uma consequência imediata:
significado deixa de ser algo que se descreve em prosa e passa a ser algo
que se constrói. Um significado será um valor, de um tipo determinado. A
pergunta "o que esta sentença significa" terá como resposta um objeto que se
pode inspecionar, comparar com outro, e avaliar contra uma situação.

## Denotação e computação

*Seven plus five* e *two times six* denotam o mesmo número por caminhos
diferentes. O valor é um; as estruturas que levam a ele são duas.

Essa distinção — entre o valor que uma expressão denota e o processo pelo
qual se chega a ele — é o que torna o assunto tratável por máquina. Se o
significado é um valor, e a estrutura da expressão diz como calculá-lo, então
interpretar é executar.

Ela também explica por que há dois modos de perguntar se algo é verdadeiro.
Verificar uma sentença contra uma situação dada é calcular: a resposta é
`true` ou `false`, e sai em tempo finito. Concluir uma sentença a partir de
outras é demonstrar: a resposta é uma prova. Os dois modos aparecem no texto,
e Lean é incomum entre as linguagens de programação por hospedar ambos.

## Composicionalidade

Uma língua tem infinitas sentenças. Uma lista de significados, portanto, não
serve: não haveria como aprendê-la nem como armazená-la.

O princípio de Frege resolve o problema. O significado de uma expressão
composta é determinado pelos significados de suas partes e pelo modo como
estão combinadas. Basta então dar o significado das palavras e uma regra por
construção sintática, e o significado de qualquer sentença segue.

Em termos de programação, o princípio diz: **a interpretação é uma função
recursiva sobre a estrutura sintática**. Cada construção da gramática tem um
caso na definição, e o caso combina os resultados obtidos para os filhos. É a
forma exata dos programas que percorrem tipos indutivos.

Daí em diante as duas metades do assunto passam a ter a mesma forma. Um
fragmento da língua é um tipo; sua semântica é uma função definida por casos
sobre esse tipo; uma construção mal formada é um termo que não tipa.

## Língua natural e linguagens formais

Os primeiros fragmentos serão pequenos e artificiais — o suficiente para
descrever um jogo de batalha naval, ou para dizer quem escreveu o quê.
Fragmentos assim são linguagens formais com vocabulário emprestado do inglês,
e a semelhança com as linguagens que lógicos e cientistas da computação
projetaram é deliberada: são os mesmos instrumentos.

A aposta é que a distância entre esses fragmentos e a língua de verdade seja
uma questão de grau. Os fenômenos que aparecem no caminho — escopo de
quantificadores, intensionalidade, anáfora — se tratam estendendo o aparato,
não trocando-o. Cada capítulo acrescenta um fenômeno e o mínimo necessário
para dar conta dele.

## Fragmentos

O preço dessa abordagem é o tamanho. Os fragmentos cobrem uma fração da
língua, e o vocabulário é estipulado palavra por palavra; nada aqui extrai
significado de texto arbitrário.

O que se ganha em troca é que tudo fica explícito — a gramática, o
significado de cada palavra, a regra de composição. Onde houver ambiguidade,
ela aparece como mais de um resultado. Onde houver lacuna, o verificador de
tipos a aponta.
-/
