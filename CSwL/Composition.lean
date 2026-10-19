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

open ModelChecking
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

::::full
Um objetivo importante da semântica computacional é dar conta do processo de tirar inferências na língua natural. Um papel-chave nesse processo cabe aos quantificadores, e por isso a quantificação é um tópico de interesse central na semântica computacional. O primeiro tratamento sistemático da quantificação é o de Aristóteles; veja {ref "InfEngine"}[Um motor de inferência]. Por impressionante que seja, a teoria aristotélica da quantificação tem dois defeitos lógicos:

1. Combinações de quantificadores não são tratadas; só se permite um
   quantificador por sentença.
2. Quantificadores como *most*, *half of*, *at least five*, não são cobertos.

Um defeito adicional, menor, é a suposição da pressuposição existencial. No
raciocínio matemático, e às vezes também no raciocínio cotidiano, queremos
poder afirmar enunciados universalmente quantificados sem o incômodo de antes
ter de fornecer provas de existência.

O primeiro desses defeitos foi removido por Frege. A teoria da quantificação de
Frege é basicamente o que hoje chamamos de lógica de predicados. Ela se baseia
na introdução de variáveis individuais ligadas pelos quantificadores ∀ ("para
todo") e ∃ ("existe"). Os quantificadores, com suas variáveis associadas, podem
se combinar com fórmulas arbitrariamente complexas da lógica de predicados para
formar novas fórmulas da lógica de predicados, de modo que uma fórmula pode
conter um número arbitrário de quantificadores.

Os quantificadores ∀ e ∃ são chamados de quantificadores padrão. Esses dois
quantificadores são interdefiníveis com a ajuda da negação: *Algo fede*
significa o mesmo que *Não é o caso que, para todo x, x não fede*, e *Tudo está
bem* significa o mesmo que *Não é o caso que existe uma coisa x com a
propriedade de que x não está bem*. Mais formalmente: $`\exists x\, P x` é
verdadeira se e somente se $`\neg \forall x\, \neg P x` é verdadeira, e
$`\forall x\, P x` é verdadeira se e somente se $`\neg \exists x\, \neg P x` é
verdadeira.

Se convenientemente esquecermos as pressuposições existenciais, os
quantificadores aristotélicos do quadrado das oposições (veja
{ref "InfEngine"}[Um motor de inferência]) podem ser expressos em termos dos
quantificadores padrão de Frege da seguinte maneira (com ⇝ para "traduz-se
como"):

:::table
* * Todo A é B
  * $`\forall x (A x \to B x)`
* * Algum A é B
  * $`\exists x (A x \land B x)`
* * Nenhum A é B
  * $`\forall x (A x \to \neg B x)`
* * Nem todo A é B
  * $`\neg \forall x (A x \to B x)`
:::

Algo a notar é que diferentes maneiras de exprimir um quantificador
aristotélico na lógica de Frege podem ser equivalentes. Outra tradução possível
para *Nenhum A é B* é $`\neg \exists x (A x \land B x)`. Não há o que escolher
entre as duas traduções, porque em toda situação em que a primeira é verdadeira
a segunda também é, e vice-versa.

Usando os quantificadores padrão e a igualdade, também é possível exprimir
restrições numéricas como *Pelo menos dois A são B*:

$$`\exists x \exists y (x \neq y \land A x \land A y \land B x \land B y).`

Não é difícil ver que todas as disjunções e conjunções de quantificadores das
formas *pelo menos n* e *no máximo m* podem ser expressas em termos dos
quantificadores padrão e da igualdade.

Para ilustrar a afirmação de que a lógica de primeira ordem não tem dificuldade
com combinações de quantificadores, considere a tradução da sentença a seguir.

*Every prince sang a ballad.* ("Todo príncipe cantou uma balada.")

$$`\forall x (\mathit{Prince}\, x \to \exists y (\mathit{Ballad}\, y \land \mathit{Sing}\, x\, y)).`

Como vimos em {ref "english-form"}[Formas linguísticas e traduções para
lógica], a tradução não contém expressões correspondentes aos sintagmas
nominais *every prince* e *a ballad*: na lógica de primeira ordem, os
sintagmas nominais quantificados desaparecem.

O próximo exemplo, com as duas traduções possíveis listadas abaixo dele, pode
servir para ilustrar mais alguns pontos.

*A ballad was sung by every prince.* ("Uma balada foi cantada por todo
príncipe.")

$$`\exists y (\mathit{Ballad}\, y \land \forall x (\mathit{Prince}\, x \to \mathit{Sing}\, x\, y))`

$$`\forall x (\mathit{Prince}\, x \to \exists y (\mathit{Ballad}\, y \land \mathit{Sing}\, x\, y))`

O fato de ambas as traduções serem apropriadas para essa sentença mostra que
ela é ambígua. Mostra também que a tradução para a lógica de primeira ordem
pode ser usada para desambiguar sentenças da língua natural. Em casos assim,
diz-se que as diferentes traduções exprimem diferentes leituras da sentença
original.

A visão fregeana dos quantificadores é um enorme avanço em relação à visão
aristotélica. Restavam três áreas com espaço para melhorias: (i) encontrar
linguagens lógicas de representação que permitam preservar os sintagmas
nominais como constituintes separados, (ii) encontrar procedimentos de tradução
da língua natural para representações lógicas que não sejam ad hoc, e (iii)
encontrar maneiras de tratar quantificadores não padrão como *most*, de
preferência num arcabouço uniforme junto com os quantificadores padrão.
::::

## A visão relacional dos quantificadores
%%%
tag := "comp-relational"
%%%

::::full
Na perspectiva relacional dos quantificadores, proposta pela primeira vez por
Mostowski {citep Bib.mostowski1957}[], um quantificador é visto como uma
relação binária sobre o conjunto das partes de um domínio de discurso (ou
universo) $`E` que satisfaz certos requisitos. (Você pode ler $`E` como um
mnemônico para o conjunto das entidades, por exemplo.) O conjunto das partes de
um conjunto $`E`, notação $`\mathcal{P}(E)`, é o conjunto de todos os
subconjuntos de $`E`. Uma relação binária sobre $`\mathcal{P}(E)` é um conjunto
de pares de subconjuntos de $`E`. A perspectiva relacional da quantificação
está implícita na gramática de Montague. Ela foi aplicada sistematicamente à
análise da língua natural pela primeira vez por Barwise e Cooper
{citep Bib.barwise1981}[]. Mostraremos a seguir que a visão relacional pode ser
usada para remediar os defeitos tanto da teoria aristotélica quanto da
fregeana. Ela cobre quantificadores não padrão, permite combinações de
quantificadores de complexidade arbitrária, não elimina sintaticamente os
sintagmas nominais quantificados e pode ser usada como um dos ingredientes de
um procedimento de tradução não ad hoc da língua natural para uma linguagem de
representações lógicas.

Essa relação já apareceu, sem esse nome, em {ref "english-lf"}[FOL como
linguagem de representação]: lá a tradução de um determinante tomava dois
argumentos, a restrição e o escopo, e com eles construía uma fórmula com ∀ ou
∃, na qual o sintagma nominal desaparecia. Na visão relacional o determinante
não constrói fórmula nenhuma: ele relaciona diretamente o conjunto das
entidades que satisfazem a restrição com o conjunto das entidades que
satisfazem o escopo.

Começaremos demonstrando que, na perspectiva relacional moderna, a sugestão de
forma enganosa desaparece. Duas sentenças de exemplo simples vão ilustrar que
uma linguagem de representação com expressões de quantificadores generalizados
(expressões que denotam relações binárias entre conjuntos) e uma notação para a
abstração lambda é eminentemente adequada para a análise composicional de
sentenças da língua natural com sintagmas nominais quantificados. Considere
primeiro a sentença a seguir.

*Every princess laughed.* ("Toda princesa riu.")

Essa sentença é composta de um sintagma nominal *every princess*, composto por
sua vez de um determinante *every* e de um substantivo *princess*, e de um
sintagma verbal *laughed*. O determinante *every* se traduz numa expressão
$`\mathbf{every}` que denota uma função de propriedades para uma função de
propriedades para valores de verdade. Mais precisamente, $`\mathbf{every}`
denota a função que leva uma propriedade $`P` à função característica do
conjunto de todas as propriedades que têm $`P` como subconjunto. O substantivo
*princess* se traduz em $`\lambda x \mapsto \mathit{Princess}\, x`, ou
simplesmente $`\mathit{Princess}`. O sintagma verbal *laughed* se traduz em
$`\lambda y \mapsto \mathit{Laugh}\, y`, ou simplesmente $`\mathit{Laugh}`. O
sintagma nominal *every princess* se traduz em
$`\mathbf{every}\ \mathit{Princess}` e, finalmente, a sentença inteira na
expressão $`(\mathbf{every}\ \mathit{Princess})\ \mathit{Laugh}`. Essa
expressão resulta verdadeira caso a propriedade de ser princesa esteja incluída
na propriedade de rir, e falsa caso contrário. Veja a tabela a seguir.

:::table +header
* * expressão
  * tradução
  * tipo
* * *every*
  * $`\mathbf{every}`
  * $`(e \to t) \to ((e \to t) \to t)`
* * *princess*
  * $`\mathit{Princess}`
  * $`e \to t`
* * *every princess*
  * $`\mathbf{every}\ \mathit{Princess}`
  * $`(e \to t) \to t`
* * *laughed*
  * $`\mathit{Laugh}`
  * $`e \to t`
* * *every princess laughed*
  * $`(\mathbf{every}\ \mathit{Princess})\ \mathit{Laugh}`
  * $`t`
:::
::::

:::terse
Com `Bool` no lugar de $`t` e `Entity` no lugar de $`e`, o determinante é uma
função de duas propriedades: `every p q` verifica que toda entidade com `p` tem
`q`.
:::

```lean
def every (p q : OnePlacePred) : Bool :=
  entities.all (fun x => !p x || q x)
```

```lean (name := everyPrincessLaughed)
#eval every princess laugh
```

::::full
Para ver como as combinações de quantificadores são tratadas de modo
composicional, considere o exemplo a seguir.

*Every mermaid hummed a song.* ("Toda sereia cantarolou uma canção.")

O truque é encontrar a tradução certa para o verbo transitivo. Ela acaba sendo
a expressão lambda $`\lambda X \lambda y \mapsto X\, (\lambda z \mapsto
\mathit{Hum}\, y\, z)`, onde $`X` é uma variável sobre expressões do tipo de
sintagma nominal. A tradução do verbo é do tipo certo para tomar a tradução do
sintagma nominal objeto como argumento; isso dá a primeira das traduções abaixo
para o sintagma verbal, que se reduz à segunda. Em
{ref "comp-reduction"}[Redução de expressões da lógica tipada] diremos mais
sobre esse processo de redução.

$$`(\lambda X \lambda y \mapsto X\, (\lambda z \mapsto \mathit{Hum}\, y\, z))\, (\mathbf{a}\ \mathit{Song})`

$$`\lambda y \mapsto (\mathbf{a}\ \mathit{Song})\, (\lambda z \mapsto \mathit{Hum}\, y\, z)`

Aqui $`\mathbf{a}` denota a função que leva toda propriedade $`P` ao (à função
característica do) conjunto de todas as propriedades que têm interseção não
vazia com $`P`. Dando a segunda delas como argumento à expressão
$`\mathbf{every}\ \mathit{Mermaid}`, a tradução do sujeito, obtém-se a seguinte
tradução para a sentença inteira.

$$`(\mathbf{every}\ \mathit{Mermaid})\, (\lambda y \mapsto ((\mathbf{a}\ \mathit{Song})\, (\lambda z \mapsto \mathit{Hum}\, y\, z)))`

Podemos resumir esses passos assim:

```display
Every mermaid hummed a song
(every Mermaid) (λy ↦ (a Song) (λz ↦ Hum y z))
├── every mermaid
│   (every Mermaid)
└── hummed a song
    λy ↦ (a Song) (λz ↦ Hum y z)
    ├── hummed
    │   λXλy ↦ X (λz ↦ Hum y z)
    └── a song
        (a Song)
```

Dissemos no início que vemos os quantificadores como relações binárias sobre o
conjunto das partes de algum domínio $`E`, que satisfazem certos requisitos.
Vejamos agora, então, esses requisitos.
::::

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
