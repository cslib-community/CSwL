import CSwLMeta
import Bib
import CSwL.Logic.FOL

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Verificação de Modelos com Lógica de Primeira Ordem" =>
%%%
tag := "ModelChecking"
htmlSplit := .never
file := "ModelChecking"
%%%

```lean
namespace ModelChecking
```

Nas linguagens formais construídas artificialmente, como a lógica proposicional e a lógica de predicados, as regras de formação de fórmulas são perfeitamente estritas, unívocas e livres de ambiguidade. A língua natural humana, por outro lado, é rica e expressiva, mas repleta de nuances estruturais. Para que um computador possa manipular e verificar sentenças em inglês, precisamos construir uma ponte entre a gramática das línguas humanas e a precisão da lógica formal.

Este capítulo constrói o pipeline clássico da semântica computacional para um fragmento do inglês. Primeiro, em {ref "english-fragment"}[Um Fragmento do Inglês], especificamos a sintaxe do fragmento por meio de uma gramática livre de contexto, implementada em Lean como tipos indutivos que representam diretamente árvores de análise sintática. Em seguida, em {ref "english-lf"}[FOL como Linguagem de Representação], traduzimos essas árvores sintáticas para fórmulas da lógica de primeira ordem, guiados pelo princípio da composicionalidade e por ferramentas do cálculo lambda. Por fim, em {ref "english-model"}[Uma Estrutura de Primeira Ordem], avaliamos as fórmulas obtidas em um modelo concreto, conectando sentenças sobre um micromundo ficcional aos seus valores de verdade. Decidir se uma fórmula é verdadeira em uma estrutura dada é o que se chama _verificação de modelos_ (_model checking_), e é isso que dá nome ao capítulo.


# Formas Linguísticas e Traduções para Lógica
%%%
tag := "english-form"
%%%

Da sentença *Alice walked on the road* segue-se que alguém caminhou na estrada, mas de *No one walked on the road* não se segue que alguém caminhou na estrada. Por isso lógicos como Gottlob Frege (1848–1925), Bertrand Russell (1872–1970), Alfred Tarski (1902–1983) e Willard Van Orman Quine (1908–2000) sustentaram que a estrutura dessas duas sentenças deveria ser diferente, e que não basta dizer que ambas são a composição de um sujeito e um predicado.

Em linguística, chamamos de _sintagma nominal_ (_Noun Phrase_, ou `NP`) qualquer bloco de palavras centrado em um substantivo que funcione como uma unidade sintática (como um sujeito ou objeto). Quando esse bloco é encabeçado por palavras lógicas como _every_ ("todo"), _some_ ("algum") ou _no_ ("nenhum"), temos um *sintagma nominal quantificado*.

Ao tentar traduzir a língua natural para a lógica de predicados de primeira ordem, os lógicos notaram uma discrepância marcante: a fórmula lógica final não acompanhava a estrutura gramatical visível da oração. Considere o exemplo:

1. _Every dwarf loved Goldilocks._ ("Todo anão amava Cachinhos Dourados.")
2. $`\forall x\,(\mathit{Dwarf}\,x \to \mathit{Love}\,x\,g)`

Na sentença original em inglês, _Every dwarf_ é o sujeito, formando um bloco sintático coeso. Na tradução, porém, o constituinte _every dwarf_ desapareceu: ele foi eliminado da fórmula. Se a sentença fosse _Alice loved Goldilocks_, o sujeito apontaria para uma pessoa específica no mundo, representada diretamente na lógica por uma constante individual $`a` (resultando em $`\mathit{Love}\,a\,g`).

Contudo, ao dizermos _Every dwarf_, não estamos nos referindo a um anão em particular: não existe no mundo um indivíduo chamado "Todo anão". Em vez de apontar para uma entidade isolada, o quantificador estabelece uma condição geral sobre todos os objetos do universo: _para qualquer objeto x, se x for um anão, então x amou Cachinhos Dourados_ (o que equivale logicamente a dizer que ou esse objeto não é um anão, ou ele amou Cachinhos Dourados).

É a isso que lógicos como Gottlob Frege chamavam de *eliminação contextual*: expressões quantificadas não denotam indivíduos e, por isso, deixam de existir como termos isolados na lógica de predicados. Seu significado só se manifesta na forma como condicionam a oração inteira.

Essa discrepância levou muitos lógicos do início do século XX a supor que a língua natural era inerentemente imperfeita ou enganosa. Contudo, a aplicação das ferramentas lógicas de abstração e redução do cálculo lambda permite ver que essa conclusão era injustificada.

A chave para resolver esse impasse está em retomar o princípio da composicionalidade (visto em {ref "IntroCS"}[IntroCS]) sob a ótica do cálculo lambda (apresentado em {ref "lambda"}[IntroL]). Quando traduzimos a língua natural para uma lógica tipada, cada constituinte da oração corresponde a uma expressão funcional bem tipada. A combinação gramatical das palavras passa a refletir diretamente a aplicação de _funções aos seus argumentos_. A eliminação contextual das expressões quantificadas é simplesmente o resultado da computação dessas funções (a β-redução), e não uma falha estrutural da sentença original.

Para ilustrar como o cálculo lambda harmoniza a análise lógica, considere a combinação de sujeitos e predicados:

* Na sentença simples _Goldilocks laughed_, a intuição imediata da lógica de primeira ordem é tratar o predicado como a função que consome o sujeito: $`\mathit{Laugh}\,g`.
* No entanto, essa estratégia falha para sujeitos quantificados como _No one laughed_: não existe um indivíduo "ninguém" que possamos passar como argumento para $`\mathit{Laugh}`.

Tudo se resolve, porém, se dissermos que o sujeito sempre toma o predicado como argumento, e fizermos isso funcionar para os sujeitos simples elevando logicamente seu estatuto de argumento a função (processo conhecido como *elevação de tipo*, ou _type raising_).

Com expressões lambda, isso se torna direto:

1. O nome próprio _Goldilocks_ deixa de ser tratado como a constante individual $`g` e passa a ser a função de ordem superior $`\lambda P \mapsto P\,g`. Essa função recebe uma propriedade $`P` e afirma que $`g` tem essa propriedade.
2. O sintagma quantificado _no one_ recebe exatamente a mesma assinatura de tipo: $`\lambda P \mapsto \neg\exists x\,(\mathit{Person}\,x \land P\,x)`, consumindo igualmente uma propriedade $`P`.
Assim, tanto _Goldilocks laughed_ quanto _no one laughed_ combinam-se sintática e semanticamente da mesma maneira: o sujeito aplica-se ao predicado. A aparente assimetria só ressurge quando efetuamos a β-redução para simplificar a fórmula lógica final.

Esse método nos permite realizar a _interpretação indireta_ da língua natural: em vez de tentar avaliar sentenças em inglês diretamente em um modelo, nós as traduzimos primeiro para fórmulas da lógica de primeira ordem, cuja semântica formal já dominamos.

Para que essa tradução composicional seja viável, porém, precisamos de um ponto de partida indispensável: delimitar a estrutura sintática das sentenças que queremos analisar. É a essa tarefa de modelagem gramatical que nos dedicamos a seguir em {ref "english-fragment"}[Um Fragmento do Inglês].


# Um Fragmento do Inglês
%%%
tag := "english-fragment"
%%%

Suponha que queiramos escrever regras gramaticais para sentenças do inglês como as seguintes:

1. The girl laughed. ("A menina riu.")
2. No dwarf admired some princess that shuddered. ("Nenhum anão admirou alguma princesa que estremeceu.")
3. Every girl that some boy loved cheered. ("Toda menina que algum menino amou torceu.")
4. The wizard that helped Snow White defeated the giant. ("O mago que ajudou Branca de Neve derrotou o gigante.")

O que precisamos é de uma regra para a estrutura sujeito–predicado das sentenças, uma regra para a estrutura interna dos sintagmas nominais, uma regra para os substantivos comuns com ou sem orações relativas, e praticamente nada além disso. A gramática a seguir dá conta dos exemplos:

```bnf
S   ::= NP VP ;
NP  ::= "Snow White" | "Alice" | "Dorothy" | "Goldilocks" | "Little Mook"
      | "Atreyu" | "everyone" | "someone" | DET CN | DET RCN ;
DET ::= "a" | "the" | "every" | "some" | "no" ;
CN  ::= "girl" | "boy" | "princess" | "dwarf" | "giant" | "wizard" | "sword"
      | "dagger" ;
ADJ ::= "fake" | "happy" | "evil" ;
RCN ::= CN "that" VP | CN "that" NP TV | ADJ CN ;
VP  ::= "laughed" | "cheered" | "shuddered" | TV NP | DV NP NP ;
TV  ::= "loved" | "admired" | "helped" | "defeated" | "caught" ;
DV  ::= "gave" ;
```

Isto é muito básico e simplificado demais, claro, mas dá uma ideia de como seria uma gramática para um fragmento do inglês.

A tradução para Lean é direta: cada não-terminal da gramática vira um tipo indutivo, e cada alternativa de uma regra vira um construtor desse tipo. Um valor do tipo `Sent` não é uma sequência de palavras, é a árvore de análise de uma sentença — a estrutura que a gramática atribui a ela.

Começamos pelos não-terminais cujas alternativas são todas palavras. Eles não dependem de nenhum outro não-terminal, e por isso podem ser declarados isoladamente. Junto de cada um declaramos a instância de `ToString` que devolve a palavra correspondente.

```lean
inductive DET where
  | a | the | every | some | no
deriving Repr

instance : ToString DET :=
  ⟨fun | .a => "a" | .the => "the" | .every => "every"
       | .some => "some" | .no => "no"⟩

inductive CN where
  | girl | boy | princess | dwarf | giant | wizard
  | sword | dagger
deriving Repr

instance : ToString CN :=
  ⟨fun | .girl => "girl" | .boy => "boy"
       | .princess => "princess" | .dwarf => "dwarf"
       | .giant => "giant" | .wizard => "wizard"
       | .sword => "sword" | .dagger => "dagger"⟩

inductive ADJ where
  | fake | happy | evil
deriving Repr

instance : ToString ADJ :=
  ⟨fun | .fake => "fake" | .happy => "happy"
       | .evil => "evil"⟩

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

inductive That where
  | that
deriving Repr

instance : ToString That := ⟨fun | .that => "that"⟩
```

O tipo `That` tem um único construtor e não carrega informação alguma. Ele está ali porque a palavra *that* ocupa uma posição na regra de `RCN`, e queremos que a árvore de análise registre essa posição como registra as outras.

As regras de `NP`, `RCN` e `VP` têm dependências circulares. `NP` usa `RCN`, `RCN` usa `VP` e `NP`, e `VP` usa `NP`. Por isso declaramos os três tipos em um bloco `mutual`. Depois do bloco, declaramos `Sent`, que representa a regra `S ::= NP VP`.

```lean
mutual

inductive NP where
  | snowWhite | alice | dorothy | goldilocks
  | littleMook | atreyu
  | everyone | someone
  | npDet (det : DET) (cn : CN)
  | npDetRel (det : DET) (rcn : RCN)
deriving Repr

inductive RCN where
  | rcnSubj (cn : CN) (compl : That) (vp : VP)
  | rcnObj (cn : CN) (compl : That) (np : NP) (tv : TV)
  | rcnAdj (adj : ADJ) (cn : CN)
deriving Repr

inductive VP where
  | laughed | cheered | shuddered
  | vpTrans (tv : TV) (np : NP)
  | vpDitrans (dv : DV) (iobj dobj : NP)
deriving Repr

end

inductive Sent where
    | sent (np : NP) (vp : VP)
deriving Repr
```

Os nomes dos construtores dizem qual alternativa da regra cada um implementa. Em `RCN`, `rcnSubj` é a oração relativa em que o substantivo modificado faz o papel de sujeito — *girl that laughed* —, e `rcnObj` aquela em que ele faz o papel de objeto — *girl that some boy loved*. Essa diferença vai reaparecer quando dermos a semântica do fragmento.

Para recuperar a sentença de superfície a partir da árvore, definimos primeiro as funções de `NP`, `RCN` e `VP` em um bloco `mutual`. Depois do bloco, `Sent.toText` junta o texto do sujeito ao do predicado.

```lean
mutual

def NP.toText : NP → String
  | .snowWhite => "Snow White"
  | .alice => "Alice"
  | .dorothy => "Dorothy"
  | .goldilocks => "Goldilocks"
  | .littleMook => "Little Mook"
  | .atreyu => "Atreyu"
  | .everyone => "everyone"
  | .someone => "someone"
  | .npDet det cn => s!"{det} {cn}"
  | .npDetRel det rcn => s!"{det} {rcn.toText}"

def RCN.toText : RCN → String
  | .rcnSubj cn compl vp => s!"{cn} {compl} {vp.toText}"
  | .rcnObj cn compl np tv =>
    s!"{cn} {compl} {np.toText} {tv}"
  | .rcnAdj adj cn => s!"{adj} {cn}"

def VP.toText : VP → String
  | .laughed => "laughed"
  | .cheered => "cheered"
  | .shuddered => "shuddered"
  | .vpTrans tv np => s!"{tv} {np.toText}"
  | .vpDitrans dv iobj dobj =>
    s!"{dv} {iobj.toText} {dobj.toText}"

end

def Sent.toText : Sent → String
  | .sent np vp => s!"{np.toText} {vp.toText}"

instance : ToString Sent := ⟨Sent.toText⟩
instance : ToString NP := ⟨NP.toText⟩
instance : ToString RCN := ⟨RCN.toText⟩
instance : ToString VP := ⟨VP.toText⟩
```

A árvore de análise de *The dwarf that Snow White helped admired every princess* corresponde diretamente ao termo Lean.

```lean
def sent1 : Sent :=
  .sent (.npDetRel .the
          (.rcnObj .dwarf .that .snowWhite .helped))
        (.vpTrans .admired (.npDet .every .princess))
```

É por isso que cada tipo do fragmento deriva `Repr`: avaliar `sent1` no editor exibe o termo, isto é, a árvore, construtor por construtor. `ToString` faz o caminho oposto e devolve a sentença de superfície.

```lean (name := sent1eval)
#eval toString sent1
```

Ir da sentença de superfície para a árvore é o problema inverso, chamado de *análise sintática*. Não o trataremos aqui: neste capítulo as árvores são construídas à mão, e o que nos interessa é o que fazer com elas depois de construídas.

## Estender uma Gramática

Um tipo indutivo em Lean é fechado. Seus construtores são fixados na declaração. Isso permite que Lean verifique se uma função definida por casos sobre `VP` cobre todos os seus cinco construtores. Para acrescentar uma alternativa diretamente a uma regra da gramática, seria preciso alterar a declaração do tipo correspondente.

Há duas situações, e elas se comportam de maneiras diferentes.

Acrescentar uma *palavra* a uma categoria — um adjetivo, um verbo transitivo — exige mesmo redeclarar o tipo daquela categoria, porque a palavra é um construtor novo. Por isso as palavras de que o capítulo precisa já entram na declaração: `ADJ` traz *fake*, *happy* e *evil* desde o início.

Para acrescentar a coordenação de sentenças, podemos declarar uma nova categoria que inclui as sentenças do fragmento original e permite combiná-las com *and*.

```lean
inductive Coord where
  | and
deriving Repr

instance : ToString Coord := ⟨fun | .and => "and"⟩

inductive SentAnd where
  | base (s : Sent)
  | coord (left : SentAnd) (c : Coord) (right : SentAnd)
deriving Repr

def SentAnd.toText : SentAnd → String
  | .base s => toString s
  | .coord l c r => s!"{l.toText} {c} {r.toText}"

instance : ToString SentAnd := ⟨SentAnd.toText⟩
```

O construtor `base` diz que toda sentença do fragmento original é uma sentença do fragmento estendido, e `coord` acrescenta a regra nova, `S ::= S COORD S`. Nada de `Sent` foi redeclarado, e as funções já escritas sobre `Sent` continuam valendo — `SentAnd.toText` chama `toString` sobre o `Sent` de dentro.

```lean (name := sentAndEval)
def sent2 : SentAnd :=
  .coord (.base (.sent .alice .laughed)) .and
         (.base (.sent .dorothy .cheered))

#eval toString sent2
```

Os dois exercícios a seguir estendem o fragmento por esse caminho.

::::exercise (rating := 3) (name := "preposition-phrase")

Estenda o fragmento com sintagmas preposicionais, de modo que a sentença *A dwarf defeated a giant with a sword* seja gerada de duas maneiras estruturalmente diferentes, enquanto há apenas uma maneira de gerar *A dwarf defeated Little Mook with a sword*.

:::solution
Primeiro acrescentamos duas regras para construir sintagmas preposicionais a partir de uma preposição e de um sintagma nominal. Em seguida estendemos a regra dos sintagmas nominais, para gerar sintagmas como *a giant with a sword*. Note que não acrescentamos simplesmente uma produção recursiva `NP ::= NP PP`: além de permitir um número arbitrário de sintagmas preposicionais modificando um mesmo sintagma nominal, ela geraria *Little Mook with a sword*, que é o que queremos excluir. Por fim, estendemos também a regra dos sintagmas verbais.

```bnf
P   ::= "with" ;
PP  ::= P NP ;
NPP ::= DET CN PP ;
VPP ::= VP | TV NPP | TV NP PP ;
S'  ::= NP VPP ;
```

A regra `NPP ::= DET CN PP` exige um determinante e um substantivo comum. Como *Little Mook* é um nome próprio, sem determinante, não há como formar *Little Mook with a sword* como um único sintagma nominal, e resta apenas a leitura em que o sintagma preposicional se liga ao sintagma verbal.
:::

A preposição *with* tem o nome de uma palavra reservada de Lean. Para usá-la assim mesmo como nome de construtor, basta cercá-la de guillemets: `«with»`. Fora da declaração, `.with` já é lido como o construtor e dispensa os guillemets.

```lean
inductive Prep where
  | «with»
deriving Repr

instance : ToString Prep := ⟨fun | .with => "with"⟩

inductive PP where
  | pp (p : Prep) (np : NP)
deriving Repr

instance : ToString PP :=
  ⟨fun | .pp p np => s!"{p} {np}"⟩

inductive NPP where
  | withPP (det : DET) (cn : CN) (pp : PP)
deriving Repr

inductive VPP where
  | base (vp : VP)
  | objPP (tv : TV) (np : NPP)
  | vpPP (tv : TV) (np : NP) (pp : PP)
deriving Repr

inductive SentPP where
  | sent (np : NP) (vp : VPP)
deriving Repr
```

Repare que `NPP` tem um único construtor, e que tanto `objPP` quanto `vpPP` exigem um sintagma preposicional. É isso que garante que a gramática estendida não gere duas vezes as sentenças que a original já gerava: uma sentença sem sintagma preposicional só pode passar por `base`.

Complete as funções que devolvem a sentença de superfície.

```lean
def NPP.toText : NPP → String :=
  solution!(
    fun | .withPP det cn pp => s!"{det} {cn} {pp}")

instance : ToString NPP := ⟨NPP.toText⟩

def VPP.toText : VPP → String :=
  solution!(
    fun
    | .base vp => toString vp
    | .objPP tv np => s!"{tv} {np}"
    | .vpPP tv np pp => s!"{tv} {np} {pp}")

instance : ToString VPP := ⟨VPP.toText⟩

def SentPP.toText : SentPP → String :=
  solution!(
    fun | .sent np vp => s!"{np} {vp}")

instance : ToString SentPP := ⟨SentPP.toText⟩
```

Agora construa as três árvores: as duas leituras de *A dwarf defeated a giant with a sword* e a única de *A dwarf defeated Little Mook with a sword*.

```lean
def withSword : PP := .pp .with (.npDet .a .sword)

def giantSword1 : SentPP :=
  solution!(
    .sent (.npDet .a .dwarf)
      (.objPP .defeated (.withPP .a .giant withSword)))

def giantSword2 : SentPP :=
  solution!(
    .sent (.npDet .a .dwarf)
      (.vpPP .defeated (.npDet .a .giant) withSword))

def mookSword : SentPP :=
  solution!(
    .sent (.npDet .a .dwarf)
      (.vpPP .defeated .littleMook withSword))

example
  : toString giantSword1 = toString giantSword2 :=
  solution!(by rfl)

example
  : toString giantSword1 =
    "a dwarf defeated a giant with a sword" :=
  solution!(by rfl)

example
  : toString mookSword =
     "a dwarf defeated Little Mook with a sword" :=
  solution!(by rfl)
```

As duas primeiras árvores são diferentes e imprimem a mesma sentença: é a ambiguidade pedida.
::::

::::exercise (rating := 3) (name := "complex-relative-clauses")

Estenda o fragmento com orações relativas complexas, em que a oração relativa coordena dois sintagmas verbais ou dois pares sintagma nominal–verbo transitivo. O fragmento deve gerar, entre outras, a sentença *The dwarf that Snow White helped and Goldilocks admired cheered*. Que problemas você encontra?

:::solution
As regras acrescentam duas alternativas para as orações relativas, cada uma coordenando duas ocorrências da mesma forma:

```bnf
RCNC ::= CN "that" VP COORD VP | CN "that" NP TV COORD NP TV ;
NPC  ::= NP | DET RCNC ;
S''  ::= NPC VP ;
```

O primeiro problema é que as duas regras não podem ser substituídas por uma só que coordenasse um sintagma verbal com um par sintagma nominal–verbo transitivo. Numa oração relativa há uma posição vazia, a *lacuna*, onde entraria o substantivo que ela modifica: em `CN "that" VP` a lacuna é o sujeito do sintagma verbal, e em `CN "that" NP TV` é o objeto do verbo transitivo. Cada uma das duas regras coordena duas lacunas do mesmo tipo. Misturá-las produziria *the dwarf that Goldilocks helped and admired Snow White*, em que a lacuna é o objeto no primeiro ramo e o sujeito no segundo, e que é agramatical. Coordenar sentenças inteiras, como em `SentAnd`, geraria exatamente essa mistura.

O segundo problema é que nenhuma das duas regras é recursiva: cada uma coordena exatamente dois ramos. Para três ramos seria preciso mais uma regra, para quatro outra, e assim por diante. O fragmento não captura a generalização "coordenação de um número qualquer de sintagmas verbais paralelos".

O terceiro é que os ramos coordenados usam os sintagmas nominais e verbais do fragmento original, e não os estendidos. Uma oração relativa coordenada não pode, portanto, conter outra oração relativa coordenada.
:::

```lean
inductive RCNC where
  | vpAnd (cn : CN) (compl : That)
      (left : VP) (c : Coord) (right : VP)
  | objAnd (cn : CN) (compl : That)
      (np1 : NP) (tv1 : TV) (c : Coord)
      (np2 : NP) (tv2 : TV)
deriving Repr

inductive NPC where
  | base (np : NP)
  | npDetRel (det : DET) (rcn : RCNC)
deriving Repr

inductive SentC where
  | sent (np : NPC) (vp : VP)
deriving Repr
```

Complete as funções de superfície e construa a sentença do enunciado.

```lean
def RCNC.toText : RCNC → String :=
  solution!(
    fun
    | .vpAnd cn compl l c r =>
      s!"{cn} {compl} {l} {c} {r}"
    | .objAnd cn compl np1 tv1 c np2 tv2 =>
      s!"{cn} {compl} {np1} {tv1} {c} {np2} {tv2}")

instance : ToString RCNC := ⟨RCNC.toText⟩

def NPC.toText : NPC → String :=
  solution!(
    fun
    | .base np => toString np
    | .npDetRel det rcn => s!"{det} {rcn}")

instance : ToString NPC := ⟨NPC.toText⟩

def SentC.toText : SentC → String :=
  solution!(
    fun | .sent np vp => s!"{np} {vp}")

instance : ToString SentC := ⟨SentC.toText⟩

def dwarfHelpedAdmired : SentC :=
  solution!(
    .sent (.npDetRel .the
            (.objAnd .dwarf .that .snowWhite .helped
              .and .goldilocks .admired))
          .cheered)

example :
    toString dwarfHelpedAdmired =
      "the dwarf that Snow White helped and " ++
        "Goldilocks admired cheered" :=
  solution!(by rfl)
```
::::


# FOL como Linguagem de Representação
%%%
tag := "english-lf"
%%%

A lógica de predicados nos dá representações para dois tipos: o tipo das entidades é representado pelos termos, e o tipo dos valores de verdade pelas fórmulas. Chamaremos de `LF` — *forma lógica* — o tipo das fórmulas de primeira ordem cujos termos são termos estruturados, o {name}`FOL.Formula` de {ref "FOL"}[FOL] com {name}`FOL.Term` no lugar do parâmetro.

```lean
open FOL

abbrev LF := Formula Term
```

Traduzimos cada sentença do fragmento para uma fórmula de tipo `LF`. As traduções de `VP` e `RCN` têm tipo `Term → LF`. Elas recebem um termo e constroem uma fórmula sobre ele. Pela elevação de tipo apresentada em {ref "english-form"}[Formas Linguísticas e Traduções para Lógica], a tradução de `NP` tem tipo `(Term → LF) → LF`. Para traduzir a regra `S ::= NP VP`, aplicamos a tradução do sujeito à do sintagma verbal, como em `lfNP np (lfVP vp)`.

Começamos pelas funções de tradução das categorias lexicais. Em seguida, definimos `lfNP`, `lfVP` e `lfRCN` em um bloco `mutual`. `lfSent` vem depois do bloco e combina as traduções de `NP` e `VP`.

As categorias lexicais são as mais simples. Um substantivo comum tem o mesmo tipo que um sintagma verbal, e um adjetivo também.

```lean
def lfCN : CN → Term → LF
  | .girl, t => .atom "girl" [t]
  | .boy, t => .atom "boy" [t]
  | .princess, t => .atom "princess" [t]
  | .dwarf, t => .atom "dwarf" [t]
  | .giant, t => .atom "giant" [t]
  | .wizard, t => .atom "wizard" [t]
  | .sword, t => .atom "sword" [t]
  | .dagger, t => .atom "dagger" [t]

def lfADJ : ADJ → Term → LF
  | .fake, t => .atom "fake" [t]
  | .happy, t => .atom "happy" [t]
  | .evil, t => .atom "evil" [t]
```

Um verbo transitivo relaciona duas entidades, e um verbo ditransitivo, três. O primeiro argumento é sempre o do sujeito; no verbo ditransitivo, o segundo é o do objeto indireto e o terceiro o do objeto direto.

```lean
def lfTV : TV → Term → Term → LF
  | .loved, t1, t2 => .atom "love" [t1, t2]
  | .admired, t1, t2 => .atom "admire" [t1, t2]
  | .helped, t1, t2 => .atom "help" [t1, t2]
  | .defeated, t1, t2 => .atom "defeat" [t1, t2]
  | .caught, t1, t2 => .atom "catch" [t1, t2]

def lfDV : DV → Term → Term → Term → LF
  | .gave, t1, t2, t3 => .atom "give" [t1, t2, t3]
```

## Variáveis Novas

A tradução de um determinante toma dois argumentos de tipo `Term → LF`, formas lógicas obtidas a partir de um termo, e produz uma forma lógica. No caso dos quantificadores, o primeiro argumento é a *restrição* e o segundo o *escopo*. Falaremos disso em {ref "comp-relational"}[A visão relacional dos quantificadores].

A tradução dos determinantes precisa evitar a captura de variáveis. Em *Every dwarf defeated some giant*, por exemplo, a tradução de *defeated some giant* introduz o quantificador do objeto, enquanto a variável do sujeito só será ligada pelo quantificador externo, de *every dwarf*. Para escolher o índice da variável do sujeito, examinamos os índices dos quantificadores internos e escolhemos um índice maior. Assim, nenhum quantificador interno pode capturar uma ocorrência da variável do sujeito.

```lean
def boundIndices : LF → List Nat
  | .atom _ _ => []
  | .eq _ _ => []
  | .top => []
  | .bot => []
  | .neg f => boundIndices f
  | .impl f1 f2 => boundIndices f1 ++ boundIndices f2
  | .equi f1 f2 => boundIndices f1 ++ boundIndices f2
  | .conj f1 f2 => boundIndices f1 ++ boundIndices f2
  | .disj f1 f2 => boundIndices f1 ++ boundIndices f2
  | .forall_ v f => v.index ++ boundIndices f
  | .exists_ v f => v.index ++ boundIndices f
```

Para calcular um índice novo, basta escolher um índice fora dessa lista. Todas as variáveis são introduzidas pelo mesmo mecanismo, que só produz variáveis da forma `⟨"x", [i]⟩` para algum natural `i`, e por isso podemos supor que toda variável que ocorre na forma lógica tem esse feitio.

Os argumentos de `lfDET` não são formas lógicas, e sim funções à espera de um termo. Para ver que variáveis elas carregam, aplicamos cada uma a um termo qualquer que não contenha variável alguma.

```lean
def dummy : Term := .struct "" []

def freshIndex (ps : List (Term → LF)) : Nat :=
  let used :=
    (ps.map (fun p => boundIndices (p dummy))).flatten
  used.foldr max 0 + 1

def freshVar (ps : List (Term → LF)) : Variable :=
  ⟨"x", [freshIndex ps]⟩
```

Em `freshIndex`, `foldr max 0` devolve o maior índice em uso, ou `0` quando nenhum quantificador foi introduzido ainda, e o `+ 1` escolhe um índice maior do que todos eles. O primeiro índice gerado é, portanto, `1`.

Podemos agora dar a tradução dos determinantes. Os indefinidos *a* e *some* recebem a mesma tradução.

```lean
def lfDET : DET → (Term → LF) → (Term → LF) → LF
  | .a, p, q =>
    let v := freshVar [p, q]
    .exists_ v (.conj (p (.var v)) (q (.var v)))
  | .some, p, q =>
    let v := freshVar [p, q]
    .exists_ v (.conj (p (.var v)) (q (.var v)))
  | .every, p, q =>
    let v := freshVar [p, q]
    .forall_ v (.impl (p (.var v)) (q (.var v)))
  | .no, p, q =>
    let v := freshVar [p, q]
    .neg (.exists_ v (.conj (p (.var v)) (q (.var v))))
  | .the, p, q =>
    let i := freshIndex [p, q]
    let v1 : Variable := ⟨"x", [i]⟩
    let v2 : Variable := ⟨"x", [i + 1]⟩
    .exists_ v1
      (.conj
        (.forall_ v2
          (.equi (p (.var v2)) (.eq (.var v1) (.var v2))))
        (q (.var v1)))
```

Para o determinante definido usamos a teoria das descrições definidas proposta por Bertrand Russell {citep Bib.russell1905}[]. Russell propôs traduzir *The king of France is bald* como a conjunção de *existe exatamente uma pessoa que é rei da França* e *essa pessoa é careca*, o que se exprime assim na lógica de predicados:

```display
∃x (∀y (King[y] <=> x = y) & Bald[x])
```

Nem todo determinante do inglês admite uma tradução para a lógica de predicados. *Most* é o exemplo clássico: não há como dizer, com os quantificadores `∀` e `∃`, que a maioria dos anões riu. Determinantes como *at least n* e *at most n* têm tradução, mas as formas lógicas ficam muito pesadas. É por isso que `DET` traz apenas os cinco determinantes acima.

## O Bloco Mutuamente Recursivo

Em `lfNP`, cada nome próprio é representado por uma constante, isto é, um símbolo funcional de aridade zero. Para *Snow White*, `lfNP` aplica a propriedade recebida ao termo `SnowWhite`.

Os sintagmas *everyone* e *someone* não têm um termo que lhes corresponda. Eles são traduzidos como quantificadores restritos à propriedade de ser uma pessoa, e é justamente essa a forma de que falamos na primeira seção: uma função que toma a representação do sintagma verbal como argumento.

Usamos a conjunção para juntar a forma lógica de um substantivo comum e a de uma oração relativa numa forma lógica para o substantivo comum complexo.

```lean
mutual

def lfNP : NP → (Term → LF) → LF
  | .snowWhite, p => p (.struct "SnowWhite" [])
  | .alice, p => p (.struct "Alice" [])
  | .dorothy, p => p (.struct "Dorothy" [])
  | .goldilocks, p => p (.struct "Goldilocks" [])
  | .littleMook, p => p (.struct "LittleMook" [])
  | .atreyu, p => p (.struct "Atreyu" [])
  | .everyone, p =>
    let v := freshVar [p]
    .forall_ v
     (.impl (.atom "person" [.var v]) (p (.var v)))
  | .someone, p =>
    let v := freshVar [p]
    .exists_ v
     (.conj (.atom "person" [.var v]) (p (.var v)))
  | .npDet det cn, p => lfDET det (lfCN cn) p
  | .npDetRel det rcn, p => lfDET det (lfRCN rcn) p

def lfVP : VP → Term → LF
  | .laughed, t => .atom "laugh" [t]
  | .cheered, t => .atom "cheer" [t]
  | .shuddered, t => .atom "shudder" [t]
  | .vpTrans tv np, subj =>
    lfNP np (fun obj => lfTV tv subj obj)
  | .vpDitrans dv np1 np2, subj =>
    lfNP np1 (fun iobj =>
      lfNP np2 (fun dobj => lfDV dv subj iobj dobj))

def lfRCN : RCN → Term → LF
  | .rcnSubj cn _ vp, t => .conj (lfCN cn t) (lfVP vp t)
  | .rcnObj cn _ np tv, t =>
    .conj (lfCN cn t)
      (lfNP np (fun subj => lfTV tv subj t))
  | .rcnAdj adj cn, t => .conj (lfADJ adj t) (lfCN cn t)
end

def lfSent : Sent → LF
  | .sent np vp => lfNP np (lfVP vp)
```

A tradução do adjetivo em `rcnAdj` é a conjunção: um *happy wizard* é alguém que é feliz e é mago. Isso está certo para *happy* e para *evil*, e está errado para *fake*: um *fake wizard* justamente não é um mago. Adjetivos desse tipo pedem uma semântica que a lógica de predicados não alcança, e o fragmento os traduz assim porque em Lean uma função tem de estar definida em todos os casos — a tradução existe, mas não é uma boa tradução.

Vejamos um primeiro exemplo passo-a-passo.

```lean
def s1 :=
  Sent.sent (.npDet .every .dwarf)
            (.vpTrans .defeated (.npDet .some .giant))

#eval toString s1

open FOL in
def l0 :=
 let x : Variable := ⟨"x", [2]⟩
 let y : Variable := ⟨"x", [1]⟩
 let dwarf := λ x ↦ Formula.atom "dwarf" [Term.var x]
 let giant := λ x ↦ Formula.atom "giant" [Term.var x]
 let defeat := λ x y ↦ Formula.atom "defeat"
  [(Term.var x),(Term.var y)]
 Formula.forall_ x (Formula.impl
  (dwarf x)
  (Formula.exists_ y (Formula.conj (giant y) (defeat x y))))

#eval toString l0

open FOL in
example : lfSent s1 = l0 := by
 unfold s1 l0
 simp [lfSent, lfNP, lfDET, lfCN, lfVP, lfCN, freshVar,
   freshIndex, lfTV, boundIndices]
```

Outros dois exemplos de fórmulas.

```lean
def lf2 : LF :=
  lfSent (.sent (.npDetRel .the
                  (.rcnObj .wizard .that .dorothy .admired))
                .laughed)

def lf3 : LF :=
  lfSent (.sent (.npDetRel .the
                  (.rcnSubj .princess .that
                    (.vpTrans .helped .alice)))
                .shuddered)
```


::::exercise (rating := 2) (name := "fragment-translations")
Construa as árvores de análise das quatro sentenças a seguir, todas geradas pelo fragmento.

1. Every girl that laughed helped a boy.
2. No giant that shuddered defeated every dwarf.
3. Every princess loved every dwarf that defeated a giant.
4. Every boy admired a girl that no wizard helped.

Os teoremas conferem que cada árvore devolve a sentença certa. Depois de construir as árvores, execute `#eval toString (lfSent tr1)` para ver a forma lógica da primeira sentença.

```lean
def tr1 : Sent :=
  solution!(
    .sent (.npDetRel .every (.rcnSubj .girl .that .laughed))
          (.vpTrans .helped (.npDet .a .boy)))

def tr2 : Sent :=
  solution!(
    .sent (.npDetRel .no (.rcnSubj .giant .that .shuddered))
          (.vpTrans .defeated (.npDet .every .dwarf)))

def tr3 : Sent :=
  solution!(
    .sent (.npDet .every .princess)
      (.vpTrans .loved
        (.npDetRel .every
          (.rcnSubj .dwarf .that
            (.vpTrans .defeated (.npDet .a .giant))))))

def tr4 : Sent :=
  solution!(
    .sent (.npDet .every .boy)
      (.vpTrans .admired
        (.npDetRel .a
          (.rcnObj .girl .that (.npDet .no .wizard)
            .helped))))

theorem tr1_surface :
    toString tr1 =
      "every girl that laughed helped a boy" :=
  solution!(by rfl)

theorem tr2_surface :
    toString tr2 =
      "no giant that shuddered defeated every dwarf" :=
  solution!(by rfl)

theorem tr3_surface :
    toString tr3 =
      "every princess loved every dwarf " ++
        "that defeated a giant" :=
  solution!(by rfl)

theorem tr4_surface :
    toString tr4 =
      "every boy admired a girl that no wizard helped" :=
  solution!(by rfl)
```

:::gradeTheorem "1" tr1_surface tr2_surface
:::

:::gradeTheorem "1" tr3_surface tr4_surface
:::
::::

Temos agora representações de sentenças declarativas da língua natural como fórmulas da lógica de predicados. Falta dizer quando essas fórmulas são verdadeiras.


# Uma Estrutura de Primeira Ordem
%%%
tag := "english-model"
%%%

Tudo o que precisamos para especificar uma estrutura de primeira ordem é um domínio de entidades e interpretações apropriadas para os nomes próprios e para os predicados. Começamos construindo um pequeno domínio de exemplo, formado pelos indivíduos `A`, …, `Z`, mais uma entidade especial.

```lean
inductive Entity where
  | A | B | C | D | E | F | G | H | I
  | J | K | L | M | N | O | P | Q | R
  | S | T | U | V | W | X | Y | Z
  | Unspec
deriving Repr, DecidableEq
```

A entidade especial `Unspec` terá um papel importante no tratamento das relações subespecificadas: ela nos permitirá definir relações com algumas posições de argumento deixadas em aberto.

Para avaliar uma fórmula quantificada é preciso percorrer o domínio, e percorrer exige uma coleção. Como em {ref "FOL"}[FOL], o tipo indutivo declara quais são os objetos e a lista os exibe na ordem em que serão percorridos.

```lean
def entities : List Entity :=
  [.A, .B, .C, .D, .E, .F, .G, .H, .I,
   .J, .K, .L, .M, .N, .O, .P, .Q, .R,
   .S, .T, .U, .V, .W, .X, .Y, .Z,
   .Unspec]

theorem mem_entities (e : Entity) : e ∈ entities := by
  cases e <;> decide
```

O teorema {name}`mem_entities` diz que na lista estão todos os elementos do tipo, e voltaremos a ele no fim da seção.

Os nomes próprios são interpretados simplesmente como entidades.

```lean
def snowWhite : Entity := .S
def alice : Entity := .A
def dorothy : Entity := .D
def goldilocks : Entity := .G
def littleMook : Entity := .M
def atreyu : Entity := .Y
```

Representamos propriedades e relações sobre `Entity` por funções que recebem um argumento de cada vez.

```lean
abbrev OnePlacePred := Entity → Bool
abbrev TwoPlacePred := Entity → Entity → Bool
abbrev ThreePlacePred := Entity → Entity → Entity → Bool
```

Como o capítulo {ref "Sets"}[Conjuntos e Relações] mostrou, um predicado de um lugar é a função característica de um conjunto, e é natural pensá-lo como a lista das entidades para as quais ele vale. Definimos então funções de conversão que transformam listas em predicados.

```lean
def list1 (xs : List Entity) : OnePlacePred :=
  fun x => xs.contains x

def list2 (ps : List (Entity × Entity)) : TwoPlacePred :=
  fun x y => ps.contains (x, y)

def list3 (ts : List (Entity × Entity × Entity)) :
    ThreePlacePred :=
  fun x y z => ts.contains (x, y, z)
```

Substantivos comuns como *girl* e *dwarf* são interpretados como propriedades de entidades.

```lean
def girl : OnePlacePred := list1 [.S, .A, .D, .G]
def boy : OnePlacePred := list1 [.M, .Y]
def princess : OnePlacePred := list1 [.E]
def dwarf : OnePlacePred := list1 [.B, .R]
def giant : OnePlacePred := list1 [.T]
def wizard : OnePlacePred := list1 [.W, .V]
def sword : OnePlacePred := list1 [.F]
def dagger : OnePlacePred := list1 [.X]
```

Com esses predicados podemos definir outros, como o de ser uma pessoa ou uma coisa: uma pessoa é um menino, uma menina, uma princesa, um anão, um gigante ou um mago, e uma coisa é tudo o que não é pessoa nem o objeto especial `Unspec`. É conveniente ter também homens e mulheres: supomos que as mulheres são as princesas e que os homens são os anões, os gigantes e os magos.

```lean
def child : OnePlacePred := fun x => girl x || boy x
def person : OnePlacePred := fun x =>
  child x || princess x || dwarf x || giant x || wizard x
def man : OnePlacePred := fun x =>
  dwarf x || giant x || wizard x
def woman : OnePlacePred := princess
def male : OnePlacePred := fun x => man x || boy x
def female : OnePlacePred := fun x => woman x || girl x
def thing : OnePlacePred := fun x =>
  !(person x || x == .Unspec)
```

Os verbos intransitivos também denotam propriedades. Seus significados são representados igualmente por predicados de um lugar.

```lean
def laugh : OnePlacePred := list1 [.A, .G, .E]
def cheer : OnePlacePred := list1 [.M, .D]
def shudder : OnePlacePred := list1 [.S]
```

Verbos transitivos são interpretados como relações, o primeiro argumento é o sujeito e o segundo é o objeto direto. Dois deles não são dados por uma lista fixa: *admire* vale de toda pessoa para Goldilocks, e *defeat* vale de todo anão para todo gigante, além dos dois pares em que Alice derrota um mago.

```lean
def love : TwoPlacePred :=
  list2 [(.Y, .E), (.B, .S), (.R, .S)]

def help : TwoPlacePred :=
  list2 [(.W, .W), (.V, .V), (.S, .B), (.D, .M)]

def admire : TwoPlacePred := fun x y =>
  person x && y == .G

def defeat : TwoPlacePred := fun x y =>
  (dwarf x && giant y) || list2 [(.A, .W), (.A, .V)] x y
```

Nas relações que interpretam os verbos ditransitivos, os argumentos são o sujeito, o objeto indireto e o objeto direto, nessa ordem.

```lean
def give : ThreePlacePred :=
  list3 [(.T, .S, .X), (.A, .E, .S)]
```

:::details "Argumentos deixados em aberto"
A entidade `Unspec` serve para definir relações subespecificadas. Podemos, por exemplo, acrescentar um verbo *kill* e interpretá-lo como uma relação de três lugares em que o primeiro argumento dá o agente, o segundo a vítima e o terceiro o instrumento. Nos casos em que não há instrumento ou agente, deixamos o argumento em aberto.

```lean
def kill : ThreePlacePred :=
  list3 [(.Y, .T, .F), (.Unspec, .D, .X),
         (.Unspec, .M, .Unspec)]
```

Atreyu matou o gigante com a espada. Dorothy foi morta com o punhal, com agente não especificado. Little Mook também figura como vítima na relação `kill`, com agente e instrumento não especificados. A lista contém a tupla `(.Unspec, .D, .X)`, então `kill .Unspec .D .X` devolve {lean}`true`. Uma consulta com Atreyu como agente, `kill .Y .D .X`, devolve {lean}`false`, pois essa tupla está ausente. Ou seja, {name}`Entity.Unspec` não é um coringa, mas uma entidade especial para designar uma entidade desconhecida.

Usar `Unspec` para deixar argumentos implícitos pode ser explorado de maneira mais geral. Um exemplo são as passivas. A passivização é um processo de redução de argumentos: o agente da ação é suprimido. Sem entrar nas propriedades sutis das construções passivas, podemos especificar uma função de passivização semântica assim:

```lean
def passivize (r : TwoPlacePred) : OnePlacePred :=
  fun x => r .Unspec x
```

O predicado resultante vale para `x` quando a relação registra `x` com agente não especificado, ou seja, quando `r .Unspec x` vale.

A redução de argumentos não aparece só nas passivas. Outro caso é uma análise dos pronomes reflexivos segundo a qual *himself* e *herself* diferem semanticamente de *him* e *her* por não serem interpretados como variáveis individuais: eles denotam funções que reduzem argumentos. Considere a sentença *Snow White admired herself*. O reflexivo *herself* é interpretado como uma função que toma o predicado de dois lugares *admired* e o transforma num predicado de um lugar, que toma o sujeito como argumento e exprime que essa entidade admira a si mesma.

```lean
def self {α β : Type} (p : α → α → β) : α → β :=
  fun x => p x x
```

Essa análise tem duas consequências desejáveis. A primeira é que a localidade dos reflexivos decorre imediatamente: como `self` se aplica a um predicado e unifica argumentos desse predicado, não há como um argumento ser unificado com outro de fora da mesma oração. Em *Snow White thinks that Alice admired herself*, portanto, *herself* só pode se referir a Alice, e não a Snow White. A segunda é que reflexivos em posição de sujeito ficam excluídos: em *Herself admired Snow White*, a interpretação composicional aplica primeiro *admired* a Snow White, o que dá um predicado de um lugar, e aplicar `self` a ele falha, porque `self` espera um predicado de dois lugares. Não sobram duas posições de argumento a unificar.

:::

::::exercise (rating := 1) (name := "reflexive-ditransitive")
Nos verbos ditransitivos, um reflexivo pode ser tanto o objeto direto quanto o objeto indireto:

1. Alice introduced herself to the rabbit.
2. Little Mook gave the figs to himself.

Defina as funções `self3DO` e `self3IO`, de tipo `ThreePlacePred → TwoPlacePred`, que unificam o sujeito com o objeto direto e com o objeto indireto, respectivamente. Lembre que, num predicado de três lugares, o primeiro argumento é o do sujeito, o segundo o do objeto indireto e o terceiro o do objeto direto.

Para testar as duas funções, `introduced x y z` diz que `x` apresentou `z` a `y`: Alice apresentou a si mesma ao anão `B`, e Snow White apresentou a princesa ao mesmo anão.

```lean
def introduced : ThreePlacePred :=
  list3 [(.A, .B, .A), (.S, .B, .E)]

def self3DO (p : ThreePlacePred) : TwoPlacePred :=
  solution!(fun x y => p x y x)

def self3IO (p : ThreePlacePred) : TwoPlacePred :=
  solution!(fun x y => p x x y)

theorem self3DO_introduced :
    self3DO introduced .A .B = true :=
  solution!(by decide)

theorem self3IO_introduced :
    self3IO introduced .A .B = false :=
  solution!(by decide)
```

:::gradeTheorem "1" self3DO_introduced self3IO_introduced
:::
::::


## Interpretando os Símbolos

Já temos, em {ref "fol-semantics"}[Semântica de FOL], tudo o que é preciso para avaliar fórmulas: {name}`FOL.Interp` interpreta os símbolos de predicado, {name}`FOL.FInterp` os símbolos funcionais, {name}`FOL.Assign` as variáveis, e {name}`FOL.Formula.eval` percorre a fórmula. Falta apenas ligar os nomes que a tradução produz às relações que acabamos de definir.

Esses nomes e essas relações são coisas diferentes, embora sejam escritos de forma parecida. Na fórmula, `"laugh"` é um símbolo de predicado: uma string produzida pela tradução, que sozinha não diz nada sobre o mundo. Na estrutura, {name}`laugh` é uma função Lean de tipo {name}`OnePlacePred`, que diz quais entidades riram. A interpretação `intFairy` associa o primeiro à segunda.

```lean
def intFairy : Interp Entity
  | "girl", [x] => girl x
  | "boy", [x] => boy x
  | "princess", [x] => princess x
  | "dwarf", [x] => dwarf x
  | "giant", [x] => giant x
  | "wizard", [x] => wizard x
  | "sword", [x] => sword x
  | "dagger", [x] => dagger x
  | "person", [x] => person x
  | "laugh", [x] => laugh x
  | "cheer", [x] => cheer x
  | "shudder", [x] => shudder x
  | "love", [x, y] => love x y
  | "admire", [x, y] => admire x y
  | "help", [x, y] => help x y
  | "defeat", [x, y] => defeat x y
  | "give", [x, y, z] => give x y z
  | _, _ => false
```

Os nomes próprios foram traduzidos como constantes, isto é, como símbolos funcionais de aridade zero. É {name}`FOL.FInterp` que diz qual entidade cada um nomeia, e `Unspec` é o valor natural para os símbolos que a estrutura não nomeia. `"Goldilocks"` é a constante da fórmula, e {name}`goldilocks`, isto é, {name}`Entity.G`, é a entidade que ela nomeia.

```lean
def fintFairy : FInterp Entity
  | "SnowWhite", [] => snowWhite
  | "Alice", [] => alice
  | "Dorothy", [] => dorothy
  | "Goldilocks", [] => goldilocks
  | "LittleMook", [] => littleMook
  | "Atreyu", [] => atreyu
  | _, _ => .Unspec
```

No fragmento deste capítulo, *catch* e os adjetivos caem no caso padrão de `intFairy`, que devolve {lean}`false` para qualquer lista de argumentos. O valor da sentença inteira depende de como esses predicados aparecem na fórmula. Por exemplo, *No dwarf caught Alice* é verdadeira nesta estrutura porque nenhum anão satisfaz a relação *catch* com Alice como objeto.

Falta a atribuição de valores às variáveis. As fórmulas que a tradução produz são sentenças, sem variáveis livres, e para elas a atribuição é irrelevante — mas {name}`FOL.Formula.eval` ainda exige alguma.

```lean
def ass0 : Assign Entity := fun _ => .A
```

Agora podemos avaliar. A fórmula que diz que a relação de amor é reflexiva é falsa nesta estrutura, como seria de esperar.

```lean (name := loveReflEval)
def loveReflexive : LF :=
  .forall_ x (.atom "love" [tx, tx])

#eval loveReflexive.eval entities intFairy ass0
        (liftAssign fintFairy)
```

```leanOutput loveReflEval
false
```

::::exercise (rating := 1) (name := "check-sentence")
Junte as duas metades. Defina a função que decide se uma sentença do fragmento é verdadeira nesta estrutura: ela deve traduzir a sentença para uma forma lógica e avaliar essa forma lógica no domínio {name}`entities`, com as interpretações {name}`intFairy` e {name}`fintFairy` e com a atribuição {name}`ass0`.

```lean
def checkSentence (s : Sent) : Bool :=
  solution!(
    (lfSent s).eval entities intFairy ass0
      (liftAssign fintFairy))

theorem goldilocksLaughed :
    checkSentence (.sent .goldilocks .laughed) = true :=
  solution!(by native_decide)

theorem dorothyLaughed :
    checkSentence (.sent .dorothy .laughed) = false :=
  solution!(by native_decide)

theorem someDwarfDefeatedSomeGiant :
    checkSentence
      (.sent (.npDet .some .dwarf)
             (.vpTrans .defeated (.npDet .some .giant)))
      = true :=
  solution!(by native_decide)

theorem everyoneCheered :
    checkSentence (.sent .everyone .cheered) = false :=
  solution!(by native_decide)
```

:::gradeTheorem "1" goldilocksLaughed dorothyLaughed
:::

:::gradeTheorem "1" someDwarfDefeatedSomeGiant everyoneCheered
:::
::::

Para avaliar os quantificadores universal e existencial, {name}`FOL.Formula.eval` percorre a lista do domínio. A hipótese `hdom` de {name}`FOL.Formula.eval_iff_denote` exige que essa lista contenha todos os elementos do domínio. Para `entities`, essa hipótese é dada por {name}`mem_entities`.

```lean
theorem eval_iff_denote_fairy (I : Interp Entity)
    (g : Assign Entity) (f : Formula Term) :
    f.eval entities I g (liftAssign fintFairy) = true ↔
      f.denote (fun n as => I n as = true) g
        (liftAssign fintFairy) :=
  Formula.eval_iff_denote entities mem_entities I
    (liftAssign fintFairy) g f
```

O teorema diz que a avaliação de uma fórmula devolve {lean}`true` se e somente se a proposição dada por {name}`FOL.Formula.denote` vale. Em particular, no exercício {cref "check-sentence"}[] vimos que {name}`checkSentence` devolve {lean}`true` exatamente quando a forma lógica da sentença é verdadeira nesta estrutura. Mas no capítulo {cref "FOL"}[], vimos que nenhuma lista finita contém todos os números naturais.

::::exercise (rating := 2) (name := "help-model")
Até aqui a estrutura estava dada e perguntávamos que sentenças são verdadeiras nela. Agora o caminho é o inverso. A interpretação `intHelp h` coincide com `intFairy` em tudo, exceto em *help*, que passa a ser interpretado pela relação `h`. A função `holdsWithHelp h` avalia uma sentença na estrutura com essa interpretação.

Defina uma relação `help'` tal que, na estrutura em que *help* é interpretado por ela, as sentenças a seguir tenham os valores indicados.

1. *Every wizard helped every wizard* — verdadeira.
2. *Alice helped a dwarf* — verdadeira.
3. *No dwarf helped Snow White* — verdadeira.
4. *Snow White helped a dwarf* — falsa.

```lean
def intHelp (h : TwoPlacePred) : Interp Entity
  | "help", [x, y] => h x y
  | n, as => intFairy n as

def holdsWithHelp (h : TwoPlacePred) (s : Sent) : Bool :=
  (lfSent s).eval entities (intHelp h) ass0
    (liftAssign fintFairy)

def help' : TwoPlacePred :=
  solution!(
    list2 [(.W, .W), (.V, .V), (.W, .V), (.V, .W),
           (.A, .B)])

theorem every_wizard_helped_every_wizard :
    holdsWithHelp help'
      (.sent (.npDet .every .wizard)
             (.vpTrans .helped (.npDet .every .wizard)))
      = true :=
  solution!(by native_decide)

theorem alice_helped_a_dwarf :
    holdsWithHelp help'
      (.sent .alice (.vpTrans .helped (.npDet .a .dwarf)))
      = true :=
  solution!(by native_decide)

theorem no_dwarf_helped_snowWhite :
    holdsWithHelp help'
      (.sent (.npDet .no .dwarf)
             (.vpTrans .helped .snowWhite))
      = true :=
  solution!(by native_decide)

theorem snowWhite_helped_a_dwarf :
    holdsWithHelp help'
      (.sent .snowWhite
             (.vpTrans .helped (.npDet .a .dwarf)))
      = false :=
  solution!(by native_decide)
```

:::gradeTheorem "4" every_wizard_helped_every_wizard alice_helped_a_dwarf no_dwarf_helped_snowWhite snowWhite_helped_a_dwarf
:::
::::


```lean
end ModelChecking
```
