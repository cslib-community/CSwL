import CSwLMeta
import Bib
import CSwL.Parsing.Combinators
import CSwL.Parsing.Lexicon

open Verso.Genre Manual
open CSwLMeta

set_option verso.code.warnLineLength 100

#doc (Manual) "Análise Sintática com Categorias" =>
%%%
tag := "parsing-categories"
file := "Categories"
%%%

```lean
namespace Parsing
```

:::terse
- Agora a entrada do parser é uma lista de categorias, e as árvores têm
  categorias nas folhas e nos nós internos: {lean}`Parser Cat (ParseTree Cat Cat)`.
- A função `t2c` devolve a categoria da raiz de uma árvore.
- As funções `agreeC` e `assignT` levam {name}`agree` e {name}`assign` para as
  árvores. Em `assignT`, `map` põe a categoria nova de volta na árvore,
  dentro da {name}`Option` devolvida por {name}`assign`.
- O parser `leafP l` lê uma categoria com rótulo `l` e a devolve como
  folha.
- As funções {name}`combine` e {name}`assign` devolvem {name}`Option`. Dentro de um
  parser, queremos que uma falha delas seja uma falha do parser, que
  então não produz nenhuma análise. A função `fromOption` faz essa
  ponte: `some b` vira `pure b`, e `none` vira {name}`failure`.
- Para exibir uma árvore, usamos um único AVM, como em HPSG
  {citep Bib.sag1999}[], onde a sentença inteira é uma estrutura de traços.
  As filhas de um nó ficam dentro dela, no atributo `ARGS`: o nó
  `.branch c ts` é o AVM de `c` com mais um atributo, `ARGS ⟨…⟩`, a
  lista dos AVMs das árvores `ts`.
  Uma folha `.leaf c` é só o AVM de `c`.
- Num sintagma, `PHON` é a lista das formas das folhas, na ordem, como
  em HPSG: o `VP` de `loved her` tem `PHON ⟨loved, her⟩`. O campo `phon`
  do nó continua `"_"`; a lista é calculada só para a exibição.
- A árvore continua lá, mas aninhada: cada `ARGS` é um nível abaixo.
:::

::::full
Vamos analisar uma entrada em que cada palavra já foi substituída
por uma categoria do léxico. Os parsers terão tipo
{lean}`Parser Cat (ParseTree Cat Cat)`. Assim, tanto as folhas
quanto os nós internos das árvores guardam categorias com rótulos,
traços e listas de subcategorização.

Para consultar a categoria de uma árvore, usamos `t2c`. Se a
árvore é uma folha, a função devolve sua categoria. Se é um nó,
devolve a categoria da raiz. A função `agreeC` usa {name}`agree`
para testar a concordância entre duas árvores.

A atribuição de um traço também pode ser feita sobre uma árvore.
A função `assignT` aplica {name}`assign` à categoria da raiz
e usa {name}`Option.map` para reconstruir a folha ou o nó com
a categoria resultante. As filhas são conservadas.
Se a atribuição falhar, o resultado será {name}`Option.none`.

O parser elementar `leafP l` reconhece uma categoria cujo rótulo
é `l` e a transforma em uma folha. Ao construir parsers mais
complexos, precisaremos também converter resultados de
{name}`combine` e {name}`assign` em passos da análise. A função
`fromOption` faz essa conversão. Para `some b`, produz
`pure b`, que entrega `b` sem consumir entrada. Para
{name}`Option.none`, produz {name}`failure`, de modo que essa
tentativa de análise não devolva resultado.

Exibiremos cada árvore como uma AVM que contém as AVMs de suas
filhas no atributo `ARGS`, como uma estrutura de traços aninhada
{citep Bib.sag1999}[]. Uma folha mostra apenas a categoria lexical.
Um nó com filhas mostra os atributos da categoria da raiz e a
lista de árvores filhas em `ARGS`. Seu atributo `PHON` reúne
as formas das folhas, na ordem em que aparecem. Por exemplo, o
`VP` de `loved her` tem `PHON ⟨loved, her⟩`. Essa lista é
calculada para a exibição; o campo {name}`Cat.phon` da categoria
do sintagma continua contendo `"_"`. O bloco de detalhes
implementa essa apresentação.
::::

```lean
abbrev CatParser := Parser Cat (ParseTree Cat Cat)

def t2c : ParseTree Cat Cat → Cat
  | .leaf c => c
  | .branch c _ => c

def agreeC (t1 t2 : ParseTree Cat Cat) : Bool :=
  agree (t2c t1) (t2c t2)

def leafP (label : CatLabel) : CatParser :=
  .leaf <$> satisfy (·.label == label)

def assignT (f : Feat) : ParseTree Cat Cat → Option (ParseTree Cat Cat)
  | .leaf c => (assign f c).map .leaf
  | .branch c ts => (assign f c).map (.branch · ts)

def fromOption {α β : Type} : Option β → Parser α β
  | some b => pure b
  | none => failure
```

:::details "Exibindo árvores como AVMs"
```lean
partial def ParseTree.yield : ParseTree Cat Cat → List String
  | .leaf c => [c.phon]
  | .branch _ ts => ts.flatMap ParseTree.yield

partial def ParseTree.fmt : ParseTree Cat Cat → Std.Format
  | .leaf c => avmFmt c.attrs
  | .branch c [] => avmFmt c.attrs
  | t@(.branch c ts) =>
    -- a phrase has no form of its own: show the forms of its leaves
    let phonAttr := "PHON " ++ listFmt (t.yield.map Std.Format.text)
    let cattrs := c.attrs.take 1 ++ [phonAttr] ++ c.attrs.drop 1
    let attrs := Std.Format.group
      (Std.Format.joinSep cattrs ("," ++ Std.Format.line))
    let args := "ARGS " ++ Std.Format.nest 5 (listFmt (ts.map ParseTree.fmt))
    Std.Format.bracket "[" (attrs ++ "," ++ Std.Format.line ++ args) "]"

instance : Repr (ParseTree Cat Cat) := ⟨fun t _ => t.fmt⟩
```
:::

```lean
open Examples in
#eval (.branch ⟨"_", "S", [], []⟩ [.leaf she, .leaf laughs] : ParseTree Cat Cat)
```

:::terse
- Determinantes, substantivos comuns, preposições e auxiliares são
  sempre lexicais: os seus parsers só leem uma folha com o rótulo certo.
- Por enquanto, um substantivo comum é sempre uma palavra do léxico.
:::

::::full
Começamos pelas categorias que reconhecemos diretamente na entrada.
Os determinantes têm rótulo `DET`, os substantivos comuns têm
rótulo `CN`, as preposições têm rótulo `PREP` e os auxiliares
têm rótulo `AUX`. Para cada uma, basta aplicar {name}`leafP`
com o rótulo correspondente.

Esses parsers reconhecem uma única categoria lexical por vez.
Em particular, o parser de `CN` aceita apenas substantivos
comuns encontrados no léxico.
::::

```lean
def parseDET : CatParser := leafP "DET"
def parseCN : CatParser := leafP "CN"
def parsePrep : CatParser := leafP "PREP"
def parseAux : CatParser := leafP "AUX"
```

:::terse
- Um `NP` é uma palavra do léxico ou é formado pela regra
  `NP → DET CN`. Na regra, o determinante e o substantivo têm de
  concordar, e o `NP` recebe os traços dos dois.
- Um `PP` é sempre formado pela regra `PP → PREP NP`. A preposição
  impõe ao `NP` o caso {lean}`Feat.accOrDat`: é o controle de traços. Por isso
  `with her` é um `PP`, mas `with she` não é: `she` tem o caso {lean}`Feat.nom`,
  que conflita com {lean}`Feat.accOrDat`.
- Os complementos de um verbo são `NP`s e `PP`s. O parser
  `parseNPsorPPs` lê uma sequência deles, com {name}`many`.
:::

::::full
Um sintagma nominal pode ser uma categoria lexical com rótulo
`NP`, como a de um pronome ou nome próprio. Também pode ser
construído pela regra `NP → DET CN`. A função `npRule`
analisa o determinante e o substantivo comum e combina seus traços.
Se houver incompatibilidade, a tentativa falha. Se a combinação
der certo, o nó `NP` recebe os traços resultantes e tem as duas
árvores como filhas. O parser `parseNP` reúne a alternativa
lexical e essa regra.

O sintagma preposicional segue a regra `PP → PREP NP`. Depois
de analisar a preposição e o sintagma nominal, `ppRule` atribui
{lean}`Feat.accOrDat` à raiz da árvore do `NP`. Esse passo
expressa controle de traços. O pronome `her` aceita esse caso,
mas `she` já tem {lean}`Feat.nom`, e a atribuição falha.
Assim, a regra aceita `with her` e recusa `with she`.

Os traços da preposição são combinados com os do sintagma nominal
atualizado, e o resultado vai para o nó `PP`. Sua segunda filha
é a árvore que recebeu o caso. Para ler os complementos de um
verbo, `parseNPorPP` permite escolher entre os dois tipos de
sintagma. A função `parseNPsorPPs` usa {name}`many` para
analisar sequências deles, incluindo a sequência vazia.
::::

```lean
def npRule : CatParser := do
  let det ← parseDET
  let cn ← parseCN
  let fs ← fromOption (combine (t2c det) (t2c cn))
  if !agreeC det cn then failure
  return .branch ⟨"_", "NP", fs, []⟩ [det, cn]

def parseNP : CatParser := leafP "NP" <|> npRule

def ppRule : CatParser := do
  let prep ← parsePrep
  let np ← parseNP
  let np' ← fromOption (assignT .accOrDat np)
  let fs ← fromOption (combine (t2c prep) (t2c np'))
  return .branch ⟨"_", "PP", fs, []⟩ [prep, np']

def parsePP : CatParser := ppRule

def parseNPorPP : CatParser := parseNP <|> parsePP

def parseNPsorPPs : Parser Cat (List (ParseTree Cat Cat)) :=
  many parseNPorPP

open Examples in
#eval ((just parseNP).run [the, child]).map (·.1)
#eval ((just parsePP).run (lexicon "with" ++ lexicon "her")).map (·.1)
#eval ((just parsePP).run (lexicon "with" ++ lexicon "she")).length
```

:::terse
- A regra do `VP` lê um verbo e uma sequência de `NP`s e `PP`s, que
  tem de casar com a lista de subcategorização do verbo.
- A lista de subcategorização funciona como uma lista de pendências: diz
  quais complementos o verbo ainda espera. A forma `loved` espera um `NP`
  com {lean}`Feat.accOrDat`, o objeto direto. Em `Alice loved the dwarf`,
  o objeto é `the dwarf`; em `Alice loved him`, é `him`. Ao encontrá-lo,
  a pendência é resolvida. O `VP` formado pela regra tem a lista vazia, porque já tem
  todos os seus complementos.
- A folha do verbo continua com a sua lista: ela registra o que o verbo
  pede. A pendência é resolvida no nó pai, e não apagada da folha.
- A função `matchSubcat` faz essa casagem, elemento a elemento: os
  rótulos têm de ser iguais, e os traços têm de concordar. É assim que
  `gave` aceita um `PP` com {lean}`Feat.to`, e não um com {lean}`Feat.with`.
- Num `VP` finito, o verbo tem de aceitar o traço {lean}`Feat.tense`.
- Um `VP` também pode ser um auxiliar seguido de um `VP` no infinitivo,
  que tem de aceitar o traço {lean}`Feat.infl`.
:::

::::full
Para construir um sintagma verbal, `vpRule` lê uma categoria
lexical com rótulo `VP` e uma sequência de sintagmas nominais
ou preposicionais. A sequência precisa satisfazer a lista de
subcategorização do verbo. A função `matchSubcat` compara as
listas na mesma ordem. Elas devem ter o mesmo comprimento, e
cada complemento deve ter o rótulo esperado e traços compatíveis
com os exigidos.

Por exemplo, `loved` espera um `NP` com
{lean}`Feat.accOrDat`. Em `Alice loved the dwarf`, o objeto
é `the dwarf`; em `Alice loved him`, é `him`. Para uma
entrada de `gave` que espera um `PP` com {lean}`Feat.to`,
um complemento com {lean}`Feat.with` falha no teste de
concordância.

A lista de subcategorização registra os complementos que ainda
precisam ser encontrados. Quando a regra os encontra, constrói
um nó `VP` com lista vazia e com o verbo e os complementos como
filhas. A folha lexical do verbo conserva a lista original,
registrando as exigências que foram satisfeitas nesse nó.

Há duas maneiras de obter um `VP` aceito por `parseVP`.
A função `finVpRule` exige que o sintagma construído por
`vpRule` aceite {lean}`Feat.tense`. Já `auxVpRule` lê
um auxiliar e um sintagma verbal que aceite {lean}`Feat.infl`.
Nesse caso, o novo nó `VP` recebe os traços do auxiliar e
tem como filhas o auxiliar e o sintagma no infinitivo.
Isso permite analisar `didn't smile`, enquanto
`didn't smiled` falha pela incompatibilidade de forma verbal.
::::

```lean
def matchSubcat : List Cat → List Cat → Bool
  | [], [] => true
  | x :: xs, y :: ys =>
    x.label == y.label && agree x y && matchSubcat xs ys
  | _, _ => false

def vpRule : CatParser := do
  let vp ← leafP "VP"
  let xps ← parseNPsorPPs
  if !matchSubcat (t2c vp).subcatList (xps.map t2c) then failure
  return .branch ⟨"_", "VP", (t2c vp).fs, []⟩ (vp :: xps)

def finVpRule : CatParser := do
  let vp ← vpRule
  fromOption (assignT .tense vp)

def auxVpRule : CatParser := do
  let aux ← parseAux
  let inf ← vpRule
  let inf' ← fromOption (assignT .infl inf)
  return .branch ⟨"_", "VP", (t2c aux).fs, []⟩ [aux, inf']

def parseVP : CatParser := finVpRule <|> auxVpRule

open Examples in
#eval ((just parseVP).run [laughs]).map (·.1)
#eval ((just parseVP).run (lexicon "didn't" ++ lexicon "smile")).map (·.1)
#eval ((just parseVP).run (lexicon "didn't" ++ lexicon "smiled")).length
```

:::terse
- Nesta gramática, uma sentença tem uma só oração, formada pela regra
  sujeito–predicado, `S → NP VP`. O sujeito e o predicado têm de concordar, o sujeito tem
  de aceitar o caso {lean}`Feat.nom`, e o predicado já tem de ter todos os seus
  complementos: a sua lista de subcategorização é vazia.
- A função `prs` analisa uma cadeia: aplica {name}`lexer`, consulta o léxico
  com {name}`collectCats` e, para cada escolha de categorias, fica com as
  análises de `parseSent` que consomem a entrada inteira.
- O resultado é um {name}`Except`, com dois erros possíveis: uma palavra
  desconhecida, vindo de {name}`collectCats`, e uma sentença que a gramática não
  aceita, quando não sobra nenhuma análise. Assim, `.ok` sempre traz
  pelo menos uma árvore.
- Em notação `do`, um `.error` interrompe o cálculo, como `none` faria
  com {name}`Option`. O comando `throw e` produz o erro `e`.
:::

::::full
A regra sujeito–predicado, `S → NP VP`, combina um sintagma
nominal com um sintagma verbal. Para que a combinação seja aceita,
o sujeito deve permitir a atribuição de {lean}`Feat.nom`,
e os traços do sujeito e do predicado devem concordar. O predicado
também deve ter completado sua lista de subcategorização. A árvore
resultante tem um nó `S` com o sujeito atualizado e o predicado
como filhas. O parser `parseSent` usa essa regra.

A função `prs` reúne as etapas da análise de um texto.
Primeiro, {name}`lexer` produz a lista de palavras. Depois,
{name}`collectCats` consulta o léxico e enumera as escolhas
de categorias para a entrada. Para cada escolha, aplicamos
`parseSent` com {name}`just`, conservando somente as análises
que consomem todas as categorias. Por fim, reunimos as árvores
dessas análises em uma lista.

O resultado usa {name}`Except`. Se uma palavra é desconhecida,
{name}`collectCats` devolve um erro com a mensagem
correspondente. Em um bloco `do` de {name}`Except`, um
resultado {name}`Except.error` interrompe a sequência de
passos e propaga o erro. Se todas as palavras são conhecidas, mas
nenhuma análise é encontrada, `throw "no parse"` produz outro
erro. Quando há sucesso, `return trees` entrega a lista de
árvores com {name}`Except.ok`. Essa lista contém pelo menos
uma árvore.

Os exemplos permitem distinguir essas situações. A entrada
`Her loved I.` viola as exigências de caso, enquanto
`She despised me.` contém uma palavra ausente do léxico.
Os exemplos com `gave` testam a preposição do complemento,
e o último combina auxiliar, infinitivo e um complemento
instrumental.
::::

```lean
def sRule : CatParser := do
  let np ← parseNP
  let vp ← parseVP
  let np' ← fromOption (assignT .nom np)
  if !agreeC np vp then failure
  if !(t2c vp).subcatList.isEmpty then failure
  return .branch ⟨"_", "S", [], []⟩ [np', vp]

def parseSent : CatParser := sRule

def prs (s : String) : Except String (List (ParseTree Cat Cat)) := do
  let catLists ← collectCats lexicon (lexer s)
  let trees := catLists.flatMap fun cs => ((just parseSent).run cs).map (·.1)
  if trees.isEmpty then throw "no parse"
  return trees

#eval prs "I loved her."
#eval prs "Her loved I."
#eval prs "She despised me."
#eval prs "Goldilocks gave the sword to Alice."
#eval prs "Goldilocks gave the sword with Alice."
#eval prs "Atreyu didn't kick the giant with a dagger."
```

```lean
end Parsing
```
