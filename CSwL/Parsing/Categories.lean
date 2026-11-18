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
  categorias nas folhas e nos nós internos: `Parser Cat (ParseTree Cat Cat)`.
- A função `t2c` devolve a categoria da raiz de uma árvore.
- As funções `agreeC` e `assignT` levam `agree` e `assign` para as
  árvores. Em `assignT`, `map` põe a categoria nova de volta na árvore,
  dentro da `Option` devolvida por `assign`.
- O parser `leafP l` lê uma categoria com rótulo `l` e a devolve como
  folha.
- As funções `combine` e `assign` devolvem `Option`. Dentro de um
  parser, queremos que uma falha delas seja uma falha do parser, que
  então não produz nenhuma análise. A função `fromOption` faz essa
  ponte: `some b` vira `pure b`, e `none` vira `failure`.
- Para exibir uma árvore, usamos um único AVM, como em HPSG
  {citep Bib.sag1999}[], onde a frase inteira é uma estrutura de traços. As filhas de um nó ficam
  dentro dela, no atributo `ARGS`: o nó `.branch c ts` é o AVM de `c`
  com mais um atributo, `ARGS ⟨…⟩`, a lista dos AVMs das árvores `ts`.
  Uma folha `.leaf c` é só o AVM de `c`.
- A árvore continua lá, mas aninhada: cada `ARGS` é um nível abaixo.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.6, from the start to the definition of
`assignT`, plus a sentence on `fromOption`, which is not in CSwFP.
:::
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
partial def ParseTree.fmt : ParseTree Cat Cat → Std.Format
  | .leaf c => avmFmt c.attrs
  | .branch c [] => avmFmt c.attrs
  | .branch c ts =>
    let attrs := Std.Format.group
      (Std.Format.joinSep c.attrs ("," ++ Std.Format.line))
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
:::dev BeforeNextRelease
TODO: translate CSwFP/9.6, "Determiners are always lexical:", "For now,
common nouns are always in the lexicon…" and "All prepositions and all
auxiliaries are lexical:".
:::
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
  impõe ao `NP` o caso `accOrDat`: é o controle de traços. Por isso
  _with her_ é um `PP`, mas _with she_ não é: _she_ tem o caso `nom`,
  que conflita com `accOrDat`.
- Os complementos de um verbo são `NP`s e `PP`s. O parser
  `parseNPsorPPs` lê uma sequência deles, com `many`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.6, from "Noun phrases can either be formed
according to a rule…" to the definition of `parseNPsorPPs`.
:::
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
  quais complementos o verbo ainda espera. _Loved_ espera um `NP` com
  `accOrDat`, o objeto direto: em _Alice loved the dwarf_, é _the
  dwarf_; em _Alice loved him_, é _him_. Ao encontrá-lo, a pendência é
  resolvida. O `VP` formado pela regra tem a lista vazia, porque já tem
  todos os seus complementos.
- A função `matchSubcat` faz essa casagem, elemento a elemento: os
  rótulos têm de ser iguais, e os traços têm de concordar. É assim que
  _gave_ aceita um `PP` com `to`, e não um com `with`.
- Num `VP` finito, o verbo tem de aceitar o traço `tense`.
- Um `VP` também pode ser um auxiliar seguido de um `VP` no infinitivo,
  que tem de aceitar o traço `infl`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.6, from "Verb phrases are either parsed with a
rule for finite VPs…" to the definition of `auxVpRule`.
:::
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
- Uma frase é sempre formada pela regra sujeito–predicado,
  `S → NP VP`. O sujeito e o predicado têm de concordar, o sujeito tem
  de aceitar o caso `nom`, e o predicado já tem de ter todos os seus
  complementos: a sua lista de subcategorização é vazia.
- A função `prs` analisa uma cadeia: aplica `lexer`, consulta o léxico
  com `collectCats` e, para cada escolha de categorias, fica com as
  análises de `parseSent` que consomem a entrada inteira.
- O resultado é um `Except`, com dois erros possíveis: uma palavra
  desconhecida, vindo de `collectCats`, e uma frase que a gramática não
  aceita, quando não sobra nenhuma análise. Assim, `.ok` sempre traz
  pelo menos uma árvore.
- Em notação `do`, um `.error` interrompe o cálculo, como `none` faria
  com `Option`. O comando `throw e` produz o erro `e`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.6, from "Sentences are all constructed by means
of the subject–predicate rule." to the definition of `parseSent`, and
from "Parsing is the process of constructing a list of parse trees…" to
the end of the section.
:::
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
