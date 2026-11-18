import CSwLMeta
import Bib
import CSwL.Parsing.Features

open Verso.Genre Manual
open CSwLMeta

set_option verso.code.warnLineLength 100

#doc (Manual) "Consulta ao Léxico e Análise Léxica" =>
%%%
tag := "lexicon-scanning"
file := "Lexicon"
%%%

```lean
namespace Parsing
```

:::terse
- O léxico leva cada palavra à lista das suas categorias. Uma palavra
  ambígua, como _that_, tem mais de uma.
- Guardamos as entradas em listas de `Cat`, uma por classe de palavras.
  Para consultar uma palavra, filtramos as entradas com essa forma.
- Cada entrada é uma categoria, e a exibimos como um AVM. Uma entrada
  do léxico sempre tem `ORTH`, a sua forma.
- Os pronomes trazem pessoa, número, caso e gênero. Os pronomes _wh_ e
  os relativos podem ter duas entradas, uma `NP` e uma `REL`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.5, from the start to the entries of the
wh-pronouns and relatives.
:::
::::

```lean
def pronouns : List Cat := [
  -- personal pronouns
  ⟨"i",    "NP", [.pers, .fst, .sg, .nom], []⟩,
  ⟨"me",   "NP", [.pers, .fst, .sg, .accOrDat], []⟩,
  ⟨"we",   "NP", [.pers, .fst, .pl, .nom], []⟩,
  ⟨"us",   "NP", [.pers, .fst, .pl, .accOrDat], []⟩,
  ⟨"you",  "NP", [.pers, .snd], []⟩,
  ⟨"he",   "NP", [.pers, .thrd, .sg, .nom, .masc], []⟩,
  ⟨"him",  "NP", [.pers, .thrd, .sg, .accOrDat, .masc], []⟩,
  ⟨"she",  "NP", [.pers, .thrd, .sg, .nom, .fem], []⟩,
  ⟨"her",  "NP", [.pers, .thrd, .sg, .accOrDat, .fem], []⟩,
  ⟨"it",   "NP", [.pers, .thrd, .sg, .neutr], []⟩,
  ⟨"they", "NP", [.pers, .thrd, .pl, .nom], []⟩,
  ⟨"them", "NP", [.pers, .thrd, .pl, .accOrDat], []⟩,
  -- reflexive pronouns
  ⟨"myself",     "NP", [.refl, .sg, .fst, .accOrDat], []⟩,
  ⟨"ourselves",  "NP", [.refl, .pl, .fst, .accOrDat], []⟩,
  ⟨"yourself",   "NP", [.refl, .sg, .snd, .accOrDat], []⟩,
  ⟨"yourselves", "NP", [.refl, .pl, .snd, .accOrDat], []⟩,
  ⟨"himself",    "NP", [.refl, .sg, .thrd, .accOrDat, .masc], []⟩,
  ⟨"herself",    "NP", [.refl, .sg, .thrd, .accOrDat, .fem], []⟩,
  ⟨"itself",     "NP", [.refl, .sg, .thrd, .accOrDat, .neutr], []⟩,
  ⟨"themselves", "NP", [.refl, .pl, .thrd, .accOrDat], []⟩,
  -- wh-pronouns and relatives
  ⟨"who",   "NP",  [.wh, .thrd, .mascOrFem], []⟩,
  ⟨"who",   "REL", [.mascOrFem], []⟩,
  ⟨"whom",  "NP",  [.sg, .wh, .thrd, .accOrDat, .mascOrFem], []⟩,
  ⟨"whom",  "REL", [.sg, .mascOrFem, .accOrDat], []⟩,
  ⟨"what",  "NP",  [.wh, .thrd, .accOrDat, .neutr], []⟩,
  ⟨"that",  "REL", [], []⟩,
  ⟨"that",  "DET", [.sg], []⟩,
  ⟨"which", "REL", [.neutr], []⟩,
  ⟨"which", "DET", [.wh], []⟩ ]
```

:::terse
- Os nomes próprios trazem só pessoa, gênero e número.
- Os determinantes trazem no máximo o número.
- Determinantes complexos, como _less than_, usam a categoria `DF`, de
  função de determinante.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.5, from "Proper names are:" to the entries of
the determiner functions.
:::
::::

```lean
def properNames : List Cat := [
  ⟨"snowwhite",  "NP", [.thrd, .fem, .sg], []⟩,
  ⟨"alice",      "NP", [.thrd, .fem, .sg], []⟩,
  ⟨"dorothy",    "NP", [.thrd, .fem, .sg], []⟩,
  ⟨"goldilocks", "NP", [.thrd, .fem, .sg], []⟩,
  ⟨"littlemook", "NP", [.thrd, .masc, .sg], []⟩,
  ⟨"atreyu",     "NP", [.thrd, .masc, .sg], []⟩ ]

def determiners : List Cat := [
  ⟨"every",   "DET", [.sg], []⟩,
  ⟨"all",     "DET", [.pl], []⟩,
  ⟨"some",    "DET", [], []⟩,
  ⟨"several", "DET", [.pl], []⟩,
  ⟨"a",       "DET", [.sg], []⟩,
  ⟨"no",      "DET", [], []⟩,
  ⟨"the",     "DET", [], []⟩,
  ⟨"most",    "DET", [.pl], []⟩,
  ⟨"many",    "DET", [.pl], []⟩,
  ⟨"few",     "DET", [.pl], []⟩,
  ⟨"this",    "DET", [.sg], []⟩,
  ⟨"these",   "DET", [.pl], []⟩,
  ⟨"those",   "DET", [.pl], []⟩,
  -- determiner functions
  ⟨"less_than", "DF", [.pl], []⟩,
  ⟨"more_than", "DF", [.pl], []⟩ ]
```

:::terse
- Os substantivos comuns vêm aos pares, singular e plural, com o mesmo
  gênero e a terceira pessoa. A função `noun` gera o par.
- Uma forma irregular a mais, como _dwarves_, entra por extenso.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.5, from "Common nouns are:" to the entries of
"More common nouns:".
:::
::::

```lean
def noun (sg pl : String) (g : Feat) : List Cat :=
  [⟨sg, "CN", [.sg, g, .thrd], []⟩, ⟨pl, "CN", [.pl, g, .thrd], []⟩]

def commonNouns : List Cat :=
  noun "thing" "things" .neutr ++
  noun "person" "persons" .masc ++
  noun "boy" "boys" .masc ++
  noun "man" "men" .masc ++
  noun "girl" "girls" .fem ++
  noun "woman" "women" .fem ++
  noun "princess" "princesses" .fem ++
  noun "dwarf" "dwarfs" .masc ++
  [⟨"dwarves", "CN", [.pl, .masc, .thrd], []⟩] ++
  noun "giant" "giants" .masc ++
  noun "wizard" "wizards" .masc ++
  noun "sword" "swords" .neutr ++
  noun "dagger" "daggers" .neutr

#eval noun "boy" "boys" .masc
```

:::terse
- Os auxiliares são _did_ e _didn't_.
- Os verbos vêm aos pares: a forma do passado, com `tense`, e o
  infinitivo, com `infl`. As duas formas têm a mesma lista de
  subcategorização, e a função `verb` gera o par.
- O infinitivo é a forma do verbo sem tempo nem pessoa, a que aparece
  no dicionário: _smile_, _love_. Em inglês, é a forma que vem depois de
  um auxiliar, como em _didn't smile_.
- Um verbo intransitivo tem a lista vazia. Um transitivo pede um `NP`
  com `accOrDat`.
- Um verbo ditransitivo, como _gave_, tem duas entradas: uma com `NP` e
  `PP` com `to`, outra com dois `NP`.
- Um complemento opcional também dá duas entradas: _kicked_ pede um `NP`
  e, opcionalmente, um `PP` com `with`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.5, from "Auxiliaries are:" to the entries of the
verb which takes an NP and an optional from-PP.
:::
::::

```lean
def auxiliaries : List Cat := [
  ⟨"did",    "AUX", [], []⟩,
  ⟨"didn't", "AUX", [], []⟩ ]

def verb (past inf : String) (subcat : List Cat) : List Cat :=
  [⟨past, "VP", [.tense], subcat⟩, ⟨inf, "VP", [.infl], subcat⟩]

def objNP : Cat := ⟨"_", "NP", [.accOrDat], []⟩
def objPP (f : Feat) : Cat := ⟨"_", "PP", [f], []⟩

def verbs : List Cat :=
  -- intransitive
  verb "smiled" "smile" [] ++
  verb "laughed" "laugh" [] ++
  verb "cheered" "cheer" [] ++
  verb "shuddered" "shudder" [] ++
  -- transitive
  verb "loved" "love" [objNP] ++
  verb "admired" "admire" [objNP] ++
  verb "helped" "help" [objNP] ++
  verb "defeated" "defeat" [objNP] ++
  -- ditransitive
  verb "gave" "give" [objNP, objPP .to] ++
  verb "gave" "give" [objNP, objNP] ++
  verb "sold" "sell" [objNP, objPP .to] ++
  verb "sold" "sell" [objNP, objNP] ++
  -- an NP and an optional with-PP
  verb "kicked" "kick" [objNP, objPP .with] ++
  verb "kicked" "kick" [objNP] ++
  -- an NP and an optional from-PP
  verb "took" "take" [objNP, objPP .from] ++
  verb "took" "take" [objNP]

#eval verb "loved" "love" [objNP]
```

:::terse
- As preposições trazem o traço da preposição, como `on` ou `with`.
  Esse traço passa para o `PP`, e é por ele que um verbo escolhe a
  preposição do complemento: _gave_ pede um `PP` com `to`, e um `PP`
  com `with` não concorda com ele.
- O ponto final entre duas frases é tratado como conjunção: _Alice
  smiled. Dorothy laughed._ se lê como _Alice smiled and Dorothy
  laughed_. O ponto no fim da entrada é descartado por `preproc`.
- O léxico junta todas as listas. Uma palavra fora delas recebe a lista
  vazia.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.5, from "Here are some prepositions:" to
"Finally, we say that there is nothing else in the lexicon:".
:::
::::

```lean
def prepositions : List Cat := [
  ⟨"on",   "PREP", [.on], []⟩,
  ⟨"with", "PREP", [.with], []⟩,
  ⟨"by",   "PREP", [.by], []⟩,
  ⟨"to",   "PREP", [.to], []⟩,
  ⟨"from", "PREP", [.from], []⟩ ]

def connectives : List Cat := [
  ⟨"and",  "CONJ", [], []⟩,
  ⟨".",    "CONJ", [], []⟩,
  ⟨"if",   "COND", [], []⟩,
  ⟨"then", "THEN", [], []⟩ ]

def lexicon (w : String) : List Cat :=
  (pronouns ++ properNames ++ determiners ++ commonNouns ++
    auxiliaries ++ verbs ++ prepositions ++ connectives).filter
    (·.phon == w)

#eval lexicon "that"
#eval lexicon "gave"
#eval lexicon "unicorn"
```

:::terse
- A análise léxica transforma o texto de entrada numa lista de palavras.
- A função `scan` põe um espaço antes de cada sinal de pontuação, para
  que ele vire uma palavra separada.
- A função `lexer` aplica `scan`, passa tudo para minúsculas, quebra o
  texto nos espaços e aplica `preproc`.
- A função `preproc` descarta as vírgulas e o ponto ou a interrogação no
  fim da entrada.
- Ela também ajusta a divisão das palavras: _did not_ vira _didn't_,
  _nobody_ vira _no person_, _less than_ vira `less_than`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.5, from "Now, the scan function scans an input
string…" to the end of the definition of `preproc`.
:::
::::

```lean
def scanChars : List Char → List Char
  | [] => []
  | x :: xs =>
    if x ∈ ['.', ',', '?'] then ' ' :: x :: scanChars xs
    else x :: scanChars xs

def scan (s : String) : String :=
  String.ofList (scanChars s.toList)

abbrev Words := List String

def preproc : Words → Words
  | [] => []
  | ["."] => []
  | ["?"] => []
  | "," :: xs => preproc xs
  | "did" :: "not" :: xs => "didn't" :: preproc xs
  | "nothing" :: xs => "no" :: "thing" :: preproc xs
  | "nobody" :: xs => "no" :: "person" :: preproc xs
  | "something" :: xs => "some" :: "thing" :: preproc xs
  | "somebody" :: xs => "some" :: "person" :: preproc xs
  | "everything" :: xs => "every" :: "thing" :: preproc xs
  | "everybody" :: xs => "every" :: "person" :: preproc xs
  | "less" :: "than" :: xs => "less_than" :: preproc xs
  | "more" :: "than" :: xs => "more_than" :: preproc xs
  | "at" :: "least" :: xs => "at_least" :: preproc xs
  | "at" :: "most" :: xs => "at_most" :: preproc xs
  | x :: xs => x :: preproc xs

def lexer (s : String) : Words :=
  preproc (((scan s).toLower.splitOn " ").filter (· ≠ ""))

#eval scan "Alice smiled, and Dorothy laughed."
#eval lexer "Alice smiled, and Dorothy laughed."
#eval lexer "Did not everybody smile?"
```

:::terse
- A função `lookupWord` consulta uma palavra num léxico.
- A função `collectCats` consulta todas as palavras da entrada. Se
  alguma não estiver no léxico, devolve um erro com a lista das palavras
  desconhecidas.
- Para isso usamos o tipo `Except ε α`. Ele é como `Option α`, mas a
  falha carrega uma informação: `.ok a` é um sucesso com o valor `a`, e
  `.error e` é uma falha com o erro `e`, aqui uma `String`.
- Senão, `initCats` escolhe uma categoria para cada palavra, de todos os
  modos possíveis: cada escolha é uma lista de categorias que o parser
  vai tentar analisar.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.5, from "The lexicon is a lexical database of
type `String -> [Cat]`." to the end of the section.
:::
::::

```lean
def lookupWord (db : String → List Cat) (w : String) : List Cat :=
  db w

def initCats : List (List Cat) → List (List Cat)
  | [] => [[]]
  | cs :: rests => cs.flatMap fun c => (initCats rests).map (c :: ·)

def collectCats (db : String → List Cat) (words : Words) :
    Except String (List (List Cat)) :=
  let listing := words.map fun x => (x, lookupWord db x)
  let unknown := (listing.filter (·.2.isEmpty)).map (·.1)
  if unknown ≠ [] then .error s!"unknown words: {unknown}"
  else .ok (initCats (listing.map (·.2)))

#eval collectCats lexicon (lexer "Alice admired that girl.")
#eval collectCats lexicon (lexer "Alice admired the unicorn.")
```

::::exercise (rating := 2) (name := "init-cats-length")
Prove que o número de escolhas devolvidas por {name}`initCats` é o
produto do número de categorias de cada palavra.

```lean
theorem length_initCats (css : List (List Cat)) :
    (initCats css).length = (css.map List.length).prod := by
  solution!
   induction css with
   | nil => rfl
   | cons cs rests ih =>
     simp [initCats, List.length_flatMap, ih, List.map_const']
```
::::

```lean
end Parsing
```
