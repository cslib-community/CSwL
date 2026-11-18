import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

set_option verso.code.warnLineLength 100

#doc (Manual) "Traços e Categorias" =>
%%%
tag := "features-categories"
file := "Features"
%%%

```lean
namespace Parsing
```

:::terse
- Traços sintáticos, como número, pessoa, gênero e caso, decidem a
  concordância: _she laughs_ é uma frase, mas _they laughs_ não é.
- Há duas visões da concordância:
  - *controle*: os traços de um constituinte são calculados a partir
    dos traços de outro, que os controla;
  - *restrição*: os constituintes especificam os traços em parte, e a
    concordância é um teste de compatibilidade, sem origem nem alvo.
- Vamos misturar as duas.
- Traços não aumentam o poder da gramática. Com um traço de número, a
  regra `S → NP VP` vira quatro regras sem traços, como
  `S → NP{Sg} VP{Sg}`. Os traços são finitos, então a gramática
  continua livre de contexto, só que com muito mais regras.
- Todos os valores de traços ficam num único tipo, `Feat`, e um
  conjunto de traços é uma lista, `Agreement`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.4, from the start to "…(at least they will not
be caught by the type checking)."
:::
::::

```lean
inductive Feat where
  | masc | fem | neutr | mascOrFem
  | sg | pl
  | fst | snd | thrd
  | nom | accOrDat
  | pers | refl | wh
  | tense | infl
  | on | with | by | to | from
  deriving Repr, DecidableEq
def Feat.toString : Feat → String
  | .masc => "Masc" | .fem => "Fem" | .neutr => "Neutr"
  | .mascOrFem => "MascOrFem"
  | .sg => "Sg" | .pl => "Pl"
  | .fst => "Fst" | .snd => "Snd" | .thrd => "Thrd"
  | .nom => "Nom" | .accOrDat => "AccOrDat"
  | .pers => "Pers" | .refl => "Refl" | .wh => "Wh"
  | .tense => "Tense" | .infl => "Infl"
  | .on => "On" | .with => "With" | .by => "By" | .to => "To"
  | .from => "From"

instance : ToString Feat := ⟨Feat.toString⟩

abbrev Agreement := List Feat
```

:::terse
- Os traços se dividem em tipos: gênero, número, pessoa, caso, tipo de
  pronome, tempo e preposição. Cada tipo tem a lista dos seus valores,
  e `allFeats` junta todas.
- O caso marca a função de um `NP` na frase. Em inglês, só os pronomes
  o mostram. O nominativo, `nom`, é o caso do sujeito: _she_, _he_, _I_.
  O acusativo é o caso do objeto direto, e o dativo, o do objeto
  indireto. O inglês não distingue os casos dativo e acusativo, e por
  isso há um único valor, `accOrDat`: _her_, _him_, _me_. É também o
  caso do `NP` que vem depois de uma preposição.
- As funções `gender`, `number`, `person` etc. selecionam, numa lista
  de traços, os de um tipo.
- Dois valores diferentes do mesmo tipo entram em conflito.
- A exceção é `mascOrFem`, a disjunção de `masc` e `fem`: conflita com
  `neutr`, mas não com `masc` nem com `fem`. Nesses casos, a função
  `prune` remove `mascOrFem`, e fica o valor mais específico.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.4, from "The following functions pick out the
gender, number, …" to the definition of `prune`.
:::
::::

```lean
def genderFeats   : Agreement := [.masc, .fem, .neutr, .mascOrFem]
def numberFeats   : Agreement := [.sg, .pl]
def personFeats   : Agreement := [.fst, .snd, .thrd]
def caseFeats     : Agreement := [.nom, .accOrDat]
def pronTypeFeats : Agreement := [.pers, .refl, .wh]
def tenseFeats    : Agreement := [.tense, .infl]
def prepTypeFeats : Agreement := [.on, .with, .by, .to, .from]

def allFeats : Agreement :=
  genderFeats ++ numberFeats ++ personFeats ++ caseFeats ++
    pronTypeFeats ++ tenseFeats ++ prepTypeFeats

def gender (fs : Agreement) : Agreement :=
  fs.filter (· ∈ genderFeats)
def number (fs : Agreement) : Agreement :=
  fs.filter (· ∈ numberFeats)
def person (fs : Agreement) : Agreement :=
  fs.filter (· ∈ personFeats)
def gcase (fs : Agreement) : Agreement :=
  fs.filter (· ∈ caseFeats)
def pronType (fs : Agreement) : Agreement :=
  fs.filter (· ∈ pronTypeFeats)
def tense (fs : Agreement) : Agreement :=
  fs.filter (· ∈ tenseFeats)
def prepType (fs : Agreement) : Agreement :=
  fs.filter (· ∈ prepTypeFeats)

def prune (fs : Agreement) : Agreement :=
  if .masc ∈ fs || .fem ∈ fs then fs.erase .mascOrFem else fs

#eval prune [.mascOrFem, .fem, .sg]
#eval prune [.mascOrFem, .neutr, .sg]
```

:::terse
- Uma categoria sintática tem quatro componentes: a forma fonológica, o
  rótulo, os traços de concordância e a *lista de subcategorização*, as
  categorias com que ela se combina.
- Só as categorias lexicais têm forma fonológica. As outras têm `"_"`
  nesse lugar.
- `Cat` é uma estrutura com um campo para cada componente. O campo
  `subcatList` é uma lista de `Cat`, então o tipo é recursivo.
- Para exibir uma categoria, usamos a notação das gramáticas de
  unificação, como HPSG {citep Bib.sag1999}[]: uma *matriz de atributos
  e valores*, ou AVM.
  Cada componente é um atributo: o rótulo é `CAT`, a forma é `ORTH` e a
  lista de subcategorização é `SUBCAT`. Cada tipo de traço também é um
  atributo: `GEN`, `NUM`, `PER`, `CASE`, `PRON`, `VFORM` e `PFORM`.
- Assim, _she_ é `[CAT NP, ORTH she, GEN fem, NUM sg, PER thrd, CASE nom,
  PRON pers]`. Um atributo sem valor não aparece, e uma categoria não
  lexical não tem `ORTH`.
- Os colchetes `[…]` delimitam um AVM, e os sinais `⟨…⟩` delimitam uma
  lista de AVMs. O valor de `SUBCAT` é uma lista: _loved_ é
  `[CAT VP, ORTH loved, VFORM tense, SUBCAT ⟨[CAT NP, CASE accOrDat]⟩]`,
  um verbo que espera um `NP` com `accOrDat`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.4, from "Now that we have features, we can
define a data type for syntactic categories." to the functions for
getting the components out of a category.
:::
::::

```lean
abbrev CatLabel := String
abbrev Phon := String

structure Cat where
  phon : Phon
  label : CatLabel
  fs : Agreement
  subcatList : List Cat
  deriving Repr, BEq
```

:::details "Exibindo categorias como AVMs"
```lean
open Std (Format)

def featPairs (fs : Agreement) : List String :=
  let attrs := [("GEN", gender fs), ("NUM", number fs),
    ("PER", person fs), ("CASE", gcase fs), ("PRON", pronType fs),
    ("VFORM", tense fs), ("PFORM", prepType fs)]
  (attrs.filter (!·.2.isEmpty)).map fun (a, vs) =>
    a ++ " " ++ "/".intercalate (vs.map fun v => (toString v).decapitalize)

def avmFmt (attrs : List Format) : Format :=
  Format.bracket "[" (Format.joinSep attrs ("," ++ Format.line)) "]"

def listFmt (xs : List Format) : Format :=
  Format.bracket "⟨" (Format.joinSep xs ("," ++ Format.line)) "⟩"

def featAVM (fs : Agreement) : String :=
  (avmFmt ((featPairs fs).map Format.text)).pretty

def Cat.attrs : Cat → List Format
  | ⟨phon, label, fs, subcatList⟩ =>
    let orth := if phon == "_" then [] else [f!"ORTH {phon}"]
    let sub := if subcatList.isEmpty then []
      else [f!"SUBCAT " ++ listFmt (subcatList.map fun c => avmFmt c.attrs)]
    [f!"CAT {label}"] ++ orth ++ (featPairs fs).map Format.text ++ sub

instance : Repr Cat := ⟨fun c _ => avmFmt c.attrs⟩
```
:::

```lean
namespace Examples

def she : Cat := ⟨"she", "NP", [.pers, .thrd, .sg, .fem, .nom], []⟩
def her : Cat := ⟨"her", "NP", [.pers, .thrd, .sg, .fem, .accOrDat], []⟩
def they : Cat := ⟨"they", "NP", [.pers, .thrd, .pl, .nom], []⟩
def alice : Cat := ⟨"Alice", "NP", [.thrd, .sg, .fem], []⟩
def laughs : Cat := ⟨"laughs", "VP", [.tense, .sg, .thrd], []⟩
def child : Cat := ⟨"child", "CN", [.sg, .thrd, .mascOrFem], []⟩
def thing : Cat := ⟨"thing", "CN", [.sg, .thrd, .neutr], []⟩
def the : Cat := ⟨"the", "DET", [], []⟩

end Examples

open Examples in

#eval she

#eval ({
   phon := "_", label := "NP", fs := [.sg],
   subcatList := [] } : Cat)
```

:::terse
- A função `combine` junta os traços de duas categorias e devolve
  `none` quando há conflito: é a visão de restrição.
- Em termos de AVMs, `combine` é uma *unificação*: junta a informação
  das duas matrizes e falha se elas se contradizem. `[PER thrd]` e
  `[NUM sg]` dão `[NUM sg, PER thrd]`; `[NUM sg]` e `[NUM pl]` não se
  unificam.
- O resultado não depende da ordem dos traços: filtramos `allFeats`,
  então cada traço aparece uma só vez, na ordem de `allFeats`.
- Duas categorias concordam, `agree`, quando `combine` não falha.
- A função `assign f c` impõe o traço `f` à categoria `c`: é a visão de
  controle. A regra que junta sujeito e predicado, por exemplo, dá ao
  sujeito o traço `nom`.
- A atribuição falha se `c` já tem um traço incompatível: `her`, que é
  `accOrDat`, não pode ser sujeito.
- Para montar a categoria nova, `assign` usa `map` sobre o resultado
  de `combine`. Numa `Option`, `o.map f` aplica `f` ao valor, se houver:
  `some a` vira `some (f a)`, e `none` continua `none`. É o mesmo `map`
  das listas, que aplica `f` a cada elemento.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.4, from "The following function combine
combines the feature lists of two categories." to the end of the
section.
:::
::::

```lean
def combine (cat1 cat2 : Cat) : Option Agreement :=
  let feats := prune (allFeats.filter (· ∈ cat1.fs ++ cat2.fs))
  if (gender feats).length ≤ 1 && (number feats).length ≤ 1 &&
      (person feats).length ≤ 1 && (gcase feats).length ≤ 1 &&
      (pronType feats).length ≤ 1 && (tense feats).length ≤ 1 &&
      (prepType feats).length ≤ 1
  then some feats
  else none

def agree (cat1 cat2 : Cat) : Bool :=
  (combine cat1 cat2).isSome

def assign (f : Feat) (c : Cat) : Option Cat :=
  (combine c ⟨"", "", [f], []⟩).map fun fs' => { c with fs := fs' }

open Examples

#eval (combine she laughs).map featAVM
#eval agree they laughs
#eval (combine the child).map featAVM
#eval agree child thing
#eval assign .nom alice
#eval assign .nom her
```

::::exercise (rating := 2) (name := "combine-comm")
Prove que o resultado de {name}`combine` não depende da ordem das duas
categorias.

```lean
theorem combine_comm (cat1 cat2 : Cat) :
    combine cat1 cat2 = combine cat2 cat1 := by
  solution!
   simp only [combine, List.mem_append, or_comm]
```
::::


```lean
end Parsing
```
