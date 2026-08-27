import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Harmonia vocálica do finlandês" =>
%%%
tag := "FinnishVowelHarmony"
%%%

```lean
namespace FinnishVowelHarmony
```

A morfologia é a parte da gramática que estuda a estrutura, formação,
flexão e a classificação das palavras de forma isolada.

Não vamos estudar morfologia no curso, mas para os interessados, recomendo
{citep Bib.beesley2003}[]. Palavras de linguagem natural são tipicamente
formadas pela concatenação de morfemas. Quando morfemas se combinam em
novas palavras, é comum haver alternâncias na pronúncia ou na escrita. A
morfologia de estados finitos assume que tanto as regras de formação de
palavras (morfotática) quanto as regras de alternância morfo-fonológica
podem ser modeladas como [máquinas de estados
finita](https://en.wikipedia.org/wiki/Finite-state_machine).

Vamos implementar um fragmento da harmonia vocálica finlandesa e o plural
sueco de forma.

Harmonia vocálica é um processo fonológico pelo qual as vogais passam a
compartilhar certos traços. No caso do finlandês, há as vogais posteriores
a, o, u, as vogais anteriores ä, ö, y, e as vogais neutras i, e. Uma
palavra finlandesa só pode conter vogais posteriores (e neutras) ou só
vogais anteriores (e neutras).

```
pouta  'fine weather'
koti`  'home'
pöytä` 'table'
```

Vogais posteriores e anteriores também induzem harmonia vocálica: se o
radical contém apenas vogais posteriores, o sufixo também contém apenas
vogais posteriores; se o radical é de vogais anteriores, as vogais do
sufixo se assimilam a anteriores.

```
pouta ++ na → poutana
koti ++ na → kotina
pöytä ++ na → pöytänä
```

Isso pode ser capturado de forma simples por uma função que muda as
vogais do sufixo conforme as vogais do radical sejam anteriores ou
posteriores (Forsberg \[For07, p. 13\]).

```lean
def front : Char → Char
  | 'a' => 'ä'
  | 'o' => 'ö'
  | 'u' => 'y'
  | c   => c

def back : Char → Char
  | 'ä' => 'a'
  | 'ö' => 'o'
  | 'y' => 'u'
  | c   => c
```

```lean (name := c2eval40)
#eval "tea".contains (fun c => "aou".toList.contains c)
```

Sufixa `suffix` ao radical `stem`, ajustando cada vogal do sufixo pela
harmonia vocálica do radical. Veja que com o `let` podemos declarar uma
função local à função `appendSuffixF`.

```lean
def appendSuffixF (stem suffix : String) : String :=
  let vh : Char → Char :=
    if stem.contains ("aou".toList.contains ·) then
      back
    else if stem.contains ("äöy".toList.contains ·) then
      front
    else id
  stem ++ String.ofList (suffix.toList.map vh)
```

```lean
#eval appendSuffixF "talo" "ssa"
#eval appendSuffixF "kylä" "ssa"
```

```lean
end FinnishVowelHarmony
```
