import CSwLMeta
import Bib
import CSwL.IntroL

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Plural do Sueco" =>
%%%
tag := "SwedishPlural"
%%%

```lean
namespace SwedishPlural
```

O sueco distribui os substantivos em cinco classes de declinação \[Hel78\],
e a forma do plural depende da classe. As cinco classes de declinação do
plural em sueco podem ser declaradas como um tipo indutivo.

```lean
inductive DeclClass where
  | One
  | Two
  | Three
  | Four
  | Five
deriving Repr

def aRing  : Char := Char.ofNat 229
def oSlash : Char := Char.ofNat 248

def swedishVowels : List Char :=
  ['a','i','o','u','e','y', 'ä', aRing, 'ö', oSlash]
```

::::exercise (rating := 2) (name := "swedishPlural")

A forma do plural é determinada pela classe de declinação. Na terceira
classe ela depende também de a palavra terminar ou não em vogal.

```lean
def swedishPlural (noun : String) : DeclClass → String :=
  solution!(fun
    | .One   => IntroL.initS noun ++ "or"
    | .Two   => IntroL.initS noun ++ "ar"
    | .Three =>
      if swedishVowels.contains noun.back
      then noun ++ "r"
      else noun ++ "er"
    | .Four  => noun ++ "n"
    | .Five  => noun)

theorem swedishPlural_test1 :
    swedishPlural "blomma" .One = "blommor" :=
  solution!(by rfl)
theorem swedishPlural_test2 :
    swedishPlural "flicka" .One = "flickor" :=
  solution!(by rfl)
theorem swedishPlural_test3 :
    swedishPlural "pojke" .Two = "pojkar" :=
  solution!(by rfl)
-- `rfl`/`decide` empacam em `swedishVowels.contains
-- noun.back` (a redução da `String` interna trava antes
-- de decidir o `Bool`); `native_decide` roda o código
-- compilado e fecha.
theorem swedishPlural_test4 :
    swedishPlural "rad" .Three = "rader" :=
  solution!(by native_decide)
theorem swedishPlural_test5 :
    swedishPlural "ko" .Three = "kor" :=
  solution!(by native_decide)
theorem swedishPlural_test6 :
    swedishPlural "äpple" .Four = "äpplen" :=
  solution!(by rfl)
theorem swedishPlural_test7 :
    swedishPlural "hus" .Five = "hus" :=
  solution!(by rfl)
```

:::gradeTheorem "1" swedishPlural_test1 swedishPlural_test2 swedishPlural_test3 swedishPlural_test4 swedishPlural_test5 swedishPlural_test6 swedishPlural_test7
:::
::::

```lean
end SwedishPlural
```
