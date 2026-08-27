import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Aplicação: representando fonemas" =>
%%%
tag := "Phonemes"
%%%

Ref. CSwFP/3 §3.14 (p. 58–61).

Vimos uma implementação simples da harmonia vocálica do finlandês por
manipulação de strings. Do ponto de vista linguístico isso não satisfaz:
processos fonológicos como harmonia vocálica não são regras de
substituição de caracteres, e sim regras disparadas por _traços
fonológicos_. Uma implementação mais adequada representa cada fonema como
um feixe de traços — o que importa ainda mais quando o padrão de harmonia
é mais complexo, como veremos a seguir. Os tipos abaixo dão essa
representação.

```lean
namespace Phonema

inductive Attr where
  | Back
  | High
  | Round
  | Cons
deriving Repr, BEq

inductive Value where
  | Plus
  | Minus
deriving Repr, BEq

structure Feature where
  attr  : Attr
  value : Value
deriving Repr, BEq

abbrev Phoneme := List Feature
```

::::exercise (rating := 2) (name := "fValue")

Consulta o valor de um traço.

```lean
def fValue (attr : Attr) : Phoneme → Option Value :=
  solution!(fun
    | []      => none
    | f :: fs =>
      if f.attr == attr then
        some f.value
      else fValue attr fs)
```

::::

Troca o valor de um traço.

```lean
def fMatch (attr : Attr) (value : Value) (fs : Phoneme) :
    Phoneme :=
  fs.map fun f =>
    if f.attr == attr then { f with value := value } else f
```

Representar fonemas por traços ajuda quando o sistema de harmonia vocálica
é mais complexo, como o de Yawelmani, variedade extinta da língua Yokuts
da Califórnia. Yawelmani tem as vogais de superfície i u e o a (ignorando
a distinção entre vogais curtas e longas), representáveis como termos de
tipo `Phoneme`, isto é, como listas de traços.

Esta seção usa uma representação *deliberadamente simplificada* de
Yawelmani. Duas simplificações merecem ser ditas antes do código, porque
sem elas os exemplos abaixo confundem mais do que ensinam:

- só as vogais têm identidade — toda consoante vira o mesmo `c` (a razão
  aparece adiante, junto da definição de `c`);
- os exemplos foram escolhidos com *uma única vogal relevante* por
  radical e por sufixo, para que a regra de harmonia seja fácil de
  acompanhar. Isso é uma escolha dos exemplos, não uma propriedade de
  Yawelmani — a função que vamos escrever localiza "a primeira vogal do
  radical" porque é isso que o exercício pede, não porque um radical não
  possa ter mais de uma.

```lean
open Attr Value

def a : Phoneme :=
  [⟨Cons, Minus⟩, ⟨High, Minus⟩,
   ⟨Round, Minus⟩, ⟨Back, Plus⟩]
def e : Phoneme :=
  [⟨Cons, Minus⟩, ⟨High, Minus⟩,
   ⟨Round, Minus⟩, ⟨Back, Minus⟩]
def i : Phoneme :=
  [⟨Cons, Minus⟩, ⟨High, Plus⟩,
   ⟨Round, Minus⟩, ⟨Back, Minus⟩]
def o : Phoneme :=
  [⟨Cons, Minus⟩, ⟨High, Minus⟩,
   ⟨Round, Plus⟩, ⟨Back, Plus⟩]
def u : Phoneme :=
  [⟨Cons, Minus⟩, ⟨High, Plus⟩,
   ⟨Round, Plus⟩, ⟨Back, Plus⟩]

def yawelmaniVowels := [i,a,o,u,e]
end Phonema
```

```lean
namespace Phonema

example : fValue .High i = some .Plus := by rfl
example : fValue .High a = some .Minus := by rfl
example : fValue .Back ([] : Phoneme) = none := by rfl
```

```lean
#eval Phonema.fMatch .Back .Plus Phonema.i
```

A seção só se ocupa da harmonia entre vogais — o que a regra de Yawelmani
apaga ou preserva é `Back`, `Round` e `High`, traços que aqui só as vogais
carregam. Por isso toda consoante é representada por um único feixe
genérico `c`, sem o traço que a distinguiria de outra consoante. Isso tem
um preço: `x`, `l`, `d`, `b`, `h`, `n`, `k'` — todas colapsam no mesmo `c`,
e `realize` (abaixo) não tem como devolver a consoante certa, só `'c'`.
Nos exemplos de \[CK97\] mais adiante, `xil` e `dub` são então lidos como
`c i c` e `c u c`: a identidade da consoante é irrelevante para a regra,
só a primeira vogal importa. O apóstrofo de `bok'` (ejetiva/glotalizada,
na notação linguística) também se perde nessa simplificação — `k'` também
colapsa em `c`.

```lean
def c : Phoneme := [Feature.mk Attr.Cons Value.Plus]
```

A realização de superfície: qual letra corresponde a este feixe.

Mais uma simplificação, e independente das anteriores: `realize` devolve
`Char`, um único caractere por fonema — como se fonema e letra fossem
sempre a mesma coisa. Não são, em nenhuma língua: `ch` e `sh` são dois
caracteres para um só fonema, e o próprio `k'` de Yawelmani (uma
consoante ejetiva) usa dois caracteres na notação. A correspondência 1-1
vale aqui só porque o inventário do exercício foi escolhido para caber
num `Char` — não é uma propriedade de fonemas em geral, e uma modelagem
que precisasse disso usaria antes `Phoneme → String`.

Um feixe arbitrário pode não corresponder a nenhuma vogal do inventário,
e `none` é a resposta correta nesse caso. O último exemplo mostra por que
isso importa — forçar `Back` a `Plus` em `i` produz um feixe que nenhuma
das três vogais realiza.

A busca abaixo compara feixes inteiros por `==`, e `Phoneme` é uma lista:
dois feixes só são iguais se os traços estiverem na *mesma ordem*.
Funciona porque toda vogal do inventário foi escrita na ordem `Cons,
High, Round, Back`, e `fMatch` preserva essa ordem ao trocar um valor —
mas é uma disciplina, não uma garantia do tipo. Uma vogal nova, se
escrita numa ordem diferente, deixaria de bater com `==` e `realize`
devolveria `none` silenciosamente.

```lean
def surfaceTable : List (Phoneme × Char) :=
  [(i, 'i'), (a, 'a'), (o, 'o'), (u, 'u'), (e, 'e'),
   (c, 'c')]

def realize (x : Phoneme) : Option Char :=
  (surfaceTable.find? (·.1 == x)).map (·.2)
```

```lean
example : realize i = some 'i' := rfl
example : realize (fMatch .Back .Plus i) = none := rfl
```

::::exercise (rating := 3) (name := "3.19")

A harmonia vocálica em Yawelmani tem a seguinte forma simplificada. As
vogais do sufixo concordam em `Back` e `Round` com a vogal do radical —
mas gatilho (vogal do radical) e alvo (vogal do suffixo) têm de ter a
mesma altura (`High`): vogais altas do radical só condicionam harmonia em
vogais altas do sufixo, e vogais baixas do radical só condicionam
harmonia em vogais baixas do sufixo. Exemplos de \[CK97\] (lembrando: `xil`
≈ `c i c`, `dub` ≈ `c u c`, `xat` ≈ `c a c`, `bok'` ≈ `c o c` — a
consoante é sempre `c`):

```
xil  ++ hin → xilhin   'tangles'
xat  ++ hin → xathin   'eats'
dub  ++ hin → dubhun   'leads by hand'
bok' ++ hin → bok'hin  'finds'
xat  ++ al  → xatal    'might eat'
xil  ++ al  → xilal    'might tangle'
bok' ++ al  → bok'ol   'might find'
dub  ++ al  → dubal    'might lead'
```

A regra não é uma tabela de substituição de letras (não é "`i` vira
`u`"): é propagação de traços entre dois feixes. Acompanhe `dub ++ hin →
dubhun` contra `xat ++ hin → xathin`, os dois pelo mesmo sufixo `hin`
(vogal `i`):

```
u = [High+, Round+, Back+]   (vogal do radical dub)
a = [High-, Round-, Back+]   (vogal do radical xat)
i = [High+, Round-, Back-]   (vogal do sufixo hin)
```

Em `dub ++ hin`: `u` e `i` concordam em `High` (`+`/`+`) — a harmonia se
aplica, e `i` copia `Round` e `Back` de `u`, tornando-se foneticamente
`u`: daí `dubhun`. Em `xat ++ hin`: `a` é `High-` e `i` é `High+` — os
valores discordam, a harmonia não se aplica, e `i` fica como está: daí
`xathin`. A diferença entre os dois casos não é uma regra especial para
`u` ou para `a`; é consequência única da condição sobre `High`.

`appendSuffixY` aplica essa harmonia: concatena `stem` e `suffix`, mas
antes ajusta cada vogal do sufixo pela primeira vogal do radical — se as
duas tiverem a mesma altura, a vogal do sufixo herda `Back` e `Round` da
vogal do radical; senão fica como está.

```lean
def stemVowel (stem : List Phoneme) : Option Phoneme :=
  solution!(stem.find? (yawelmaniVowels.contains ·))

def harmonize (stemV suffixPh : Phoneme) : Phoneme :=
  match fValue .High stemV, fValue .High suffixPh with
  | some hStem, some hSuffix =>
    if hStem == hSuffix then
      match fValue .Back stemV, fValue .Round stemV with
      | some b, some r =>
        fMatch .Round r (fMatch .Back b suffixPh)
      | _, _ => suffixPh
    else suffixPh
  | _, _ => suffixPh

def appendSuffixY (stem suffix : List Phoneme) :
    List Phoneme :=
  solution!(match stemVowel stem with
    | none => stem ++ suffix
    | some v => stem ++ suffix.map (harmonize v))

theorem appendSuffixY_test1 :
    (appendSuffixY [c, u, c] [c, i, c]).map realize
    = [some 'c', some 'u', some 'c', some 'c', some 'u',
       some 'c'] :=
  solution!(by rfl)

theorem appendSuffixY_test2 :
    (appendSuffixY [c, a, c] [c, i, c]).map realize
    = [some 'c', some 'a', some 'c', some 'c', some 'i',
       some 'c'] :=
  solution!(by rfl)
```

:::gradeTheorem "1" appendSuffixY_test1 appendSuffixY_test2
:::
::::

`appendSuffixY` trabalha sobre `List Phoneme`. Este exercício pede a
mesma harmonia partindo de `String`, como já fizemos para o finlandês na
seção de harmonia vocálica do finlandês. O texto de entrada precisa
primeiro ser cortado em "letras" — e `k'` mostra que uma letra pode ter
mais de um caractere. `tokenize` reconhece esse único caso especial; as
duas equações consomem `rest`, estruturalmente menor, então não precisa
de `partial`.

```lean
def tokenize : List Char → List String
  | []                => []
  | c :: '\'' :: rest =>
    String.ofList [c, '\''] :: tokenize rest
  | c :: rest =>
    String.ofList [c] :: tokenize rest
```

Só as vogais atravessam o modelo de traços; qualquer outro token é
copiado sem conversão. Convertê-los também seria um erro: como toda
consoante colapsa no mesmo `c` genérico, reconvertê-la devolveria sempre
`'c'`, apagando a consoante original em vez de preservá-la — `"dub"`
viraria `"cuc"`. Por isso `unrealizeVowel` só reconhece os 5 tokens de
vogal, e tokenizar `k'` como uma unidade não muda o resultado de
`appendSuffix` (consoantes nunca são harmonizadas): só deixa explícito,
também do lado da entrada, que fonema não é o mesmo que caractere.

```lean
def unrealizeVowel (tok : String) : Option Phoneme :=
  if      tok == "i" then some i
  else if tok == "a" then some a
  else if tok == "o" then some o
  else if tok == "u" then some u
  else if tok == "e" then some e
  else none
```

::::exercise (rating := 3) (name := "appendSuffix-texto")

`appendSuffixY` trabalha sobre `List Phoneme`. Este exercício pede a
mesma harmonia partindo de `String`.

```lean
def appendSuffix (stem suffix : String) : Option String :=
  solution!(
    let stemTokens := tokenize stem.toList
    match (stemTokens.filterMap unrealizeVowel).head? with
    | none => some (stem ++ suffix)
    | some triggerV =>
      let harmonizedSuffix : Option (List String) :=
        (tokenize suffix.toList).mapM fun tok =>
          match unrealizeVowel tok with
          | none    => some tok
          | some vP =>
            (realize (harmonize triggerV vP)).map
              (fun ch => String.ofList [ch])
      harmonizedSuffix.map fun toks =>
        stem ++ String.join toks)

theorem appendSuffix_test1 :
    appendSuffix "dub" "hin" = some "dubhun" :=
  solution!(by rfl)
theorem appendSuffix_test2 :
    appendSuffix "xat" "hin" = some "xathin" :=
  solution!(by rfl)
theorem appendSuffix_test3 :
    appendSuffix "bok'" "al" = some "bok'ol" :=
  solution!(by rfl)
```

i (High+) vs a (High-): sem harmonia

```lean
theorem appendSuffix_test4 :
    appendSuffix "xil" "al" = some "xilal" :=
  solution!(by rfl)
```

gatilho e alvo já são o mesmo `a`

```lean
theorem appendSuffix_test5 :
    appendSuffix "xat" "al" = some "xatal" :=
  solution!(by rfl)

```

:::gradeTheorem "1" appendSuffix_test1 appendSuffix_test2 appendSuffix_test3 appendSuffix_test4 appendSuffix_test5
:::
::::
