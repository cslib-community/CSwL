import CSwLMeta
import Bib
import CSwL.Parsing.ParseTrees
import Mathlib.Data.List.Palindrome

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Reconhecendo e analisando linguagens livres de contexto" =>
%%%
tag := "cf-recognition"
%%%

```lean
namespace Parsing
```

:::terse
- *Reconhecer*: dizer se a gramática gera ou não uma sequência.
  *Analisar* (*parsing*): dizer também como ela é gerada, isto é, dar as
  suas árvores sintáticas.
- O exemplo é a gramática dos palíndromos sobre `{a, b, c}`, as palavras
  iguais à sua inversa:
  A → ε | a | b | c | aAa | bAb | cAc.
- A ideia para qualquer gramática livre de contexto: uma regra com `n`
  símbolos à direita divide a entrada em `n` pedaços, de todos os modos
  possíveis, e testa cada pedaço contra o seu símbolo.
- `split2` dá todas as divisões de uma lista em duas; `splitN n`, em `n`.
- Em Lean, uma `String` não é uma lista. `"Jan".toList` dá a lista de
  caracteres, e `String.ofList` faz o caminho de volta.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.2, from the start to the definition of `splitN`.
:::
::::

```lean
def split2 {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs =>
    ([], x :: xs) ::
      (split2 xs).map fun (ys, zs) => (x :: ys, zs)

#eval split2 "Jan".toList

def splitN {α : Type} : Nat → List α → List (List (List α))
  | 0, _ | 1, _ => []
  | 2, xs => (split2 xs).map fun (ys, zs) => [ys, zs]
  | n + 3, xs =>
    (split2 xs).flatMap fun (ys, zs) =>
      (splitN (n + 2) zs).map fun rs => ys :: rs

#eval splitN 3 "Jan".toList
```

:::terse
- O reconhecedor segue a gramática: uma linha por regra. Para A → aAa,
  ele procura uma divisão em três pedaços `[a]`, `ys`, `[a]` e reconhece
  `ys`.
- `recognize` chama a si mesma em `ys`. Lean exige que toda função
  termine, e aqui ele não consegue ver sozinho que `ys` é menor do que
  `xs`.
- `partial def` aceita a definição sem essa verificação. O preço: Lean
  roda a função, mas não sabe nada sobre o que ela calcula, e nenhuma
  prova pode olhar dentro dela.
- Ela termina: `ys` tem dois elementos a menos. Uma regra recursiva à
  esquerda, V → V T, também não seria problema, porque V recebe um pedaço
  menor da entrada, desde que o pedaço de T não seja vazio.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.2, from "Now the function for recognizing…" to
"…for splitting the input into n substrings."
:::
::::

```lean
partial def recognize (xs : List Char) : Bool :=
  xs == [] || xs == ['a'] || xs == ['b'] || xs == ['c'] ||
  (splitN 3 xs).any fun
    | [['a'], ys, ['a']] => recognize ys
    | [['b'], ys, ['b']] => recognize ys
    | [['c'], ys, ['c']] => recognize ys
    | _ => false

#eval recognize "aabcbbcbaa".toList
#eval recognize "aabcbbcba".toList
```

:::terse
- Do reconhecimento à geração: gerar todas as palavras sobre o alfabeto e
  ficar com as reconhecidas.
- `gener n` dá as palavras de comprimento `n`; `generUpTo n`, as de
  comprimento até `n`. As palavras são infinitas, mas uma lista em Lean é
  finita, por isso a geração para num comprimento dado.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.2, from "From recognition to generation…" to the
first fifteen palindromes.
:::
::::

```lean
def gener {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | n + 1, alphabet =>
    alphabet.flatMap fun x =>
      (gener n alphabet).map (x :: ·)

def generUpTo {α : Type} (n : Nat) (alphabet : List α) :
    List (List α) :=
  (List.range (n + 1)).flatMap fun k => gener k alphabet

#eval ((generUpTo 3 "abc".toList).filter recognize).map
  String.ofList
```

:::terse
- O Mathlib define palíndromo como um predicado indutivo,
  `List.Palindrome`. Os seus três construtores são as regras da
  gramática: a lista vazia, uma lista de um elemento, e `x :: (l ++ [x])`
  para `l` palíndromo.
- O teorema confere que `recognize` concorda com essa definição em todas
  as palavras sobre `{a, b, c}` de comprimento até 6.
- `decide` não serve, porque o Lean não olha dentro de um `partial def`.
  `native_decide` roda o código compilado e aceita o resultado.
:::

:::details "O reconhecedor e a definição de palíndromo"
```lean
theorem recognize_upTo6 :
    ∀ w ∈ generUpTo 6 "abc".toList,
      recognize w = true ↔ w.Palindrome := by
  native_decide
```
:::

:::terse
- Analisar é construir as árvores. A entrada é uma `List Char`, e as
  árvores são do tipo `ParseTree Char Char`: caracteres nas folhas e o
  rótulo `A` nos nós.
- Mesma receita do reconhecedor, uma linha por regra; agora cada linha
  devolve a lista das suas árvores, vazia quando a regra não se aplica.
- A palavra vazia vira a árvore vazia `ep`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.2, from "Parsing with a context-free grammar…"
to the end of the section.
:::
::::

```lean
partial def parse (xs : List Char) :
    List (ParseTree Char Char) :=
  (if xs == [] then [.ep] else []) ++
  (if xs == ['a'] then [.leaf 'a'] else []) ++
  (if xs == ['b'] then [.leaf 'b'] else []) ++
  (if xs == ['c'] then [.leaf 'c'] else []) ++
  (splitN 3 xs).flatMap fun
    | [['a'], ys, ['a']] =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'a', t, .leaf 'a']
    | [['b'], ys, ['b']] =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'b', t, .leaf 'b']
    | [['c'], ys, ['c']] =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'c', t, .leaf 'c']
    | _ => []

#eval IO.println (parse "aabaa".toList)
#eval IO.println (parse "aabbaa".toList)
#eval IO.println (parse "aabcbbcba".toList)
```

::::exercise (rating := 2) (name := "split-nonempty")
Numa gramática sem regras ε, nenhum pedaço da divisão pode ser vazio.
Defina `split2'` e `splitN'`, que dão só as divisões sem pedaços vazios.
Confira o resultado em `"Jan"`.

```lean
def split2' {α : Type} : List α → List (List α × List α)
  | [] | [_] => []
  | x :: y :: ys =>
    solution!(
      ([x], y :: ys) ::
        (split2' (y :: ys)).map fun (us, vs) =>
          (x :: us, vs))

def splitN' {α : Type} : Nat → List α → List (List (List α))
  | 0, _ | 1, _ => []
  | 2, xs =>
    solution!((split2' xs).map fun (ys, zs) => [ys, zs])
  | n + 3, xs =>
    solution!(
      (split2' xs).flatMap fun (ys, zs) =>
        (splitN' (n + 2) zs).map fun rs => ys :: rs)

theorem split2'_jan :
    split2' "Jan".toList =
      [(['J'], ['a', 'n']), (['J', 'a'], ['n'])] := by
  solution!
   decide

theorem splitN'_jan :
    splitN' 3 "Jan".toList = [[['J'], ['a'], ['n']]] := by
  solution!
   decide
```
::::

```lean
end Parsing
```
