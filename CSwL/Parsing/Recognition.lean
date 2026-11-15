import CSwLMeta
import Bib
import CSwL.Parsing.ParseTrees
import Mathlib.Data.List.Palindrome
import CSwLCompat

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Reconhecendo e analisando linguagens livres de contexto" =>
%%%
tag := "cf-recognition"
file := "Recognition"
%%%

```lean
namespace Parsing
```

:::terse
- *Reconhecer*: dizer se a gramática gera ou não uma sequência.
- *Analisar*: ou *parsing*, dizer como ela é gerada, isto é, dar as
  suas árvores sintáticas.
- O exemplo é a gramática dos palíndromos sobre `{a, b, c}`.
- gramáticas livre de contexto: regras com
  apenas um não terminal à esquerda e `n` símbolos à direita, divide a
  entrada em `n` pedaços, de todos os modos possíveis, e testa cada
  pedaço contra o seu símbolo.
:::

::::full
A linguagem de uma gramática pode ser palavras (sobre um alfabeto de caracteres) ou frases (sobre um alfabeto de palavras ou tokens).

*Reconhecer* é dizer se a gramática gera ou não uma sequência. *Analisar* (ou *parsing*) é dizer como ela é gerada, isto é, dar as suas árvores sintáticas, que indicam as regras da gramática que devem ser aplicadas para justificar que a palavra pertence à linguagem gerada pela gramática.

O exemplo é a gramática dos palíndromos sobre `{a, b, c}`, as palavras iguais à sua inversa:

```bnf
A ::= ε | a | b | c | aAa | bAb | cAc ;
```

A ideia para qualquer gramática livre de contexto: uma regra com `n` símbolos à direita divide a entrada em `n` pedaços, de todos os modos possíveis, e testa cada pedaço contra o seu símbolo.

A função `split2` dá todas as divisões de uma lista em duas; `splitN n`, em `n`. Em Lean, {lean}`"Jan".toList` transforma uma string em uma lista de caracteres, e `String.ofList` faz o caminho inverso.

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

#eval split2 "Jan".toList |>.map
  λ (a, b) ↦ (String.ofList a, String.ofList b)

def splitN {α : Type} : Nat → List α → List (List (List α))
  | 0, [] => [[]]
  | 0, a :: as => []
  | 1, xs => [[xs]]
  | n + 2, xs =>
    (split2 xs).flatMap fun (ys, zs) =>
      (splitN (n + 1) zs).map fun rs => ys :: rs

#eval splitN 3 "Jan".toList |>.map
   λ xs => xs.map String.ofList
```

:::terse
- O reconhecedor segue a gramática: uma linha por regra. Para A → aAa,
  ele procura uma divisão em três pedaços `[a]`, `ys`, `[a]` e reconhece
  `ys`.
- A função `recognize` chama a si mesma em `ys`. Lean exige que toda função
  termine, e sozinho ele não vê que `ys` é menor do que `xs`: o padrão
  `[['a'], ys, ['a']]` não diz de onde a lista veio.
- A função `attach` junta a cada divisão a prova de que ela está em
  `splitN 3 xs`. A cláusula `termination_by xs.length` diz o que
  diminui, e `decreasing_by` prova que diminui, com o lema do bloco
  acima: os pedaços juntos dão `xs`, então `ys` tem dois elementos a
  menos.
- Uma regra recursiva à esquerda, V → V T, também não seria problema,
  porque V recebe um pedaço menor da entrada, desde que o pedaço de T
  não seja vazio.
- Se o pedaço de T puder ser vazio, V recebe a entrada inteira e chama
  a si mesma sem fim. As divisões com pedaço vazio têm de ser
  descartadas antes da chamada; sem isso, `decreasing_by` não prova
  nada e o Lean recusa a definição.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.2, from "Now the function for recognizing…" to
"…for splitting the input into n substrings."
:::
::::

:::details "As divisões juntam-se de volta na entrada"
```lean
theorem append_of_mem_split2 {α : Type} :
    ∀ {xs : List α} {p : List α × List α},
      p ∈ split2 xs → p.1 ++ p.2 = xs
  | [], p, h => by
    simp [split2] at h
    simp [h]
  | x :: xs, p, h => by
    simp only [split2, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨⟨ys, zs⟩, h, rfl⟩
    · rfl
    · simp [← append_of_mem_split2 h]

theorem flatten_of_mem_splitN {α : Type} :
    ∀ {n : Nat} {xs : List α} {l : List (List α)},
      l ∈ splitN n xs → l.flatten = xs
  | 0, [], l, h | 1, _, l, h => by
    simp [splitN] at h
    simp [h]
  | 0, _ :: _, _, h => by simp [splitN] at h
  | n + 2, xs, l, h => by
    simp only [splitN, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨ys, zs⟩, h1, rs, h2, rfl⟩ := h
    simp [flatten_of_mem_splitN h2, append_of_mem_split2 h1]
```
:::

```lean +error
def recognize₀ (xs : List Char) : Bool :=
  xs == [] || xs == ['a'] || xs == ['b'] || xs == ['c'] ||
  (splitN 3 xs).any fun
    | [['a'], ys, ['a']] => recognize₀ ys
    | [['b'], ys, ['b']] => recognize₀ ys
    | [['c'], ys, ['c']] => recognize₀ ys
    | _ => false
```

```lean
def recognize (xs : List Char) : Bool :=
  xs == [] || xs == ['a'] || xs == ['b'] || xs == ['c'] ||
  (splitN 3 xs).attach.any fun
    | ⟨[['a'], ys, ['a']], h⟩ => recognize ys
    | ⟨[['b'], ys, ['b']], h⟩ => recognize ys
    | ⟨[['c'], ys, ['c']], h⟩ => recognize ys
    | _ => false
termination_by xs.length
decreasing_by
  all_goals
    have := congrArg List.length (flatten_of_mem_splitN h)
    simp at this
    omega

#eval recognize "aabcbbcbaa".toList
#eval recognize "aabcbbcba".toList
```

:::terse
- A função `gener n` dá as palavras de comprimento `n`; `generUpTo n`,
  as de comprimento até `n`. As palavras são infinitas, mas uma lista
  em Lean é finita, por isso a geração para num comprimento dado.
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

def language (n : Nat) (alphabet : List Char)
  : List (List Char) :=
  (generUpTo n alphabet).filter recognize

#eval language 3 "abc".toList |>.map
  String.ofList
```

:::terse
- O Mathlib define palíndromo como um predicado indutivo, `List.Palindrome`. Os seus três construtores são as regras da gramática: a lista vazia, uma lista de um elemento, e `x :: (l ++ [x])` para `l` palíndromo.
- O teorema `recognize_iff_palindrome` diz que `recognize` concorda com essa definição em toda palavra sobre `{a, b, c}`, de qualquer comprimento.
- Para listas, `w ⊆ l` diz que todo elemento de `w` está em `l`. Assim  `w ⊆ "abc".toList` diz que `w` só usa as letras `a`, `b` e `c` (alfabeto).
- O teorema precisa dessa hipótese porque `List.Palindrome` vale sobre qualquer alfabeto, enquanto `recognize` só conhece os símbolos `a`, `b` e `c`. Em outras palavras, embora `xx` é um palíndromo, mas `recognize` o recusa.
- A prova é por indução no comprimento da palavra, uma direção de cada vez. Ela só é possível porque `recognize` não é `partial`: o Lean conhece a equação que a define.
:::

:::details "O reconhecedor e a definição de palíndromo"
```lean
theorem mem_split2_append {α : Type} :
    ∀ ys zs : List α, (ys, zs) ∈ split2 (ys ++ zs)
  | [], [] => by simp [split2]
  | [], z :: zs => by simp [split2]
  | y :: ys, zs => by
    simp only [List.cons_append, split2, List.mem_cons,
      List.mem_map]
    exact Or.inr ⟨(ys, zs), mem_split2_append ys zs, rfl⟩

theorem mem_splitN_flatten {α : Type} :
    ∀ l : List (List α), l ∈ splitN l.length l.flatten
  | [] => by simp [splitN]
  | [ys] => by simp [splitN]
  | ys :: zs :: rs => by
    simp only [List.length_cons, List.flatten_cons]
    simp only [splitN, List.mem_flatMap, List.mem_map]
    refine ⟨(ys, (zs :: rs).flatten),
      by simpa using mem_split2_append ys _,
      zs :: rs, ?_, rfl⟩
    simpa using mem_splitN_flatten (zs :: rs)

theorem recognize_sound (n : Nat) :
    ∀ w : List Char, w.length ≤ n →
      recognize w → w.Palindrome := by
  induction n with
  | zero =>
    intro w hw hr
    simp at hw
    rw [hw]
    exact .nil
  | succ n ih =>
    intro w hw h
    rw [recognize] at h
    simp only [Bool.or_eq_true, beq_iff_eq,
      List.any_eq_true] at h
    rcases h with (((rfl | rfl) | rfl) | rfl)
      | ⟨⟨l, hl⟩, _, hm⟩
    · exact .nil
    · exact .singleton _
    · exact .singleton _
    · exact .singleton _
    · split at hm <;> (try contradiction) <;>
      · rename_i ys hys _
        have he := flatten_of_mem_splitN hys
        simp at he
        subst he
        apply List.Palindrome.cons_concat
        exact ih ys (by simp at hw; omega) hm

theorem recognize_complete (n : Nat) :
    ∀ w : List Char, w.length ≤ n → w ⊆ "abc".toList →
      w.Palindrome → recognize w = true := by
  induction n with
  | zero =>
    intro w hw _ _
    simp at hw
    subst hw
    rw [recognize]
    simp
  | succ n ih =>
    intro w hw ha hp
    cases hp with
    | nil =>
      rw [recognize]
      simp
    | singleton x =>
      have hx : x ∈ "abc".toList := ha (by simp)
      simp at hx
      rcases hx with rfl | rfl | rfl <;>
        (rw [recognize]; simp)
    | cons_concat x hl =>
      rename_i l
      have hx : x ∈ "abc".toList := ha (by simp)
      have hl' : l ⊆ "abc".toList :=
        fun c hc => ha (by simp [hc])
      have ih' := ih l (by simp at hw; omega) hl' hl
      rw [recognize]
      simp only [Bool.or_eq_true, beq_iff_eq,
        List.any_eq_true]
      right
      have hmem :
          [[x], l, [x]] ∈ splitN 3 (x :: (l ++ [x])) := by
        simpa using mem_splitN_flatten [[x], l, [x]]
      refine ⟨⟨_, hmem⟩, List.mem_attach _ _, ?_⟩
      simp at hx
      rcases hx with rfl | rfl | rfl <;> simpa using ih'

theorem recognize_iff_palindrome (w : List Char)
    (hw : w ⊆ "abc".toList) :
    recognize w ↔ w.Palindrome :=
  ⟨recognize_sound _ w (Nat.le_refl _),
   recognize_complete _ w (Nat.le_refl _) hw⟩
```
:::

:::terse
- Analisar é construir as árvores. A entrada é uma `List Char`, e as
  árvores são do tipo `ParseTree Char Char`: caracteres nas folhas e o
  rótulo `A` nos nós.
- Mesma receita do reconhecedor, uma linha por regra; agora cada linha
  devolve a lista das suas árvores, vazia quando a regra não se aplica.
- As regras de uma gramática podem valer ao mesmo tempo, por isso as
  listas de todas as linhas são concatenadas com `++`. Numa gramática
  ambígua, uma palavra recebe assim mais de uma árvore.
- Cada regra usada vira um nó `A`, inclusive `A → ε`, que dá um nó sem
  filhas, e `A → a`, que dá um nó com uma folha.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.2, from "Parsing with a context-free grammar…"
to the end of the section.
:::
::::

```lean
def parse (xs : List Char) : List (ParseTree Char Char) :=
  (if xs == [] then [.branch 'A' []] else []) ++
  (if xs == ['a'] then [.branch 'A' [.leaf 'a']] else []) ++
  (if xs == ['b'] then [.branch 'A' [.leaf 'b']] else []) ++
  (if xs == ['c'] then [.branch 'A' [.leaf 'c']] else []) ++
  (splitN 3 xs).attach.flatMap fun
    | ⟨[['a'], ys, ['a']], h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'a', t, .leaf 'a']
    | ⟨[['b'], ys, ['b']], h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'b', t, .leaf 'b']
    | ⟨[['c'], ys, ['c']], h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'c', t, .leaf 'c']
    | _ => []
termination_by xs.length
decreasing_by
  all_goals
    have := congrArg List.length (flatten_of_mem_splitN h)
    simp at this
    omega

#eval IO.println (parse "".toList)
#eval IO.println (parse "aab".toList)
#eval IO.println (parse "aabaa".toList)
```

:::details "Árvores mais enxutas"
Como a gramática tem um só não terminal, poderíamos omitir o nó `A`
nas regras que não chamam `A` de novo: `A → ε` daria a árvore vazia
`ep`, e `A → a` daria só a folha `a`. Nenhuma informação se perderia,
porque o único rótulo possível é `A`. Mas a árvore deixaria de ter um
nó para cada regra usada, e a correspondência entre a gramática e o
parser ficaria menos direta. Por isso mantemos um nó para cada regra.
:::

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
  | 0, [] => [[]]
  | 0, _ :: _ => []
  | 1, [] => []
  | 1, xs => [[xs]]
  | n + 2, xs =>
    solution!(
      (split2' xs).flatMap fun (ys, zs) =>
        (splitN' (n + 1) zs).map fun rs => ys :: rs)

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
