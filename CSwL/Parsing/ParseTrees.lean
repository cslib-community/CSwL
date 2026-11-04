import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Falando de árvores sintáticas" =>
%%%
tag := "parse-trees"
file := "ParseTrees"
%%%

```lean
namespace Parsing
```

:::terse
- Uma árvore sintática tem informação lexical nas folhas e informação
  sintática nos nós internos.
- O tipo deixa as duas em aberto: `α` para as folhas, `β` para os rótulos
  dos nós. `ep` é a árvore vazia.
- Um `branch` guarda a *lista* das suas subárvores, por isso cada nó pode
  ter quantas filhas quiser.
- A função `toText` escreve a árvore entre colchetes, com o rótulo depois
  de `[.` e as filhas separadas por espaços.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.1, from the start to the example tree.
:::
::::

```lean
inductive ParseTree (α β : Type) where
  | ep
  | leaf (a : α)
  | branch (b : β) (ts : List (ParseTree α β))
  deriving Repr, BEq

def ParseTree.toText {α β : Type}
    [ToString α] [ToString β] : ParseTree α β → String
  | .ep => "[]"
  | .leaf a => toString a
  | .branch b ts =>
    "[." ++ toString b ++ " " ++
      " ".intercalate (ts.map toText) ++ "]"

instance {α β : Type} [ToString α] [ToString β] :
    ToString (ParseTree α β) :=
  ⟨ParseTree.toText⟩

def snowWhite : ParseTree String String :=
  .branch "S"
    [.branch "NP" [.leaf "Snow White"],
     .branch "VP" [.branch "TV" [.leaf "loved"],
                   .branch "NP" [.leaf "the dwarfs"]]]

#eval IO.println snowWhite
```

:::terse
- Uma mesma subárvore pode ocorrer mais de uma vez numa árvore: em
  *Snow White loved Snow White*, `[NP Snow White]` ocorre duas vezes.
- Para apontar uma ocorrência usamos uma *posição*: a lista dos índices
  das filhas no caminho desde a raiz, contando a partir de 0. A raiz é a
  posição `[]`.
- `pos` lista todas as posições. Como a recursão desce por uma lista de
  subárvores, ela é escrita junto com `posFrom`, num bloco `mutual`:
  `posFrom i ts` dá as posições das árvores de `ts`, a primeira com
  índice `i`.
- `subtree t p` é a subárvore de `t` na posição `p`. Numa posição que
  não existe em `t`, devolve `ep`; isso nunca acontece com as posições
  de `pos t`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.1, from "In this first section, we will develop…"
to the definition of `subtrees`.
:::
::::

```lean
abbrev Pos := List Nat

def pos {α β : Type} (p : ParseTree α β) : List Pos :=
  let rec posFrom {α β : Type} :
    Nat → List (ParseTree α β) → List Pos
   | _, [] => []
   | i, t :: ts =>
     (pos t).map (i :: ·) ++ posFrom (i + 1) ts
  match p with
  | .ep => [[]]
  | .leaf _ => [[]]
  | .branch _ ts => [] :: posFrom 0 ts

#eval pos snowWhite

def subtree {α β : Type} :
  ParseTree α β → Pos → ParseTree α β
  | t, [] => t
  | .branch _ ts, i :: is =>
    match ts[i]? with
    | some t => subtree t is
    | none => .ep
  | _, _ :: _ => .ep

def subtrees {α β : Type} (t : ParseTree α β)
  : List (ParseTree α β) :=
  (pos t).map (subtree t)

#eval IO.println (subtree snowWhite [1])
```

:::terse
- Uma posição `p` *domina* `q` quando `p` é prefixo de `q`: a subárvore
  em `q` está dentro da subárvore em `p`. Toda posição domina a si mesma;
  a dominância *própria* exclui esse caso.
- Em Lean, `p <+: q` diz que `p` é prefixo de `q`. É uma proposição
  decidível, então pode ser usada como `Bool` num `filter`.
- As relações sobre as posições de uma árvore são listas de pares.
  `posPairs` lista todos os pares de posições; cada relação filtra os
  que lhe interessam.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.1, from "If p, q are tree positions…" to the
definition of `dominance`.
:::
::::

```lean
def posPairs {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (pos t).flatMap fun p => (pos t).map fun q => (p, q)

def properDominance {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (posPairs t).filter fun (p, q) => p ≠ q && p <+: q

def dominance {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (posPairs t).filter fun (p, q) => p <+: q

#eval properDominance snowWhite
```

::::exercise (rating := 2) (name := "imm-dominance")
A posição `p` *domina imediatamente* `q` quando `p` domina propriamente
`q` e não há posição `r`, diferente das duas, tal que `p` domina `r` e
`r` domina `q`. Defina `immDominance` e confira o resultado na árvore
`snowWhite`.

```lean
def immDominance {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  solution!(
    (properDominance t).filter fun (p, q) =>
      !(pos t).any fun r =>
        r != p && r != q && p <+: r && r <+: q)

theorem immDominance_snowWhite :
    immDominance snowWhite =
      [([], [0]), ([], [1]), ([0], [0, 0]), ([1], [1, 0]),
       ([1], [1, 1]), ([1, 0], [1, 0, 0]),
       ([1, 1], [1, 1, 0])] := by
  solution!
   decide
```
::::

:::terse
- Duas posições são *irmãs* quando são filhas diferentes da mesma mãe:
  coincidem em tudo, menos no último índice.
- O *c-comando* é a composição de duas relações: `p` c-comanda `q` quando
  uma irmã de `p` domina `q`.
- `relComp r s` liga `x` a `z` quando `r` liga `x` a algum `y` e `s` liga
  esse `y` a `z`. `eraseDups` tira os pares repetidos.
- Na árvore `snowWhite`, o sujeito `[0]` c-comanda tudo o que está dentro
  do VP; o objeto `[1, 1]` c-comanda o verbo `[1, 0]`, mas não o sujeito.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.1, from "Two positions p, q are sister positions…"
to the c-command relation of the example tree.
:::
::::

```lean
def sisters : Pos → Pos → Bool
  | [i], [j] => i != j
  | i :: is, j :: js => i == j && sisters is js
  | _, _ => false

def sisterhood {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (posPairs t).filter fun (p, q) => sisters p q

#eval sisterhood snowWhite

def relComp {γ : Type} [BEq γ] (r s : List (γ × γ)) :
    List (γ × γ) :=
  (r.flatMap fun (x, y) =>
    (s.filter fun (w, _) => y == w).map fun (_, z) =>
      (x, z)).eraseDups

def cCommand {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  relComp (sisterhood t) (dominance t)

#eval dominance snowWhite
#eval cCommand snowWhite
```

:::terse
- Uma posição *ramifica* quando tem pelo menos duas filhas. Na árvore
  `snowWhite`, só a raiz e o VP ramificam.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.1, the branching positions.
:::
::::

```lean
def branchingPos {α β : Type} (t : ParseTree α β) :
    List Pos :=
  let ps := pos t
  ps.filter fun p =>
    ps.contains (p ++ [0]) && ps.contains (p ++ [1])

#eval branchingPos snowWhite
```

:::terse
- Os fatos sobre o c-comando valem para quaisquer posições, não só para
  as de uma árvore. Por isso os teoremas abaixo falam de posições.
- Dois lemas sobre irmãs: elas têm o mesmo comprimento, e nenhuma é
  prefixo da outra.
:::

:::details "Dois lemas sobre posições irmãs"
```lean
theorem sisters_length (p r : Pos)
    (h : sisters p r = true) : p.length = r.length := by
  induction p generalizing r with
  | nil => simp [sisters] at h
  | cons i is ih =>
    cases r with
    | nil => simp [sisters] at h
    | cons j js =>
      cases is with
      | nil =>
        cases js with
        | nil => rfl
        | cons k ks => simp [sisters] at h
      | cons i' is' =>
        cases js with
        | nil => simp [sisters] at h
        | cons k ks =>
          simp only [sisters, Bool.and_eq_true] at h
          simp [ih _ h.2]

theorem sisters_not_prefix (p r : Pos)
    (h : sisters p r = true) : ¬ p <+: r := by
  induction p generalizing r with
  | nil => simp [sisters] at h
  | cons i is ih =>
    cases r with
    | nil => simp [sisters] at h
    | cons j js =>
      cases is with
      | nil =>
        cases js with
        | nil => simp_all [sisters]
        | cons k ks => simp_all [sisters]
      | cons i' is' =>
        cases js with
        | nil => simp [sisters] at h
        | cons k ks =>
          simp only [sisters, Bool.and_eq_true,
            beq_iff_eq] at h
          obtain ⟨rfl, h⟩ := h
          rw [List.cons_prefix_cons]
          intro ⟨_, hp⟩
          exact ih _ h hp
```
:::

::::exercise (rating := 3) (name := "c-command-dominance")
Suponha que `p` c-comanda `q`: uma irmã `r` de `p` domina `q`. Prove que
`p` não domina `q` e que `q` não domina `p`.

Dica: um prefixo de `q` que não é mais longo do que outro prefixo de `q`
é prefixo dele (`List.prefix_of_prefix_length_le`), e um prefixo do mesmo
comprimento é a própria lista (`List.IsPrefix.eq_of_length`).

```lean
theorem cCommand_not_dominates (p r q : Pos)
    (hs : sisters p r = true) (hd : r <+: q) :
    ¬ p <+: q := by
  solution!
   intro hp
   have hl := sisters_length p r hs
   have h : p <+: r :=
     List.prefix_of_prefix_length_le hp hd (by omega)
   exact sisters_not_prefix p r hs h

theorem cCommand_not_dominated (p r q : Pos)
    (hs : sisters p r = true) (hd : r <+: q) :
    ¬ q <+: p := by
  solution!
   intro hq
   have hl := sisters_length p r hs
   have h1 := hd.length_le
   have h2 := hq.length_le
   have hqp : q = p := hq.eq_of_length (by omega)
   have hrq : r = q := hd.eq_of_length (by omega)
   rw [hrq, hqp] at hs
   exact sisters_not_prefix p p hs (List.prefix_refl p)
```
::::

::::exercise (rating := 2) (name := "mutual-c-command")
O c-comando não é simétrico, mas o *c-comando mútuo* é: `p` e `q` se
c-comandam mutuamente quando `p` c-comanda `q` e `q` c-comanda `p`.
Defina `mutualCCommand` e confira, na árvore `snowWhite`, que ele coincide
com a relação de irmãs.

```lean
def mutualCCommand {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  solution!(
    (cCommand t).filter fun (p, q) =>
      (cCommand t).contains (q, p))

theorem mutualCCommand_snowWhite :
    mutualCCommand snowWhite = sisterhood snowWhite := by
  solution!
   decide
```
::::

:::terse
- `p` *precede* `q` quando, no primeiro índice em que diferem, o de `p` é
  menor. Uma posição não precede as que ela domina.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.1, from "A position p in a syntax tree precedes…"
to the precedence relation of the example tree.
:::
::::

```lean
def precede : Pos → Pos → Bool
  | i :: is, j :: js => i < j || (i == j && precede is js)
  | _, _ => false

def precedence {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (posPairs t).filter fun (p, q) => precede p q

#eval precedence snowWhite
```

::::exercise (rating := 2) (name := "imm-precedence")
Defina a *precedência imediata*, a partir da precedência, do mesmo modo
que a dominância imediata foi definida a partir da dominância. Confira o
resultado na árvore `snowWhite`.

```lean
def immPrecedence {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  solution!(
    (precedence t).filter fun (p, q) =>
      !(pos t).any fun r => precede p r && precede r q)

theorem immPrecedence_snowWhite :
    immPrecedence snowWhite =
      [([0], [1]), ([0], [1, 0]), ([0], [1, 0, 0]),
       ([0, 0], [1]), ([0, 0], [1, 0]),
       ([0, 0], [1, 0, 0]), ([1, 0], [1, 1]),
       ([1, 0], [1, 1, 0]), ([1, 0, 0], [1, 1]),
       ([1, 0, 0], [1, 1, 0])] := by
  solution!
   decide
```
::::

:::terse
- O *comando* é uma noção anterior ao c-comando: `p` comanda `q` quando
  nenhuma das duas domina a outra e o S mais próximo acima de `p` também
  domina `q`.
:::

::::full
:::dev BeforeNextRelease
TODO: translate CSwFP/9.1, the paragraph on command.
:::
::::

::::exercise (rating := 2) (name := "command")
Defina `command` supondo que o S mais próximo é sempre a raiz da árvore.
Confira o resultado na árvore `snowWhite`.

```lean
def command {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  solution!(
    (posPairs t).filter fun (p, q) =>
      !(p <+: q) && !(q <+: p))

theorem command_snowWhite :
    (command snowWhite).length = 28 := by
  solution!
   decide
```
::::

```lean
end Parsing
```
