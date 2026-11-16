import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

set_option verso.code.warnLineLength 100

#doc (Manual) "Árvores Sintáticas" =>
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
  dos nós.
- Um `branch` guarda a *lista* das suas subárvores, por isso cada nó pode
  ter quantas filhas quiser.
- A função `ParseTree.toText` escreve a árvore entre colchetes, com o rótulo depois
  de `[.` e as filhas separadas por espaços.
:::

::::full
Uma árvore sintática representa a estrutura de uma expressão. As folhas
guardam informação lexical, e os nós internos guardam informação
sintática. O tipo `ParseTree α β` deixa em aberto que informação
guardamos em cada caso. Uma folha, construída com `.leaf`, contém um
valor de tipo `α`. Um nó, construído com `.branch`, contém um rótulo de
tipo `β` e uma lista de subárvores. O número de filhas do nó é o
comprimento dessa lista.

Para exibir uma árvore, precisamos saber como exibir os valores de
tipos `α` e `β`. A função `ParseTree.toText` usa {name}`ToString`
para ambos. Ela escreve uma folha como o texto do seu conteúdo. Para
um nó, escreve `[.`, o rótulo e as subárvores, separadas por espaços,
e fecha com `]`.

Na árvore `snowWhite`, tanto os rótulos quanto o conteúdo das folhas
são textos de tipo {name}`String`. A raiz, rotulada `S`, tem duas
filhas. A primeira é um `NP` com a folha `Snow White`. A segunda é um
`VP`, que contém o verbo sob o rótulo `TV` e o objeto sob outro
`NP`.
::::

```lean
inductive ParseTree (α β : Type) where
  | leaf (a : α)
  | branch (b : β) (ts : List (ParseTree α β))
  deriving Repr, BEq

def ParseTree.toText {α β : Type}
    [ToString α] [ToString β] : ParseTree α β → String
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
  `Snow White loved Snow White`, `[.NP Snow White]` ocorre duas vezes.
- Para apontar uma ocorrência, usamos uma *posição*: a lista dos índices
  das filhas no caminho desde a raiz, contando a partir de zero. A raiz é a
  posição `[]`.
- A função `pos` lista todas as posições. Como a recursão desce por uma
  lista de subárvores, ela usa uma função auxiliar local, definida com
  `let rec`: `posFrom i ts` dá as posições das árvores de `ts`, a
  primeira com índice `i`.
- A função `subtree` dá subárvores: `subtree t p` é {name}`Option.some` da subárvore
  de `t` na posição `p`, ou {name}`Option.none` se a posição não existe em `t`.
- A função `subtrees` aplica `subtree t` a todas as posições de `pos t`
  com {name}`List.filterMap`. Como essas posições são válidas,
  nenhuma aplicação devolve {name}`Option.none`.
:::

::::full
Uma mesma subárvore pode ocorrer em mais de um lugar. Se, na árvore
{name}`snowWhite`, trocássemos a folha `the dwarfs` por `Snow White`,
a subárvore `[.NP Snow White]` teria duas ocorrências. Para distinguir
uma da outra, usamos o caminho da raiz até cada ocorrência. O primeiro
`NP` fica em `[0]`, a primeira filha da raiz. O segundo fica em
`[1, 1]`, a segunda filha da segunda filha da raiz.

Uma *posição* é uma lista de índices naturais. Em cada passo, o índice
indica qual filha visitar, contando a partir de zero. O caminho vazio
`[]` aponta para a própria raiz. Para listar as posições de uma
árvore, `pos` inclui `[]` e, para cada filha, acrescenta seu índice ao
início de cada caminho que parte dela. A função auxiliar local
`posFrom i ts`, definida com `let rec`, percorre as filhas em `ts` a
partir do índice `i`.

A função `subtree t p` percorre a árvore `t` seguindo os índices de
`p`. O acesso `ts[i]?` devolve a filha de índice `i` quando ela existe.
Se um índice estiver fora da lista ou se ainda houver passos a dar
ao chegar a uma folha, o resultado é {name}`Option.none`. Quando o
caminho termina, a função devolve a subárvore encontrada com
{name}`Option.some`. Por fim, `subtrees` usa {name}`List.filterMap`
para aplicar `subtree t` às posições de `pos t` e recolher as
subárvores. Esses caminhos vêm da própria árvore e, portanto, todos
são válidos.
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
  | .leaf _ => [[]]
  | .branch _ ts => [] :: posFrom 0 ts

#eval pos snowWhite

def subtree {α β : Type} :
  ParseTree α β → Pos → Option (ParseTree α β)
  | t, [] => some t
  | .branch _ ts, i :: is =>
    match ts[i]? with
    | some t => subtree t is
    | none => none
  | .leaf t, a :: as => none

def subtrees {α β : Type} (t : ParseTree α β)
  : List (ParseTree α β) :=
  (pos t).filterMap (subtree t)

#eval IO.println (subtree snowWhite [1])
```

:::terse
- Uma posição `p` *domina* `q` quando `p` é prefixo de `q`: a subárvore
  em `q` está dentro da subárvore em `p`. Toda posição domina a si mesma;
  a dominância *própria* exclui esse caso.
- Em Lean, `p <+: q` diz que `p` é prefixo de `q`. É uma proposição
  decidível, então o Lean a converte em {name}`Bool` para {name}`List.filter`.
- As relações sobre as posições de uma árvore são listas de pares.
  A função `posPairs` lista todos os pares de posições; cada relação
  filtra os que lhe interessam.
:::

::::full
Uma posição `p` domina uma posição `q` se o caminho até `q` começa
pelo caminho até `p`. Nesse caso, a subárvore em `q` está contida na
subárvore em `p`. Em {name}`snowWhite`, por exemplo, `[1]` domina
`[1, 0]` e também domina a si mesma. A *dominância própria* exige
ainda que as duas posições sejam distintas.

Para representar essas relações, `posPairs t` forma todos os pares
de posições da árvore `t`. A notação `p <+: q` exprime a proposição
de que `p` é prefixo de `q`, definida por {name}`List.IsPrefix`.
Como essa proposição é decidível para listas de naturais, o Lean
pode convertê-la em um {name}`Bool` para
{name}`List.filter`. Assim, `dominance` conserva os pares em que
`p <+: q`, e `properDominance` exige também que `p ≠ q`.
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
{name}`snowWhite`.

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
- A composição é `relComp`: `relComp r s` liga `x` a `z` quando `r`
  liga `x` a algum `y` e `s` liga esse `y` a `z`. A função {name}`List.eraseDups`
  tira os pares repetidos.
- Na árvore {name}`snowWhite`, o sujeito `[0]` c-comanda tudo o que está dentro
  do `VP`; o objeto `[1, 1]` c-comanda o verbo `[1, 0]`, mas não o sujeito.
:::

::::full
Duas posições são *irmãs* quando são filhas diferentes do
mesmo nó. Os caminhos até elas coincidem até a mãe e diferem no
último índice. A função `sisters` testa essa condição, e
`sisterhood` reúne os pares de posições que a satisfazem.

Uma posição `p` *c-comanda* uma posição `q` quando alguma irmã de
`p` domina `q`. Para expressar isso, `cCommand` usa a composição
das relações de irmandade e dominância. Em `relComp r s`, cada
`(x, y)` de `r` é combinado com os pares de `s` que começam em
`y`. Cada combinação com um par `(y, z)` produz `(x, z)`.
{name}`List.eraseDups` elimina os pares repetidos.

Em {name}`snowWhite`, a posição do sujeito, `[0]`, tem como irmã a
posição do `VP`, `[1]`. Por isso, o sujeito c-comanda o `VP` e
todas as posições que ele domina. Já o objeto, em `[1, 1]`, tem como
irmã a posição do verbo, `[1, 0]`. O objeto c-comanda essa posição
e a folha do verbo. A posição do sujeito está fora desse ramo.
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
  {name}`snowWhite`, só a raiz e o `VP` ramificam.
:::

::::full
Uma posição ramifica quando domina imediatamente pelo menos duas
posições distintas. Como as filhas são numeradas a partir de zero,
basta verificar se os caminhos `p ++ [0]` e `p ++ [1]` existem.
Em {name}`snowWhite`, apenas a raiz, `[]`, e o `VP`, `[1]`,
satisfazem essa condição.
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
- Três lemas sobre irmãs: elas têm o mesmo comprimento, nenhuma é
  prefixo da outra, e as duas têm a mesma mãe.
:::

::::full
Para estudar a relação entre c-comando e dominância, basta considerar
os caminhos envolvidos. Se `p` c-comanda `q`, existe uma irmã `r`
de `p` que é prefixo de `q`. Os três lemas abaixo descrevem o que
sabemos sobre `p` e `r` a partir de {name}`sisters`: os caminhos
têm o mesmo comprimento, `p` não é prefixo de `r`, e, sem o último
índice, os dois caminhos coincidem, isto é, `p` e `r` têm a mesma
mãe. O exercício
usa esses fatos para investigar a dominância entre `p` e `q`.
::::

:::details "Três lemas sobre posições irmãs"
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

theorem sisters_dropLast (p r : Pos)
    (h : sisters p r = true) : p.dropLast = r.dropLast := by
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
          simp only [sisters, Bool.and_eq_true,
            beq_iff_eq] at h
          obtain ⟨rfl, h⟩ := h
          simp [List.dropLast_cons_cons, ih _ h]
```
:::

::::exercise (rating := 3) (name := "c-command-dominance")
Suponha que `p` c-comanda `q`, isto é, uma irmã `r` de `p` domina `q`. Prove que
`p` não domina `q` e que `q` não domina `p`. Prove também que a mãe
de `p` domina `q`. A mãe ramifica, porque tem as filhas
`p` e `r`, e é a posição ramificada mais baixa acima de `p`.

Dicas, uma para cada teorema:

- Se `p` dominasse `q`, `p` e `r` seriam prefixos de `q` com o mesmo
  comprimento. Então `p` seria prefixo de `r`
  ({name}`List.prefix_of_prefix_length_le`), o que {name}`sisters_not_prefix`
  proíbe.
- Se `q` dominasse `p`, teríamos `r` prefixo de `q` e `q` prefixo de `p`,
  com `p` e `r` do mesmo comprimento. Os três teriam o mesmo comprimento e
  seriam iguais ({name}`List.IsPrefix.eq_of_length`), e `p` seria irmã de
  si mesma.
- As irmãs `p` e `r` têm a mesma mãe ({name}`sisters_dropLast`), e uma lista
  sem o último elemento é prefixo dela ({name}`List.dropLast_prefix`).

```lean
theorem cCommand_not_dominates (p r q : Pos)
    (hs : sisters p r) (hd : r <+: q)
    : ¬ p <+: q := by
  solution!
   intro hp
   have hl := sisters_length p r hs
   have h : p <+: r :=
     List.prefix_of_prefix_length_le hp hd (by omega)
   exact sisters_not_prefix p r hs h

theorem cCommand_not_dominated (p r q : Pos)
    (hs : sisters p r) (hd : r <+: q)
    : ¬ q <+: p := by
  solution!
   intro hq
   have hl := sisters_length p r hs
   have h1 := hd.length_le
   have h2 := hq.length_le
   have hqp : q = p := hq.eq_of_length (by omega)
   have hrq : r = q := hd.eq_of_length (by omega)
   rw [hrq, hqp] at hs
   exact sisters_not_prefix p p hs (List.prefix_refl p)

theorem cCommand_mother_dominates (p r q : Pos)
    (hs : sisters p r) (hd : r <+: q)
    : p.dropLast <+: q := by
  solution!
   rw [sisters_dropLast p r hs]
   exact (List.dropLast_prefix r).trans hd
```
::::

::::exercise (rating := 2) (name := "mutual-c-command")
O c-comando não é simétrico, mas o *c-comando mútuo* é: `p` e `q` se
c-comandam mutuamente quando `p` c-comanda `q` e `q` c-comanda `p`.
Defina `mutualCCommand` e confira, na árvore {name}`snowWhite`, que ele coincide
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

::::exercise (rating := 3) (name := "c-command-variants")
A definição de c-comando deste capítulo não é a única em
uso. Outras duas partem do primeiro nó ramificado acima de `p`:

- `p` c-comanda `q` quando o primeiro nó ramificado acima de `p` domina
  `q`, com a dominância reflexiva. É uma definição usada para descrever a
  ligação de variáveis.
- `p` c-comanda `q` quando nenhuma das duas posições domina a outra e o
  primeiro nó ramificado acima de `p` domina `q`. É a definição que o
  verbete _C-command_ {citep Bib.wikipediaCCommand}[] apresenta como padrão.

A função `lowestBranchingAbove` dá o primeiro nó ramificado acima de uma
posição, se houver um. A função `labelPairs` troca cada par de posições
pelo par dos rótulos dos nós nessas posições; na árvore `cTree`, cada
rótulo aparece uma só vez, e o rótulo identifica o nó. Defina
`cCommandBranching` e `cCommandStandard`, uma para cada definição. Os teoremas
abaixo comparam as três definições na árvore `cTree`, em que `A` está em `[0]`,
`B` em `[1]`, `C` em `[1, 0]`, `E` em `[1, 0, 0]`, `D` em `[1, 1]`, `F` em
`[1, 1, 0]` e `G` em `[1, 1, 1]`:

:::diagramWithAlt
```diagram (cssWidth := "12em") (texWidth := "9em")
CSwLMeta.Diagrams.cCommandTree
```

```
        M
      ┌─┴─┐
      A   B
        ┌─┴─┐
        C   D
        │ ┌─┴─┐
        E F   G

A raiz M tem as filhas A e B. B tem as filhas C e D. C tem uma só filha, E. D tem
as filhas F e G.
```
:::

O nó `C` tem uma só filha, `E`. Pela definição deste capítulo, `E` não
c-comanda nada, porque não tem irmãs. Por `cCommandStandard`, `E` c-comanda
`D`, `F` e `G`. O exemplo do próprio verbete diz que `E` não c-comanda
nada: ele segue a definição pelas irmãs, a da primeira frase do verbete, e
não a que o verbete chama de padrão. Então `cCommandBranching`
acrescenta os pares em que uma posição domina a outra: `E`, por
exemplo, passa a c-comandar também a si mesmo, a sua mãe, `C`, e a sua
avó, `B`.

```lean
def cTree : ParseTree Char Char :=
  .branch 'M' [.leaf 'A',
    .branch 'B' [.branch 'C' [.leaf 'E'],
      .branch 'D' [.leaf 'F', .leaf 'G']]]

def lowestBranchingAbove {α β : Type} (t : ParseTree α β)
    (p : Pos) : Option Pos :=
  ((List.range p.length).map p.take).reverse.find?
    (branchingPos t).contains

def ParseTree.label {α : Type} : ParseTree α α → α
  | .leaf a => a
  | .branch b _ => b

def labelPairs {α : Type} (t : ParseTree α α)
    (r : List (Pos × Pos)) : List (α × α) :=
  r.filterMap fun (p, q) => do
    let s ← subtree t p
    let u ← subtree t q
    pure (s.label, u.label)

def cCommandBranching {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  solution!(
    (posPairs t).filter fun (p, q) =>
      match lowestBranchingAbove t p with
      | some m => m <+: q
      | none => false)

def cCommandStandard {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  solution!(
    (posPairs t).filter fun (p, q) =>
      !(p <+: q) && !(q <+: p) &&
      match lowestBranchingAbove t p with
      | some m => m <+: q
      | none => false)

theorem cCommand_sub_standard :
  (cCommand cTree).all (cCommandStandard cTree).contains := by
  solution!
   decide

theorem cCommandStandard_sub_branching :
  (cCommandStandard cTree).all (cCommandBranching cTree).contains := by
  solution!
   decide

theorem cCommandStandard_E :
    (labelPairs cTree (cCommandStandard cTree)).filter
      (fun ab => ab.1 == 'E') =
      [('E', 'D'), ('E', 'F'), ('E', 'G')] := by
  solution!
   decide

theorem cCommandBranching_E :
    (labelPairs cTree (cCommandBranching cTree)).filter
      (fun ab => ab.1 == 'E') =
      [('E', 'B'), ('E', 'C'), ('E', 'E'), ('E', 'D'), ('E', 'F'),
        ('E', 'G')] := by
  solution!
   decide
```
::::

:::terse
Uma posição `p` *precede* `q` quando, no primeiro índice em que diferem, o de
`p` é menor. Uma posição não precede as que ela domina.
:::

::::full
Para saber se uma posição `p` precede outra posição `q`,
comparamos os caminhos até elas a partir da raiz. Enquanto os índices
coincidem, avançamos nas duas listas. Na primeira diferença, `p`
precede `q` se o seu índice é menor. Se um dos caminhos termina antes
de encontrarmos uma diferença, a precedência não vale. Em particular,
uma posição não precede nenhuma das posições que domina.

Por exemplo, em {name}`snowWhite`, a posição do sujeito, `[0]`,
precede a do objeto, `[1, 1]`, pois já diferem no primeiro índice.
A função `precedence` aplica o teste `precede` aos pares de
posições da árvore.
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
resultado na árvore {name}`snowWhite`.

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
O *comando* é uma noção anterior ao c-comando: `p` comanda `q` quando nenhuma
das duas domina a outra e o `S` mais próximo acima de `p` também domina `q`.
:::

::::full
Antes da noção de c-comando, foi proposta a relação de *comando*.
Uma posição `p` comanda `q` quando nenhuma das duas domina a outra
e o nó com rótulo `S` mais próximo que domina `p` também domina
`q`.
::::

::::exercise (rating := 2) (name := "command")
Defina `command` supondo que o `S` mais próximo é sempre a raiz da árvore.
Confira o resultado na árvore {name}`snowWhite`.

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
