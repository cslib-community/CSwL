import CSwLMeta
import Bib
import Mathlib.Tactic
import CSwLCompat
import CSwL.IntroL

open Verso.Genre Manual
open CSwLMeta

set_option verso.code.warnLineLength 100

#doc (Manual) "Prova em Lean" =>
%%%
tag := "Proof"
%%%

Lógica, aqui, é duas coisas ao mesmo tempo. É o assunto — proposições,
conectivos, quantificadores, o que se segue de quê — e é a ferramenta com que
se escreve e se confere qualquer afirmação neste livro. Esta seção trata da
ferramenta: o tipo `Prop`, o que conta como prova em Lean, e as táticas com
que se constrói uma. As seções seguintes tratam do assunto, e o fazem
implementando cada lógica como um tipo de dado.

Supomos conhecida a lógica proposicional e a de predicados — sintaxe,
semântica, e a noção de consequência. Para uma apresentação a partir do
início, ver {citep Bib.logicandproof}[].

```lean
namespace Proof

-- `square₁` and `square₂` are the two definitions of squaring from the Lean
-- chapter; the examples below reuse them rather than introducing new ones.
open IntroL
```

# O tipo Prop e Provas

O que diferencia Lean de outras linguagens como Python e Java é a capacidade de na mesma linguagem que usamos para 'programar' funções, escrevermos 'provas' sobre estas funções.

Nesta 'Exemplos extraídos de {citep Bib.FAA2025}[]. Uma proposição é um enunciado que pode ser verdadeiro ou falso. O enunciado `1 = 1` é verdadeiro, enquanto `square₁ 12 = 2` é falso. Toda proposição é todo tipo `Prop`.

```lean
#check square₁ 12 = 2
```

Podemos declarar proposições como a seguir e verificar que `1 = 1 : Prop`, mas não podemos _avaliar_ uma proposição.

```lean
def p1 : Prop := 1 = 1

#check p1
```

Toda proposição verdadeira tem uma prova, e uma prova é um _termo_ do tipo da proposição que testemunha a verdade da proposição. Provar `1 = 1` é exibir um termo de tipo `1 = 1`, exatamente o que o termo `Eq.refl 1` faz abaixo. Declarar um teorema é muito parecido com declarar uma função.

```lean
theorem OneEqSelf : 1 = 1 := Eq.refl 1
```

A mesma ideia vale para dizer que duas funções são a mesma coisa — não é
analogia, é a proposição `f = g`, provável do mesmo jeito. Agora usando o
modo `tactic` iniciado com `by`. Usamos as taticas `rfl` e `intro` que iremos explicar a seguir. Com `example` não precisamos dar nomes a teoremas que não serão reusados.

```lean
example :
  ∀ (z : Nat), (λ x ↦ x * x) z = (fun y => y * y) z := by
  intro n
  rfl
```

Note que perguntar pelo tipo não é o mesmo que decidir se ela é verdadeira:

```lean
#check (square₁ = square₂)
```

Provar é dar um termo cujo tipo é a proposição. Para uma igualdade em que
os dois lados reduzem ao mesmo valor, o termo é `rfl` — de _reflexividade_,
que é o princípio de que tudo é igual a si mesmo. Ver {citep Bib.love2026}[]
para uma explicação sobre `rfl`.

```lean
theorem square₁_eq_square₂ : square₁ = square₂ := by
 rfl
```

Escrito com `by`, `rfl` é uma _tática_: uma instrução para construir a
prova. Você pode inspecionar a definição de Lean para `Eq.refl`.

```lean (name := c2print1)
#print square₁_eq_square₂
```

```leanOutput c2print1
theorem Proof.square₁_eq_square₂ : square₁ = square₂ :=
Eq.refl square₁
```

Além de `rfl`, um pequeno repertório de táticas resolve o que os capítulos
seguintes precisam — conferido nos próprios arquivos, não escolhido a
priori. A
ordem abaixo é a de {citep Bib.FAA2025}[], que apresenta as táticas nesta
sequência; `decide`, `omega`, `obtain`, `cases`, `simp` e `induction` não
vêm de lá (o curso os introduz onde a necessidade aparece) e ficam ao
final, fora da ordem do FAA2025:

```
rfl          fecha a = b quando os dois lados calculam o mesmo valor
exact e      fornece o termo que é a prova
intro h      introduz uma hipótese, para provar uma implicação ou ∀
constructor  parte um ∧ ou um ↔ em dois objetivos
apply h      aplica uma implicação ou lema, deixando a(s) premissa(s)
             como novo(s) objetivo(s)
unfold nome  desdobra uma definição, antes de continuar
rw [h]       reescreve o objetivo usando a igualdade h, da esquerda para
             a direita
assumption   fecha o objetivo com uma hipótese já disponível
decide       fecha um objetivo decidível calculando a resposta
omega        resolve aritmética linear em Nat e Int
obtain ⟨_,_⟩ := h  desmonta uma hipótese composta (conjunção, existencial)
cases h      dado h : P ∨ Q, parte a prova em dois casos
simp [...]   reescreve com um conjunto de lemas até não haver mais o que
             simplificar
induction x  prova por casos sobre a forma como x foi construído
funext x     duas funções são iguais quando concordam em todo ponto
```

Duas notações de prova não são táticas: `⟨t, h⟩` monta um par (para provar
uma conjunção ou exibir a testemunha de um existencial), e `h.1`/`h.2`
desmontam um par que está numa hipótese.

::::exercise (rating := 1) (name := "rfl-arithmetic")

Termine a prova usando `rfl`.

```lean
example : 7 * 6 = 42 :=
  solution!(rfl)
```

::::

::::exercise (rating := 1) (name := "square-unfold")

Prove que `square₁ n = n * n`; uma variável aparece, então `rfl` não basta
sozinho — é preciso desdobrar a definição antes.

```lean
example (n : Nat) : square₁ n = n * n := by
  solution!
    unfold square₁
    rfl
```

::::

::::exercise (rating := 1) (name := "identity-implication")

Provar `P → Q` é: suponha `P`, derive `Q`. Prove `P → P`. Fonte:
{citep Bib.FAA2025}[]

```lean
example (P : Prop) : P → P := by
  solution!
    intro h
    exact h
```

::::

::::exercise (rating := 1) (name := "p-implies-q-implies-p")

Complete a prova abaixo. Fonte: {citep Bib.FAA2025}[]

```lean
example (P Q : Prop) : P → (Q → P) := by
  solution!
    intro h _
    exact h
```

::::

::::exercise (rating := 1) (name := "and-intro")

Prove `P ∧ Q` a partir de `P` e de `Q`. Fonte: {citep Bib.FAA2025}[]. Dica:
`constructor` parte o objetivo `P ∧ Q` em dois; cada um se fecha com
`exact`.

```lean (name := c2check24)
#check And.intro
```

```leanOutput c2check24
And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
```

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  solution!
    apply And.intro
    · exact hP
    · exact hQ
```

::::

::::exercise (rating := 2) (name := "and-comm")

Prove que a conjunção comuta. Fonte: {citep Bib.FAA2025}[]. Dica: um `↔` se parte em dois objetivos com
`constructor`; em cada um, `intro h` seguido de `obtain ⟨_,_⟩ := h` desmonta
a conjunção da hipótese, e `constructor` reconstrói a conjunção invertida.

Veja também o que acontece ao avaliar `(10,20).1`. `And` em Lean é uma
`structure` com dois campos.

```lean
example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
 solution!
   constructor
   · intro h
     obtain ⟨h1, h2⟩ := h
     apply And.intro
     · exact h2
     · exact h1
   · intro h
     constructor
     · exact h.2
     · exact h.1
```

::::

::::exercise (rating := 1) (name := "implication-transitivity")

Fonte: {citep Bib.FAA2025}[]. Dica: `intro`, depois `apply` duas vezes,
encadeando as duas hipóteses.

```lean
example (P Q R : Prop) (h : P → Q) (h2 : Q → R) :
    P → R := by
  solution!
    intro hp
    apply h2
    apply h
    exact hp
```

::::

::::exercise (rating := 1) (name := "apply-several-premises")

Adaptado de {citep Bib.FAA2025}[].

```lean
example (P Q R S : Prop) (h0 : P ∧ Q ∧ R)
    (h : P → Q → R → S) : S := by
  solution!
    apply h
    · exact h0.1
    · exact h0.2.1
    · exact h0.2.2
```

::::

Nem toda prova precisa de lógica proposicional abstrata — às vezes o que
falta é desdobrar uma definição local antes de concluir.

::::exercise (rating := 1) (name := "unfold-direct-proof")

Fonte: {citep Bib.FAA2025}[], com `f` definida localmente igual ao arquivo.
Dica: `intro h`, `unfold f at h` (ou `rw [f] at h`), depois concluir por
`omega` ou `assumption`.

```lean
def f₁ (x y : Nat) : Prop := x = y

example (x : Nat) : f₁ x 1 → x ≠ 2 := by
  solution!
    intro h
    unfold f₁ at h
    omega
```

::::

::::exercise (rating := 1) (name := "unfold-conjunction")

Fonte: {citep Bib.FAA2025}[].

```lean
example (x y : Nat) : f₁ 0 x ∧ f₁ 0 y → x = y := by
  solution!
    intro h
    obtain ⟨h1, h2⟩ := h
    unfold f₁ at h1 h2
    omega
```

::::

::::exercise (rating := 1) (name := "exists-witness")

Prove que `∃ n : Nat, n + n = 10`, exibindo a testemunha com `⟨_, _⟩` ou
usando `Exists.intro`.

```lean (name := c2check25)
#check Exists.intro
```

```leanOutput c2check25
Exists.intro.{u} {α : Sort u} {p : α → Prop} (w : α) (h : p w) : Exists p
```

```lean
example : ∃ n : Nat, n + n = 10 := by
  solution!
    apply Exists.intro 5
    rfl
```

::::

::::exercise (rating := 1) (name := "cases-on-or")

Prove que `P ∨ Q → Q ∨ P`, usando `cases` sobre a hipótese, complete a
prova.

```lean (name := c2check26)
#check Or.intro_left
```

```leanOutput c2check26
Or.intro_left {a : Prop} (b : Prop) (h : a) : a ∨ b
```

```lean (name := c2check27)
#check Or.intro_right
```

```leanOutput c2check27
Or.intro_right {b : Prop} (a : Prop) (h : b) : a ∨ b
```

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp =>
    solution!
      exact Or.inr hp
  | inr hq =>
    solution!
      exact Or.inl hq
```

::::

# Prova por indução

A última tática da tabela, `induction`, prova algo para todo valor de um
tipo indutivo, e não para um valor de cada vez.

::::exercise (rating := 1) (name := "add-zero-induction")

Prove que `n + 0 = n` para todo `n`, usando `induction n`. No caso `0`,
`rfl` fecha; no caso `n + 1`, a hipótese de indução (`ih`) resolve `omega`.

```lean
example (n : Nat) : n + 0 = n := by
 solution!
   induction n with
   | zero => rfl
   | succ a ih =>
     -- try `apply?`
     omega
```

::::

Quem quiser praticar Lean provas em Lean, pode jogar o [Natural Number
Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4/).

# Lógica Proposicional em Lean

O Lean possui `Prop`, como tipo predefinido, cujos elementos são proposições. Os conectivos lógicos  `∧`, `∨`, `→`, `↔` e `¬` estão disponíveis diretamente no Lean, de modo que uma fórmula proposicional pode ser representada como uma proposição em Lean. Isso nos fornece uma ponte conveniente entre a semântica da linguagem natural e o raciocínio formal. Podemos traduzir o conteúdo semântico de uma sentença para uma proposição em Lean e, em seguida, usar Lean para verificar se uma conclusão decorre de um conjunto de hipóteses.

Continuando a partir do quiz anterior. Para começar, vamos introduzir variáveis do tipo `Prop`, cada uma delas representado uma proposição. São 3 pessoas e 3 cores. Vamos representar "Ana veste azul" por `Aa` e assim por diante.

```lean
variable (
   Aa Ab Ap
   Ma Mb Mp
   Ca Cb Cp  : Prop)
```
A ideia é que as condições do problema sejam traduzidas em fórmulas proposicionais. Por exemplo, podemos formalizar a sentença "Ana veste azul, branco ou preto" com a fórmula em LP.

```lean
#check Aa ∨ Ab ∨ Ap
```

Aqui cabe a observação de que a formalização em LP não foi obtida diretamente a partir da construção linguística original, uma oração coordenando seus constituintes no predicado. Intuitivamente, a sentença foi antes interpretada como três orações coordenadas (proposições completas), "Ana veste azul ou Ana veste branco ou Ana veste preto".

A formalização completa do problema deve levar em consideração não apenas o que foi dito explicitamente mas algumas condições implicitamente assumidas. Definimos a estrutura `Premissas` por conveniência, ao invés de uma variável por premissa.

```lean
structure Premissas : Prop where
   -- cada pessoa veste algum vestido
   hA : Aa ∨ Ab ∨ Ap
   hM : Ma ∨ Mb ∨ Mp
   hC : Ca ∨ Cb ∨ Cp

   -- cada vestido é de alguma pessoa
   ha : Ma ∨ Aa ∨ Ca
   hb : Ab ∨ Mb ∨ Cb
   hp : Ap ∨ Mp ∨ Cp

   -- uma pessoa veste apenas um vestido
   hA1 : (Aa → ¬ Ab ∧ ¬ Ap) ∧ (Ab → ¬ Aa ∧ ¬ Ap) ∧ (Ap → ¬ Aa ∧ ¬ Ab)
   hM1 : (Ma → ¬ Mb ∧ ¬ Mp) ∧ (Mb → ¬ Ma ∧ ¬ Mp) ∧ (Mp → ¬ Ma ∧ ¬ Mb)
   hC1 : (Ca → ¬ Cb ∧ ¬ Cp) ∧ (Cb → ¬ Ca ∧ ¬ Cp) ∧ (Cp → ¬ Ca ∧ ¬ Cb)

   -- cada vestido é de apenas uma pessoa
   ha1 : (Ma → ¬ Aa ∧ ¬ Ca) ∧ (Ca → ¬ Aa ∧ ¬ Ma) ∧ (Aa → ¬ Ma ∧ ¬ Ca)
   hb1 : (Mb → ¬ Ab ∧ ¬ Cb) ∧ (Cb → ¬ Ab ∧ ¬ Mb) ∧ (Ab → ¬ Mb ∧ ¬ Cb)
   hp1 : (Mp → ¬ Ap ∧ ¬ Cp) ∧ (Cp → ¬ Ap ∧ ¬ Mp) ∧ (Ap → ¬ Mp ∧ ¬ Cp)

   -- resposta 1
   h1 : Aa → Ab
   h2 : Ca → ¬ Ab

   -- resposta 2
   h3 : ¬ Ab

   -- resposta 3
   h4 : Ap → Cb
   h5 : Cp → ¬ Cb
```

Podemos então enunciar o problema do quiz na forma do teorema abaixo. Neste caso,

```lean
theorem vestidos (h : Premissas Aa Ab Ap Ma Mb Mp Ca Cb Cp)
  : Ap ∧ Cb ∧ Ma := sorry
```

Consultar o tipo deste teorema com `#check vestidos` nos revela que ele tem o formato de uma implicação, que pode ser lido como `Γ ⊢ α` Do conjunto `Γ` de premissas em `Premissas` posso *derivar* `Ap ∧ Cb ∧ Ma`. A leitura é sintática. Podemos construir a prova de `α` a partir da aplicação de regras de dedução a partir das fórmulas de `Γ`.

Chamamos "sistema dedutivo" um conjunto das regras de dedução. Existem vários sistemas dedutivos. A formalização de Prop em Lean corresponde a implementação do sistema chamado *dedução natural* definido por Gerhard Gentzen em 1930s.

Neste sistema dedutivo, cada conectivo vem com dois tipos de regra: as de *introdução*, que dizem como construir uma prova cuja conclusão usa o conectivo, e as de *eliminação*, que dizem como usar uma prova cuja hipótese o usa.

```lean
variable {P Q R : Prop}
```

A regra de introdução de `→` diz que para provar `P → Q`, supomos `P` e derivamos `Q`. A tatica `intro` move o antecedente para as hipóteses. A regra de eliminação é a chamada regra *modus ponens*. De `P → Q` e de `P`, conclua `Q`. Em Lean isso é aplicação `h hP` já é a prova de `Q`. A tática `apply` faz o mesmo de trás para frente, ela transforma o objetivo `Q` no objetivo `P`.


```lean
example : P → (Q → P) := by
  intro hP hQ
  exact hP

example (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  intro hP
  apply h₂
  apply h₁
  exact hP

example (h : P → Q) (hP : P) : Q := h hP
```

Para a conjunção. Provar `P ∧ Q` depende de uma prova de `P` e `Q`. A tática `constructor` parte o objetivo em dois; o construtor anônimo `⟨_, _⟩` faz o mesmo em forma de termo. A eliminação de `∧` em `P ∧ Q` significa que podemos concluir `P` ou `Q`. São duas regras, e em Lean são as projeções `.1` (ou `.left`) e `.2` (ou `.right`). A tática `obtain` desmonta a hipótese de uma vez, dando nome às duas partes.


```lean
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩
example (hP : P) (hQ : Q) : P ∧ Q := And.intro hP hQ

example (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

example (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩
```

Para provar `P ∨ Q` basta provar um dos dois lados. São duas regras, e as táticas `left` e `right` escolhem qual. A eliminação de `∨` é a prova por casos. De `P ∨ Q` não se sabe qual dos dois vale. Para concluir `R` a partir dela é preciso concluir `R` nos dois casos. A tática `cases` abre exatamente esses dois objetivos.


```lean
example (hP : P) : P ∨ Q := by
  left
  exact hP

example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => right; exact hP
  | inr hQ => left; exact hQ
```

Não há um conectivo primitivo para a negação: `¬ P` é notação para `P → False` onde `False` é a proposição sem nenhuma prova. A introdução de `¬` é a introdução de `→`, para provar `¬P`, suponha `P` e derive `False`. A eliminação é a eliminação de `→`. A regra que a tradição chama de *ex falso quodlibet* (princípio da explosão), é uma regra que dita que, a partir de uma contradição ou de uma premissa falsa, qualquer conclusão pode ser deduzida. `False.elim` em Lean. As duas juntas são `absurd`.


```lean
example (h : P → Q) : ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (h hP)

example (hP : P) (hn : ¬P) : False := hn hP
example (h : False) : P := False.elim h
example (hP : P) (hn : ¬P) : Q := absurd hP hn
```

A `P ↔ Q` é a conjunção das duas implicações, e as regras seguem disso. A tática `constructor` parte o objetivo nas duas direções, e `.mp` e `.mpr` são as eliminações de `P → Q` e de `Q → P`.

```lean
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩

example (h : P ↔ Q) (hP : P) : Q := h.mp hP
```

Até aqui não usamos em nenhum momento "ou `P` vale ou não vale". Todas as regras até aqui são *construtivas*, uma prova de `P ∨ Q` traz consigo qual dos dois lados foi usado. Uma prova de `P` é uma construção de `P`.  O raciocínio *clássico* acrescenta o princípio chamado de terceiro excluído. Dele saem as duas táticas. A primeira é `by_cases`, que parte a prova em dois casos, supondo `P` num e `¬P` no outro. E a tatica `by_contra` prova `P` supondo `¬P` e derivando `False`, a redução ao absurdo.

```lean
example : P ∨ ¬P := Classical.em P

example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exact absurd hP h

example (h : ¬¬P) : P := by
  by_contra hn
  exact h hn
```

::::exercise (rating := 1) (name := "contrapositive")

Prove a contrapositiva. Só uma das direções precisa de raciocínio clássico.

```lean
example : (P → Q) ↔ (¬Q → ¬P) := solution!(by
  constructor
  · intro h hnQ hP
    exact hnQ (h hP)
  · intro h hP
    by_contra hnQ
    exact h hnQ hP)
```

::::

::::exercise (rating := 2) (name := "de-morgan")

Uma das leis de De Morgan vale construtivamente; a outra precisa do terceiro
excluído.

```lean
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := solution!(by
  constructor
  · intro h
    exact ⟨fun hP => h (Or.inl hP), fun hQ => h (Or.inr hQ)⟩
  · intro h hor
    cases hor with
    | inl hP => exact h.1 hP
    | inr hQ => exact h.2 hQ)

example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := solution!(by
  constructor
  · intro h
    by_cases hP : P
    · right; intro hQ; exact h ⟨hP, hQ⟩
    · left; exact hP
  · intro h hand
    cases h with
    | inl hnP => exact hnP hand.1
    | inr hnQ => exact hnQ hand.2)
```

::::

::::exercise (rating := 1) (name := "exchange-prop")
Complete a representação do argumento abaixo em linguagem lógica.

> Se o câmbio cair, temos inflação. Se as exportações crescerem, diminuímos o déficit. O câmbio cai ou diminuímos o déficit. Logo, temos inflação ou as exportações crescem.

```lean
section

variable (
  p -- o câmbio cai
  q -- temos inflação
  r -- as exportações crescem
  s -- Diminuimos o déficit
  : Prop)

def exchange : Prop :=
  solution!(
   ((p → q) ∧ (r → s) ∧ (p ∨ s)) → (q ∨ r)
  )
end
```
::::

::::exercise (rating := 2) (name := "dresses")
Complete a prova do teorema que responde o quiz anterior.

```lean
theorem vestidos₁ (h : Premissas Aa Ab Ap Ma Mb Mp Ca Cb Cp)
  : Ap ∧ Cb ∧ Ma := by
  obtain
    ⟨hA, hM, hC, ha, hb, hp, hA1, hM1,
     hC1, ha1, hb1, hp1, h1, h2, h3, h4, h5⟩ := h

  -- Ana não está de azul: se estivesse, por `h1` ela estaria de branco, mas Ana
  -- não está de branco por `h3`.
  have hnAa : ¬ Aa := by
    solution!(
      intro hAa
      exact h3 (h1 hAa)
    )

  have hAp : Ap := by
   cases hA with
   | inl hAa => exact absurd hAa hnAa
   | inr hx =>
     cases hx with
     | inl hAb => exact absurd hAb h3
     | inr hAp => exact hAp

  have hCb : Cb := solution!(
     h4 hAp
  )

  have hnCa : ¬ Ca := solution!(
     (hC1.2.1 hCb).1
  )

  have hMa : Ma := by
    solution!(
    rcases ha with hMa | hAa | hCa
    · exact hMa
    · exact absurd hAa hnAa
    · exact absurd hCa hnCa
    )

  exact ⟨hAp, hCb, hMa⟩
```

::::

# As regras dos quantificadores em Lean

O Lean se baseia em na teoria dos tipos, na qual se assume que cada variável pertence a algum tipo. Você pode pensar em um tipo como um "universo" ou um "domínio de discurso", no sentido da lógica de primeira ordem.

Seguindo a apresentação de Lógica Proposicional, quatro novas regras precisam ser explicadas, duas para cada quantificador.

```lean
section

variable (U : Type)
variable (P Q : U → Prop)
```

A introdução de `∀` diz que para provar que algo vale de todo `x`, tome um `x`
arbitrário e prove que vale para ele. É a mesma `intro` agora sobre um objeto em vez de uma hipótese. A eliminação de `∀` é aplicação: de `∀ x P x` e de um objeto `d`, sai `P d`.

```lean
example (h : ∀ x, P x) : ∀ y, P y := by
  intro n
  exact h n
```

A introdução de `∃` exige exibir a testemunha. A tática `use` substitui a variável quantificada pelo objeto passado, e deixa como objetivo o que falta provar sobre ele.

```lean
example (y : U) (h : P y) : ∃ x, P x :=
  Exists.intro y h

example (y : U) (h : P y) : ∃ x, P x := by
  use y
```

A eliminação de `∃` é a mais delicada. De `∃ x P x` sabe-se que há uma testemunha, mas não sabemos qual elemento do domínio ela é. A tática `obtain` aplica o teorema `Exists.elim`, introduz com um nome, junto com a propriedade que ele satisfaz.

```lean
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  apply Exists.elim h
  intro d hd
  use d
  exact hd.2

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨d, hP, hQ⟩ := h
  exact ⟨d, hQ⟩
```

Podemos ainda considera uma lógica de múltiplos tipos, onde podemos ter múltiplos universos. Por exemplo, podemos querer usar a lógica de primeira ordem para geometria, com quantificadores sobre pontos e linhas. Mas acima restringimos os predicados a um único universo `U`.

A demonstração abaixo não é válida se não declararmos uma variável `u : U`, mesmo que `u` não apareça no enunciado do teorema. Isso destaca uma diferença entre a lógica de primeira ordem e a lógica implementada em Lean. Na dedução natural, podemos provar `∀ x P x → ∃ x P x`, o que mostra que nosso sistema de prova assume implicitamente que o universo tem pelo menos um objeto. Em contraste, a afirmação `(∀ x : U, P x) → ∃ x : U, P x` não é demonstrável em Lean. Em outras palavras, em Lean, é possível que um tipo esteja vazio, e, portanto, a prova acima requer uma suposição explícita de que existe um elemento `u : U`.

```lean
variable (u : U)

example: (∀ x , P x) → ∃ x, P x := by
 intro h
 use u
 exact h u

end
```

::::exercise (rating := 2) (name := "forall-exists-swap")

Prove o primeiro exemplo.

```lean
example {U : Type} (R : U → U → Prop) :
  (∃ y, ∀ x, R x y) → (∀ x, ∃ y, R x y) :=
 solution!(by
  intro h
  obtain ⟨d, hd⟩ := h
  intro x
  exact ⟨d, hd x⟩)
```

Explique porque a volta da implicação não vale.

:::solution
A volta não vale. De `∀x ∃y Rxy` cada `x` pode ter a sua testemunha, e nada obriga que seja a mesma para todos.
:::

::::

```lean
end Proof
```
