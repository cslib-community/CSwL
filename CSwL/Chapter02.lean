import Mathlib.Tactic

namespace Chapter02

/-
# 2. Programação Funcional no Lean

Ref. CSwFP/3. Functional Programming with Haskell. Adaptado para apresentar
Lean.

Neste capítulo, apresentamos o essencial sobre a linguagem de programação Lean.
Outros conceitos de Lean serão apresentados ao longo do texto.

Em algumas seções, a linha `Ref.` aponta para a seção correspondente de CSwFP/3,
quando existe uma.

## 2.1 Primeiros experimentos

Ref. CSwFP/3 §3.3 (p. 35–38).

### Termos e Tipos

Tudo em Lean é um _termo_ (ou _expressão_), e todo termo tem um _tipo_.

Um tipo pode ser básico - `ℤ`, `ℚ` ou `Bool` — ou uma função total `σ → τ`, onde
`σ` e `τ` são, eles mesmos, tipos. O tipo diz quais valores uma expressão pode
assumir, impondo uma disciplina que a matemática segue apenas implicitamente:
nada impede escrever `1 ∈ 2`, mas em Lean a tipagem marca a expressão como o
erro que provavelmente é.

Semanticamente, um tipo pode ser visto como um conjunto — mas Lean e a
matemática são linguagens distintas, e os tipos de Lean não são conjuntos.

Um tipo é de ordem superior quando tem `→` aninhada à esquerda de outra `→`,
como em `(ℤ → ℤ) → ℚ`: o tipo das funções que recebem uma função de `ℤ` em `ℤ` e
devolvem um `ℚ`.

Um termo, nesse sentido básico, é:

- uma constante `c`;
- uma variável `x`;
- uma aplicação `t u`;
- uma função anônima `fun x → t` (também chamada de _expressão λ_).

Aqui `t` e `u` denotam termos arbitrários, e `t : σ` diz que o termo `t` tem o
tipo `σ`. Ver mais em [Love2026].

Uma `def`inição introduz um termo (constante). Os dois-pontos anunciam o tipo, e
o `:=` dá o valor. `100` é um termo do tipo `Nat`, e `"Chomsky"` é um termo do
tipo `String`. Em alguns contextos, o tipo não precisa ser declarado quando Lean
consegue descobri-lo sozinho. Escrever `def n := 100` funciona, porque Lean irá
interpretar `100 : ℕ` e logo estabelecer que a constante `n : ℕ` — mas escrever
o tipo é conveniente e ajuda a tornar o código mais legível.
-/

def n : Nat := 100
def author : String := "Chomsky"

/-
O comando `#eval` calcula o valor; `#check` pergunta ou confirma o tipo, sem
calcular nada. -/

#eval  author
#check author
#check (1 + n : Nat)

/-
Tipos também são termos, e portanto têm tipo. O tipo de `true` é `Bool`, o tipo
de `Bool` é `Type`, e o de `Type` é `Type 1`. Esta hierarquia de universos
existe para que não exista um tipo de todos os tipos, o que produziria um
paradoxo. Para nós, em geral, basta saber que a pergunta "qual o tipo disto?"
tem sempre resposta. -/

#check true
#check Bool
#check Nat
#check Type

/-
### Funções

Um termo do tipo `Nat → Nat` é construído por abstração. E a aplicação
corresponde a passarmos um valor para esta abstração. Isto é o que chamamos de
`λ-abstraction` ou _função anônima_
-/

#eval (fun x => x * x) 12

/-
Mas podemos associarmos abstrações a novas constantes, principalmente quando
queremos que elas possam ser reusadas. A segunda privilegiando o uso de
caracteres Unicode (passe o Mouse sobre os caracteres para aprender como
digitá-los no VS Code). -/

def square₁ : Nat → Nat :=
  fun x => x * x

def square₂ : ℕ → ℕ :=
  λ x ↦ x * x

/-
Mas a sintaxe para declaração de funções pode nomear explicitamente os
parâmetros e normalmente é mais conveniente. A seguir, parâmetros de mesmo tipo
podem ser agrupados.

Nomes são definidos em `namespaces`. As definições deste capítulo estarão no
namespace `Chapter01`. A notação `name.length` infere pelo tipo de `name` que
estamos falando da função `length` definida no namespace `String` mesmo nome do
tipo `String`. Ver [FPiL]. -/

def square₃ (x : Nat) : Nat := x * x

def agePlusNameSize (age : Nat) (name : String) : Nat :=
  age * name.length

def maximum (n k : Nat) : Nat :=
  if n < k then
    k
  else n

/-
Perguntado sobre um nome que foi definido, o `#check` responde com a assinatura,
e não com o tipo seta. Envolver o nome em parênteses força a segunda forma. Mas
as duas dizem o mesmo. As três versões de `square` tem o mesmo tipo e como
veremos logo a seguir, podemos provar que são iguais. -/

#check square₁
#check square₂
#check square₃
#check (square₃)

/-
Às vezes interessa dizer que uma função _existe_, com um certo tipo, sem dizer
qual função é. `opaque` declara o nome com o tipo e não dá corpo. Exemplos de
[Love2026]. -/

opaque someF₁ : Nat → Nat
opaque someF₂ {α : Type} [Inhabited α] : α → α

#check someF₂

/-
O `#check` responde, porque conferir tipo não precisa do corpo. O `#eval` não
teria como calcular — e o que ele devolve merece atenção, porque não é erro e
não é o valor calculado pela função. `0` é o valor _default_ de `Nat`. Para
aceitar um `opaque`, Lean exige que o tipo seja _habitado_, que exista pelo
menos um valor nele. E é uma classe de tipos que registra isso — `Inhabited α`,
cuja instância fornece o valor default de `α`. O `{α : Type}` declara um
parâmetro implicito, o Lean não precisa receber este valor do usuário, pode
inferir. O uso dos colchetes indica que o tipo deve ter uma instância para a
class `Inhabited`. -/


/-
### Exercício' — Soma de quadrados

Defina `sumOfSquares m n`, que devolve `m² + n²`.
-/

def sumOfSquares (m n : Nat) : Nat :=
  (square₁ m) + (square₁ n)

/-- info: 25 -/
#guard_msgs in
#eval sumOfSquares 3 4

/-
### Funções são valores

A abstração lambda — é a operação básica para construir funções. O `def` acima
apenas deu nome ao valor que ela produz. A seta `↦` e o `=>` são a mesma coisa,
como `λ` e `fun`; a escolha é de gosto.
-/

#check (fun x => x * x)

/-
Sem dizer o tipo de `x`, Lean não tem como saber em que `*` se está pensando — o
de `Nat`, o de `Int`, o de qualquer outro tipo com multiplicação. O que aparece
no lugar do tipo (`?m.7`, e coisas assim) é uma _metavariável_: um buraco que
Lean deixa em aberto à espera de informação que decida a questão.

Anotar o argumento resolve, e a resposta passa a ser o tipo esperado. O contexto
também resolve, quando existe. Aplicada a `4`, a função não tem mais o que
decidir. -/

#check fun (x : Nat) => x * x
#check (fun x => x * x) 4

/-! Se função é valor, então nada impede que ela seja _argumento_ de outra
função. `g` recebe uma função de `Nat → Nat` e um valor, e é isso que o torna
uma função de ordem superior.
-/

def g (f : Nat → Nat) (x : Nat) : Nat := f x

#eval g (λ x => x + 1) 10
#check (g)

/-! Uma função também pode ser produzida como resultado. Ou podemos pensar que
funções podem receber seus argumentos de forma parcial. -/

def h₁ (x : Nat) : (Nat → Nat) :=
  fun y => x + y

def h₂ (x y : Nat) : Nat :=
  x + y

#check (h₁)
#check (h₁ 1)
#check (h₂ 1)
#check (agePlusNameSize 1)


/-
### Exercício' — Construindo termos

Adaptado de [Love2026]. Cada `def` declara `{α β γ : Type}`, são funções
polimórficas (parametrizadas por tipo). Um tipo diz o que existe; um termo é uma
testemunha disso. As quatro funções abaixo pedem só isso: dado o tipo, construa
um termo. Dica, use `_` para identificar no _InfoView_ qual tipo o termo na
posição deverá ter.

O `section` permite que possamos criar uma seção, onde definições podem
compartilhar, por exemplo, a declaração de variáveis. Veja o tipo de `projFst`.
-/

section
variable {α β γ : Type}

def I : α → α :=
  fun x => x

def K : α → β → α :=
  fun a _b ↦ a

def C : (α → β → γ) → β → α → γ :=
  λ f => λ b => λ a => f a b

def projFst : α → α → α :=
  fun a _b => a

def projSnd : α → α → α := sorry

def someNonsense  : (α → β → γ) → α → (α → γ) → β → γ := sorry

end

/-
### Expressões são termos

Uma expressão tem valor e tipo; um comando faz algo e não devolve nada. Em Lean
não há a segunda categoria — o que em outras linguagens é comando aqui é
expressão, e portanto pode aparecer em qualquer lugar onde um valor cabe.

`let` nomeia um valor dentro de uma expressão, e a expressão inteira tem valor.
O ponto-e-vírgula é uma alternativa a quebra de linha e alinhamento de
identação. -/

def twenty : Nat := (let a := 10; a) + (let b := 10; b)

/-- info: 20 -/
#guard_msgs in
#eval twenty

/-! O `if-then-else` também é expressão, e não desvio de fluxo: os dois ramos
têm de ter o mesmo tipo. É por isso que o resultado pode ser atribuído: -/

/-- info: 1-/
#guard_msgs in
#eval
  let a := if 5 < 10 then 1 else 0
  a

/-
## 2.2 Structures

Seção sem `Ref.` a CSwFP/3 — o livro não usa `structure`. Ver [FPiL].

Uma `structure` agrupa vários valores num só, dando nome a cada campo. `Point`
tem dois campos, `x` e `y`, ambos `Float`. E a estrutura introduz um novo tipo
chamado `Point`. -/

structure Point where
  x : Float
  y : Float
deriving Repr

/- `Point.mk` é o construtor — o nome vem de `Point` seguido de `.mk`, a menos
que a `structure` declare outro nome. Os dois jeitos de construir um `Point`
são equivalentes: -/

def origin : Point := { x := 0.0, y := 0.0 }
def origin' : Point := Point.mk 0.0 0.0

#eval origin
#check Point.mk

/- Cada campo tem uma função de projeção — `Point.x` e `Point.y` — acessível
também pela notação `.`: -/

#eval origin.x
#eval Point.x origin

/- `⟨_, _⟩` é a **notação de anônima** para o construtor: serve quando o tipo
esperado já deixa claro qual construtor usar, sem repetir `Point.mk`. -/

def origin'' : Point := ⟨0.0, 0.0⟩

/- Uma função sobre `Point` também pode desmontar o argumento com `⟨_, _⟩`,
em vez de projetar campo a campo: -/

def addPoints (p1 p2 : Point) : Point :=
  ⟨p1.x + p2.x, p1.y + p2.y⟩

#eval addPoints origin ⟨1.0, 2.0⟩

/- `with` cria uma cópia alterando só alguns campos — útil quando a
`structure` tem muitos campos. -/

def scaleX (p : Point) (factor : Float) : Point :=
  { p with x := p.x * factor }

#eval scaleX ⟨2.0, 3.0⟩ 10.0

/-
## 2.3 O tipo Prop e provas

Seção sem `Ref.` a CSwFP/3 — o livro não trata prova formal neste capítulo.
Exemplos extraídos de [FAA2025]. No `Chapter03.lean` vamos usar `Prop` desde as
primeiras linhas, sem explicá-lo; esta seção dá o mínimo necessário.

Uma proposição é um enunciado que pode ser verdadeiro ou falso, como `1 = 1`
(verdadeiro) ou `1 = 2` (falso). A constante `p1 : Prop`, um nome para a
proposição `(1 = 1) : Prop`.
-/

def p1 : Prop := 1 = 1

#check (1 = 1)
#check p1

/- Toda proposição verdadeira tem uma prova, e uma prova é um _termo_: um
elemento do tipo da proposição. Provar `1 = 1` é exibir um termo de tipo `1 =
1`, exatamente como construir um termo de tipo `Nat → Nat` na seção anterior. A
seguir iremos entender `rfl`. O `example` é um `theorem` sem nome. -/

example : 1 = 1 := rfl

/- A mesma ideia vale para dizer que duas funções são a mesma coisa — não é
analogia, é a proposição `f = g`, provável do mesmo jeito. Agora usando o modo
`tactic` iniciado com `by`. Além da `rfl`, usamos `intro` que também iremos
explicar a diante. -/

example : ∀ (z : Nat), (λ x ↦ x * x) z = (fun y => y * y) z := by
  intro z
  rfl

/- Uma igualdade é uma _proposição_. Note que perguntar pelo tipo não é o mesmo
que decidir se ela é verdadeira: -/

#check (square₁ = square₂)

/-
Provar é dar um termo cujo tipo é a proposição. Para uma igualdade em que os
dois lados reduzem ao mesmo valor, o termo é `rfl` — de _reflexividade_, que é o
princípio de que tudo é igual a si mesmo. Ver [Love2026] para uma explicação
sobre `rfl`. -/

theorem square₁_eq_square₂ : square₁ = square₂ := by
 rfl

/-
Escrito com `by`, `rfl` é uma _tática_: uma instrução para construir a prova.
Você pode inspecionar a definição de Lean para `Eq.refl`. -/

#print square₁_eq_square₂

/- Além de `rfl`, um pequeno repertório de táticas resolve o que os capítulos 3
e 4 precisam — conferido nos próprios arquivos, não escolhido a priori. A ordem
abaixo é a de [FAA2025], que apresenta as táticas nesta sequência; `decide`,
`omega`, `obtain`, `cases`, `simp` e `induction` não vêm de lá (o curso os
introduz onde a necessidade aparece) e ficam ao final, fora da ordem do FAA2025:

    `rfl`          fecha `a = b` quando os dois lados calculam o mesmo valor
    `exact e`      fornece o termo que é a prova
    `intro h`      introduz uma hipótese, para provar uma implicação ou `∀`
    `constructor`  parte um `∧` ou um `↔` em dois objetivos
    `apply h`      aplica uma implicação ou lema, deixando a(s) premissa(s)
                   como novo(s) objetivo(s)
    `unfold nome`  desdobra uma definição, antes de continuar
    `rw [h]`       reescreve o objetivo usando a igualdade `h`, da esquerda para
                   a direita
    `assumption`   fecha o objetivo com uma hipótese já disponível
    `decide`       fecha um objetivo decidível calculando a resposta
    `omega`        resolve aritmética linear em `Nat` e `Int`
    `obtain ⟨_,_⟩ := h` desmonta uma hipótese composta (conjunção, existencial)
    `cases h`      dado `h : P ∨ Q`, parte a prova em dois casos
    `simp [...]`   reescreve com um conjunto de lemas até não haver mais o que
                   simplificar
    `induction x`  prova por casos sobre a forma como `x` foi construído

Duas notações de prova não são táticas: `⟨t, h⟩` monta um par (para provar uma
conjunção ou exibir a testemunha de um existencial), e `h.1`/`h.2` desmontam um
par que está numa hipótese. -/

/-
### Exercício'

Termine a prova usando `rfl`.
-/

example : 7 * 6 = 42 :=
  rfl

/-
### Exercício' — `double n = n + n`

Prove que `double n = n + n`; uma variável aparece, então `rfl` não basta.
-/

example (n : Nat) : square₁ n = n * n := by
  unfold square₁
  rfl

/-
### Exercício' — `P → P`

Provar `P → Q` é: suponha `P`, derive `Q`. Provar `P ∧ Q` é provar as duas
coisas. Fonte: [FAA2025]
-/

example (P : Prop) : P → P := by
  intro h
  exact h

/-
### Exercício' — `P → (Q → P)`

Fonte: [FAA2025]
-/

example (P Q : Prop) : P → (Q → P) := by
  sorry

/-
### Exercício' — Conjunção a partir das partes

Fonte: [FAA2025]. Dica: `constructor` parte o objetivo `P ∧ Q` em dois; cada um
se fecha com `exact`.
-/

#check And.intro

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  apply And.intro
  · exact hP
  · exact hQ

/-
### Exercício' — Comutatividade da conjunção

Fonte: [FAA2025]. Dica: um `↔` se parte em dois objetivos com `constructor`;
em cada um, `intro h` seguido de `obtain ⟨_,_⟩ := h` desmonta a conjunção da
hipótese, e `constructor` reconstrói a conjunção invertida.

Veja também o que acontece ao avaliar `(10,20).1`. `And` em Lean é uma
`structure` com dois campos.
-/

example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
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


/-
### Exercício' — Transitividade da implicação

Fonte: [FAA2025]. Dica: `intro`, depois `apply` duas vezes, encadeando as duas
hipóteses.
-/

example (P Q R : Prop) (h : P → Q) (h2 : Q → R) : P → R := sorry

/-
### Exercício' — `apply` com várias premissas

Adaptado de [FAA2025].
-/

example (P Q R S : Prop) (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := sorry

/-
Nem toda prova precisa de lógica proposicional abstrata — às vezes o que falta é
desdobrar uma definição local antes de concluir. -/

/-
### Exercício' — Prova direta com `unfold`

Fonte: [FAA2025], com `f` definida localmente igual ao arquivo. Dica: `intro h`,
`unfold f at h` (ou `rw [f] at h`), depois concluir por `omega` ou `assumption`.
-/

def f (x y : Nat) : Prop := x = y

example (x : Nat) : f x 1 → x ≠ 2 := sorry

/-
### Exercício' — Desmontando uma conjunção com `unfold`

Fonte: [FAA2025].
-/

example (x y : Nat) : f 0 x ∧ f 0 y → x = y := sorry


/-
### Exercício' — Existe um par par

Prove que `∃ n : Nat, n + n = 10`, exibindo a testemunha com `⟨_, _⟩` ou usando
`Exists.intro`.
-/

#check Exists.intro

example : ∃ n : Nat, n + n = 10 := by
  apply Exists.intro 5
  rfl

/-
### Exercício' — Casos sobre `∨`

Prove que `P ∨ Q → Q ∨ P`, usando `cases` sobre a hipótese, complete a prova.
-/

#check Or.intro_left
#check Or.intro_right

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp => sorry
  | inr hq => sorry


/-
## 2.5 Tipos indutivos

Ref. CSwFP/3 §3.13 (p. 55) — adiantado para antes da recursão, por
necessidade Lean-vs-Haskell: em Lean a recursão se apresenta por casamento
de padrão sobre um `inductive`, então o tipo indutivo tem de vir primeiro.

`inductive` declara um tipo listando as formas que seus valores podem ter.
Quando nenhuma forma carrega argumento, o tipo é uma enumeração; quando
carrega, é um registro variante; quando a forma se refere ao próprio tipo
sendo definido, é uma árvore. As três coisas são o mesmo mecanismo.

Essa é a construção mais importante do curso. O capítulo 3 mostra que uma
gramática escrita na notação usual — a Forma de Backus-Naur — é literalmente
um tipo `inductive`, e do capítulo 4 em diante todo fragmento da língua é
declarado assim.

A enumeração é o caso mais simples. `deriving Repr, DecidableEq` pede que a
exibição e o teste de igualdade sejam gerados em vez de escritos à mão.
-/

/-- Os dias da semana, nada mais são dias da semana. -/
inductive Day where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

/-
### Exercício' — Day

Complete `isWeekend`, que responde se o dia é sábado ou domingo.
-/

def isWeekend (d : Day) : Bool :=
 match d with
 | .saturday => true
 | .sunday => true
 | _ => false

/-
`Bool` é a enumeração de duas formas; `Nat` é o caso em que uma das formas se
refere ao próprio tipo que está sendo definido. E `#print` mostra a declaração.
-/

#print Bool
#print Day
#print Nat

/-
Ou seja: um natural é `Nat.zero`, ou é `Nat.succ n` para algum natural `n`, e
nada mais. O `2` que se escreve é notação para `Nat.succ (Nat.succ Nat.zero)`.
-/

example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

/-
## 2.6 Prova por indução

A última tática da tabela, `induction`, prova algo para todo valor de um tipo
indutivo, e não para um valor de cada vez. -/


/-
### Exercício' — Indução sobre `Nat`

Prove que `n + 0 = n` para todo `n`, usando `induction n`. No caso `0`, `rfl`
fecha; no caso `n + 1`, a hipótese de indução (`ih`) resolve `omega`. -/

example (n : Nat) : n + 0 = n := by
 induction n with
 | zero => rfl
 | succ a ih =>
   -- try `apply?`
   omega

/-
Quem quiser praticar Lean provas em Lean, pode jogar o
[Natural Number Game](<https://adam.math.hhu.de/#/g/leanprover-community/nng4/>).
-/

/-
## 2.7 Recursão

Ref. CSwFP/3 §3.5 (p. 40).

Uma definição recursiva precisa de duas coisas: ter caso base, e chegar nele. O
segundo não é uma recomendação — é uma exigência que o compilador verifica, e a
definição é rejeitada se ele não conseguir ver que a recursão termina.

Em `Nat`, os dois casos do tipo dão as duas coisas de uma vez. Casar por `0`
(`Nat.zero`) e `n + 1` (`Nat.succ n`). O caso base é `0`, e a chamada recursiva
recebe o `n` que estava dentro do `succ`, necessariamente menor. Não há um
terceiro caso a esquecer, e não há argumento para o qual a função não responda.

O fatorial é o exemplo mínimo dessa forma: um caso base e um caso que
chama a si mesmo com um argumento menor. -/

def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5
#eval factorial 0

/-- A mesma função sem casar padrão, decidindo o caso base com um `if`. Funciona,
e serve de contraste: aqui o argumento da chamada recursiva é `x - 1`, e que ele
seja menor que `x` é um fato a ser verificado, não algo que a forma da definição
já garanta. Neste caso Lean verifica sozinho; em definições menos óbvias, não —
e aí a prova de terminação passa a ser trabalho do programador.  -/

def factorial' (x : Nat) : Nat :=
  if x = 0 then 1
  else x * factorial' (x - 1)

/- O casamento de padrão de `factorial` é um _açucar sintático_, na verdade a
expressão `match` está oculta na definição. A seguir, usamos de forma explicita.

Como exemplo, vamos implementar em Lean um gerador recursivo de sentença.
-/

def gen (x : Nat) : String :=
  match x with
  | 0     => "Sentences can go on"
  | n + 1 => gen n ++ " and on"

def genS (n : Nat) : String := gen n ++ "."

#eval genS 3

/-
A função de story a seguir fornece outro exemplo de recursão.
 -/

def story : Nat → String
  | 0     => "Let's cook and eat that final missionary, and off to bed."
  | k + 1 =>
    "The night was pitch dark, mysterious and deep.\n"
    ++ "Ten cannibals were seated around a boiling cauldron.\n"
    ++ "Their leader got up and addressed them like this:\n'"
    ++ story k ++ "'"

/-
podemos usar `#eval story 2` direto, mas as quebras de linha não seriam
interpretadas. o símbolo `<|` faz com que a expressão `story 2` seja
interpretada antes de passada para a função `IO.println` que efetivamente
imprime uma linha na saída. -/

#eval IO.println <| story 2

/-
### Exercício' — sumTo

Implemente `sumTo n` para devolver `0 + 1 + ... + n` e termine a prova de que a
função está correta para a entrada `4`.
-/

def sumTo : Nat → Nat
  | 0 => sorry
  | n + 1 => sorry

example : sumTo 4 = 10 := sorry

/-
## 2.7 Listas e polimorfismo

Ref. CSwFP/3 §3.6 (p. 41) + §3.4 (p. 39, polimorfismo genérico).

`List α` é o tipo das listas de elementos do tipo  `α`, e é um tipo indutivo
como os da seção anterior: uma lista é vazia, `[]` (`List.nil`), ou é um
elemento seguido de uma lista, `x :: xs` (`List.cons`). Nada mais é uma lista.
-/

#print List

/- É por isso que a recursão sobre lista tem exatamente a forma da recursão
sobre `Nat` — dois casos, e o segundo dá acesso a algo estritamente menor, aqui
a cauda.

O `α` em `List α` é um parâmetro: `List Nat` e `List String` são tipos
diferentes, produzidos pelo mesmo `List`. Uma função que não olha para dentro
dos elementos não tem por que se comprometer com um deles.

Como já falamos, `{α : Type}` declara o parâmetro entre chaves, o que o torna
_implícito_. Lean o descobre a partir do argumento, e quem chama não escreve. -/

def size {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + size xs

#eval size [10, 20, 30]
#eval size ["Chomsky", "Montague"]

/-
### Exercício' — sumList

`sumList` soma os elementos de uma lista. Complete e termine a prova.
-/

def sumList : List Nat → Nat
  | []      => sorry
  | x :: xs => sorry

example : sumList [1, 2, 3, 4] = 10 := sorry

/-
### Exercício' — countZeros

`countZeros` conta quantos zeros a lista tem. Idem.
-/

def countZeros : List Nat → Nat
  | []      => sorry
  | x :: xs => sorry

example : countZeros [0, 1, 0, 2, 0] = 3 := sorry


/-
## 2.8 O tipo Option

Uma função de tipo `List α → α` promete devolver um elemento para qualquer lista
que receba. Para a lista vazia não existe elemento nenhum, e a promessa é
impossível. Não por falta de cuidado do programador, mas porque o tipo afirma
algo falso.

A correção é no tipo, não no corpo: `List α → Option α` promete devolver _ou_ um
elemento (`some x`) _ou_ nada (`none`). Quem chama fica obrigado a tratar os
dois casos. O ganho é que o caso sem resposta deixa de ser invisível: ele está
na assinatura, e não há como esquecê-lo.
-/

#print Option

def myLast {α : Type} : List α → Option α
  | []      => none
  | [x]     => some x
  | _ :: xs => myLast xs

#eval myLast [1,2,3]
#eval myLast ([] : List Nat)

def average (xs : List Int) : Option Rat :=
  if xs.isEmpty then none
  else some ((xs.sum : Rat) / (xs.length : Rat))

#eval average [1,2,3,4]
#eval average []

/-
Algumas funções devolvem um valor default no caso ruim, em vez de `Option`.
`String.back` é uma delas, e vale conhecer as que são assim. -/

#eval "rad".back
#eval "".back


/-
## 2.10 Processamento de listas e composição de funções

Ref. CSwFP/3 §3.7 e CSwFP/3 §3.8 (p. 42–43).

Algumas perações cobrem quase todo uso de lista no curso. Todas se escreveriam
por recursão, como `size` acima, mas estas função de ordem superior simplificam
nosso trabalho.

`map` aplica uma função a cada elemento; `filter` filtra a lista com os que
satisfazem uma condição. A `foldl` (e também temos a `foldr`) reduzem a lista a
um valor final a partir do processamento sucesso de uma função. -/

def entities : List String := ["Dorothy", "Toto", "Aunt Em", "Scarecrow"]

#eval entities.map String.length
#eval entities.filter (fun x => x.length > 4)
#eval entities.foldl (fun s a => a.length + s) 0

/-! `all` e `any` perguntam se _todos_ os elementos satisfazem uma condição, ou
se _algum_ satisfaz, ambas devolvem `Bool`. -/

#eval entities.all (fun e => e.length > 2)
#eval entities.any (fun e => e.startsWith "T")

/-! E a composição: `f ∘ g` é a função que aplica `g` e depois `f`, de modo que
`(f ∘ g) x` é `f (g x)`. Ela produz função nova sem nomear argumento nenhum —
`double ∘ double` é quadruplicar. -/

#eval (square₁ ∘ square₂) 5

#eval entities.map (size ∘ String.toList)

/-
## 2.12 Classes de tipos

Ref. CSwFP/3 §3.9 (p. 45).

Nós já vimos isso lá no começo, mas `count` conta ocorrências em qualquer lista
cujos elementos se possam comparar. Essa exigência entra na assinatura entre
colchetes, `[BEq α]`: uma instância de igualdade para `α`, que Lean encontra
sozinho no ponto de uso.

Duas noções de igualdade convivem, e vale separá-las desde já:

* `BEq α` devolve `Bool` e se escreve `==`.
* `DecidableEq α` devolve uma _prova_ de igualdade ou de desigualdade. Permite
  usar `=` num `if` e usar o resultado numa demonstração.

Tente remover `[BEq α]` na definição abaixo.
-/

def count {α : Type} [BEq α] (x : α) : List α → Nat
  | []      => 0
  | y :: ys => if x == y then count x ys + 1 else count x ys

#eval count 2 [1, 2, 2, 3]
#eval count "thou" ["thou","art","thou"]

/-
## 2.13 Cadeias e textos

Ref. CSwFP/3 §3.10 (p. 47–48).

`String` é uma sequência UTF-8 empacotada, não uma lista de caracteres. Isso a
torna eficiente para guardar texto e inadequada para percorrer a cadeia. Não há
padrão `c :: cs` para casar diretamente numa `String`.

Mas podemos converter uma `String` em uma lista de caracteres e uma lista de
caracteres em uma `String`.
-/

def hword : List Char → Bool
  | []      => false
  | c :: cs => c == 'h' || hword cs

#eval hword "shrimptoast".toList
#eval hword "antiquing".toList

def reversal : List Char → List Char
  | []     => []
  | c :: t => reversal t ++ [c]

#eval String.ofList (reversal "Chomsky".toList)

/-- Remove o último caractere. -/
def initS (s : String) : String :=
  String.ofList s.toList.dropLast

#eval initS "flicka"

/-
## 2.14 Um fragmento linguístico

Ref. CSwFP/3 §3.13 (p. 56–57).

Vamos construir uma sentença a partir de um sujeito e um predicado. Não se trata
da concatenação de strings, é um construtor de sentenças que respeitam uma
estrutura esperada. O verificador de tipos passa a recusar as combinações que
não são sentenças. Um embrião do que vamos ver pela frente.

A keyword `deriving` pede que uma instância para a classe `Repr` seja
automaticamente gerada para cada tipo.
-/

inductive Subject where
  | Chomsky
  | Montague
deriving Repr

inductive Predicate where
  | Wrote (title : String)
deriving Repr

inductive Sentence where
  | S (subj : Subject) (pred : Predicate)
deriving Repr

/-- A abreviações são como `def` mas são `unfold` automaticamente. -/
abbrev Sentences := List Sentence

#eval Subject.Chomsky
#eval Sentence.S Subject.Chomsky (Predicate.Wrote "Syntactic Structures")

/- A última saida acima lembra uma árvore, o que iremos chamar de _árvore
sintática_.

         Sentence
          /    \
    Subject   Predicate

O passo inverso é a _geração_, serializar uma estrutura que representa uma
sentença. Para isso temos que transformar a representação interna em uma String.
Já existe a classe `ToString` e `IO.println` pede como entrada um tipo que seja
instância desta classe. Então só precisamos definir as instâncias para
`ToString` de nossos tipos. Criar uma instância de uma classe é implementar os
campos que a classe demanda e classes são `structure`. Algumas variações de
sintaxe na declaração das instâncias. -/

#print ToString

instance : ToString Subject where
  toString
  | .Chomsky  => "Chomsky"
  | .Montague => "Montague"

instance : ToString Predicate :=
  ⟨ fun p => match p with
    | .Wrote t => s!"wrote \"{t}\"" ⟩

instance : ToString Sentence :=
  ⟨ fun | .S s p => s!"{s} {p}" ⟩

/- Algumas funções auxiliares para conveniência. -/

def makeP (title : String) : Predicate := .Wrote title
def makeS (s : Subject) (p : Predicate) : Sentence := .S s p

#eval IO.println $ makeS .Chomsky (makeP "Syntactic Structures")

/-
## 2.15 Harmonia vocálica do finlandês

Ref. CSwFP/3 §3.11 (p. 52–55).

A morfologia é a parte da gramática que estuda a estrutura, formação, flexão e a
classificação das palavras de forma isolada.

Não vamos estudar morfologia no curso, mas para os interessados, recomendo
[beesley2003]. Palavras de linguagem natural são tipicamente formadas pela
concatenação de morfemas. Quando morfemas se combinam em novas palavras, é comum
haver alternâncias na pronúncia ou na escrita. A morfologia de estados finitos
assume que tanto as regras de formação de palavras (morfotática) quanto as
regras de alternância morfo-fonológica podem ser modeladas como [máquinas de
estados finita](https://en.wikipedia.org/wiki/Finite-state_machine).

Vamos implementar um fragmento da harmonia vocálica finlandesa e o plural sueco
de forma.

Harmonia vocálica é um processo fonológico pelo qual as vogais passam a
compartilhar certos traços. No caso do finlandês, há as vogais posteriores a,
o, u, as vogais anteriores ä, ö, y, e as vogais neutras i, e. Uma palavra
finlandesa só pode conter vogais posteriores (e neutras) ou só vogais
anteriores (e neutras).

    pouta  'fine weather'
    koti`  'home'
    pöytä` 'table'

Vogais posteriores e anteriores também induzem harmonia vocálica: se o radical
contém apenas vogais posteriores, o sufixo também contém apenas vogais
posteriores; se o radical é de vogais anteriores, as vogais do sufixo se
assimilam a anteriores.

    pouta ++ na → poutana
    koti ++ na → kotina
    pöytä ++ na → pöytänä

Isso pode ser capturado de forma simples por uma função que muda as vogais do
sufixo conforme as vogais do radical sejam anteriores ou posteriores
(Forsberg [For07, p. 13]).
-/

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

#eval "tea".contains (fun c => "aou".toList.contains c)

/--
Sufixa `suffix` ao radical `stem`, ajustando cada vogal do sufixo pela harmonia
vocálica do radical. Veja que com o `let` podemos declarar uma função local à
função `appendSuffixF`. -/

def appendSuffixF (stem suffix : String) : String :=
  let vh : Char → Char :=
    if      stem.contains ("aou".toList.contains ·) then back
    else if stem.contains ("äöy".toList.contains ·) then front
    else id
  stem ++ String.ofList (suffix.toList.map vh)

/-- info: "talossa" -/
#guard_msgs in
#eval appendSuffixF "talo" "ssa"

/-- info: "kylässä" -/
#guard_msgs in
#eval appendSuffixF "kylä" "ssa"


/- ## 2.16 Plural do Suéco

O sueco distribui os substantivos em cinco classes de declinação [Hel78], e a
forma do plural depende da classe. As cinco classes de declinação do plural em
sueco podem ser declaradas como um tipo indutivo.
-/

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

/-
### Exercício - implementar swedishPlural

A forma do plural é determinada pela classe de declinação. Na terceira classe
ela depende também de a palavra terminar ou não em vogal. -/

def swedishPlural (noun : String) : DeclClass → String := sorry

example : swedishPlural "blomma" .One   = "blommor" := sorry
example : swedishPlural "flicka" .One   = "flickor" := sorry
example : swedishPlural "pojke"  .Two   = "pojkar"  := sorry
example : swedishPlural "rad"    .Three = "rader"   := sorry
example : swedishPlural "ko"     .Three = "kor"     := sorry
example : swedishPlural "äpple"  .Four  = "äpplen"  := sorry
example : swedishPlural "hus"    .Five  = "hus"     := sorry


/-
## 2.17 Aplicação: representando fonemas

Ref. CSwFP/3 §3.14 (p. 58–61).

Vimos uma implementação simples da harmonia vocálica do finlandês por
manipulação de strings. Do ponto de vista linguístico isso não satisfaz:
processos fonológicos como harmonia vocálica não são regras de substituição
de caracteres, e sim regras disparadas por _traços fonológicos_. Uma
implementação mais adequada representa cada fonema como um feixe de traços —
o que importa ainda mais quando o padrão de harmonia é mais complexo, como
veremos a seguir. Os tipos abaixo dão essa representação. -/

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

/- ### Exercício - implementar fValue -/

/-- Consulta o valor de um traço. -/
def fValue (attr : Attr) : Phoneme → Option Value := sorry

/-- Troca o valor de um traço. -/
def fMatch (attr : Attr) (value : Value) (fs : Phoneme) : Phoneme :=
  fs.map fun f =>
    if f.attr == attr then { f with value := value } else f

/- Representar fonemas por traços ajuda quando o sistema de harmonia vocálica é
mais complexo, como o de Yawelmani, variedade extinta da língua Yokuts da
Califórnia. Yawelmani tem as vogais de superfície i u e o a (ignorando a
distinção entre vogais curtas e longas), representáveis como termos de tipo
`Phoneme`, isto é, como listas de traços.

Esta seção usa uma representação **deliberadamente simplificada** de Yawelmani.
Duas simplificações merecem ser ditas antes do código, porque sem elas os
exemplos abaixo confundem mais do que ensinam:

- só as vogais têm identidade — toda consoante vira o mesmo `c` (a razão aparece
  adiante, junto da definição de `c`);
- os exemplos foram escolhidos com **uma única vogal relevante** por radical e
  por sufixo, para que a regra de harmonia seja fácil de acompanhar. Isso é uma
  escolha dos exemplos, não uma propriedade de Yawelmani — a função que vamos
  escrever localiza "a primeira vogal do radical" porque é isso que o exercício
  pede, não porque um radical não possa ter mais de uma. -/

section
open Attr Value

def a : Phoneme := [⟨Cons, Minus⟩, ⟨High, Minus⟩, ⟨Round, Minus⟩, ⟨Back, Plus⟩]
def e : Phoneme := [⟨Cons, Minus⟩, ⟨High, Minus⟩, ⟨Round, Minus⟩, ⟨Back, Minus⟩]
def i : Phoneme := [⟨Cons, Minus⟩, ⟨High, Plus⟩,  ⟨Round, Minus⟩, ⟨Back, Minus⟩]
def o : Phoneme := [⟨Cons, Minus⟩, ⟨High, Minus⟩, ⟨Round, Plus⟩,  ⟨Back, Plus⟩]
def u : Phoneme := [⟨Cons, Minus⟩, ⟨High, Plus⟩,  ⟨Round, Plus⟩,  ⟨Back, Plus⟩]

def yawelmaniVowels := [i,a,o,u,e]
end

example : fValue .High i = some .Plus := sorry
example : fValue .High a = some .Minus := sorry
example : fValue .Back ([] : Phoneme) = none := sorry
#eval fMatch .Back .Plus i

/- A seção só se ocupa da harmonia entre vogais — o que a regra de Yawelmani
apaga ou preserva é `Back`, `Round` e `High`, traços que aqui só as vogais
carregam. Por isso toda consoante é representada por um único feixe genérico
`c`, sem o traço que a distinguiria de outra consoante. Isso tem um preço: `x`,
`l`, `d`, `b`, `h`, `n`, `k'` — todas colapsam no mesmo `c`, e `realize`
(abaixo) não tem como devolver a consoante certa, só `'c'`. Nos exemplos de
[CK97] mais adiante, `xil` e `dub` são então lidos como `c i c` e `c u c`: a
identidade da consoante é irrelevante para a regra, só a primeira vogal importa.
O apóstrofo de `bok'` (ejetiva/glotalizada, na notação linguística) também se
perde nessa simplificação — `k'` também colapsa em `c`. -/

def c : Phoneme := [Feature.mk Attr.Cons Value.Plus]

/-- A realização de superfície: qual letra corresponde a este feixe.

Mais uma simplificação, e independente das anteriores: `realize` devolve `Char`,
um único caractere por fonema — como se fonema e letra fossem sempre a mesma
coisa. Não são, em nenhuma língua: `ch` e `sh` são dois caracteres para um só
fonema, e o próprio `k'` de Yawelmani (uma consoante ejetiva) usa dois
caracteres na notação. A correspondência 1-1 vale aqui só porque o inventário do
exercício foi escolhido para caber num `Char` — não é uma propriedade de fonemas
em geral, e uma modelagem que precisasse disso usaria antes `Phoneme → String`.

Um feixe arbitrário pode não corresponder a nenhuma vogal do inventário, e
`none` é a resposta correta nesse caso. O último exemplo mostra por que isso
importa — forçar `Back` a `Plus` em `i` produz um feixe que nenhuma das três
vogais realiza.

A busca abaixo compara feixes inteiros por `==`, e `Phoneme` é uma lista: dois
feixes só são iguais se os traços estiverem na **mesma ordem**. Funciona porque
toda vogal do inventário foi escrita na ordem `Cons, High, Round, Back`, e
`fMatch` preserva essa ordem ao trocar um valor — mas é uma disciplina, não uma
garantia do tipo. Uma vogal nova, se escrita numa ordem diferente, deixaria de
bater com `==` e `realize` devolveria `none` silenciosamente. -/

def surfaceTable : List (Phoneme × Char) :=
  [(i, 'i'), (a, 'a'), (o, 'o'), (u, 'u'), (e, 'e'), (c, 'c')]

def realize (x : Phoneme) : Option Char :=
  (surfaceTable.find? (·.1 == x)).map (·.2)

example : realize i = some 'i' := rfl
example : realize (fMatch .Back .Plus i) = none := rfl


/-
### Exercício 3.19 (p. 61)

A harmonia vocálica em Yawelmani tem a seguinte forma simplificada. As vogais do
sufixo concordam em `Back` e `Round` com a vogal do radical — mas gatilho (vogal
do radical) e alvo (vogal do suffixo) têm de ter a mesma altura (`High`): vogais
altas do radical só condicionam harmonia em vogais altas do sufixo, e vogais
baixas do radical só condicionam harmonia em vogais baixas do sufixo. Exemplos
de [CK97] (lembrando: `xil` ≈ `c i c`, `dub` ≈ `c u c`, `xat` ≈ `c a c`, `bok'`
≈ `c o c` — a consoante é sempre `c`):

    xil  ++ hin → xilhin   'tangles'
    xat  ++ hin → xathin   'eats'
    dub  ++ hin → dubhun   'leads by hand'
    bok' ++ hin → bok'hin  'finds'
    xat  ++ al  → xatal    'might eat'
    xil  ++ al  → xilal    'might tangle'
    bok' ++ al  → bok'ol   'might find'
    dub  ++ al  → dubal    'might lead'

A regra não é uma tabela de substituição de letras (não é "`i` vira `u`"): é
propagação de traços entre dois feixes. Acompanhe `dub ++ hin → dubhun` contra
`xat ++ hin → xathin`, os dois pelo mesmo sufixo `hin` (vogal `i`):

    u = [High+, Round+, Back+]   (vogal do radical `dub`)
    a = [High-, Round-, Back+]   (vogal do radical `xat`)
    i = [High+, Round-, Back-]   (vogal do sufixo `hin`)

Em `dub ++ hin`: `u` e `i` concordam em `High` (`+`/`+`) — a harmonia se aplica,
e `i` copia `Round` e `Back` de `u`, tornando-se foneticamente `u`: daí
`dubhun`. Em `xat ++ hin`: `a` é `High-` e `i` é `High+` — os valores discordam,
a harmonia não se aplica, e `i` fica como está: daí `xathin`. A diferença entre
os dois casos não é uma regra especial para `u` ou para `a`; é consequência
única da condição sobre `High`.

`appendSuffixY` aplica essa harmonia: concatena `stem` e `suffix`, mas antes
ajusta cada vogal do sufixo pela primeira vogal do radical — se as duas tiverem
a mesma altura, a vogal do sufixo herda `Back` e `Round` da vogal do radical;
senão fica como está.
-/

def stemVowel (stem : List Phoneme) : Option Phoneme := sorry

def harmonize (stemV suffixPh : Phoneme) : Phoneme :=
  match fValue .High stemV, fValue .High suffixPh with
  | some hStem, some hSuffix =>
    if hStem == hSuffix then
      match fValue .Back stemV, fValue .Round stemV with
      | some b, some r => fMatch .Round r (fMatch .Back b suffixPh)
      | _, _ => suffixPh
    else suffixPh
  | _, _ => suffixPh

def appendSuffixY (stem suffix : List Phoneme) : List Phoneme := sorry

/-- dub ++ hin → dubhun -/
example : (appendSuffixY [c, u, c] [c, i, c]).map realize
    = [some 'c', some 'u', some 'c', some 'c', some 'u', some 'c'] := sorry

/-- xat ++ hin → xathin -/
example : (appendSuffixY [c, a, c] [c, i, c]).map realize
    = [some 'c', some 'a', some 'c', some 'c', some 'i', some 'c'] := sorry


/- ### Exercício — `appendSuffix` em texto

`appendSuffixY` trabalha sobre `List Phoneme`. Este exercício pede a mesma
harmonia partindo de `String`, como já fizemos para o finlandês na seção 2.15.
O texto de entrada precisa primeiro ser cortado em "letras" — e `k'` mostra
que uma letra pode ter mais de um caractere. `tokenize` reconhece esse único
caso especial; as duas equações consomem `rest`, estruturalmente menor, então
não precisa de `partial`. -/

def tokenize : List Char → List String
  | []                => []
  | c :: '\'' :: rest => String.ofList [c, '\''] :: tokenize rest
  | c :: rest         => String.ofList [c] :: tokenize rest

/-! Só as vogais atravessam o modelo de traços; qualquer outro token é copiado
sem conversão. Convertê-los também seria um erro: como toda consoante colapsa no
mesmo `c` genérico, reconvertê-la devolveria sempre `'c'`, apagando a consoante
original em vez de preservá-la — `"dub"` viraria `"cuc"`. Por isso
`unrealizeVowel` só reconhece os 5 tokens de vogal, e tokenizar `k'` como uma
unidade não muda o resultado de `appendSuffix` (consoantes nunca são
harmonizadas): só deixa explícito, também do lado da entrada, que fonema não é o
mesmo que caractere.
-/

def unrealizeVowel (tok : String) : Option Phoneme :=
  if      tok == "i" then some i
  else if tok == "a" then some a
  else if tok == "o" then some o
  else if tok == "u" then some u
  else if tok == "e" then some e
  else none

def appendSuffix (stem suffix : String) : Option String := sorry

example : appendSuffix "dub" "hin" = some "dubhun" := sorry
example : appendSuffix "xat" "hin" = some "xathin" := sorry
example : appendSuffix "bok'" "al" = some "bok'ol" := sorry

/-- i (High+) vs a (High-): sem harmonia -/
example : appendSuffix "xil" "al" = some "xilal" := sorry

/-- gatilho e alvo já são o mesmo `a` -/
example : appendSuffix "xat" "al" = some "xatal" := sorry

end Chapter02
