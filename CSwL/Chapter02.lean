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
Exemplos extraídos de[FAA2025]. No `Chapter03.lean` vamos usar `Prop` desde as
primeiras linhas, sem explicá-lo; esta seção dá o mínimo necessário.

Uma proposição é um enunciado que pode ser verdadeiro ou falso, como `1 = 1`
(verdadeiro) ou `1 = 2` (falso). A constante `p1 : Prop`, um nome para a
proposição `(1 = 1) : Prop`.
-/

def p1 : Prop := 1 = 1

#check (1 = 1)
#check p1

/- Toda proposição verdadeira tem uma prova, e uma prova é um _termo_: um
elemento do tipo da proposição. Provar `1 = 1` é exibir um termo de
tipo `1 = 1`, exatamente como construir um termo de tipo `Nat → Nat` na
seção anterior. A seguir iremos entender `rfl`. -/

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
abaixo é a de `FAA2025/Lectures/Week01/Sheet1-3.lean`, que apresenta as táticas
nesta sequência; `decide`, `omega`, `obtain`, `cases`, `simp` e `induction` não
vêm de lá (o curso os introduz onde a necessidade aparece) e ficam ao final,
fora da ordem do FAA2025:

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

Fonte: `[FAA2025]`. Dica: um `↔` se parte em dois objetivos com `constructor`;
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

/-!
### Exercício' — `apply` com várias premissas

Adaptado de [FAA2025].
-/

example (P Q R S : Prop) (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := sorry

/-! Nem toda prova precisa de lógica proposicional abstrata — às vezes o que
falta é desdobrar uma definição local antes de concluir.

### Exercício' — Prova direta com `unfold`

Fonte: [FAA2025], com `f` definida localmente igual ao arquivo. Dica: `intro h`,
`unfold f at h` (ou `rw [f] at h`), depois concluir por `omega` ou `assumption`.
-/

def f (x y : Nat) : Prop := x = y

example (x : Nat) : f x 1 → x ≠ 2 := sorry

/-!
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

/-!
### Exercício' — Day

Complete `isWeekend`, que responde se o dia é sábado ou domingo.
-/

def isWeekend (d : Day) : Bool :=
 match d with
 | .saturday => true
 | .sunday => true
 | _ => false


/-!
### Os naturais são um tipo indutivo

Isso não vale só para os tipos que se declara: os que vêm com a linguagem são
declarados do mesmo modo, e `#print` mostra a declaração. `Bool` é a
enumeração de duas formas; `Nat` é o caso em que uma das formas se refere ao
próprio tipo que está sendo definido: -/

#print Bool
#print Day
#print Nat

/-! Ou seja: um natural é `Nat.zero`, ou é `Nat.succ n` para algum natural
`n`, e nada mais. O `2` que se escreve é notação para
`Nat.succ (Nat.succ Nat.zero)`: -/

example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

/-!
A primeira: _casar padrão_ é perguntar por qual das formas um valor foi
construído. Como as formas são conhecidas e são todas, Lean consegue conferir
se uma definição por casos tratou o tipo inteiro.

A segunda: como cada `Nat.succ n` guarda dentro de si um `n` menor, a recursão
sobre naturais tem por onde descer.

## 2.6 Prova por indução

/-! A última tática da tabela, `induction`, prova algo para **todo** valor
de um tipo indutivo, e não para um valor de cada vez — é o que o capítulo 4
usa para a Proposição 4.2 (número de parênteses), com `simp` fechando os
casos indutivos.

### Exercício' — Indução sobre `Nat` (inventado)

Prove que `n + 0 = n` para todo `n`, usando `induction n`. No caso `0`,
`rfl` fecha; no caso `n + 1`, a hipótese de indução (`ih`) resolve com
`simp [ih]` ou `omega`.
-/

example (n : Nat) : n + 0 = n := sorry

/-! Este é todo o aparato de prova que o capítulo usa. Ele volta no capítulo 3,
com os tipos, e no capítulo 4, com `induction` sobre `Form`; é também o
assunto do capítulo 6, onde verificar se uma sentença é verdadeira num
modelo passa a ser exatamente essa questão — enunciar algo versus
calculá-lo.

Quem quiser praticar Lean por si, fora do curso, o _Natural Number Game_
(<https://adam.math.hhu.de/#/g/leanprover-community/nng4/>) é o caminho curto.
Nada do que vem depois depende dele.-/

/-
## 2.7 Recursão

Ref. CSwFP/3 §3.5 (p. 40).

Uma definição recursiva precisa de dois cuidados: ter caso base, e chegar
nele. O segundo não é uma recomendação — é uma exigência que o compilador
verifica, e a definição é rejeitada se ele não conseguir ver que a recursão
termina.

Em `Nat`, os dois casos do tipo dão as duas coisas de uma vez. Casar por `0` e
`n + 1` — que é como se escreve `Nat.zero` e `Nat.succ n` — cobre o tipo
inteiro: o caso base é `0`, e a chamada recursiva recebe o `n` que estava
dentro do `succ`, necessariamente menor. Não há um terceiro caso a esquecer, e
não há argumento para o qual a função não responda.
-/

/-- O fatorial é o exemplo mínimo dessa forma: um caso base e um caso que
chama a si mesmo com um argumento menor. -/
def factorial : Nat → Nat
  | 0       => 1
  | .succ n => (n + 1) * factorial n

#eval factorial 5
#eval factorial 0

/-- A mesma função sem casar padrão, decidindo o caso base com um `if`. Funciona,
e serve de contraste: aqui o argumento da chamada recursiva é `x - 1`, e que ele
seja menor que `x` é um fato a ser verificado, não algo que a forma da definição
já garanta. Neste caso Lean verifica sozinho; em definições menos óbvias, não —
e aí a prova de terminação passa a ser trabalho do programador. Casar por `0` e
`n + 1` dispensa a questão, e é por isso que é a forma preferida no texto. -/
def factorial' (x : Nat) : Nat :=
  if x = 0 then 1
  else x * factorial' (x - 1)

def gen : Nat → String
  | 0     => "Sentences can go on"
  | n + 1 => gen n ++ " and on"

def genS (n : Nat) : String := gen n ++ "."

#eval genS 3

/-- Recursão que encaixa uma fala dentro da outra: o chefe dos canibais
repete, entre aspas, o discurso do chefe anterior. -/
def story : Nat → String
  | 0     => "Let's cook and eat that final missionary, and off to bed."
  | k + 1 =>
    "The night was pitch dark, mysterious and deep.\n"
    ++ "Ten cannibals were seated around a boiling cauldron.\n"
    ++ "Their leader got up and addressed them like this:\n'"
    ++ story k ++ "'"

/-! podemos usar `#eval story 2` direto, mas as quebras de linha não seriam
    interpretadas. o símbolo `<|` faz com que a expressão `story 2` seja
    interpretada antes de passada para a função `IO.println`. -/

#eval IO.println <| story 2

/-!
### Exercício' — sumTo

`sumTo n` devolve `0 + 1 + ... + n`.
-/

def sumTo : Nat → Nat
  | 0 => sorry
  | n + 1 => sorry

example : sumTo 4 = 10 := sorry

/-!
## 2.7 Listas e polimorfismo

Ref. CSwFP/3 §3.6 (p. 41) + §3.4 (p. 39, polimorfismo genérico).

`List α` é o tipo das listas de elementos do tipo  `α`, e é um tipo indutivo
como os da seção anterior: uma lista é vazia, `[]`, ou é um elemento seguido de
uma lista, `x :: xs`. Nada mais é uma lista. -/

#print List

/-! É por isso que a recursão sobre lista tem exatamente a forma da recursão
sobre `Nat` — dois casos, e o segundo dá acesso a algo estritamente menor, aqui
a cauda.

O `α` em `List α` é um parâmetro: `List Nat` e `List String` são tipos
diferentes, produzidos pelo mesmo `List`. Uma função que não olha para dentro
dos elementos não tem por que se comprometer com um deles, e o tipo pode dizer
isso.

`{α : Type}` declara o parâmetro entre chaves, o que o torna _implícito_: Lean
o descobre a partir do argumento, e quem chama não escreve. -/

def size {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + size xs

#eval size [10, 20, 30]
#eval size ["Chomsky", "Montague"]

/-! O mesmo `size` serve para as duas listas, sem conversão no meio. Essa é a
forma que quase todo tipo do curso vai ter: o fragmento da língua se declara uma
vez e vale para o domínio de entidades que o modelo fornecer.

### Exercício' — sumList

`sumList` soma os elementos de uma lista.
-/

def sumList : List Nat → Nat
  | []      => sorry
  | x :: xs => sorry

example : sumList [1, 2, 3, 4] = 10 := sorry

/-!
### Exercício' — countZeros

`countZeros` conta quantos zeros a lista tem.
-/

def countZeros : List Nat → Nat
  | []      => sorry
  | x :: xs => sorry

example : countZeros [0, 1, 0, 2, 0] = 3 := sorry

/-!
### Exercício' — applyToAll

`applyToAll` aplica `f` a cada elemento da lista, por recursão. (Existe uma
função da biblioteca que faz isso, `List.map` — mas o exercício é escrever a
sua.)
-/

def applyToAll (f : Nat → Nat) : List Nat → List Nat
  | []      => sorry
  | x :: xs => sorry

example : applyToAll (· + 1) [1, 2, 3] = [2, 3, 4] := sorry

/-!
## 2.8 Quando não há resposta: Option

Uma função de tipo `List α → α` promete devolver um elemento para qualquer
lista que receba. Para a lista vazia não existe elemento nenhum, e a promessa
é impossível — não por falta de cuidado do programador, mas porque o tipo
afirma algo falso.

A correção é no tipo, não no corpo: `List α → Option α` promete devolver _ou_
um elemento (`some x`) _ou_ nada (`none`). Quem chama fica obrigado a tratar
os dois casos. O ganho é que o caso sem resposta deixa de ser invisível: ele
está na assinatura, e não há como esquecê-lo.
-/

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

/-!
  Nem toda função da biblioteca é honesta desse modo: algumas devolvem um valor
  default no caso ruim, em vez de `Option`. `String.back` é uma delas, e vale
  conhecer as que são assim. -/

#eval "rad".back
#eval "".back      -- não é erro, é o `Char` default

/-!
## 2.10 Processamento de listas com map e filter

Ref. CSwFP/3 §3.7 (p. 42–43).

Quatro operações cobrem quase todo uso de lista no curso. Todas se escreveriam
por recursão, como `size` acima, mas já existem — e o hábito a adquirir é
procurar antes de escrever.

`map` aplica uma função a cada elemento; `filter` guarda os que satisfazem uma
condição. -/

def entities : List String := ["Dorothy", "Toto", "Aunt Em", "Scarecrow"]

#eval entities.map String.length
#eval entities.filter (fun e => e.length > 4)

/-! `all` e `any` perguntam se _todos_ os elementos satisfazem uma condição, ou
se _algum_ satisfaz. Devolvem `Bool`, e portanto se calculam. -/

#eval entities.all (fun e => e.length > 2)
#eval entities.any (fun e => e.startsWith "T")

/-! E a composição: `f ∘ g` é a função que aplica `g` e depois `f`, de modo que
`(f ∘ g) x` é `f (g x)`. Ela produz função nova sem nomear argumento nenhum —
`double ∘ double` é quadruplicar. -/

#eval (double ∘ double) 5

#eval entities.map (size ∘ String.toList)

/-!
## 2.11 Composição, conjunção, disjunção, quantificação

Ref. CSwFP/3 §3.8 (p. 44–45).

Vale parar aqui, porque `all` e `any` não são conveniência de programação: são
como a quantificação vai ser **calculada**.

Sobre um domínio finito, "todo `P` é `Q`" é: tome os elementos que são `P` e
pergunte se todos são `Q` — `filter` seguido de `all`. E "algum `P` é `Q`" é
`filter` seguido de `any`. Escrito, é isto: -/

def every (p q : String → Bool) : Bool := (entities.filter p).all q
def exists' (p q : String → Bool) : Bool := (entities.filter p).any q

def isLong (e : String) : Bool := e.length > 4
def hasSpace (e : String) : Bool := e.any (· == ' ')

#eval every  isLong hasSpace
#eval exists' isLong hasSpace

/-! No capítulo 7 o determinante *every* é literalmente essa definição, com
entidades no lugar de `String`. Que um quantificador seja uma função de dois
predicados em um valor de verdade é a ideia central daquele capítulo; que ele se
_calcule_ assim, percorrendo um domínio finito, é a do capítulo 6. Aqui basta ver
que a operação é ordinária, e que já se sabe escrevê-la.

## 2.12 Classes de tipos

Ref. CSwFP/3 §3.9 (p. 45).

`count` conta ocorrências em qualquer lista cujos elementos se possam
comparar. Essa exigência entra na assinatura entre colchetes, `[BEq α]`: uma
instância de igualdade para `α`, que Lean encontra sozinho no ponto de uso.

Duas noções de igualdade convivem, e vale separá-las desde já:

* `BEq α` devolve `Bool` e se escreve `==`. Serve para calcular.
* `DecidableEq α` devolve uma _prova_ de igualdade ou de desigualdade.
  Permite usar `=` num `if` e usar o resultado numa demonstração.

Essa diferença — entre calcular uma resposta e afirmar algo que se prova —
volta no capítulo 3 como a distinção entre `Bool` e `Prop`, e é o assunto do
capítulo 6, onde verificar uma sentença num modelo será exatamente calcular
o que em geral só se enunciaria.
-/

def count [BEq α] (x : α) : List α → Nat
  | []      => 0
  | y :: ys => if x == y then count x ys + 1 else count x ys

#eval count 2 [1, 2, 2, 3]
#eval count "thou" ["thou","art","thou"]

/-!
## 2.13 Cadeias e textos

Ref. CSwFP/3 §3.10 (p. 47–48).

`String` é uma sequência UTF-8 empacotada. Isso a torna eficiente para
guardar texto e inadequada para percorrer: não há padrão `c :: cs` para casar
diretamente numa `String`.

A divisão de trabalho é essa — `String` para armazenar, `List Char` para
computar. Converte-se com `.toList`, faz-se a recursão na lista, onde o
padrão existe, e volta-se com `String.ofList`.
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
def initS (s : String) : String := String.ofList s.toList.dropLast

#eval initS "flicka"

/-!
## 2.14 Um fragmento linguístico

Ref. CSwFP/3 §3.13 (p. 56–57).

Sujeito, predicado e sentença como tipos. A estrutura deixa de ser texto e
passa a ser um valor, e o verificador de tipos passa a recusar as combinações
que não são sentenças. Este é o embrião do capítulo 4.

`ToString` é a instância que diz como exibir um valor para leitores. É
distinta de `Repr`, que existe para depuração e mostra a estrutura interna.
-/

inductive Subject where
  | Chomsky | Montague
deriving Repr, DecidableEq

inductive Predicate where
  | Wrote (title : String)
deriving Repr

inductive Sentence where
  | S (subj : Subject) (pred : Predicate)

abbrev Sentences := List Sentence

instance : ToString Subject where
  toString
    | .Chomsky  => "Chomsky"
    | .Montague => "Montague"

instance : ToString Predicate where
  toString | .Wrote t => s!"wrote \"{t}\""

instance : ToString Sentence where
  toString | .S s p => s!"{s} {p}"

def makeP (title : String) : Predicate := .Wrote title
def makeS (s : Subject) (p : Predicate) : Sentence := .S s p

#eval IO.println $ toString (makeS .Chomsky (makeP "Syntactic Structures"))

/-!
## 2.15 Harmonia vocálica do finlandês e plural sueco

Ref. CSwFP/3 §3.11 (p. 52–55). Movida para o fim da sequência numerada —
desvio de ordem, decisão do professor, registrado em
`CSwL/README.md` § Desvios de CSwFP.

O livro apresenta a harmonia vocálica finlandesa e o plural sueco na mesma
seção, como dois exemplos do mesmo fenômeno: uma regra morfológica que
depende de um traço que a palavra já carrega.

Em finlandês, as vogais de uma palavra concordam em anterioridade: um sufixo
adicionado a um radical "posterior" (`a`, `o`, `u`) usa a forma posterior de
cada vogal que varia por esse traço; a um radical "anterior" (`ä`, `ö`, `y`),
a forma anterior. `front`/`back` traduzem uma vogal para a forma do outro
lado do par; `vh` decide qual delas aplicar, olhando o radical inteiro. -/

-- Vogais fora do ASCII: 'ä' = 228, 'å' = 229, 'ö' = 246, 'ø' = 248.
def aUml   : Char := Char.ofNat 228
def aRing  : Char := Char.ofNat 229
def oUml   : Char := Char.ofNat 246
def oSlash : Char := Char.ofNat 248

def front : Char → Char
  | 'a' => aUml
  | 'o' => oUml
  | 'u' => 'y'
  | c   => c

def back : Char → Char
  | c => if c == aUml then 'a'
         else if c == oUml then 'o'
         else if c == 'y' then 'u'
         else c

/-- Sufixa `suffix` ao radical `stem`, ajustando cada vogal do sufixo pela
harmonia vocálica do radical. -/
def appendSuffixF (stem suffix : String) : String :=
  let vh : Char → Char :=
    if stem.toList.any (fun c => c == 'a' || c == 'o' || c == 'u') then back
    else if stem.toList.any (fun c => c == aUml || c == oUml || c == 'y') then front
    else id
  stem ++ String.ofList (suffix.toList.map vh)

#eval appendSuffixF "talo" "ssa"    -- radical posterior: sufixo fica posterior
#eval appendSuffixF "kylä" "ssa"    -- radical anterior: sufixo vira "ssä"

/-! Com o `inductive` e a recursão em texto, dá para escrever também uma
regra de plural de verdade. O sueco distribui os substantivos em cinco
classes de declinação, e a forma do plural depende da classe.
-/

/-- As cinco classes de declinação do plural em sueco. -/
inductive DeclClass where
  | One | Two | Three | Four | Five
deriving Repr, DecidableEq

#check DeclClass.Three
#eval  DeclClass.Three

def swedishVowels : List Char :=
  ['a','i','o','u','e','y', aUml, aRing, oUml, oSlash]

/-- A forma do plural é determinada pela classe de declinação. Na terceira
classe ela depende também de a palavra terminar ou não em vogal: uma regra
morfológica que consulta a forma fonológica. -/
def swedishPlural (noun : String) : DeclClass → String
  | .One   => initS noun ++ "or"
  | .Two   => initS noun ++ "ar"
  | .Three => if swedishVowels.contains noun.back then noun ++ "r"
              else noun ++ "er"
  | .Four  => noun ++ "n"
  | .Five  => noun

#eval swedishPlural "flicka" .One
#eval swedishPlural "pojke"  .Two
#eval swedishPlural "rad"    .Three
#eval swedishPlural "ko"     .Three
#eval swedishPlural "hus"    .Five


/-!
## 2.16 Aplicação: representando fonemas

Ref. CSwFP/3 §3.14 (p. 58–61). Movida para o fim da sequência numerada —
mesmo desvio de ordem que a seção anterior.

Harmonia vocálica é o fenômeno em que as vogais de uma palavra têm de
concordar em algum traço — em turco e em finlandês, no traço de anterioridade.
Descrevê-la como substituição de letras erra o alvo: o processo não vê letras,
vê traços fonológicos, e a letra é só a realização de superfície.

Então o fonema não é um `Char`. É um conjunto de traços, e cada traço é um par
atributo/valor. Com essa representação, a harmonia vocálica é uma operação de
uma linha: forçar um traço a um valor.

Um `structure` diz melhor o que se quer aqui que um construtor com dois
argumentos posicionais — os campos ganham nome, e `f.attr` e `f.value` passam
a existir.
-/

inductive Attr where
  | Back | High | Round | Cons
deriving Repr, DecidableEq, BEq

inductive Value where
  | Plus | Minus
deriving Repr, DecidableEq, BEq

structure Feature where
  attr  : Attr
  value : Value
deriving Repr, DecidableEq, BEq

abbrev Phoneme := List Feature

section
open Attr Value

def i : Phoneme := [⟨Cons, Minus⟩, ⟨High, Plus⟩,  ⟨Round, Minus⟩, ⟨Back, Minus⟩]
def a : Phoneme := [⟨Cons, Minus⟩, ⟨High, Minus⟩, ⟨Round, Minus⟩, ⟨Back, Plus⟩]
def u : Phoneme := [⟨Cons, Minus⟩, ⟨High, Plus⟩,  ⟨Round, Plus⟩,  ⟨Back, Plus⟩]

end

/-- Consulta o valor de um traço no feixe. `Option` outra vez: o traço pode
não estar especificado. -/
def fValue (attr : Attr) : Phoneme → Option Value
  | []      => none
  | f :: fs => if f.attr == attr then some f.value else fValue attr fs

#eval fValue .High i
#eval fValue .High a
#eval fValue .Back ([] : Phoneme)

/-- Força um traço a um valor. É a operação da harmonia vocálica. -/
def fMatch (attr : Attr) (value : Value) (fs : Phoneme) : Phoneme :=
  fs.map fun f => if f.attr == attr then { f with value := value } else f

#eval fMatch .Back .Plus i

/-- A realização de superfície: qual letra corresponde a este feixe.

A função é total, e tem de ser: um feixe arbitrário pode não corresponder a
nenhuma vogal do inventário, e `none` é a resposta correta nesse caso. O
último exemplo mostra por que isso importa — forçar `Back` a `Plus` em `i`
produz um feixe que nenhuma das três vogais realiza. -/
def realize (x : Phoneme) : Option Char :=
  if x == i then some 'i'
  else if x == a then some 'a'
  else if x == u then some 'u'
  else none

#eval realize i
#eval realize (fMatch .Back .Plus i)

/-!
### Exercício 3.19 (p. 61)

`appendSuffixY` aplica a harmonia vocálica em Yawelmani: sufixa `-y` à
palavra, forçando o traço `Round` do sufixo a concordar com o `Round` da
última vogal do radical (as auxiliares `fValue`/`fMatch` acima já fazem o
trabalho — falta compor).
-/

def appendSuffixY (stem : List Phoneme) (suffixVowel : Phoneme) : List Phoneme :=
  sorry

end Chapter02
