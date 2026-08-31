import CSwLMeta
import Bib
import Mathlib.Tactic

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Programação Funcional no Lean" =>
%%%
tag := "IntroL"
htmlSplit := .never
file := "IntroL"
%%%

Neste capítulo, apresentamos o essencial sobre a linguagem de programação Lean. Nosso objetivo é apresentar o suficiente para que o leitor possa acompanhar os exemplos do restante do livro. Para uma apresentação completa, sugerimos a leitura de {citep Bib.FPiL}[] e {citep Bib.LLR}[].

```lean
namespace IntroL
```

# Termos e Tipos

Em Lean, um termo é uma expressão sintaticamente válida que representa um objeto e possui um tipo.

Semanticamente, tipos como conjuntos, mas eles não são conjuntos. Podemos pensar em tipos como classes para classificarmos termos. Com tipos podemos impor uma disciplina que a matemática segue apenas implicitamente. No papel podemos escrever `1 ∈ 2`, mas em Lean a tipagem marca a expressão como um erro.

Alguns tipos básicos já estão definidos no sistema como `ℕ`, `ℤ`, `ℚ` ou `Bool`. Se `σ` e `τ` são tipos, `σ → τ` representa o tipo das funções de `σ` em `τ`. Um tipo é de ordem superior quando tem `→` aninhada à esquerda de outra `→`, como em `(ℤ → ℤ) → ℚ`: o tipo das funções que recebem uma função de `ℤ` em `ℤ` e devolvem um `ℚ`.

Ao abrir um arquivo Lean, podemos além de escrever declarações, podemos interagir diretamente com o sistema através de comandos. Comandos são prefixados com `#`. O comando `#eval` calcula o valor de um termo.

```lean
#eval 1 + 2
#eval "Olá, " ++ "mundo"
```

Uma `def`inição introduz um nome no ambiente. Os dois-pontos anunciam o tipo,
e o `:=` dá o valor. `100` é um termo do tipo `Nat`, e `"Chomsky"` é um termo
do tipo `String`. Em alguns contextos, o tipo não precisa ser declarado quando
Lean consegue descobri-lo sozinho. Escrever `def n := 100` funciona, porque
Lean irá interpretar `100 : ℕ` e logo estabelecer que a constante `n : ℕ` —
mas escrever o tipo é conveniente e ajuda a tornar o código mais legível. O comando `#check` pergunta ou confirma o tipo, sem calcular nada.

```lean
def author : String := "Chomsky"

#eval  author
#check author
#check (author : String)
```

Tipos também são termos, e portanto têm tipo. O tipo de `true` é `Bool`, o
tipo de `Bool` é `Type`, e o de `Type` é `Type 1`. Esta hierarquia de
universos existe para que não exista um tipo de todos os tipos, o que
produziria um paradoxo. Para nós, em geral, basta saber que a pergunta "qual o
tipo disto?" tem sempre resposta.

```lean
#check true
#check Bool
#check Nat
#check Type
```

# Funções

O tipo `Nat → Nat` representa todas as funções que recebem um número natual e devolvem um número natural. O termo `fun x => x * x : Nat → Nat` é uma particular função deste tipo. Ao aplicar o termo `12 : Nat`, temos o `144 : Nat` como resposta. Ao invés de `fun` podemos usar `λ` e ao invés de `=>` podemos usar `↦`, em Lean podemos usar os caracteres unicode.

```lean
#check (λ x ↦ x * x) 12
#eval (λ x ↦ x * x) 12
```

Mas podemos nomear abstrações, principalmente quando queremos que elas possam ser reusadas. E em Lean podemos usar caracteres unicode como mostramos a seguir.

```lean
def square₁ : Nat → Nat :=
  fun x => x * x

def square₂ : ℕ → ℕ :=
  λ x ↦ x * x
```

Normalmente pode ser conveniente nomear os parâmetros de uma função. A seguir, parâmetros de mesmo tipo podem ser agrupados.

```lean
def square₃ (x : ℕ) : ℕ := x * x

def agePlusNameSize (age : ℕ) (name : String) : ℕ :=
  age * name.length

def maximum (n k : Nat) : Nat :=
  if n < k then
    k
  else n
```

Nomes são definidos em `namespaces`. As definições deste capítulo estarão no
namespace `IntroL`. A notação `name.length` acima infere pelo tipo de `name` que
estamos falando da função `length` definida no namespace `String` mesmo nome
do tipo `String`. Ver {citep Bib.FPiL}[].

Perguntado sobre um nome que foi definido, o `#check` responde com a
assinatura, e não com o tipo seta. Envolver o nome em parênteses força a
segunda forma. Mas as duas dizem o mesmo. As três versões de `square` tem o
mesmo tipo e como veremos, podemos provar que são iguais.

```lean
#check square₃
#check (square₃)
```

As vezes podemos querer introduzir uma constante ou tipo sem especificar seu comportamento o valor. Para isso usamos `opaque`, um símbolo com o tipo mas sem implementação. Exemplos de {citep Bib.love2026}[].

```lean
opaque a : ℕ
opaque b : ℕ
opaque f : ℕ → ℕ
opaque g : ℕ → ℕ → ℕ
```

Conferir tipo não demanda computação, logo o comando `#check` funciona retornando o tipo da expressão sem avaliá-la.

```lean
#check g a
```

::::exercise (rating := 1) (name := "sumOfSquares")

Defina `sumOfSquares` que recebe dois naturais e devolve `m² + n²`.

```lean
def sumOfSquares (m n : Nat) : Nat :=
 solution!(
  (square₁ m) + (square₁ n)
 )

example : sumOfSquares 3 4 = 25 := by
 solution!
  rfl
```
::::

Lean é uma linguagem muito extensiva, na verdade, boa parte de Lean é escrita em Lean, usando os recursos de _meta programação_. Os operadores `+` ou `*` entre outros são símbolos sintáticos associados a definições. Lean tem um mecanismo de `classes` para definir operadores polimorficos como o `+` para os naturais (interpretado como a função `Nat.add`) ou para números de ponto flutuante.

```lean
#eval Nat.add 2 2
#eval Float.add 2.1 2
#eval 2.1 + 2
```

Podemos forçar o tipo do primeiro argumento, definimos qual multiplicação estamos interessados. O segundo argumento, `10`, recebe o tipo correspondente.

```lean
#eval (1 : Int) * 10
#eval (1 : Float) * 10
```

No comando abaixo, o tipo de `x` é algo como `?m.7`. Isto significa que Lean sem dizer o tipo de `x`, Lean não tem como saber qual o `*` desejado, `Nat`, `Int`, ou qualquer outro tipo com multiplicação. O `?m.7` é uma _metavariável_: um buraco que Lean deixa em aberto à espera de informação que decida a questão.

```lean
#check fun x => x * x
```

Anotar o argumento resolve, e a resposta passa a ser o tipo esperado. O
contexto também resolve. Aplicada a `4`, a função agora é sobre `Nat` assumida a interpretação padrão de números como `Nat`.

```lean
#check fun (x : Nat) => x * x
#check (fun x => x * x) 4
```

Se função é valor, então nada impede que ela seja _argumento_ de outra
função. `h` recebe uma função de `Nat → Nat` e um valor, e é isso que o
torna uma função de ordem superior.

```lean
def h (f : Nat → Nat) (x : Nat) : Nat := f x
#eval h (λ x => x + 1) 10
```

Uma função também pode ser produzida como resultado. O que é equivalente a uma avaliação parcial. Abaixo, a função `h₁` recebe dois naturais para produzir a saída. A função `h₂` recebe um natural, para então devolver a função que ao receber um natural irá produzir como saída a soma dos dois valores recebidos. O interessante que não preciso escrever `h₁` como `h₂`, é perfeitamente aceitável passar apenas um dos argumentos para `h₁` e ver que o tipo da expressão resultante.

```lean
def h₁ (x y : Nat) : Nat :=
  x + y

def h₂ (x : Nat) : (Nat → Nat) :=
  fun y => x + y

#check h₁ 1
```

::::exercise (rating := 1) (name := "construindo-termos")

Adaptado de {citep Bib.love2026}[]. Cada `def` declara `{α β γ : Type}`, são funções parametrizadas por tipo. Para as quatro funções abaixo, cujo tipo foi definido, pede-se fornecer o termo para o tipo correspondente. Dica, use `_` para identificar no _InfoView_ qual tipo o termo na posição deverá ter.

O `section` permite criar uma seção, onde definições podem compartilhar, por exemplo, a declaração de variáveis. Veja o tipo de `projFst`.

```lean
section
variable {α β γ : Type}

def I : α → α :=
  fun x => x

def K : α → β → α :=
  fun a _b ↦ a

def C : (α → β → γ) → β → α → γ :=
  solution!(λ f => λ b => λ a => f a b)

def projFst : α → α → α :=
  solution!(fun a _b => a)

def projSnd : α → α → α :=
  solution!(fun _a b => b)

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  solution!(fun f a _g b => f a b)

end
```
::::

# Expressões

Uma _expressão_ é  uma construção sintática da linguagem. Toda expressão é um termo. Um _termo canônico_ é um termo que já está na forma final de sua computação, não podendo ser reduzido. Construções sintáticas que normalmente não tem valor em linguagens imperativas, também são termos em Lean.

O `let` nomeia um valor dentro de uma expressão, e a expressão inteira tem valor. O ponto-e-vírgula é uma alternativa a quebra de linha e alinhamento de identação.

```lean
#eval
  let a := (let a := 10; a) + (let b := 10; b)
  a
```

O `if-then-else` também é expressão. Os dois ramos têm de ter o mesmo tipo. É por isso que o resultado pode ser atribuído:

```lean
#eval
  let a := if 5 < 10 then 1 else 0
  a
```

# Estruturas

Uma `structure` agrupa vários valores num só, dando nome a cada campo.
`Point` tem dois campos, `x` e `y`, ambos `Float`. E a estrutura introduz um
novo tipo chamado `Point` e um `namespace` de mesmo nome.

```lean
structure Point where
  x : Float
  y : Float
deriving Repr
```

Além do tipo, algumas definições como `Point.mk`, função (construtor) que cria termos do tipo `Point` também são criadas pela declaração acima. Também podemos usar a sintaxe com chaves. Para mais detalhes, ver {citep Bib.FPiL}[capítulo~1].

```lean
def origin₁ : Point := { x := 0.0, y := 0.0 }
def origin₂ : Point := Point.mk 0.0 0.0

#eval origin₁
#check Point.mk
```

Cada campo tem uma função de projeção. No exemplo, `Point.x` e `Point.y`. Todas as funções introduzidas na declaração da estrutura ficam no namespace criado pelo comando `structure`.

```lean
#eval origin₁.x
```

A notação `⟨_, _⟩` é a *notação de anônima* para o construtor: serve quando o tipo
esperado já deixa claro qual construtor usar.

```lean
def origin₃ : Point := ⟨0.0, 0.0⟩
```

Uma função sobre `Point` também pode desmontar o argumento com `⟨_, _⟩`, em
vez de projetar campo a campo:

```lean
def addPoints (p1 p2 : Point) : Point :=
  ⟨p1.x + p2.x, p1.y + p2.y⟩

#eval addPoints origin₁ ⟨1.0, 2.0⟩
```

Também podemos usar `with` para criar uma cópia da estrutura alterando só alguns campos. Isti é útil quando a `structure` tem muitos campos.

```lean
def scaleX (p : Point) (factor : Float) : Point :=
  { p with x := p.x * factor }

#eval scaleX ⟨2.0, 3.0⟩ 10.0
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
theorem IntroL.square₁_eq_square₂ : square₁ = square₂ :=
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
```

Duas notações de prova não são táticas: `⟨t, h⟩` monta um par (para provar
uma conjunção ou exibir a testemunha de um existencial), e `h.1`/`h.2`
desmontam um par que está numa hipótese.

## Exercício'

Termine a prova usando `rfl`.

```lean
example : 7 * 6 = 42 :=
  rfl
```

## Exercício' — `double n = n + n`

Prove que `double n = n + n`; uma variável aparece, então `rfl` não basta.

```lean
example (n : Nat) : square₁ n = n * n := by
  unfold square₁
  rfl
```

## Exercício' — `P → P`

Provar `P → Q` é: suponha `P`, derive `Q`. Provar `P ∧ Q` é provar as duas
coisas. Fonte: {citep Bib.FAA2025}[]

```lean
example (P : Prop) : P → P := by
  intro h
  exact h
```

::::exercise (rating := 1) (name := "p-implica-q-implica-p")

Complete a prova abaixo. Fonte: {citep Bib.FAA2025}[]

```lean
example (P Q : Prop) : P → (Q → P) := by
  solution!
    intro h _
    exact h
```

::::

## Exercício' — Conjunção a partir das partes

Fonte: {citep Bib.FAA2025}[]. Dica: `constructor` parte o objetivo `P ∧ Q`
em dois; cada um se fecha com `exact`.

```lean (name := c2check24)
#check And.intro
```

```leanOutput c2check24
And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
```

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  apply And.intro
  · exact hP
  · exact hQ
```

## Exercício' — Comutatividade da conjunção

Fonte: {citep Bib.FAA2025}[]. Dica: um `↔` se parte em dois objetivos com
`constructor`; em cada um, `intro h` seguido de `obtain ⟨_,_⟩ := h` desmonta
a conjunção da hipótese, e `constructor` reconstrói a conjunção invertida.

Veja também o que acontece ao avaliar `(10,20).1`. `And` em Lean é uma
`structure` com dois campos.

```lean
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
```

::::exercise (rating := 1) (name := "transitividade-implicacao")

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

::::exercise (rating := 1) (name := "apply-varias-premissas")

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

::::exercise (rating := 1) (name := "prova-direta-unfold")

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

::::exercise (rating := 1) (name := "desmontando-conjuncao-unfold")

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

## Exercício' — Existe um par par

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
  apply Exists.intro 5
  rfl
```

::::exercise (rating := 1) (name := "casos-sobre-ou")

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

# Tipos indutivos

Tipos indutivos vêm antes da recursão porque, em Lean, uma função
recursiva se escreve casando padrão sobre as formas de um tipo indutivo:
sem o tipo declarado, não há sobre o que recursar.

`inductive` declara um tipo listando as formas que seus valores podem ter.
Quando nenhuma forma carrega argumento, o tipo é uma enumeração; quando
carrega, é um registro variante; quando a forma se refere ao próprio tipo
sendo definido, é uma árvore. As três coisas são o mesmo mecanismo.

Essa é a construção mais importante do curso. Em {ref "Games"}[Gramáticas para jogos]
veremos que uma gramática escrita na notação usual — a Forma de
Backus-Naur — é literalmente um tipo `inductive`, e daí em diante todo
fragmento da língua é declarado assim.

A enumeração é o caso mais simples. `deriving Repr, DecidableEq` pede que a
exibição e o teste de igualdade sejam gerados em vez de escritos à mão.

Os dias da semana, nada mais são dias da semana.

```lean
inductive Day where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr
```

## Exercício' — Day

Complete `isWeekend`, que responde se o dia é sábado ou domingo.

```lean
def isWeekend (d : Day) : Bool :=
 match d with
 | .saturday => true
 | .sunday => true
 | _ => false
```

`Bool` é a enumeração de duas formas; `Nat` é o caso em que uma das formas
se refere ao próprio tipo que está sendo definido. E `#print` mostra a
declaração.

```lean (name := c2print2)
#print Bool
```

```leanOutput c2print2
inductive Bool : Type
number of parameters: 0
constructors:
Bool.false : Bool
Bool.true : Bool
```

```lean (name := c2print3)
#print Day
```

```leanOutput c2print3
inductive IntroL.Day : Type
number of parameters: 0
constructors:
IntroL.Day.monday : Day
IntroL.Day.tuesday : Day
IntroL.Day.wednesday : Day
IntroL.Day.thursday : Day
IntroL.Day.friday : Day
IntroL.Day.saturday : Day
IntroL.Day.sunday : Day
```

```lean (name := c2print4)
#print Nat
```

```leanOutput c2print4
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : ℕ
Nat.succ : ℕ → ℕ
```

Ou seja: um natural é `Nat.zero`, ou é `Nat.succ n` para algum natural `n`,
e nada mais. O `2` que se escreve é notação para `Nat.succ (Nat.succ
Nat.zero)`.

```lean
example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl
```

# Prova por indução

A última tática da tabela, `induction`, prova algo para todo valor de um
tipo indutivo, e não para um valor de cada vez.

## Exercício' — Indução sobre `Nat`

Prove que `n + 0 = n` para todo `n`, usando `induction n`. No caso `0`,
`rfl` fecha; no caso `n + 1`, a hipótese de indução (`ih`) resolve `omega`.

```lean
example (n : Nat) : n + 0 = n := by
 induction n with
 | zero => rfl
 | succ a ih =>
   -- try `apply?`
   omega
```

Quem quiser praticar Lean provas em Lean, pode jogar o [Natural Number
Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4/).

# Recursão

Uma definição recursiva precisa de duas coisas: ter caso base, e chegar
nele. O segundo não é uma recomendação — é uma exigência que o compilador
verifica, e a definição é rejeitada se ele não conseguir ver que a
recursão termina.

Em `Nat`, os dois casos do tipo dão as duas coisas de uma vez. Casar por
`0` (`Nat.zero`) e `n + 1` (`Nat.succ n`). O caso base é `0`, e a chamada
recursiva recebe o `n` que estava dentro do `succ`, necessariamente menor.
Não há um terceiro caso a esquecer, e não há argumento para o qual a
função não responda.

O fatorial é o exemplo mínimo dessa forma: um caso base e um caso que
chama a si mesmo com um argumento menor.

```lean
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

```lean (name := c2eval12)
#eval factorial 5
```

```leanOutput c2eval12
120
```

```lean (name := c2eval13)
#eval factorial 0
```

```leanOutput c2eval13
1
```

A mesma função sem casar padrão, decidindo o caso base com um `if`.
Funciona, e serve de contraste: aqui o argumento da chamada recursiva é `x
- 1`, e que ele seja menor que `x` é um fato a ser verificado, não algo que
a forma da definição já garanta. Neste caso Lean verifica sozinho; em
definições menos óbvias, não — e aí a prova de terminação passa a ser
trabalho do programador.

```lean
def factorial' (x : Nat) : Nat :=
  if x = 0 then 1
  else x * factorial' (x - 1)
```

O casamento de padrão de `factorial` é um _açucar sintático_, na verdade a
expressão `match` está oculta na definição. A seguir, usamos de forma
explicita.

Como exemplo, vamos implementar em Lean um gerador recursivo de sentença.

```lean
def gen (x : Nat) : String :=
  match x with
  | 0     => "Sentences can go on"
  | n + 1 => gen n ++ " and on"

def genS (n : Nat) : String := gen n ++ "."
```

```lean (name := c2eval14)
#eval genS 3
```

```leanOutput c2eval14
"Sentences can go on and on and on and on."
```

A função de story a seguir fornece outro exemplo de recursão.

```lean
def story : Nat → String
  | 0     =>
    "Let's cook and eat that final missionary, " ++
    "and off to bed."
  | k + 1 =>
    "The night was pitch dark, mysterious and deep.\n" ++
    "Ten cannibals were seated around a boiling " ++
    "cauldron.\n" ++
    "Their leader got up and addressed them like " ++
    "this:\n'" ++
    story k ++ "'"
```

podemos usar `#eval story 2` direto, mas as quebras de linha não seriam
interpretadas. o símbolo `<|` faz com que a expressão `story 2` seja
interpretada antes de passada para a função `IO.println` que efetivamente
imprime uma linha na saída.

```lean (name := c2eval15)
#eval IO.println <| story 2
```

```leanOutput c2eval15
The night was pitch dark, mysterious and deep.
Ten cannibals were seated around a boiling cauldron.
Their leader got up and addressed them like this:
'The night was pitch dark, mysterious and deep.
Ten cannibals were seated around a boiling cauldron.
Their leader got up and addressed them like this:
'Let's cook and eat that final missionary, and off to bed.''
```

::::exercise (rating := 1) (name := "sumTo")

Implemente `sumTo n` para devolver `0 + 1 + ... + n` e termine a prova de
que a função está correta para a entrada `4`.

```lean
def sumTo : Nat → Nat :=
  solution!(fun
    | 0 => 0
    | n + 1 => (n + 1) + sumTo n)

theorem sumTo_test : sumTo 4 = 10 := solution!(by rfl)
```

:::gradeTheorem "1" sumTo_test
:::
::::

# Listas e polimorfismo

`List α` é o tipo das listas de elementos do tipo `α`, e é um tipo indutivo
como os da seção anterior: uma lista é vazia, `[]` (`List.nil`), ou é um
elemento seguido de uma lista, `x :: xs` (`List.cons`). Nada mais é uma
lista.

```lean (name := c2print5)
#print List
```

```leanOutput c2print5
inductive List.{u} : Type u → Type u
number of parameters: 1
constructors:
List.nil : {α : Type u} → List α
List.cons : {α : Type u} → α → List α → List α
```

É por isso que a recursão sobre lista tem exatamente a forma da recursão
sobre `Nat` — dois casos, e o segundo dá acesso a algo estritamente menor,
aqui a cauda.

O `α` em `List α` é um parâmetro: `List Nat` e `List String` são tipos
diferentes, produzidos pelo mesmo `List`. Uma função que não olha para
dentro dos elementos não tem por que se comprometer com um deles.

Como já falamos, `{α : Type}` declara o parâmetro entre chaves, o que o
torna _implícito_. Lean o descobre a partir do argumento, e quem chama não
escreve.

```lean
def size {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + size xs
```

```lean (name := c2eval16)
#eval size [10, 20, 30]
```

```leanOutput c2eval16
3
```

```lean (name := c2eval17)
#eval size ["Chomsky", "Montague"]
```

```leanOutput c2eval17
2
```

::::exercise (rating := 1) (name := "sumList")

`sumList` soma os elementos de uma lista. Complete e termine a prova.

```lean
def sumList : List Nat → Nat :=
  solution!(fun
    | []      => 0
    | x :: xs => x + sumList xs)

theorem sumList_test : sumList [1, 2, 3, 4] = 10 :=
  solution!(by rfl)
```

:::gradeTheorem "1" sumList_test
:::
::::

::::exercise (rating := 1) (name := "countZeros")

`countZeros` conta quantos zeros a lista tem. Idem.

```lean
def countZeros : List Nat → Nat :=
  solution!(fun
    | []      => 0
    | x :: xs =>
      if x == 0 then 1 + countZeros xs else countZeros xs)

theorem countZeros_test : countZeros [0, 1, 0, 2, 0] = 3 :=
  solution!(by rfl)
```

:::gradeTheorem "1" countZeros_test
:::
::::

# O tipo Option

Uma função de tipo `List α → α` promete devolver um elemento para qualquer
lista que receba. Para a lista vazia não existe elemento nenhum, e a
promessa é impossível. Não por falta de cuidado do programador, mas porque
o tipo afirma algo falso.

A correção é no tipo, não no corpo: `List α → Option α` promete devolver
_ou_ um elemento (`some x`) _ou_ nada (`none`). Quem chama fica obrigado a
tratar os dois casos. O ganho é que o caso sem resposta deixa de ser
invisível: ele está na assinatura, e não há como esquecê-lo.

```lean (name := c2print6)
#print Option
```

```leanOutput c2print6
inductive Option.{u} : Type u → Type u
number of parameters: 1
constructors:
Option.none : {α : Type u} → Option α
Option.some : {α : Type u} → α → Option α
```

```lean
def myLast {α : Type} : List α → Option α
  | []      => none
  | [x]     => some x
  | _ :: xs => myLast xs
```

```lean (name := c2eval18)
#eval myLast [1,2,3]
```

```leanOutput c2eval18
some 3
```

```lean (name := c2eval19)
#eval myLast ([] : List Nat)
```

```leanOutput c2eval19
none
```

```lean
def average (xs : List Int) : Option Rat :=
  if xs.isEmpty then none
  else some ((xs.sum : Rat) / (xs.length : Rat))
```

```lean (name := c2eval20)
#eval average [1,2,3,4]
```

```leanOutput c2eval20
some (5 / 2)
```

```lean (name := c2eval21)
#eval average []
```

```leanOutput c2eval21
none
```

Algumas funções devolvem um valor default no caso ruim, em vez de
`Option`. `String.back` é uma delas, e vale conhecer as que são assim.

```lean (name := c2eval22)
#eval "rad".back
```

```leanOutput c2eval22
'd'
```

```lean (name := c2eval23)
#eval "".back
```

```leanOutput c2eval23
'A'
```

# Processamento de listas e composição de funções

Algumas perações cobrem quase todo uso de lista no curso. Todas se
escreveriam por recursão, como `size` acima, mas estas função de ordem
superior simplificam nosso trabalho.

`map` aplica uma função a cada elemento; `filter` filtra a lista com os
que satisfazem uma condição. A `foldl` (e também temos a `foldr`) reduzem
a lista a um valor final a partir do processamento sucesso de uma função.

```lean
def entities : List String :=
  ["Dorothy", "Toto", "Aunt Em", "Scarecrow"]
```

```lean (name := c2eval24)
#eval entities.map String.length
```

```leanOutput c2eval24
[7, 4, 7, 9]
```

```lean (name := c2eval25)
#eval entities.filter (fun x => x.length > 4)
```

```leanOutput c2eval25
["Dorothy", "Aunt Em", "Scarecrow"]
```

```lean (name := c2eval26)
#eval entities.foldl (fun s a => a.length + s) 0
```

```leanOutput c2eval26
27
```

`all` e `any` perguntam se _todos_ os elementos satisfazem uma condição,
ou se _algum_ satisfaz, ambas devolvem `Bool`.

```lean (name := c2eval27)
#eval entities.all (fun e => e.length > 2)
```

```leanOutput c2eval27
true
```

```lean (name := c2eval28)
#eval entities.any (fun e => e.startsWith "T")
```

```leanOutput c2eval28
true
```

E a composição: `f ∘ g` é a função que aplica `g` e depois `f`, de modo que
`(f ∘ g) x` é `f (g x)`. Ela produz função nova sem nomear argumento
nenhum — `double ∘ double` é quadruplicar.

```lean (name := c2eval29)
#eval (square₁ ∘ square₂) 5
```

```leanOutput c2eval29
625
```

```lean (name := c2eval30)
#eval entities.map (size ∘ String.toList)
```

```leanOutput c2eval30
[7, 4, 7, 9]
```

# As duas leituras de uma função

Uma função admite duas leituras, e as duas importam:

* *extensional* — a função como tabela: o conjunto de pares
  entrada/saída. Uma conversão de Celsius para Fahrenheit é a tabela
  `{(0, 32), (100, 212), …}`, ponto.
* *intensional* — a função como instrução de cálculo. A mesma conversão
  é `x ↦ x * 9 / 5 + 32`, uma receita que produz a tabela sem precisar
  listá-la.

Em Lean, `def` escreve sempre a versão intensional — a instrução —, mas
duas instruções diferentes podem ser a mesma função, no sentido
extensional, se produzem a mesma tabela. É isso que `funext` verifica:
duas funções são iguais quando concordam em todo ponto do domínio.

```lean
def celsiusToFahrenheit (c : Int) : Int := c * 9 / 5 + 32
```

```lean (name := c3eval6)
#eval celsiusToFahrenheit 0
```

```leanOutput c3eval6
32
```

```lean (name := c3eval7)
#eval celsiusToFahrenheit 100
```

```leanOutput c3eval7
212
```

## Composição

Componhamos duas conversões: de Kelvin para Celsius, depois de Celsius
para Fahrenheit. `∘` é `Function.comp`, e `(f ∘ g) x = f (g x)` —
primeiro `g`, depois `f`, na ordem em que a leitura da notação sugere o
contrário.

```lean
def kelvinToCelsius (k : Int) : Int := k - 273

def kelvinToFahrenheit : Int → Int :=
  celsiusToFahrenheit ∘ kelvinToCelsius
```

```lean (name := c3eval8)
#eval kelvinToFahrenheit 373
```

```leanOutput c3eval8
212
```

# Classes de tipos

Nós já vimos isso lá no começo, mas `count` conta ocorrências em qualquer
lista cujos elementos se possam comparar. Essa exigência entra na
assinatura entre colchetes, `[BEq α]`: uma instância de igualdade para
`α`, que Lean encontra sozinho no ponto de uso.

Duas noções de igualdade convivem, e vale separá-las desde já:

* `BEq α` devolve `Bool` e se escreve `==`.
* `DecidableEq α` devolve uma _prova_ de igualdade ou de desigualdade.
  Permite usar `=` num `if` e usar o resultado numa demonstração.

Tente remover `[BEq α]` na definição abaixo.

```lean
def count {α : Type} [BEq α] (x : α) : List α → Nat
  | []      => 0
  | y :: ys => if x == y then count x ys + 1 else count x ys
```

```lean (name := c2eval31)
#eval count 2 [1, 2, 2, 3]
```

```leanOutput c2eval31
2
```

```lean (name := c2eval32)
#eval count "thou" ["thou","art","thou"]
```

```leanOutput c2eval32
2
```

Até aqui só *usamos* classes: `[BEq α]` pede uma instância que o Lean
encontra sozinho. Falta o outro lado — declarar uma.

Na verdade já declaramos várias, sem escrever nenhuma. Toda vez que um
tipo termina com `deriving Repr`, o Lean escreve por nós a instância de
`Repr` que o `#eval` usa para exibir valores daquele tipo. É o que
`Day` faz:

```lean (name := c2evalDayRepr)
#eval Day.saturday
```

```leanOutput c2evalDayRepr
IntroL.Day.saturday
```

O que sai é o nome do construtor, porque é isso que uma instância
derivada sabe fazer. Para escolher a forma de exibição, a instância
tem de ser escrita à mão, com a palavra-chave `instance`. A classe
para isso é `ToString`, que dá sentido a `toString`:

```lean
instance : ToString Day where
  toString
    | .monday    => "segunda"
    | .tuesday   => "terça"
    | .wednesday => "quarta"
    | .thursday  => "quinta"
    | .friday    => "sexta"
    | .saturday  => "sábado"
    | .sunday    => "domingo"
```

```lean (name := c2evalDayToString)
#eval toString Day.saturday
```

```leanOutput c2evalDayToString
"sábado"
```

A instância não tem nome: quem a procura é o Lean, pelo tipo, e não
nós pelo nome. Declarar uma instância é dizer "este tipo pertence a
esta classe, e eis como" — implementar os campos que a classe exige,
aqui só o `toString`.

`Repr` e `ToString` convivem porque servem a coisas diferentes: `Repr`
exibe para quem está programando e tende a mostrar a estrutura;
`ToString` produz o texto que se quer mostrar a quem lê. Nos capítulos
seguintes, quase toda instância escrita à mão será de `ToString` — para
que uma árvore sintática se imprima como a sentença que ela representa.

# Cadeias e textos

`String` é uma sequência UTF-8 empacotada, não uma lista de caracteres.
Isso a torna eficiente para guardar texto e inadequada para percorrer a
cadeia. Não há padrão `c :: cs` para casar diretamente numa `String`.

Mas podemos converter uma `String` em uma lista de caracteres e uma lista
de caracteres em uma `String`.

```lean
def hword : List Char → Bool
  | []      => false
  | c :: cs => c == 'h' || hword cs
```

```lean (name := c2eval33)
#eval hword "shrimptoast".toList
```

```leanOutput c2eval33
true
```

```lean (name := c2eval34)
#eval hword "antiquing".toList
```

```leanOutput c2eval34
false
```

```lean
def reversal : List Char → List Char
  | []     => []
  | c :: t => reversal t ++ [c]
```

```lean (name := c2eval35)
#eval String.ofList (reversal "Chomsky".toList)
```

```leanOutput c2eval35
"yksmohC"
```

Remove o último caractere.

```lean
def initS (s : String) : String :=
  String.ofList s.toList.dropLast
```

```lean (name := c2eval36)
#eval initS "flicka"
```

```leanOutput c2eval36
"flick"
```


```lean
end IntroL
```
