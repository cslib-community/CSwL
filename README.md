# CSwL — Computational Semantics with Lean

Tradução para [Lean 4](https://lean-lang.org) de *Computational Semantics
with Functional Programming*, de Jan van Eijck e Christina Unger (Cambridge
University Press, 2010). Material da disciplina **Processamento de Linguagem
Natural**, EMAp/FGV, 2026.2 — o programa está em
[emap-nlp/syllabus](https://github.com/emap-nlp/syllabus).

O texto é escrito para ser lido por si — os conceitos e suas implementações em
Lean, na forma mais idiomática que a linguagem permite. Segue o percurso de
van Eijck & Unger, capítulo por capítulo, mas não é uma tradução: nem do
texto, que é original, nem do código, que é reescrito e não transliterado.

Os exercícios ficam dentro de cada capítulo, na posição da seção do livro a
que correspondem — ver [Exercícios](#exercícios) abaixo.

## Como usar

Cada capítulo existe em três formas, geradas do mesmo arquivo `.lean`:

- **livro** — o texto para ler no navegador, sem instalar nada.
- **documentação** — a referência de API: uma entrada por declaração, com
  tipo e assinatura.
- **fonte** — para abrir no VS Code e editar, com o Lean respondendo ao vivo.

Para o ambiente local: [Install Lean](https://lean-lang.org/install), depois
`lake exe cache get` (baixa a Mathlib compilada — sem isso o `lake build`
compilaria a biblioteca do zero) e `lake build`.

Sem instalar nada, há dois caminhos: colar trechos em
[live.lean-lang.org](https://live.lean-lang.org/), ou abrir o repositório num
**Codespace** (botão *Code ▸ Codespaces*), que já vem com o Lean na versão do
projeto, a extensão do VS Code e a Mathlib compilada. A configuração está em
`.devcontainer/` e serve também para o **Reopen in Container** do VS Code
local.

Para gerar e ver o livro localmente:

```bash
make all     # gera as quatro variantes em _out/
make serve   # serve em http://127.0.0.1:8000/
```

## Capítulos

- **1. O estudo formal da língua natural** —
  [livro](https://emap-nlp.github.io/CSwL/cap01/) ·
  [documentação](https://emap-nlp.github.io/CSwL/docs/CSwL/Chapter01.html) ·
  [fonte](CSwL/Chapter01.lean)
- **2. Programação funcional** —
  [livro](https://emap-nlp.github.io/CSwL/cap02/) ·
  [documentação](https://emap-nlp.github.io/CSwL/docs/CSwL/Chapter02.html) ·
  [fonte](CSwL/Chapter02.lean)
- **3. Funções, tipos e abstração** —
  [livro](https://emap-nlp.github.io/CSwL/cap03/) ·
  [documentação](https://emap-nlp.github.io/CSwL/docs/CSwL/Chapter03.html) ·
  [fonte](CSwL/Chapter03.lean)
- **4. Sintaxe formal de fragmentos** —
  [livro](https://emap-nlp.github.io/CSwL/cap04/) ·
  [documentação](https://emap-nlp.github.io/CSwL/docs/CSwL/Chapter04.html) ·
  [fonte](CSwL/Chapter04.lean)
- Capítulo 5: Semântica formal de fragmentos — *a fazer*
- Capítulo 6: Model checking com lógica de predicados — *a fazer*
- Capítulo 7: A composição do significado — *a fazer*
- Capítulo 8: Extensão e intensão — *a fazer*
- Capítulo 9: Parsing — *a fazer*
- Capítulo 10: Relações e escopo — *a fazer*
- Capítulo 11: Semântica em continuation passing style — *a fazer*
- Capítulo 12: Representação de discurso e contexto — *a fazer*
- Capítulo 13: Comunicação como ação informativa — *a fazer*

## Exercícios

Os exercícios ficam dentro do capítulo, `CSwL/ChapterNN.lean`, imediatamente
após a seção do livro a que correspondem. Cada `sorry` é um item a completar
(ou `example`, para o que não é reaproveitado depois no próprio capítulo), e
o aviso que o Lean emite para ele é a sua lista do que falta:

```bash
lake build              # o livro; passa sem aviso, exceto sorry deixado de propósito
```

Quem resolve cada `sorry` depende da origem do exercício: um exercício
tirado do `CSwFP` (`### Exercício N.M`, com a página do livro) ou um
exercício novo do professor (`### Exercício*`, sem número — a numeração
fixa é difícil de manter enquanto o exercício ainda está sendo criado) é
sempre tarefa do aluno, a completar no próprio fork; o gabarito fica em
`Solutions/SolutionNN.lean` (gitignored). Qualquer outro `sorry`, fora de
uma seção `### Exercício`, é exemplo do texto e é resolvido em sala, pelo
professor, ao vivo.

Onde a resposta certa não é uma prova Lean, e sim discursiva, o exercício
fica marcado com **✎**: enunciado e resposta ficam juntos, no mesmo bloco
`/-! ... -/`, sem gabarito separado, e sem cobrança formal do aluno.

## Convenções

- **Um módulo por capítulo**, `CSwL/ChapterNN.lean`, com `namespace ChapterNN`.
  O namespace por capítulo é necessário: o livro redefine os mesmos nomes em
  capítulos diferentes.
- **As seções são numeradas por capítulo do `CSwL`, não pelo número da
  seção do livro** — `## 3.1 Conjuntos e notação de conjuntos`, por
  exemplo. Cada `##` leva uma linha `Ref. CSwFP/N §N.M` apontando para a
  seção correspondente, quando existe uma. Uma seção sem correspondência
  direta no livro (motivada por necessidade de apresentação, não por
  conteúdo do `CSwFP`) ainda ganha número, desde que caiba na sequência
  ascendente do capítulo — é o caso de "Proposições e provas" em
  `Chapter02.lean` (`## 2.2`, sem `Ref.`).
- **A numeração é a daqui, não a do livro.** Os capítulos 2 e 3 estão
  invertidos em relação a van Eijck & Unger: lá o cap. 2 é a teoria de
  funções, tipos e conjuntos, sem código, e o cap. 3 introduz a programação
  funcional. Aqui a programação vem primeiro, porque a teoria do cap. 3 é
  escrita *em* Lean — usa `inductive`, `Prop` e classes de tipos — e o livro
  não tinha esse problema, já que o cap. 2 dele não tem Haskell nenhum. Cada
  capítulo abre declarando a que capítulo do livro corresponde; quando o texto
  diz "capítulo N", é o N daqui.
- O cabeçalho de cada capítulo aponta o módulo Haskell correspondente do
  livro (`CSwFP/src/*.hs`) como referência, mas o código aqui não é uma
  transliteração dele.
- Funções que o livro deixa parciais aparecem aqui como totais, devolvendo
  `Option`. O caso sem resposta fica visível no tipo.

## Desvios de CSwFP

Registro contínuo dos pontos em que o `CSwL` diverge da estrutura do livro —
seja por exigência de apresentação Lean-vs-Haskell, seja por decisão do
professor. Cresce a cada capítulo; ver também a numeração invertida dos
capítulos 2/3, já registrada em **Convenções** acima.

| Onde | CSwFP | CSwL | Motivo |
|------|-------|------|--------|
| Cap. 3 | `Rel` (relação binária) só entra em §2.2 do livro | primeiro uso de `Rel` fica no capítulo 3, não no 2 | Lean vs Haskell — `Chapter02.lean` não importa nada, de propósito; `Rel` é `Mathlib.Data.Rel`, e o capítulo 2 só ganha o primeiro import de Mathlib no capítulo 3 |
| Cap. 3 | §2.5 "Types in Grammar and Computation" mistura motivação de tipos com a leitura categorial (`S → NP VP`) numa única seção | as duas ficam num só nível `##`, sem uma subordinada à outra | decisão do professor — a versão anterior do capítulo subordinava a leitura categorial como `###`, escondendo que ela é o resultado da seção, não um adendo |
| Cap. 1–3 | build sem nenhum aviso | `sorry` é permitido em `CSwL/`, não só em exercícios, quando deixado de propósito | decisão do professor — alguns exemplos do capítulo ficam de propósito com `sorry`, para resolver em aula, ao vivo, em vez de já vir prontos |
| Cap. 1–3 | exercícios num arquivo `Exercises/` separado, um por capítulo | exercícios movidos para dentro do capítulo, na posição da seção a que correspondem | decisão do professor — reduz repetição entre o capítulo e o arquivo de exercícios, e mostra a dependência entre o exercício e a seção que o motiva |
| Cap. 1–2 | seções sem numeração explícita, ou numeradas só no arquivo de exercícios | `## N.M Título`, alinhado à seção do `CSwFP` correspondente; seções só do `CSwL`, sem contrapartida no livro, ficam sem número | decisão do professor — facilita conferir a correspondência entre capítulo e livro; a numeração é a do capítulo do `CSwL` (ver Convenções), não a numeração absoluta do livro |
| Cap. 2 | seções numeradas pela numeração do livro (`## 3.3`–`## 3.14`) | renumeradas `## 2.1`–`## 2.15`, própria do `CSwL` — cada `##` leva uma linha `Ref. CSwFP/3 §3.N` apontando para a seção do livro | decisão do professor — a numeração do livro colidia textualmente com a de `Chapter03.lean` (ambos usavam `## 3.N`, referindo-se a capítulos diferentes do livro); alinha o capítulo 2 ao mesmo padrão que os capítulos 1 e 4 já seguiam |
| Cap. 2 | §3.9 Type Classes / §3.11 Harmonia vocálica / §3.14 Fonemas, na ordem do livro (§3.9 antes de §3.11 e §3.14) | "Harmonia vocálica do finlandês e plural sueco" (`## 2.14`) e "Aplicação: representando fonemas" (`## 2.15`) movidas para o fim da sequência numerada, depois de "Classes de tipos" (`## 2.11`) | decisão do professor — os dois exemplos de PLN concentram-se no fim do capítulo, como aplicação do que vem antes, em vez de intercalados na ordem do livro |
| Cap. 2 | livro não trata `Prop` nem prova formal neste capítulo | seção nova "Proposições e provas" (`## 2.2`), sem `Ref.` a CSwFP/3 | decisão do professor — `Chapter03.lean` usa `Prop` desde as primeiras linhas sem explicá-lo; a seção cobre o mínimo necessário para lê-lo, com tabela de táticas e exercícios de construção de termo modelados em `FAA2025/Lectures/Week01-02/Sheet*.lean` e `logical_verification_2026/lean/LoVe/LoVe01_TypesAndTerms_Demo.lean` |
| Cap. 2 | 14 dos exercícios do capítulo eram rotulados `E0.n`, fora de ordem sequencial no arquivo | todos os 14 recebem `### Exercício\* — <título>`, sem número | correção de registro — conferido em `CSwFP/txt/chapter-03.txt` que nenhum dos 14 corresponde a um exercício real do livro (que tem `Exercise 3.1`–`3.19`); eram placeholders do professor, herdados de quando o material morava em `Exercises/` |
| Cap. 2 | Exercícios 3.18 (p. 54) e 3.19 (p. 61), reais do livro | promovidos a `### Exercício 3.18`/`### Exercício 3.19`, antes ausentes do capítulo | correção de registro — o material de apoio (`fValue`/`fMatch`) já estava escrito; faltava só abrir o exercício |
| Cap. 2 | "User-defined Data Types" (§3.13) introduz `data`/`inductive` | "Tipos indutivos" (`## 2.5`, o `inductive` geral) vem antes de "Recursão" (`## 2.6`) | Lean vs Haskell — a recursão sobre `Nat`/`List` precisa que `inductive` já tenha sido apresentado; o livro pode adiar isso para §3.13 porque Haskell não exige declarar o tipo indutivo primeiro |
| Cap. 2 | `opaque`/`Option` não têm seção própria no livro | `opaque` entra em `## 2.1` (junto com tipos e termos); `Option` entra em `## 2.8` (depois de tipos indutivos e listas) | decisão do professor — segue o padrão de apresentação do `logical_verification_2026/lean/LoVe/LoVe01_TypesAndTerms_Demo.lean` para `opaque`, e agrupa `Option` com o `{α : Type}` que `Option α` usa |
| Cap. 4 | §4.4 dá `Cnj [Form]`/`Dsj [Form]` (Haskell) sobre uma BNF binária | `Form` com construtores binários (`conj`, `disj`) + `Form.conjs`/`Form.disjs : List Form → Form` para a notação n-ária | Lean vs Haskell — lista dentro do próprio tipo é *nested*: perde `deriving DecidableEq` e a tática `induction`, que os Exercícios 4.11/4.15 (leitura única) exigem; medido, não suposto |
| Cap. 4 | `Cnj []`/`Dsj []` mostrados como `"true"`/`"false"` (§4.6, comentário do livro) | `Form` ganha construtores próprios `top`/`bot`, não átomos de nome `"⊤"`/`"⊥"` | decisão do professor — um átomo nomeado dependeria da atribuição de valores do capítulo 5; `top`/`bot` são constantes, sempre `true`/`false` |
| Cap. 4 | linhas do tabuleiro numeradas de 1 a 10 | `Row := Fin 10`, 0 a 9 — linha do livro é `Row` menos 1 | Lean vs Haskell — `Fin 10` não rejeita o literal `10` (`OfNat` embrulha para `0`); só a construção validada (`⟨n, by omega⟩`) recusa `n ≥ 10`; a prosa do capítulo nomeia o deslocamento explicitamente |
| Cap. 4 | `Sent`/`NP`/`RCN`/`VP`/`INF` (Haskell) derivam `Eq` | os cinco tipos mutuamente recursivos não derivam `DecidableEq`, só `Repr` | Lean vs Haskell — `deriving DecidableEq` sobre um bloco `mutual` de 5 tipos gera avisos de `termination_by` inócuo; verificado que o próprio `FSynF.hs` só deriva `Show`, e nenhum capítulo posterior compara esses valores por igualdade |
| Cap. 4 | §4.3 não tem código Haskell (adiado para o capítulo 5) | `inductive Query`/`Statement` já em Lean | decisão do professor — desvio barato que o capítulo 5 aproveita |
| Cap. 4 | `Sheer` em `FSynF.hs:53` | `cheer` | typo do fonte distribuído — o texto do livro (p. 71) imprime `Cheer`, coerente com `VP.Cheered` |
| Cap. 4 | `Sent`/`NP`/`RCN`/`VP`/`INF` derivam só `Show` (imprime construtor, ex. `Sent (NP2 The (RCN2 ...))`) | `ToString` escrito à mão devolve a sentença em inglês de superfície (`"the dwarf that Snow White helped..."`) | decisão do professor — não é o que o livro faz; é o caminho inverso do parsing (capítulo 9), incluído aqui como antecipação, não como tradução do `Show` do livro |

## Licença e direitos

O livro é © Jan van Eijck e Christina Unger, 2010, Cambridge University
Press. Este repositório contém código e comentários originais, com
referências ao livro; não reproduz o texto do livro.
