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

Os exercícios avaliados não ficam aqui. Cada trabalho é um repositório
próprio, `trabalho-NN`, autocontido.

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

Para gerar as duas saídas web localmente:

```bash
./build-web.sh    # livro (Verso) + documentação (doc-gen4)
./serve.py        # http://localhost:8000/  e  /docs/
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
- Capítulo 4: Sintaxe formal de fragmentos — *a fazer*
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

Os exercícios ficam neste mesmo projeto, em `Exercises/ChapterNN.lean`, um
arquivo por capítulo. Cada `sorry` é um item a completar, e o aviso que o Lean
emite para ele é a sua lista do que falta:

```bash
lake build              # só o livro; tem de passar sem nenhum aviso
lake build Exercises    # os enunciados; cada aviso de `sorry` é um item aberto
```

`Exercises` fica fora do alvo padrão justamente por isso — se entrasse, o build
do livro nunca ficaria limpo. As questões marcadas com **✎** são discursivas e
se respondem em [`Exercises/RESPOSTAS.md`](Exercises/RESPOSTAS.md).

| arquivo                     | capítulo                          | itens |
|-----------------------------|-----------------------------------|------:|
| `Exercises/Chapter01.lean`  | 1. Estudo formal da língua natural|    19 |
| `Exercises/Chapter02.lean`  | 2. Programação funcional          |    33 |
| `Exercises/Chapter03.lean`  | 3. Funções, tipos e abstração     |    28 |

## Convenções

- **Um módulo por capítulo**, `CSwL/ChapterNN.lean`, com `namespace ChapterNN`.
  O namespace por capítulo é necessário: o livro redefine os mesmos nomes em
  capítulos diferentes. Os exercícios espelham isso em
  `Exercises/ChapterNN.lean`, com `namespace Exercises.ChapterNN`.
- **`CSwL/` e `Exercises/` são árvores separadas**, e o texto dos capítulos
  nunca se edita para resolver exercício. É o que permite atualizar o material
  sem conflitar com o que você escreveu: capítulo novo só *acrescenta* arquivo.
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

## Licença e direitos

O livro é © Jan van Eijck e Christina Unger, 2010, Cambridge University
Press. Este repositório contém código e comentários originais, com
referências ao livro; não reproduz o texto do livro.
