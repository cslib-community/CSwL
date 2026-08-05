# CSwL — Computational Semantics with Lean

Tradução para [Lean 4](https://lean-lang.org) de *Computational Semantics
with Functional Programming*, de Jan van Eijck e Christina Unger (Cambridge
University Press, 2010). Material da disciplina **Processamento de Linguagem
Natural**, EMAp/FGV, 2026.2 — o programa está em
[emap-nlp/syllabus](https://github.com/emap-nlp/syllabus).

Esta não é uma tradução linha a linha do livro, e não substitui o livro. É um
companheiro anotado: o texto original é referenciado, não reproduzido, e as
construções são reescritas na forma mais idiomática em Lean, não na mais
próxima do original. Onde o livro deixa algo como exercício, aqui aparece um
`sorry`.

## Como usar

Cada capítulo existe em três formas, geradas do mesmo arquivo `.lean`:

- **livro** — o texto para ler no navegador, sem instalar nada.
- **documentação** — a referência de API: uma entrada por declaração, com
  tipo e assinatura.
- **fonte** — para abrir no VS Code e editar, com o Lean respondendo ao vivo.

Para o ambiente local: [Install Lean](https://lean-lang.org/install), depois
`lake build`. Sem instalar nada, dá para colar trechos em
[live.lean-lang.org](https://live.lean-lang.org/).

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
- **2. Funções, tipos e abstração** —
  [livro](https://emap-nlp.github.io/CSwL/cap02/) ·
  [documentação](https://emap-nlp.github.io/CSwL/docs/CSwL/Chapter02.html) ·
  [fonte](CSwL/Chapter02.lean)
- **3. Programação funcional** —
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

## Convenções

- **Um módulo por capítulo do livro**, `CSwL/ChapterNN.lean`, com
  `namespace ChapterNN`. O namespace por capítulo é necessário: o livro
  redefine os mesmos nomes em capítulos diferentes.
- O cabeçalho de cada capítulo aponta o módulo Haskell correspondente do
  livro (`CSwFP/src/*.hs`) como referência, mas o código aqui não é uma
  transliteração dele.
- Funções que o livro deixa parciais aparecem aqui como totais, devolvendo
  `Option`. O caso sem resposta fica visível no tipo.

## Licença e direitos

O livro é © Jan van Eijck e Christina Unger, 2010, Cambridge University
Press. Este repositório contém código e comentários originais, com
referências ao livro; não reproduz o texto do livro.
