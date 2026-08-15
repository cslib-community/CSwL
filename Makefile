# Makefile do CSwL — gera o livro nas quatro variantes.
#
# Cada variante produz `_out/<variante>/{html-multi,lean}`:
#
#   student    prosa completa, gabaritos elididos (viram `sorry`)
#              -> é o corte que vira assignment no GitHub Classroom e o
#                 livro HTML publicado
#   solutions  prosa completa, gabaritos à mostra
#              -> gabarito, publicado depois de cada entrega
#   terse      prosa de aula, gabaritos elididos e provas `workinclass!`
#              stubadas -> aberto no VS Code durante a aula
#   grading    prosa completa, gabaritos à mostra mais `import AutograderLib`
#              e os atributos `[autogradedProof …]` -> nunca sai do
#              repositório privado; é sobre ele que se roda
#                 lake exe autograder --local <entrega> <arquivo>
#
# `_out/<variante>/lean/` é um projeto Lake autônomo (tem `lakefile.toml` e
# `lean-toolchain` próprios), gerado por `CSwLMeta/Save/Project.lean`. O
# `lean4-autograder-main` é dependência só do projeto gerado da variante
# `grading` — nunca do `lakefile.toml` do CSwL, onde colidiria com o Mathlib
# que o `cslib` traz.
#
# A saída web dos capítulos que ainda estão no gênero `Literate` continua
# saindo pelo `./build-web.sh` (`literate.toml`), fora deste Makefile, até que
# todos sejam convertidos.

.PHONY: all student solutions terse grading build serve clean

default: all

all: student solutions terse grading

# Compila o executável antes de rodar qualquer variante. Nas chamadas
# seguintes o Lake percebe que nada mudou e sai na hora.
build:
	lake build cswl-book

student: build
	lake exe cswl-book student

solutions: build
	lake exe cswl-book solutions

terse: build
	lake exe cswl-book terse

grading: build
	lake exe cswl-book grading

# Serve as quatro variantes em http://localhost:8000/ (cada uma em
# `<variante>/html-multi/`).
serve: all
	python3 -m http.server 8000 -d _out/

clean:
	rm -rf _out/
