import Exercises.Chapter01
import Exercises.Chapter02
import Exercises.Chapter03

/-
Raiz da biblioteca `Exercises`: um módulo por capítulo, com os enunciados a
completar. `Exercises/ChapterNN.lean` acompanha `CSwL/ChapterNN.lean`.

Esta biblioteca **não** entra no `lake build`, e é de propósito: os enunciados
vêm cheios de `sorry`, e `sorry` emite aviso — que é justamente a lista do que
falta fazer. Se ela entrasse no alvo padrão, o build do livro nunca ficaria
limpo.

    lake build              -- só o livro (`CSwL`), tem de passar sem avisos
    lake build Exercises    -- os enunciados; os avisos de `sorry` são a sua lista
-/
