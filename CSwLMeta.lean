-- Adapted from /Users/ar/r/sf-in-lean/SFLMeta.lean, com só os módulos que o
-- CSwL usa (o `sf-in-lean` tem ainda Details, Epigraph, Hide, Ignore,
-- Instructors, SlideBreak, Terse, Theme, Version e Volume).
-- Acrescentar um deles é copiar o arquivo e somar um `import` aqui.
import CSwLMeta.Bnf
import CSwLMeta.Comment
import CSwLMeta.DisplayMath
import CSwLMeta.Exercise
import CSwLMeta.Grade
import CSwLMeta.Quiz
import CSwLMeta.Save
import CSwLMeta.Solution
import CSwLMeta.Variant

namespace CSwLMeta

export Verso.Genre.Manual.InlineLean (name leanCommand leanTerm module leanSection leanOutput)

end CSwLMeta
