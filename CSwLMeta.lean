-- Adapted from sf-in-lean/SFLMeta.lean, with only the modules
-- CSwL uses (`sf-in-lean` also has Details, Epigraph, Hide, Ignore,
-- Instructors, SlideBreak, Theme, Version, and Volume).
-- Adding one of those is copying the file and adding an `import` here.
import CSwLMeta.Bnf
import CSwLMeta.Comment
import CSwLMeta.DisplayMath
import CSwLMeta.Exercise
import CSwLMeta.Grade
import CSwLMeta.Quiz
import CSwLMeta.Save
import CSwLMeta.Solution
import CSwLMeta.Terse
import CSwLMeta.Variant

namespace CSwLMeta

export Verso.Genre.Manual.InlineLean (name leanCommand leanTerm module leanSection leanOutput)

end CSwLMeta
