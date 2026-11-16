import VersoManual

open Verso.Genre.Manual

/-!
Citing uses `{citep Bib.key}[]` or `{citet Bib.key}[]`, and a missing key
becomes a compile error instead of a dangling `[Key]` in the text.

Verso offers four citable types (`VersoManual/Bibliography.lean`):
`InProceedings`, `Thesis`, `ArXiv`, and `Article`. There is no type for
`@book` or `@unpublished`, so entries that are not articles are entered as
`Article` with the `journal` field used for the publisher or the nature of
the text — the same convention as `sf-in-lean/Bib.lean`, which records books
(Pierce, Harper, Nipkow) this way.
-/

namespace Bib



def logicandproof : Article where
  title  := inlines!"Logic and Proof"
  authors := #[inlines!"Jeremy Avigad", inlines!"Joseph Hua",
               inlines!"Robert Y. Lewis",  inlines!"Floris van Doorn"]
  journal := inlines!""
  year := 2017
  month := none
  volume := inlines!""
  number := inlines!""
  url := "https://leanprover-community.github.io/logic_and_proof/"

def beesley2003 : Article where
  title   := inlines!"Finite State Morphology"
  authors := #[inlines!"Kenneth R. Beesley", inlines!"Lauri Karttunen"]
  journal := inlines!"CSLI Publications"
  year    := 2003
  month   := none
  volume  := inlines!"18"
  number  := inlines!""

def love2026 : Article where
  title   := inlines!"The Hitchhiker's Guide to Logical Verification"
  authors := #[inlines!"Anne Baanen", inlines!"Alexander Bentkamp",
               inlines!"Jasmin Blanchette", inlines!"Xavier Généreux",
               inlines!"Johannes Hölzl", inlines!"Jannis Limperg"]
  journal := inlines!"Manuscrito não publicado, edição de 2026"
  year    := 2026
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://github.com/lean-forward/logical_verification_2026"

def danielsson2010 : InProceedings where
  title     := inlines!"Total Parser Combinators"
  authors   := #[inlines!"Nils Anders Danielsson"]
  year      := 2010
  booktitle := inlines!"Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP 2010)"

def FPiL : Article where
  title   := inlines!"Functional Programming in Lean"
  authors := #[inlines!"David Thrane Christiansen"]
  journal := inlines!"Manuscrito não publicado"
  year    := 2023
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://lean-lang.org/functional_programming_in_lean/"

def LLR : Article where
  title   := inlines!"The Lean Language Reference"
  authors := #[inlines!"Lean FRO"]
  journal := inlines!"Manuscrito não publicado"
  year    := 2026
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://lean-lang.org/doc/reference/latest/"

def grice1975 : Article where
  title   := inlines!"Logic and Conversation"
  authors := #[inlines!"H. Paul Grice"]
  journal := inlines!"Syntax and Semantics, Vol. 3: Speech Acts (P. Cole e J. Morgan, eds.), Academic Press, p. 41–58"
  year    := 1975
  month   := none
  volume  := inlines!"3"
  number  := inlines!""

def montague1974 : Article where
  title   := inlines!"Formal Philosophy: Selected Papers of Richard Montague"
  authors := #[inlines!"Richard Montague"]
  journal := inlines!"Editado por Richmond H. Thomason. Yale University Press, New Haven"
  year    := 1974
  month   := none
  volume  := inlines!""
  number  := inlines!""

def keller1902 : Article where
  title   := inlines!"The Story of My Life"
  authors := #[inlines!"Helen Keller"]
  journal := inlines!"Doubleday, Page & Co., Nova York"
  year    := 1902
  month   := none
  volume  := inlines!""
  number  := inlines!""

def carroll1865 : Article where
  title   := inlines!"Alice in Wonderland"
  authors := #[inlines!"Lewis Carroll"]
  journal := inlines!"Macmillan, Londres"
  year    := 1865
  month   := none
  volume  := inlines!""
  number  := inlines!""

def russell1905 : Article where
  title   := inlines!"On Denoting"
  authors := #[inlines!"Bertrand Russell"]
  journal := inlines!"Mind"
  year    := 1905
  month   := none
  volume  := inlines!"14"
  number  := inlines!"56"

def enderton2001 : Article where
  title   := inlines!"A Mathematical Introduction to Logic"
  authors := #[inlines!"Herbert B. Enderton"]
  journal := inlines!"2ª edição. Harcourt/Academic Press, San Diego"
  year    := 2001
  month   := none
  volume  := inlines!""
  number  := inlines!""

def nederpelt2014 : Article where
  title   := inlines!"Type Theory and Formal Proof: An Introduction"
  authors := #[inlines!"Rob Nederpelt", inlines!"Herman Geuvers"]
  journal := inlines!"Cambridge University Press, Cambridge"
  year    := 2014
  month   := none
  volume  := inlines!""
  number  := inlines!""

def wadler2003 : Article where
  title   := inlines!"A Prettier Printer"
  authors := #[inlines!"Philip Wadler"]
  journal := inlines!"The Fun of Programming: A symposium in honour of Richard Bird's 60th birthday, Oxford"
  year    := 2003
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf"

def FAA2025 : Article where
  title   := inlines!"Formalizing Analysis of Algorithms, Autumn 2025"
  authors := #[inlines!"Sorrachai Yingchareonthawornchai"]
  journal := inlines!"Manuscrito não publicado"
  year    := 2025
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://github.com/sorrachai/FAA2025"

def mostowski1957 : Article where
  title   := inlines!"On a generalization of quantifiers"
  authors := #[inlines!"Andrzej Mostowski"]
  journal := inlines!"Fundamenta Mathematicae"
  year    := 1957
  month   := none
  volume  := inlines!"44"
  number  := inlines!""

def barwise1981 : Article where
  title   := inlines!"Generalized quantifiers and natural language"
  authors := #[inlines!"Jon Barwise", inlines!"Robin Cooper"]
  journal := inlines!"Linguistics and Philosophy"
  year    := 1981
  month   := none
  volume  := inlines!"4"
  number  := inlines!""

def blackburn1993 : InProceedings where
  title     := inlines!"Talking about trees"
  authors   := #[inlines!"Patrick Blackburn", inlines!"Claire Gardent",
                 inlines!"Wilfried Meyer-Viol"]
  year      := 1993
  booktitle := inlines!"Proceedings of the 6th Conference of the European Chapter of the Association for Computational Linguistics, p. 21–29"

def backofen1995 : Article where
  title   := inlines!"A first-order axiomatization of the theory of finite trees"
  authors := #[inlines!"Rolf Backofen", inlines!"James Rogers",
               inlines!"K. Vijay-Shanker"]
  journal := inlines!"Journal of Logic, Language and Information"
  year    := 1995
  month   := none
  volume  := inlines!"4"
  number  := inlines!""

def pereira1983 : InProceedings where
  title     := inlines!"Parsing as deduction"
  authors   := #[inlines!"Fernando C. N. Pereira", inlines!"David H. D. Warren"]
  year      := 1983
  booktitle := inlines!"Proceedings of the 21st Annual Meeting of the ACL, MIT, Cambridge, Mass."

def aho1972 : Article where
  title   := inlines!"The Theory of Parsing, Translation and Compiling, Volume I: Parsing"
  authors := #[inlines!"Alfred V. Aho", inlines!"Jeffrey D. Ullman"]
  journal := inlines!"Prentice-Hall, Englewood Cliffs, NJ"
  year    := 1972
  month   := none
  volume  := inlines!""
  number  := inlines!""

def pereira1987 : Article where
  title   := inlines!"Prolog and Natural-Language Analysis"
  authors := #[inlines!"Fernando C. N. Pereira", inlines!"Stuart M. Shieber"]
  journal := inlines!"CSLI Lecture Notes 10. CSLI, Stanford"
  year    := 1987
  month   := none
  volume  := inlines!""
  number  := inlines!""

def wadler1985 : InProceedings where
  title     := inlines!"How to replace failure by a list of successes"
  authors   := #[inlines!"Philip Wadler"]
  year      := 1985
  booktitle := inlines!"Functional Programming Languages and Computer Architecture (FPCA), LNCS 201, p. 113–128"

def hutton1992 : Article where
  title   := inlines!"Higher-order functions for parsing"
  authors := #[inlines!"Graham Hutton"]
  journal := inlines!"Journal of Functional Programming"
  year    := 1992
  month   := none
  volume  := inlines!"2"
  number  := inlines!"3"

def jeuring2001 : Article where
  title   := inlines!"Grammars and Parsing"
  authors := #[inlines!"Johan Jeuring", inlines!"Doaitse Swierstra"]
  journal := inlines!"Notas de aula, Universiteit Utrecht"
  year    := 2001
  month   := none
  volume  := inlines!""
  number  := inlines!""

def eijck2003 : InProceedings where
  title     := inlines!"Parser combinators for extraction"
  authors   := #[inlines!"Jan van Eijck"]
  year      := 2003
  booktitle := inlines!"Proceedings of the Fourteenth Amsterdam Colloquium (P. Dekker e R. van Rooy, eds.), ILLC, p. 99–104"

def gazdar1988 : InProceedings where
  title     := inlines!"Applicability of indexed grammars to natural languages"
  authors   := #[inlines!"Gerald Gazdar"]
  year      := 1988
  booktitle := inlines!"Natural Language Parsing and Linguistic Theories (U. Reyle e C. Rohrer, eds.), Reidel, Dordrecht, p. 69–94"

def eijck2007 : Article where
  title   := inlines!"Sequentially indexed grammars"
  authors := #[inlines!"Jan van Eijck"]
  journal := inlines!"Journal of Logic and Computation"
  year    := 2007
  month   := none
  volume  := inlines!""
  number  := inlines!""

def ranta2009 : InProceedings where
  title     := inlines!"Grammars as software libraries"
  authors   := #[inlines!"Aarne Ranta"]
  year      := 2009
  booktitle := inlines!"From Semantics to Computer Science: Essays in Honour of Gilles Kahn (G. Huet, J.-J. Lévy e G. Plotkin, eds.), Cambridge University Press"

def jurafsky2026 : Article where
  title   := inlines!"Speech and Language Processing"
  authors := #[inlines!"Daniel Jurafsky", inlines!"James H. Martin"]
  journal := inlines!"3ª edição, manuscrito não publicado, versão de 19 de agosto de 2026"
  year    := 2026
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://web.stanford.edu/~jurafsky/slp3/"

def allen1995 : Article where
  title   := inlines!"Natural Language Understanding"
  authors := #[inlines!"James Allen"]
  journal := inlines!"2ª edição. Benjamin/Cummings, Redwood City"
  year    := 1995
  month   := none
  volume  := inlines!""
  number  := inlines!""

def carroll2022 : InProceedings where
  title     := inlines!"Parsing"
  authors   := #[inlines!"John Carroll"]
  year      := 2022
  booktitle := inlines!"The Oxford Handbook of Computational Linguistics, 2ª edição (R. Mitkov, ed.), Oxford University Press, cap. 25"

def bender2024 : InProceedings where
  title     := inlines!"Computational linguistics and grammar engineering"
  authors   := #[inlines!"Emily M. Bender", inlines!"Guy Emerson"]
  year      := 2024
  booktitle := inlines!"Head-Driven Phrase Structure Grammar: The handbook, 2ª edição (S. Müller, A. Abeillé, R. D. Borsley e J.-P. Koenig, eds.), Language Science Press, Berlim, cap. 25"
  url       := "https://langsci-press.org/catalog/book/478"

def bunt2004 : Article where
  title   := inlines!"New Developments in Parsing Technology"
  authors := #[inlines!"Harry Bunt", inlines!"John Carroll",
               inlines!"Giorgio Satta"]
  journal := inlines!"Organizadores. Text, Speech and Language Technology 23. Kluwer, Dordrecht"
  year    := 2004
  month   := none
  volume  := inlines!""
  number  := inlines!""

end Bib
