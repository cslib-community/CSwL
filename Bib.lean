import VersoManual

open Verso.Genre.Manual

/-!
Quem cita usa `{citep Bib.chave}[]` ou `{citet Bib.chave}[]`, e uma chave
inexistente vira erro de compilação em vez de `[Chave]` pendurado no texto.

O Verso oferece quatro tipos citáveis (`VersoManual/Bibliography.lean`):
`InProceedings`, `Thesis`, `ArXiv` e `Article`. Não há tipo para `@book` nem
para `@unpublished`, então as entradas que não são artigo entram como `Article`
com o campo `journal` usado para a editora ou para a natureza do texto — é a
mesma convenção do `sf-in-lean/Bib.lean`, que registra livros (Pierce, Harper,
Nipkow) assim.
-/

namespace Bib

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

def FAA2025 : Article where
  title   := inlines!"Formalizing Analysis of Algorithms, Autumn 2025"
  authors := #[inlines!"Sorrachai Yingchareonthawornchai"]
  journal := inlines!"Manuscrito não publicado"
  year    := 2025
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://github.com/sorrachai/FAA2025"

end Bib
