import CSwLMeta
import Bib

import CSwL.IntroCS
import CSwL.IntroL
import CSwL.Morphology
import CSwL.Games
import CSwL.Logic
import CSwL.Sets
import CSwL.InfEngine
import CSwL.English

import VersoManual

open Verso Genre Manual

set_option verso.code.warnLineLength 80

-- Root of the book in the `Manual` genre. To add a chapter: an `import
-- CSwL.Name` above and an `{include CSwL.Name}` below, in the book's order.
-- (The body of `#doc` has no comment syntax — do not write comments between
-- the `{include}`s.) A chapter can be a single file (`IntroCS`,
-- `Sets`) or a "glue" file that gathers sections living in their own
-- file via `{include 1 ...}` (see `Morphology.lean`).
--
-- The book is only built from here, in the four variants of
-- `make all`/`Makefile`.

#doc (Manual) "Semântica computacional com Lean" =>
{include CSwL.IntroCS}
{include CSwL.IntroL}
{include CSwL.Morphology}
{include CSwL.Games}
{include CSwL.Logic}
{include CSwL.Sets}
{include CSwL.InfEngine}
{include CSwL.English}
