import CSwLMeta
import Bib

import CSwL.IntroCS
import CSwL.IntroL
import CSwL.Applications
import CSwL.Foundation
import CSwL.Games
import CSwL.English
import CSwL.Logic

import VersoManual

open Verso Genre Manual

set_option verso.code.warnLineLength 80

-- Root of the book in the `Manual` genre. To add a chapter: an `import
-- CSwL.Name` above and an `{include CSwL.Name}` below, in the book's order.
-- (The body of `#doc` has no comment syntax — do not write comments between
-- the `{include}`s.) A chapter can be a single file (`IntroCS`,
-- `Foundation`) or a "glue" file that gathers sections living in their own
-- file via `{include 1 ...}` (see `Applications.lean`).
--
-- The book is only built from here, in the four variants of
-- `make all`/`Makefile`.

#doc (Manual) "Semântica computacional com Lean" =>
{include CSwL.IntroCS}
{include CSwL.IntroL}
{include CSwL.Applications}
{include CSwL.Foundation}
{include CSwL.Games}
{include CSwL.English}
{include CSwL.Logic}
