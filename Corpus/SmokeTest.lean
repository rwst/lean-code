/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-! Smoke test for the theorem-database attributes. Exercises every attribute,
the registry, the unknown-key warning, and the extractor accessors. -/

open TheoremDB

-- A registry stub node.
informal_result "riemann-hypothesis"
  latex "All nontrivial zeros of $\\zeta$ have real part $1/2$."
  refs "Rie1859"

namespace Demo

/-- A bespoke definition that a statement depends on. -/
def myDef (n : Nat) : Nat := n + 1

/-- A fully annotated declaration. -/
@[category research open, AMS 11 5,
  ref "BEGL96" "Er97", extern_id "OEIS:A000045", group "demo",
  conjectured_by "Erdős" 1997, solved_by "Boris Alexeev" 2024,
  formal_uses myDef, informal_uses "riemann-hypothesis"]
theorem demo_thm : True := by sorry

/-- This must emit a warning for the unknown key, but still record the edge. -/
@[informal_uses "not-in-registry"]
theorem demo_warn : True := trivial

end Demo

-- Read everything back the way the extractor will.
open TheoremDB in
#eval show Lean.CoreM Unit from do
  let refs ← getRefTags
  let externs ← getExternTags
  let groups ← getGroupTags
  let fUses ← getFormalUsesTags
  let iUses ← getInformalUsesTags
  let attrs ← getAttributionTags
  let irs ← getInformalResults
  IO.println s!"refTags          = {refs.size}"
  IO.println s!"externTags       = {externs.size}"
  IO.println s!"groupTags        = {groups.size}"
  IO.println s!"formalUsesTags   = {fUses.size}"
  IO.println s!"informalUsesTags = {iUses.size}"
  IO.println s!"attributionTags  = {attrs.size}"
  IO.println s!"informalResults  = {irs.size}"
  for t in fUses do
    IO.println s!"  formal_uses {t.declName} -> {t.targets}"
  for t in attrs do
    IO.println s!"  attribution {t.who} ({t.year}) role={repr t.role}"
