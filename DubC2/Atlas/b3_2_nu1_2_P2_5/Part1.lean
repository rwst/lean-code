/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b3_2_nu1_2_P2_5.Data

/-! Certificate pieces for `DubC2.Atlas.b3_2_nu1_2_P2_5`, part 1/1 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_nu1_2_P2_5_r0 : (List.range' 0 6).all (roundOK b3_2_nu1_2_P2_5P b3_2_nu1_2_P2_5C) = true := by
  decide +kernel

theorem b3_2_nu1_2_P2_5_d0 : (List.range' 0 7).all (detOK b3_2_nu1_2_P2_5P b3_2_nu1_2_P2_5C) = true := by
  decide +kernel

end DubC2.Atlas
