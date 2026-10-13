/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b6_5_num1_P2_3_5.Data

/-! Certificate pieces for `DubC2.Atlas.b6_5_num1_P2_3_5`, part 1/1 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b6_5_num1_P2_3_5_r0 : (List.range' 0 1).all (roundOK b6_5_num1_P2_3_5P b6_5_num1_P2_3_5C) = true := by
  decide +kernel

theorem b6_5_num1_P2_3_5_d0 : (List.range' 0 6).all (detOK b6_5_num1_P2_3_5P b6_5_num1_P2_3_5C) = true := by
  decide +kernel

end DubC2.Atlas
