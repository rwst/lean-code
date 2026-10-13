/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b3_2_num1_P2_3.Data

/-! Certificate pieces for `DubC2.Atlas.b3_2_num1_P2_3`, part 1/1 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_num1_P2_3_r0 : (List.range' 0 1).all (roundOK b3_2_num1_P2_3P b3_2_num1_P2_3C) = true := by
  decide +kernel

theorem b3_2_num1_P2_3_d0 : (List.range' 0 1).all (detOK b3_2_num1_P2_3P b3_2_num1_P2_3C) = true := by
  decide +kernel

end DubC2.Atlas
