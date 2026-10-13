/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b5_2_nu1_2_P2_3_7_11.Part3

/-! Certificate pieces for `DubC2.Atlas.b5_2_nu1_2_P2_3_7_11`, part 4/4 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b5_2_nu1_2_P2_3_7_11_r85 : (List.range' 85 35).all (roundOK b5_2_nu1_2_P2_3_7_11P b5_2_nu1_2_P2_3_7_11C) = true := by
  decide +kernel

theorem b5_2_nu1_2_P2_3_7_11_d0 : (List.range' 0 133).all (detOK b5_2_nu1_2_P2_3_7_11P b5_2_nu1_2_P2_3_7_11C) = true := by
  decide +kernel

end DubC2.Atlas
