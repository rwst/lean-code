/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b3_2_nu0_P3_5_7_11.Part11

/-! Certificate pieces for `DubC2.Atlas.b3_2_nu0_P3_5_7_11`, part 12/35 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_nu0_P3_5_7_11_r812 : (List.range' 812 123).all (roundOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d0_u0 : (List.range' 0 173).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 0 264) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d0_u173 : (List.range' 173 173).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 0 264) = true := by
  decide +kernel

end DubC2.Atlas
