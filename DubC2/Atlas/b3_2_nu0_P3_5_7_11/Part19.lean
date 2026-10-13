/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b3_2_nu0_P3_5_7_11.Part18

/-! Certificate pieces for `DubC2.Atlas.b3_2_nu0_P3_5_7_11`, part 19/35 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_nu0_P3_5_7_11_d12_u0 : (List.range' 0 173).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 12 59) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d12_u173 : (List.range' 173 63).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 12 59) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d12 : (List.range' 12 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 173 63 236 b3_2_nu0_P3_5_7_11_d12_u0 b3_2_nu0_P3_5_7_11_d12_u173 rfl))

theorem b3_2_nu0_P3_5_7_11_d13 : (List.range' 13 3).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d16 : (List.range' 16 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true := by
  decide +kernel

end DubC2.Atlas
