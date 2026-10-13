/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b3_2_nu0_P3_5_7_11.Part19

/-! Certificate pieces for `DubC2.Atlas.b3_2_nu0_P3_5_7_11`, part 20/35 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_nu0_P3_5_7_11_d17 : (List.range' 17 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d18 : (List.range' 18 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d19_u0 : (List.range' 0 173).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 19 72) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d19_u173 : (List.range' 173 115).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 19 72) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d19 : (List.range' 19 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 173 115 288 b3_2_nu0_P3_5_7_11_d19_u0 b3_2_nu0_P3_5_7_11_d19_u173 rfl))

end DubC2.Atlas
