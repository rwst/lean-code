/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b3_2_nu0_P3_5_7_11.Part15

/-! Certificate pieces for `DubC2.Atlas.b3_2_nu0_P3_5_7_11`, part 16/35 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_nu0_P3_5_7_11_d2_u519 : (List.range' 519 121).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 2 160) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d2 : (List.range' 2 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 346 294 640 (all_glue _ 0 173 173 346 b3_2_nu0_P3_5_7_11_d2_u0 b3_2_nu0_P3_5_7_11_d2_u173 rfl) (all_glue _ 346 173 121 294 b3_2_nu0_P3_5_7_11_d2_u346 b3_2_nu0_P3_5_7_11_d2_u519 rfl) rfl))

theorem b3_2_nu0_P3_5_7_11_d3 : (List.range' 3 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d4_u0 : (List.range' 0 173).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 4 61) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d4_u173 : (List.range' 173 71).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 4 61) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d4 : (List.range' 4 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 173 71 244 b3_2_nu0_P3_5_7_11_d4_u0 b3_2_nu0_P3_5_7_11_d4_u173 rfl))

end DubC2.Atlas
