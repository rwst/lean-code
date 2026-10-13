/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b3_2_nu0_P3_5_7_11.Part13

/-! Certificate pieces for `DubC2.Atlas.b3_2_nu0_P3_5_7_11`, part 14/35 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_nu0_P3_5_7_11_d0_u865 : (List.range' 865 173).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 0 264) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d0_u1038 : (List.range' 1038 18).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 0 264) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d0 : (List.range' 0 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 519 537 1056 (all_glue _ 0 173 346 519 b3_2_nu0_P3_5_7_11_d0_u0 (all_glue _ 173 173 173 346 b3_2_nu0_P3_5_7_11_d0_u173 b3_2_nu0_P3_5_7_11_d0_u346 rfl) rfl) (all_glue _ 519 346 191 537 (all_glue _ 519 173 173 346 b3_2_nu0_P3_5_7_11_d0_u519 b3_2_nu0_P3_5_7_11_d0_u692 rfl) (all_glue _ 865 173 18 191 b3_2_nu0_P3_5_7_11_d0_u865 b3_2_nu0_P3_5_7_11_d0_u1038 rfl) rfl) rfl))

theorem b3_2_nu0_P3_5_7_11_d1_u0 : (List.range' 0 173).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 1 73) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d1_u173 : (List.range' 173 119).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 1 73) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d1 : (List.range' 1 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 173 119 292 b3_2_nu0_P3_5_7_11_d1_u0 b3_2_nu0_P3_5_7_11_d1_u173 rfl))

end DubC2.Atlas
