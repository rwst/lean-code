/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2767.Part56

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2767`, part 57/64 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2767_d14_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 14 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d14_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 14 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d14_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 14 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d14_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 14 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d14_u76 : (List.range' 76 4).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 14 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d14 : (List.range' 14 1).all (detOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 38 42 80 (all_glue _ 0 19 19 38 b3_2_P2_5_D768_j2767_d14_u0 b3_2_P2_5_D768_j2767_d14_u19 rfl) (all_glue _ 38 19 23 42 b3_2_P2_5_D768_j2767_d14_u38 (all_glue _ 57 19 4 23 b3_2_P2_5_D768_j2767_d14_u57 b3_2_P2_5_D768_j2767_d14_u76 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2767_d15_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 15 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d15_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 15 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d15_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 15 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d15_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 15 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d15_u76 : (List.range' 76 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 15 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d15_u95 : (List.range' 95 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 15 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d15_u114 : (List.range' 114 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 15 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d15_u133 : (List.range' 133 12).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 15 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d15 : (List.range' 15 1).all (detOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 76 69 145 (all_glue _ 0 38 38 76 (all_glue _ 0 19 19 38 b3_2_P2_5_D768_j2767_d15_u0 b3_2_P2_5_D768_j2767_d15_u19 rfl) (all_glue _ 38 19 19 38 b3_2_P2_5_D768_j2767_d15_u38 b3_2_P2_5_D768_j2767_d15_u57 rfl) rfl) (all_glue _ 76 38 31 69 (all_glue _ 76 19 19 38 b3_2_P2_5_D768_j2767_d15_u76 b3_2_P2_5_D768_j2767_d15_u95 rfl) (all_glue _ 114 19 12 31 b3_2_P2_5_D768_j2767_d15_u114 b3_2_P2_5_D768_j2767_d15_u133 rfl) rfl) rfl))

end DubC2.Atlas
