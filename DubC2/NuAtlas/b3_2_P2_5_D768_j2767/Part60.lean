/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2767.Part59

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2767`, part 60/64 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2767_d20 : (List.range' 20 1).all (detOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u76 : (List.range' 76 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u95 : (List.range' 95 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u114 : (List.range' 114 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u133 : (List.range' 133 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21_u152 : (List.range' 152 18).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 21 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d21 : (List.range' 21 1).all (detOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 76 94 170 (all_glue _ 0 38 38 76 (all_glue _ 0 19 19 38 b3_2_P2_5_D768_j2767_d21_u0 b3_2_P2_5_D768_j2767_d21_u19 rfl) (all_glue _ 38 19 19 38 b3_2_P2_5_D768_j2767_d21_u38 b3_2_P2_5_D768_j2767_d21_u57 rfl) rfl) (all_glue _ 76 38 56 94 (all_glue _ 76 19 19 38 b3_2_P2_5_D768_j2767_d21_u76 b3_2_P2_5_D768_j2767_d21_u95 rfl) (all_glue _ 114 19 37 56 b3_2_P2_5_D768_j2767_d21_u114 (all_glue _ 133 19 18 37 b3_2_P2_5_D768_j2767_d21_u133 b3_2_P2_5_D768_j2767_d21_u152 rfl) rfl) rfl) rfl))

end DubC2.Atlas
