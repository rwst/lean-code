/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2767.Part60

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2767`, part 61/64 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2767_d22_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 22 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d22_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 22 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d22_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 22 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d22_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 22 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d22_u76 : (List.range' 76 14).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 22 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d22 : (List.range' 22 1).all (detOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 38 52 90 (all_glue _ 0 19 19 38 b3_2_P2_5_D768_j2767_d22_u0 b3_2_P2_5_D768_j2767_d22_u19 rfl) (all_glue _ 38 19 33 52 b3_2_P2_5_D768_j2767_d22_u38 (all_glue _ 57 19 14 33 b3_2_P2_5_D768_j2767_d22_u57 b3_2_P2_5_D768_j2767_d22_u76 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2767_d23_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 23 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d23_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 23 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d23_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 23 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d23_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 23 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d23_u76 : (List.range' 76 9).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 23 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d23 : (List.range' 23 1).all (detOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 38 47 85 (all_glue _ 0 19 19 38 b3_2_P2_5_D768_j2767_d23_u0 b3_2_P2_5_D768_j2767_d23_u19 rfl) (all_glue _ 38 19 28 47 b3_2_P2_5_D768_j2767_d23_u38 (all_glue _ 57 19 9 28 b3_2_P2_5_D768_j2767_d23_u57 b3_2_P2_5_D768_j2767_d23_u76 rfl) rfl) rfl))

end DubC2.Atlas
