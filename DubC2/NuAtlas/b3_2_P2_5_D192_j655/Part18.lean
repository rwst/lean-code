/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j655.Part17

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j655`, part 18/20 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j655_d23_u136 : (List.range' 136 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 23 36) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d23_u170 : (List.range' 170 10).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 23 36) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d23 : (List.range' 23 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 102 78 180 (all_glue _ 0 34 68 102 b3_2_P2_5_D192_j655_d23_u0 (all_glue _ 34 34 34 68 b3_2_P2_5_D192_j655_d23_u34 b3_2_P2_5_D192_j655_d23_u68 rfl) rfl) (all_glue _ 102 34 44 78 b3_2_P2_5_D192_j655_d23_u102 (all_glue _ 136 34 10 44 b3_2_P2_5_D192_j655_d23_u136 b3_2_P2_5_D192_j655_d23_u170 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d24 : (List.range' 24 2).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d26_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 26 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d26_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 26 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d26_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 26 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d26_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 26 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d26_u136 : (List.range' 136 14).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 26 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d26 : (List.range' 26 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 68 82 150 (all_glue _ 0 34 34 68 b3_2_P2_5_D192_j655_d26_u0 b3_2_P2_5_D192_j655_d26_u34 rfl) (all_glue _ 68 34 48 82 b3_2_P2_5_D192_j655_d26_u68 (all_glue _ 102 34 14 48 b3_2_P2_5_D192_j655_d26_u102 b3_2_P2_5_D192_j655_d26_u136 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d27 : (List.range' 27 3).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

end DubC2.Atlas
