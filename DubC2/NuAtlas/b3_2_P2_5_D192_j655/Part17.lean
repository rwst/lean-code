/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j655.Part16

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j655`, part 17/20 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j655_d18_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 18 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d18_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 18 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d18_u136 : (List.range' 136 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 18 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d18_u170 : (List.range' 170 5).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 18 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d18 : (List.range' 18 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 102 73 175 (all_glue _ 0 34 68 102 b3_2_P2_5_D192_j655_d18_u0 (all_glue _ 34 34 34 68 b3_2_P2_5_D192_j655_d18_u34 b3_2_P2_5_D192_j655_d18_u68 rfl) rfl) (all_glue _ 102 34 39 73 b3_2_P2_5_D192_j655_d18_u102 (all_glue _ 136 34 5 39 b3_2_P2_5_D192_j655_d18_u136 b3_2_P2_5_D192_j655_d18_u170 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d19 : (List.range' 19 3).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d22 : (List.range' 22 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d23_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 23 36) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d23_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 23 36) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d23_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 23 36) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d23_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 23 36) = true := by
  decide +kernel

end DubC2.Atlas
