/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j655.Part12

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j655`, part 13/20 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j655_d5_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 5 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d5_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 5 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d5_u136 : (List.range' 136 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 5 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d5_u170 : (List.range' 170 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 5 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d5_u204 : (List.range' 204 6).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 5 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d5 : (List.range' 5 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 102 108 210 (all_glue _ 0 34 68 102 b3_2_P2_5_D192_j655_d5_u0 (all_glue _ 34 34 34 68 b3_2_P2_5_D192_j655_d5_u34 b3_2_P2_5_D192_j655_d5_u68 rfl) rfl) (all_glue _ 102 68 40 108 (all_glue _ 102 34 34 68 b3_2_P2_5_D192_j655_d5_u102 b3_2_P2_5_D192_j655_d5_u136 rfl) (all_glue _ 170 34 6 40 b3_2_P2_5_D192_j655_d5_u170 b3_2_P2_5_D192_j655_d5_u204 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d6_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 6 45) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d6_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 6 45) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d6_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 6 45) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d6_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 6 45) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d6_u136 : (List.range' 136 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 6 45) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d6_u170 : (List.range' 170 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 6 45) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d6_u204 : (List.range' 204 21).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 6 45) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 102 123 225 (all_glue _ 0 34 68 102 b3_2_P2_5_D192_j655_d6_u0 (all_glue _ 34 34 34 68 b3_2_P2_5_D192_j655_d6_u34 b3_2_P2_5_D192_j655_d6_u68 rfl) rfl) (all_glue _ 102 68 55 123 (all_glue _ 102 34 34 68 b3_2_P2_5_D192_j655_d6_u102 b3_2_P2_5_D192_j655_d6_u136 rfl) (all_glue _ 170 34 21 55 b3_2_P2_5_D192_j655_d6_u170 b3_2_P2_5_D192_j655_d6_u204 rfl) rfl) rfl))

end DubC2.Atlas
