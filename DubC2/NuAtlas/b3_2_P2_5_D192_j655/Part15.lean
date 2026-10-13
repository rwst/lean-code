/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j655.Part14

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j655`, part 15/20 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j655_d10_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 10 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d10_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 10 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d10_u136 : (List.range' 136 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 10 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d10_u170 : (List.range' 170 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 10 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d10_u204 : (List.range' 204 26).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 10 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d10 : (List.range' 10 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 102 128 230 (all_glue _ 0 34 68 102 b3_2_P2_5_D192_j655_d10_u0 (all_glue _ 34 34 34 68 b3_2_P2_5_D192_j655_d10_u34 b3_2_P2_5_D192_j655_d10_u68 rfl) rfl) (all_glue _ 102 68 60 128 (all_glue _ 102 34 34 68 b3_2_P2_5_D192_j655_d10_u102 b3_2_P2_5_D192_j655_d10_u136 rfl) (all_glue _ 170 34 26 60 b3_2_P2_5_D192_j655_d10_u170 b3_2_P2_5_D192_j655_d10_u204 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d11 : (List.range' 11 2).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d13 : (List.range' 13 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d14_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 14 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d14_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 14 32) = true := by
  decide +kernel

end DubC2.Atlas
