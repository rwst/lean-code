/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j655.Part7

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j655`, part 8/20 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j655_d1_u204 : (List.range' 204 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 1 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d1_u238 : (List.range' 238 17).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 1 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 136 119 255 (all_glue _ 0 68 68 136 (all_glue _ 0 34 34 68 b3_2_P2_5_D192_j655_d1_u0 b3_2_P2_5_D192_j655_d1_u34 rfl) (all_glue _ 68 34 34 68 b3_2_P2_5_D192_j655_d1_u68 b3_2_P2_5_D192_j655_d1_u102 rfl) rfl) (all_glue _ 136 68 51 119 (all_glue _ 136 34 34 68 b3_2_P2_5_D192_j655_d1_u136 b3_2_P2_5_D192_j655_d1_u170 rfl) (all_glue _ 204 34 17 51 b3_2_P2_5_D192_j655_d1_u204 b3_2_P2_5_D192_j655_d1_u238 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d2_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u136 : (List.range' 136 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u170 : (List.range' 170 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u204 : (List.range' 204 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u238 : (List.range' 238 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u272 : (List.range' 272 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u306 : (List.range' 306 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

end DubC2.Atlas
