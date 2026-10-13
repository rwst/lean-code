/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j655.Part15

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j655`, part 16/20 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j655_d14_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 14 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d14_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 14 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d14_u136 : (List.range' 136 24).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 14 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d14 : (List.range' 14 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 68 92 160 (all_glue _ 0 34 34 68 b3_2_P2_5_D192_j655_d14_u0 b3_2_P2_5_D192_j655_d14_u34 rfl) (all_glue _ 68 34 58 92 b3_2_P2_5_D192_j655_d14_u68 (all_glue _ 102 34 24 58 b3_2_P2_5_D192_j655_d14_u102 b3_2_P2_5_D192_j655_d14_u136 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d15 : (List.range' 15 2).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d17 : (List.range' 17 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d18_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 18 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d18_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 18 35) = true := by
  decide +kernel

end DubC2.Atlas
