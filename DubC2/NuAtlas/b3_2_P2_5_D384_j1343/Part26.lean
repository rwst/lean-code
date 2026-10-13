/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1343.Part25

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1343`, part 26/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1343_d9_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 9 28) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d9_u112 : (List.range' 112 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 9 28) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d9 : (List.range' 9 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 84 140 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1343_d9_u0 b3_2_P2_5_D384_j1343_d9_u28 rfl) (all_glue _ 56 28 56 84 b3_2_P2_5_D384_j1343_d9_u56 (all_glue _ 84 28 28 56 b3_2_P2_5_D384_j1343_d9_u84 b3_2_P2_5_D384_j1343_d9_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d10_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 10 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d10_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 10 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d10_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 10 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d10_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 10 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d10_u112 : (List.range' 112 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 10 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d10_u140 : (List.range' 140 15).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 10 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d10 : (List.range' 10 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 84 71 155 (all_glue _ 0 28 56 84 b3_2_P2_5_D384_j1343_d10_u0 (all_glue _ 28 28 28 56 b3_2_P2_5_D384_j1343_d10_u28 b3_2_P2_5_D384_j1343_d10_u56 rfl) rfl) (all_glue _ 84 28 43 71 b3_2_P2_5_D384_j1343_d10_u84 (all_glue _ 112 28 15 43 b3_2_P2_5_D384_j1343_d10_u112 b3_2_P2_5_D384_j1343_d10_u140 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d11 : (List.range' 11 2).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d13 : (List.range' 13 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true := by
  decide +kernel

end DubC2.Atlas
