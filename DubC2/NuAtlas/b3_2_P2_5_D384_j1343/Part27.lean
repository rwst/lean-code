/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1343.Part26

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1343`, part 27/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1343_d14_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 14 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d14_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 14 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d14_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 14 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d14_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 14 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d14_u112 : (List.range' 112 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 14 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d14_u140 : (List.range' 140 10).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 14 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d14 : (List.range' 14 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 84 66 150 (all_glue _ 0 28 56 84 b3_2_P2_5_D384_j1343_d14_u0 (all_glue _ 28 28 28 56 b3_2_P2_5_D384_j1343_d14_u28 b3_2_P2_5_D384_j1343_d14_u56 rfl) rfl) (all_glue _ 84 28 38 66 b3_2_P2_5_D384_j1343_d14_u84 (all_glue _ 112 28 10 38 b3_2_P2_5_D384_j1343_d14_u112 b3_2_P2_5_D384_j1343_d14_u140 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d15 : (List.range' 15 2).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d17_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 17 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d17_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 17 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d17_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 17 24) = true := by
  decide +kernel

end DubC2.Atlas
