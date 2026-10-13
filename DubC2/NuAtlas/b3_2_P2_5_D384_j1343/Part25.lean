/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1343.Part24

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1343`, part 25/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1343_d6_u140 : (List.range' 140 15).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 6 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 84 71 155 (all_glue _ 0 28 56 84 b3_2_P2_5_D384_j1343_d6_u0 (all_glue _ 28 28 28 56 b3_2_P2_5_D384_j1343_d6_u28 b3_2_P2_5_D384_j1343_d6_u56 rfl) rfl) (all_glue _ 84 28 43 71 b3_2_P2_5_D384_j1343_d6_u84 (all_glue _ 112 28 15 43 b3_2_P2_5_D384_j1343_d6_u112 b3_2_P2_5_D384_j1343_d6_u140 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d7 : (List.range' 7 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d8_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 8 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d8_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 8 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d8_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 8 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d8_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 8 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d8_u112 : (List.range' 112 23).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 8 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d8 : (List.range' 8 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 79 135 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1343_d8_u0 b3_2_P2_5_D384_j1343_d8_u28 rfl) (all_glue _ 56 28 51 79 b3_2_P2_5_D384_j1343_d8_u56 (all_glue _ 84 28 23 51 b3_2_P2_5_D384_j1343_d8_u84 b3_2_P2_5_D384_j1343_d8_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d9_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 9 28) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d9_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 9 28) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d9_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 9 28) = true := by
  decide +kernel

end DubC2.Atlas
