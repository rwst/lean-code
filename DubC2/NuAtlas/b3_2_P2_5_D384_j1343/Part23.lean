/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1343.Part22

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1343`, part 23/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1343_d3_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 3 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d3_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 3 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d3_u112 : (List.range' 112 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 3 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d3_u140 : (List.range' 140 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 3 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d3_u168 : (List.range' 168 17).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 3 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d3 : (List.range' 3 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 84 101 185 (all_glue _ 0 28 56 84 b3_2_P2_5_D384_j1343_d3_u0 (all_glue _ 28 28 28 56 b3_2_P2_5_D384_j1343_d3_u28 b3_2_P2_5_D384_j1343_d3_u56 rfl) rfl) (all_glue _ 84 56 45 101 (all_glue _ 84 28 28 56 b3_2_P2_5_D384_j1343_d3_u84 b3_2_P2_5_D384_j1343_d3_u112 rfl) (all_glue _ 140 28 17 45 b3_2_P2_5_D384_j1343_d3_u140 b3_2_P2_5_D384_j1343_d3_u168 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d4_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 4 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d4_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 4 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d4_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 4 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d4_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 4 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d4_u112 : (List.range' 112 13).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 4 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 69 125 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1343_d4_u0 b3_2_P2_5_D384_j1343_d4_u28 rfl) (all_glue _ 56 28 41 69 b3_2_P2_5_D384_j1343_d4_u56 (all_glue _ 84 28 13 41 b3_2_P2_5_D384_j1343_d4_u84 b3_2_P2_5_D384_j1343_d4_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d5_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 5 50) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d5_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 5 50) = true := by
  decide +kernel

end DubC2.Atlas
