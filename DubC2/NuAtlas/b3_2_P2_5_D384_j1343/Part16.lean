/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1343.Part15

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1343`, part 16/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1343_d1_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1_u112 : (List.range' 112 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1_u140 : (List.range' 140 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1_u168 : (List.range' 168 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1_u196 : (List.range' 196 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1_u224 : (List.range' 224 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1_u252 : (List.range' 252 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 1 56) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 140 140 280 (all_glue _ 0 56 84 140 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1343_d1_u0 b3_2_P2_5_D384_j1343_d1_u28 rfl) (all_glue _ 56 28 56 84 b3_2_P2_5_D384_j1343_d1_u56 (all_glue _ 84 28 28 56 b3_2_P2_5_D384_j1343_d1_u84 b3_2_P2_5_D384_j1343_d1_u112 rfl) rfl) rfl) (all_glue _ 140 56 84 140 (all_glue _ 140 28 28 56 b3_2_P2_5_D384_j1343_d1_u140 b3_2_P2_5_D384_j1343_d1_u168 rfl) (all_glue _ 196 28 56 84 b3_2_P2_5_D384_j1343_d1_u196 (all_glue _ 224 28 28 56 b3_2_P2_5_D384_j1343_d1_u224 b3_2_P2_5_D384_j1343_d1_u252 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d2_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 2 404) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d2_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 2 404) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d2_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 2 404) = true := by
  decide +kernel

end DubC2.Atlas
