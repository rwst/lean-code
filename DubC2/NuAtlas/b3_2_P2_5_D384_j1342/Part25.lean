/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1342.Part24

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1342`, part 25/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1342_d6_u112 : (List.range' 112 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 6 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d6_u140 : (List.range' 140 20).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 6 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 84 76 160 (all_glue _ 0 28 56 84 b3_2_P2_5_D384_j1342_d6_u0 (all_glue _ 28 28 28 56 b3_2_P2_5_D384_j1342_d6_u28 b3_2_P2_5_D384_j1342_d6_u56 rfl) rfl) (all_glue _ 84 28 48 76 b3_2_P2_5_D384_j1342_d6_u84 (all_glue _ 112 28 20 48 b3_2_P2_5_D384_j1342_d6_u112 b3_2_P2_5_D384_j1342_d6_u140 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1342_d7 : (List.range' 7 1).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d8_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 8 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d8_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 8 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d8_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 8 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d8_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 8 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d8_u112 : (List.range' 112 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 8 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d8_u140 : (List.range' 140 5).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 8 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d8 : (List.range' 8 1).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 84 61 145 (all_glue _ 0 28 56 84 b3_2_P2_5_D384_j1342_d8_u0 (all_glue _ 28 28 28 56 b3_2_P2_5_D384_j1342_d8_u28 b3_2_P2_5_D384_j1342_d8_u56 rfl) rfl) (all_glue _ 84 28 33 61 b3_2_P2_5_D384_j1342_d8_u84 (all_glue _ 112 28 5 33 b3_2_P2_5_D384_j1342_d8_u112 b3_2_P2_5_D384_j1342_d8_u140 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1342_d9_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 9 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d9_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 9 29) = true := by
  decide +kernel

end DubC2.Atlas
