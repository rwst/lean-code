/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1342.Part22

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1342`, part 23/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1342_d3_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 3 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d3_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 3 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d3_u112 : (List.range' 112 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 3 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d3_u140 : (List.range' 140 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 3 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d3_u168 : (List.range' 168 22).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 3 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d3 : (List.range' 3 1).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 84 106 190 (all_glue _ 0 28 56 84 b3_2_P2_5_D384_j1342_d3_u0 (all_glue _ 28 28 28 56 b3_2_P2_5_D384_j1342_d3_u28 b3_2_P2_5_D384_j1342_d3_u56 rfl) rfl) (all_glue _ 84 56 50 106 (all_glue _ 84 28 28 56 b3_2_P2_5_D384_j1342_d3_u84 b3_2_P2_5_D384_j1342_d3_u112 rfl) (all_glue _ 140 28 22 50 b3_2_P2_5_D384_j1342_d3_u140 b3_2_P2_5_D384_j1342_d3_u168 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1342_d4_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 4 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d4_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 4 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d4_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 4 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d4_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 4 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d4_u112 : (List.range' 112 18).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 4 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 74 130 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1342_d4_u0 b3_2_P2_5_D384_j1342_d4_u28 rfl) (all_glue _ 56 28 46 74 b3_2_P2_5_D384_j1342_d4_u56 (all_glue _ 84 28 18 46 b3_2_P2_5_D384_j1342_d4_u84 b3_2_P2_5_D384_j1342_d4_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1342_d5_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 5 52) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d5_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 5 52) = true := by
  decide +kernel

end DubC2.Atlas
