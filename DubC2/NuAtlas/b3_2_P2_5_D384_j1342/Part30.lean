/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1342.Part29

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1342`, part 30/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1342_d28_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 28 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d28_u112 : (List.range' 112 3).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 28 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d28 : (List.range' 28 1).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 59 115 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1342_d28_u0 b3_2_P2_5_D384_j1342_d28_u28 rfl) (all_glue _ 56 28 31 59 b3_2_P2_5_D384_j1342_d28_u56 (all_glue _ 84 28 3 31 b3_2_P2_5_D384_j1342_d28_u84 b3_2_P2_5_D384_j1342_d28_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1342_d29 : (List.range' 29 1).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d30_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 30 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d30_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 30 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d30_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 30 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d30_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 30 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d30_u112 : (List.range' 112 18).all (detRowOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C 30 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1342_d30 : (List.range' 30 1).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 74 130 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1342_d30_u0 b3_2_P2_5_D384_j1342_d30_u28 rfl) (all_glue _ 56 28 46 74 b3_2_P2_5_D384_j1342_d30_u56 (all_glue _ 84 28 18 46 b3_2_P2_5_D384_j1342_d30_u84 b3_2_P2_5_D384_j1342_d30_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1342_d31 : (List.range' 31 2).all (detOK b3_2_P2_5_D384_j1342P b3_2_P2_5_D384_j1342C) = true := by
  decide +kernel

end DubC2.Atlas
