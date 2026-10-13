/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1344.Part22

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1344`, part 23/29 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1344_d3_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 3 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d3_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 3 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d3_u58 : (List.range' 58 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 3 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d3_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 3 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d3_u116 : (List.range' 116 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 3 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d3_u145 : (List.range' 145 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 3 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d3_u174 : (List.range' 174 1).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 3 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d3 : (List.range' 3 1).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 87 88 175 (all_glue _ 0 29 58 87 b3_2_P2_5_D384_j1344_d3_u0 (all_glue _ 29 29 29 58 b3_2_P2_5_D384_j1344_d3_u29 b3_2_P2_5_D384_j1344_d3_u58 rfl) rfl) (all_glue _ 87 58 30 88 (all_glue _ 87 29 29 58 b3_2_P2_5_D384_j1344_d3_u87 b3_2_P2_5_D384_j1344_d3_u116 rfl) (all_glue _ 145 29 1 30 b3_2_P2_5_D384_j1344_d3_u145 b3_2_P2_5_D384_j1344_d3_u174 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1344_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d5_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 5 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d5_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 5 46) = true := by
  decide +kernel

end DubC2.Atlas
