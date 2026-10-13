/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1371.Part20

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1371`, part 21/24 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1371_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d5_u0 : (List.range' 0 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 5 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d5_u32 : (List.range' 32 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 5 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d5_u64 : (List.range' 64 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 5 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d5_u96 : (List.range' 96 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 5 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d5_u128 : (List.range' 128 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 5 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d5_u160 : (List.range' 160 30).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 5 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d5 : (List.range' 5 1).all (detOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 96 94 190 (all_glue _ 0 32 64 96 b3_2_P2_5_D384_j1371_d5_u0 (all_glue _ 32 32 32 64 b3_2_P2_5_D384_j1371_d5_u32 b3_2_P2_5_D384_j1371_d5_u64 rfl) rfl) (all_glue _ 96 32 62 94 b3_2_P2_5_D384_j1371_d5_u96 (all_glue _ 128 32 30 62 b3_2_P2_5_D384_j1371_d5_u128 b3_2_P2_5_D384_j1371_d5_u160 rfl) rfl) rfl))

end DubC2.Atlas
