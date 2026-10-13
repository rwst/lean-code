/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2740.Part70

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2740`, part 71/82 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2740_d13_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 13 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d13_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 13 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d13_u80 : (List.range' 80 10).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 13 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d13 : (List.range' 13 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 48 42 90 (all_glue _ 0 16 32 48 b3_2_P2_5_D768_j2740_d13_u0 (all_glue _ 16 16 16 32 b3_2_P2_5_D768_j2740_d13_u16 b3_2_P2_5_D768_j2740_d13_u32 rfl) rfl) (all_glue _ 48 16 26 42 b3_2_P2_5_D768_j2740_d13_u48 (all_glue _ 64 16 10 26 b3_2_P2_5_D768_j2740_d13_u64 b3_2_P2_5_D768_j2740_d13_u80 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2740_d14_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d14_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d14_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d14_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d14_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d14_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d14_u96 : (List.range' 96 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d14_u112 : (List.range' 112 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d14_u128 : (List.range' 128 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 14 33) = true := by
  decide +kernel

end DubC2.Atlas
