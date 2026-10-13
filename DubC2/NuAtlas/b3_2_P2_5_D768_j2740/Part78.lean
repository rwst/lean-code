/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2740.Part77

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2740`, part 78/82 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2740_d26_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 26 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d26_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 26 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d26_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 26 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d26_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 26 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d26_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 26 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d26_u96 : (List.range' 96 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 26 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d26_u112 : (List.range' 112 3).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 26 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d26 : (List.range' 26 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 64 51 115 (all_glue _ 0 32 32 64 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2740_d26_u0 b3_2_P2_5_D768_j2740_d26_u16 rfl) (all_glue _ 32 16 16 32 b3_2_P2_5_D768_j2740_d26_u32 b3_2_P2_5_D768_j2740_d26_u48 rfl) rfl) (all_glue _ 64 32 19 51 (all_glue _ 64 16 16 32 b3_2_P2_5_D768_j2740_d26_u64 b3_2_P2_5_D768_j2740_d26_u80 rfl) (all_glue _ 96 16 3 19 b3_2_P2_5_D768_j2740_d26_u96 b3_2_P2_5_D768_j2740_d26_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2740_d27_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d27_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d27_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d27_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d27_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 27 20) = true := by
  decide +kernel

end DubC2.Atlas
