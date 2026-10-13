/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2740.Part76

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2740`, part 77/82 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2740_d24_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u96 : (List.range' 96 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u112 : (List.range' 112 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u128 : (List.range' 128 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24_u144 : (List.range' 144 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 24 32) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d24 : (List.range' 24 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 80 80 160 (all_glue _ 0 32 48 80 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2740_d24_u0 b3_2_P2_5_D768_j2740_d24_u16 rfl) (all_glue _ 32 16 32 48 b3_2_P2_5_D768_j2740_d24_u32 (all_glue _ 48 16 16 32 b3_2_P2_5_D768_j2740_d24_u48 b3_2_P2_5_D768_j2740_d24_u64 rfl) rfl) rfl) (all_glue _ 80 32 48 80 (all_glue _ 80 16 16 32 b3_2_P2_5_D768_j2740_d24_u80 b3_2_P2_5_D768_j2740_d24_u96 rfl) (all_glue _ 112 16 32 48 b3_2_P2_5_D768_j2740_d24_u112 (all_glue _ 128 16 16 32 b3_2_P2_5_D768_j2740_d24_u128 b3_2_P2_5_D768_j2740_d24_u144 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2740_d25 : (List.range' 25 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d26_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 26 23) = true := by
  decide +kernel

end DubC2.Atlas
