/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2740.Part80

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2740`, part 81/82 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2740_d31_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 31 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d31_u80 : (List.range' 80 15).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 31 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d31 : (List.range' 31 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 48 47 95 (all_glue _ 0 16 32 48 b3_2_P2_5_D768_j2740_d31_u0 (all_glue _ 16 16 16 32 b3_2_P2_5_D768_j2740_d31_u16 b3_2_P2_5_D768_j2740_d31_u32 rfl) rfl) (all_glue _ 48 16 31 47 b3_2_P2_5_D768_j2740_d31_u48 (all_glue _ 64 16 15 31 b3_2_P2_5_D768_j2740_d31_u64 b3_2_P2_5_D768_j2740_d31_u80 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2740_d32 : (List.range' 32 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d33_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 33 13) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d33_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 33 13) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d33_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 33 13) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d33_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 33 13) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d33_u64 : (List.range' 64 1).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 33 13) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d33 : (List.range' 33 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 32 33 65 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2740_d33_u0 b3_2_P2_5_D768_j2740_d33_u16 rfl) (all_glue _ 32 16 17 33 b3_2_P2_5_D768_j2740_d33_u32 (all_glue _ 48 16 1 17 b3_2_P2_5_D768_j2740_d33_u48 b3_2_P2_5_D768_j2740_d33_u64 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2740_d34 : (List.range' 34 2).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d36_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 36 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d36_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 36 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d36_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 36 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d36_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 36 18) = true := by
  decide +kernel

end DubC2.Atlas
