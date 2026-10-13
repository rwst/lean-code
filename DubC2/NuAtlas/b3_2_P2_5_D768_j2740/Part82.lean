/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2740.Part81

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2740`, part 82/82 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2740_d36_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 36 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d36_u80 : (List.range' 80 10).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 36 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d36 : (List.range' 36 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 48 42 90 (all_glue _ 0 16 32 48 b3_2_P2_5_D768_j2740_d36_u0 (all_glue _ 16 16 16 32 b3_2_P2_5_D768_j2740_d36_u16 b3_2_P2_5_D768_j2740_d36_u32 rfl) rfl) (all_glue _ 48 16 26 42 b3_2_P2_5_D768_j2740_d36_u48 (all_glue _ 64 16 10 26 b3_2_P2_5_D768_j2740_d36_u64 b3_2_P2_5_D768_j2740_d36_u80 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2740_d37_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 37 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d37_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 37 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d37_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 37 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d37_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 37 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d37_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 37 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d37_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 37 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d37_u96 : (List.range' 96 14).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 37 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d37 : (List.range' 37 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 48 62 110 (all_glue _ 0 16 32 48 b3_2_P2_5_D768_j2740_d37_u0 (all_glue _ 16 16 16 32 b3_2_P2_5_D768_j2740_d37_u16 b3_2_P2_5_D768_j2740_d37_u32 rfl) rfl) (all_glue _ 48 32 30 62 (all_glue _ 48 16 16 32 b3_2_P2_5_D768_j2740_d37_u48 b3_2_P2_5_D768_j2740_d37_u64 rfl) (all_glue _ 80 16 14 30 b3_2_P2_5_D768_j2740_d37_u80 b3_2_P2_5_D768_j2740_d37_u96 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2740_d38 : (List.range' 38 3).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true := by
  decide +kernel

end DubC2.Atlas
