/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2740.Part75

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2740`, part 76/82 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2740_d21_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 21 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d21_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 21 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d21_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 21 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d21_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 21 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d21_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 21 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d21_u80 : (List.range' 80 15).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 21 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d21 : (List.range' 21 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 48 47 95 (all_glue _ 0 16 32 48 b3_2_P2_5_D768_j2740_d21_u0 (all_glue _ 16 16 16 32 b3_2_P2_5_D768_j2740_d21_u16 b3_2_P2_5_D768_j2740_d21_u32 rfl) rfl) (all_glue _ 48 16 31 47 b3_2_P2_5_D768_j2740_d21_u48 (all_glue _ 64 16 15 31 b3_2_P2_5_D768_j2740_d21_u64 b3_2_P2_5_D768_j2740_d21_u80 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2740_d22 : (List.range' 22 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d23_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 23 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d23_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 23 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d23_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 23 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d23_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 23 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d23_u64 : (List.range' 64 6).all (detRowOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C 23 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2740_d23 : (List.range' 23 1).all (detOK b3_2_P2_5_D768_j2740P b3_2_P2_5_D768_j2740C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 32 38 70 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2740_d23_u0 b3_2_P2_5_D768_j2740_d23_u16 rfl) (all_glue _ 32 16 22 38 b3_2_P2_5_D768_j2740_d23_u32 (all_glue _ 48 16 6 22 b3_2_P2_5_D768_j2740_d23_u48 b3_2_P2_5_D768_j2740_d23_u64 rfl) rfl) rfl))

end DubC2.Atlas
