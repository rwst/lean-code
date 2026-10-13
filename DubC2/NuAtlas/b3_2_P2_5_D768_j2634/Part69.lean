/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2634.Part68

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2634`, part 69/80 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2634_d16_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 16 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d16_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 16 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d16_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 16 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d16_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 16 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d16_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 16 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d16_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 16 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d16_u96 : (List.range' 96 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 16 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d16_u112 : (List.range' 112 8).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 16 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d16 : (List.range' 16 1).all (detOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 64 56 120 (all_glue _ 0 32 32 64 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2634_d16_u0 b3_2_P2_5_D768_j2634_d16_u16 rfl) (all_glue _ 32 16 16 32 b3_2_P2_5_D768_j2634_d16_u32 b3_2_P2_5_D768_j2634_d16_u48 rfl) rfl) (all_glue _ 64 32 24 56 (all_glue _ 64 16 16 32 b3_2_P2_5_D768_j2634_d16_u64 b3_2_P2_5_D768_j2634_d16_u80 rfl) (all_glue _ 96 16 8 24 b3_2_P2_5_D768_j2634_d16_u96 b3_2_P2_5_D768_j2634_d16_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2634_d17_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 17 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d17_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 17 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d17_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 17 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d17_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 17 18) = true := by
  decide +kernel

end DubC2.Atlas
