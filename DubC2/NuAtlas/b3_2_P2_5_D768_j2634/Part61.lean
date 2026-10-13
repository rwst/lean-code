/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2634.Part60

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2634`, part 61/80 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2634_d7_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 7 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d7_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 7 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d7_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 7 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d7_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 7 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d7_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 7 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d7_u96 : (List.range' 96 9).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 7 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d7 : (List.range' 7 1).all (detOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 48 57 105 (all_glue _ 0 16 32 48 b3_2_P2_5_D768_j2634_d7_u0 (all_glue _ 16 16 16 32 b3_2_P2_5_D768_j2634_d7_u16 b3_2_P2_5_D768_j2634_d7_u32 rfl) rfl) (all_glue _ 48 32 25 57 (all_glue _ 48 16 16 32 b3_2_P2_5_D768_j2634_d7_u48 b3_2_P2_5_D768_j2634_d7_u64 rfl) (all_glue _ 80 16 9 25 b3_2_P2_5_D768_j2634_d7_u80 b3_2_P2_5_D768_j2634_d7_u96 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2634_d8_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 8 72) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d8_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 8 72) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d8_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 8 72) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d8_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 8 72) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d8_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 8 72) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d8_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 8 72) = true := by
  decide +kernel

end DubC2.Atlas
