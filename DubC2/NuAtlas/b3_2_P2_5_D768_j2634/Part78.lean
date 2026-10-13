/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2634.Part77

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2634`, part 78/80 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2634_d33_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 33 15) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d33_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 33 15) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d33_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 33 15) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d33_u64 : (List.range' 64 11).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 33 15) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d33 : (List.range' 33 1).all (detOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 32 43 75 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2634_d33_u0 b3_2_P2_5_D768_j2634_d33_u16 rfl) (all_glue _ 32 16 27 43 b3_2_P2_5_D768_j2634_d33_u32 (all_glue _ 48 16 11 27 b3_2_P2_5_D768_j2634_d33_u48 b3_2_P2_5_D768_j2634_d33_u64 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2634_d34_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 34 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d34_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 34 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d34_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 34 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d34_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 34 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d34_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 34 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d34 : (List.range' 34 1).all (detOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 32 48 80 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2634_d34_u0 b3_2_P2_5_D768_j2634_d34_u16 rfl) (all_glue _ 32 16 32 48 b3_2_P2_5_D768_j2634_d34_u32 (all_glue _ 48 16 16 32 b3_2_P2_5_D768_j2634_d34_u48 b3_2_P2_5_D768_j2634_d34_u64 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2634_d35_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 35 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d35_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 35 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2634_d35_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2634P b3_2_P2_5_D768_j2634C 35 17) = true := by
  decide +kernel

end DubC2.Atlas
