/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2635.Part79

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2635`, part 80/80 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2635_d33_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 33 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d33_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 33 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d33_u96 : (List.range' 96 9).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 33 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d33 : (List.range' 33 1).all (detOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 48 57 105 (all_glue _ 0 16 32 48 b3_2_P2_5_D768_j2635_d33_u0 (all_glue _ 16 16 16 32 b3_2_P2_5_D768_j2635_d33_u16 b3_2_P2_5_D768_j2635_d33_u32 rfl) rfl) (all_glue _ 48 32 25 57 (all_glue _ 48 16 16 32 b3_2_P2_5_D768_j2635_d33_u48 b3_2_P2_5_D768_j2635_d33_u64 rfl) (all_glue _ 80 16 9 25 b3_2_P2_5_D768_j2635_d33_u80 b3_2_P2_5_D768_j2635_d33_u96 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2635_d34_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 34 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d34_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 34 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d34_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 34 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d34_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 34 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d34_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 34 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d34_u80 : (List.range' 80 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 34 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d34_u96 : (List.range' 96 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 34 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d34_u112 : (List.range' 112 8).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 34 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d34 : (List.range' 34 1).all (detOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 64 56 120 (all_glue _ 0 32 32 64 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2635_d34_u0 b3_2_P2_5_D768_j2635_d34_u16 rfl) (all_glue _ 32 16 16 32 b3_2_P2_5_D768_j2635_d34_u32 b3_2_P2_5_D768_j2635_d34_u48 rfl) rfl) (all_glue _ 64 32 24 56 (all_glue _ 64 16 16 32 b3_2_P2_5_D768_j2635_d34_u64 b3_2_P2_5_D768_j2635_d34_u80 rfl) (all_glue _ 96 16 8 24 b3_2_P2_5_D768_j2635_d34_u96 b3_2_P2_5_D768_j2635_d34_u112 rfl) rfl) rfl))

end DubC2.Atlas
