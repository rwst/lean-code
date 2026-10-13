/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2635.Part72

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2635`, part 73/80 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2635_d18_u288 : (List.range' 288 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 18 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d18_u304 : (List.range' 304 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 18 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d18_u320 : (List.range' 320 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 18 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d18_u336 : (List.range' 336 4).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 18 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d18 : (List.range' 18 1).all (detOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 176 164 340 (all_glue _ 0 80 96 176 (all_glue _ 0 32 48 80 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2635_d18_u0 b3_2_P2_5_D768_j2635_d18_u16 rfl) (all_glue _ 32 16 32 48 b3_2_P2_5_D768_j2635_d18_u32 (all_glue _ 48 16 16 32 b3_2_P2_5_D768_j2635_d18_u48 b3_2_P2_5_D768_j2635_d18_u64 rfl) rfl) rfl) (all_glue _ 80 48 48 96 (all_glue _ 80 16 32 48 b3_2_P2_5_D768_j2635_d18_u80 (all_glue _ 96 16 16 32 b3_2_P2_5_D768_j2635_d18_u96 b3_2_P2_5_D768_j2635_d18_u112 rfl) rfl) (all_glue _ 128 16 32 48 b3_2_P2_5_D768_j2635_d18_u128 (all_glue _ 144 16 16 32 b3_2_P2_5_D768_j2635_d18_u144 b3_2_P2_5_D768_j2635_d18_u160 rfl) rfl) rfl) rfl) (all_glue _ 176 80 84 164 (all_glue _ 176 32 48 80 (all_glue _ 176 16 16 32 b3_2_P2_5_D768_j2635_d18_u176 b3_2_P2_5_D768_j2635_d18_u192 rfl) (all_glue _ 208 16 32 48 b3_2_P2_5_D768_j2635_d18_u208 (all_glue _ 224 16 16 32 b3_2_P2_5_D768_j2635_d18_u224 b3_2_P2_5_D768_j2635_d18_u240 rfl) rfl) rfl) (all_glue _ 256 48 36 84 (all_glue _ 256 16 32 48 b3_2_P2_5_D768_j2635_d18_u256 (all_glue _ 272 16 16 32 b3_2_P2_5_D768_j2635_d18_u272 b3_2_P2_5_D768_j2635_d18_u288 rfl) rfl) (all_glue _ 304 16 20 36 b3_2_P2_5_D768_j2635_d18_u304 (all_glue _ 320 16 4 20 b3_2_P2_5_D768_j2635_d18_u320 b3_2_P2_5_D768_j2635_d18_u336 rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2635_d19 : (List.range' 19 2).all (detOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d21 : (List.range' 21 1).all (detOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C) = true := by
  decide +kernel

end DubC2.Atlas
