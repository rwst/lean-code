/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2635.Part77

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2635`, part 78/80 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2635_d25_u304 : (List.range' 304 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 25 71) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d25_u320 : (List.range' 320 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 25 71) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d25_u336 : (List.range' 336 16).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 25 71) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d25_u352 : (List.range' 352 3).all (detRowOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C 25 71) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d25 : (List.range' 25 1).all (detOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 176 179 355 (all_glue _ 0 80 96 176 (all_glue _ 0 32 48 80 (all_glue _ 0 16 16 32 b3_2_P2_5_D768_j2635_d25_u0 b3_2_P2_5_D768_j2635_d25_u16 rfl) (all_glue _ 32 16 32 48 b3_2_P2_5_D768_j2635_d25_u32 (all_glue _ 48 16 16 32 b3_2_P2_5_D768_j2635_d25_u48 b3_2_P2_5_D768_j2635_d25_u64 rfl) rfl) rfl) (all_glue _ 80 48 48 96 (all_glue _ 80 16 32 48 b3_2_P2_5_D768_j2635_d25_u80 (all_glue _ 96 16 16 32 b3_2_P2_5_D768_j2635_d25_u96 b3_2_P2_5_D768_j2635_d25_u112 rfl) rfl) (all_glue _ 128 16 32 48 b3_2_P2_5_D768_j2635_d25_u128 (all_glue _ 144 16 16 32 b3_2_P2_5_D768_j2635_d25_u144 b3_2_P2_5_D768_j2635_d25_u160 rfl) rfl) rfl) rfl) (all_glue _ 176 96 83 179 (all_glue _ 176 48 48 96 (all_glue _ 176 16 32 48 b3_2_P2_5_D768_j2635_d25_u176 (all_glue _ 192 16 16 32 b3_2_P2_5_D768_j2635_d25_u192 b3_2_P2_5_D768_j2635_d25_u208 rfl) rfl) (all_glue _ 224 16 32 48 b3_2_P2_5_D768_j2635_d25_u224 (all_glue _ 240 16 16 32 b3_2_P2_5_D768_j2635_d25_u240 b3_2_P2_5_D768_j2635_d25_u256 rfl) rfl) rfl) (all_glue _ 272 48 35 83 (all_glue _ 272 16 32 48 b3_2_P2_5_D768_j2635_d25_u272 (all_glue _ 288 16 16 32 b3_2_P2_5_D768_j2635_d25_u288 b3_2_P2_5_D768_j2635_d25_u304 rfl) rfl) (all_glue _ 320 16 19 35 b3_2_P2_5_D768_j2635_d25_u320 (all_glue _ 336 16 3 19 b3_2_P2_5_D768_j2635_d25_u336 b3_2_P2_5_D768_j2635_d25_u352 rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2635_d26 : (List.range' 26 1).all (detOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2635_d27 : (List.range' 27 2).all (detOK b3_2_P2_5_D768_j2635P b3_2_P2_5_D768_j2635C) = true := by
  decide +kernel

end DubC2.Atlas
