/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1371.Part14

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1371`, part 15/24 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1371_d0_u1632 : (List.range' 1632 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 0 358) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d0_u1664 : (List.range' 1664 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 0 358) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d0_u1696 : (List.range' 1696 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 0 358) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d0_u1728 : (List.range' 1728 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 0 358) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d0_u1760 : (List.range' 1760 30).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 0 358) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 896 894 1790 (all_glue _ 0 448 448 896 (all_glue _ 0 224 224 448 (all_glue _ 0 96 128 224 (all_glue _ 0 32 64 96 b3_2_P2_5_D384_j1371_d0_u0 (all_glue _ 32 32 32 64 b3_2_P2_5_D384_j1371_d0_u32 b3_2_P2_5_D384_j1371_d0_u64 rfl) rfl) (all_glue _ 96 64 64 128 (all_glue _ 96 32 32 64 b3_2_P2_5_D384_j1371_d0_u96 b3_2_P2_5_D384_j1371_d0_u128 rfl) (all_glue _ 160 32 32 64 b3_2_P2_5_D384_j1371_d0_u160 b3_2_P2_5_D384_j1371_d0_u192 rfl) rfl) rfl) (all_glue _ 224 96 128 224 (all_glue _ 224 32 64 96 b3_2_P2_5_D384_j1371_d0_u224 (all_glue _ 256 32 32 64 b3_2_P2_5_D384_j1371_d0_u256 b3_2_P2_5_D384_j1371_d0_u288 rfl) rfl) (all_glue _ 320 64 64 128 (all_glue _ 320 32 32 64 b3_2_P2_5_D384_j1371_d0_u320 b3_2_P2_5_D384_j1371_d0_u352 rfl) (all_glue _ 384 32 32 64 b3_2_P2_5_D384_j1371_d0_u384 b3_2_P2_5_D384_j1371_d0_u416 rfl) rfl) rfl) rfl) (all_glue _ 448 224 224 448 (all_glue _ 448 96 128 224 (all_glue _ 448 32 64 96 b3_2_P2_5_D384_j1371_d0_u448 (all_glue _ 480 32 32 64 b3_2_P2_5_D384_j1371_d0_u480 b3_2_P2_5_D384_j1371_d0_u512 rfl) rfl) (all_glue _ 544 64 64 128 (all_glue _ 544 32 32 64 b3_2_P2_5_D384_j1371_d0_u544 b3_2_P2_5_D384_j1371_d0_u576 rfl) (all_glue _ 608 32 32 64 b3_2_P2_5_D384_j1371_d0_u608 b3_2_P2_5_D384_j1371_d0_u640 rfl) rfl) rfl) (all_glue _ 672 96 128 224 (all_glue _ 672 32 64 96 b3_2_P2_5_D384_j1371_d0_u672 (all_glue _ 704 32 32 64 b3_2_P2_5_D384_j1371_d0_u704 b3_2_P2_5_D384_j1371_d0_u736 rfl) rfl) (all_glue _ 768 64 64 128 (all_glue _ 768 32 32 64 b3_2_P2_5_D384_j1371_d0_u768 b3_2_P2_5_D384_j1371_d0_u800 rfl) (all_glue _ 832 32 32 64 b3_2_P2_5_D384_j1371_d0_u832 b3_2_P2_5_D384_j1371_d0_u864 rfl) rfl) rfl) rfl) rfl) (all_glue _ 896 448 446 894 (all_glue _ 896 224 224 448 (all_glue _ 896 96 128 224 (all_glue _ 896 32 64 96 b3_2_P2_5_D384_j1371_d0_u896 (all_glue _ 928 32 32 64 b3_2_P2_5_D384_j1371_d0_u928 b3_2_P2_5_D384_j1371_d0_u960 rfl) rfl) (all_glue _ 992 64 64 128 (all_glue _ 992 32 32 64 b3_2_P2_5_D384_j1371_d0_u992 b3_2_P2_5_D384_j1371_d0_u1024 rfl) (all_glue _ 1056 32 32 64 b3_2_P2_5_D384_j1371_d0_u1056 b3_2_P2_5_D384_j1371_d0_u1088 rfl) rfl) rfl) (all_glue _ 1120 96 128 224 (all_glue _ 1120 32 64 96 b3_2_P2_5_D384_j1371_d0_u1120 (all_glue _ 1152 32 32 64 b3_2_P2_5_D384_j1371_d0_u1152 b3_2_P2_5_D384_j1371_d0_u1184 rfl) rfl) (all_glue _ 1216 64 64 128 (all_glue _ 1216 32 32 64 b3_2_P2_5_D384_j1371_d0_u1216 b3_2_P2_5_D384_j1371_d0_u1248 rfl) (all_glue _ 1280 32 32 64 b3_2_P2_5_D384_j1371_d0_u1280 b3_2_P2_5_D384_j1371_d0_u1312 rfl) rfl) rfl) rfl) (all_glue _ 1344 224 222 446 (all_glue _ 1344 96 128 224 (all_glue _ 1344 32 64 96 b3_2_P2_5_D384_j1371_d0_u1344 (all_glue _ 1376 32 32 64 b3_2_P2_5_D384_j1371_d0_u1376 b3_2_P2_5_D384_j1371_d0_u1408 rfl) rfl) (all_glue _ 1440 64 64 128 (all_glue _ 1440 32 32 64 b3_2_P2_5_D384_j1371_d0_u1440 b3_2_P2_5_D384_j1371_d0_u1472 rfl) (all_glue _ 1504 32 32 64 b3_2_P2_5_D384_j1371_d0_u1504 b3_2_P2_5_D384_j1371_d0_u1536 rfl) rfl) rfl) (all_glue _ 1568 96 126 222 (all_glue _ 1568 32 64 96 b3_2_P2_5_D384_j1371_d0_u1568 (all_glue _ 1600 32 32 64 b3_2_P2_5_D384_j1371_d0_u1600 b3_2_P2_5_D384_j1371_d0_u1632 rfl) rfl) (all_glue _ 1664 64 62 126 (all_glue _ 1664 32 32 64 b3_2_P2_5_D384_j1371_d0_u1664 b3_2_P2_5_D384_j1371_d0_u1696 rfl) (all_glue _ 1728 32 30 62 b3_2_P2_5_D384_j1371_d0_u1728 b3_2_P2_5_D384_j1371_d0_u1760 rfl) rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1371_d1_u0 : (List.range' 0 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d1_u32 : (List.range' 32 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d1_u64 : (List.range' 64 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d1_u96 : (List.range' 96 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d1_u128 : (List.range' 128 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d1_u160 : (List.range' 160 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d1_u192 : (List.range' 192 18).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 96 114 210 (all_glue _ 0 32 64 96 b3_2_P2_5_D384_j1371_d1_u0 (all_glue _ 32 32 32 64 b3_2_P2_5_D384_j1371_d1_u32 b3_2_P2_5_D384_j1371_d1_u64 rfl) rfl) (all_glue _ 96 64 50 114 (all_glue _ 96 32 32 64 b3_2_P2_5_D384_j1371_d1_u96 b3_2_P2_5_D384_j1371_d1_u128 rfl) (all_glue _ 160 32 18 50 b3_2_P2_5_D384_j1371_d1_u160 b3_2_P2_5_D384_j1371_d1_u192 rfl) rfl) rfl))

end DubC2.Atlas
