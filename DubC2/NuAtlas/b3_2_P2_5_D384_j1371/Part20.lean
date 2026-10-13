/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1371.Part19

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1371`, part 20/24 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1371_d2_u1536 : (List.range' 1536 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 2 350) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d2_u1568 : (List.range' 1568 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 2 350) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d2_u1600 : (List.range' 1600 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 2 350) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d2_u1632 : (List.range' 1632 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 2 350) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d2_u1664 : (List.range' 1664 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 2 350) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d2_u1696 : (List.range' 1696 32).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 2 350) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d2_u1728 : (List.range' 1728 22).all (detRowOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C 2 350) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1371_d2 : (List.range' 2 1).all (detOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 864 886 1750 (all_glue _ 0 416 448 864 (all_glue _ 0 192 224 416 (all_glue _ 0 96 96 192 (all_glue _ 0 32 64 96 b3_2_P2_5_D384_j1371_d2_u0 (all_glue _ 32 32 32 64 b3_2_P2_5_D384_j1371_d2_u32 b3_2_P2_5_D384_j1371_d2_u64 rfl) rfl) (all_glue _ 96 32 64 96 b3_2_P2_5_D384_j1371_d2_u96 (all_glue _ 128 32 32 64 b3_2_P2_5_D384_j1371_d2_u128 b3_2_P2_5_D384_j1371_d2_u160 rfl) rfl) rfl) (all_glue _ 192 96 128 224 (all_glue _ 192 32 64 96 b3_2_P2_5_D384_j1371_d2_u192 (all_glue _ 224 32 32 64 b3_2_P2_5_D384_j1371_d2_u224 b3_2_P2_5_D384_j1371_d2_u256 rfl) rfl) (all_glue _ 288 64 64 128 (all_glue _ 288 32 32 64 b3_2_P2_5_D384_j1371_d2_u288 b3_2_P2_5_D384_j1371_d2_u320 rfl) (all_glue _ 352 32 32 64 b3_2_P2_5_D384_j1371_d2_u352 b3_2_P2_5_D384_j1371_d2_u384 rfl) rfl) rfl) rfl) (all_glue _ 416 224 224 448 (all_glue _ 416 96 128 224 (all_glue _ 416 32 64 96 b3_2_P2_5_D384_j1371_d2_u416 (all_glue _ 448 32 32 64 b3_2_P2_5_D384_j1371_d2_u448 b3_2_P2_5_D384_j1371_d2_u480 rfl) rfl) (all_glue _ 512 64 64 128 (all_glue _ 512 32 32 64 b3_2_P2_5_D384_j1371_d2_u512 b3_2_P2_5_D384_j1371_d2_u544 rfl) (all_glue _ 576 32 32 64 b3_2_P2_5_D384_j1371_d2_u576 b3_2_P2_5_D384_j1371_d2_u608 rfl) rfl) rfl) (all_glue _ 640 96 128 224 (all_glue _ 640 32 64 96 b3_2_P2_5_D384_j1371_d2_u640 (all_glue _ 672 32 32 64 b3_2_P2_5_D384_j1371_d2_u672 b3_2_P2_5_D384_j1371_d2_u704 rfl) rfl) (all_glue _ 736 64 64 128 (all_glue _ 736 32 32 64 b3_2_P2_5_D384_j1371_d2_u736 b3_2_P2_5_D384_j1371_d2_u768 rfl) (all_glue _ 800 32 32 64 b3_2_P2_5_D384_j1371_d2_u800 b3_2_P2_5_D384_j1371_d2_u832 rfl) rfl) rfl) rfl) rfl) (all_glue _ 864 448 438 886 (all_glue _ 864 224 224 448 (all_glue _ 864 96 128 224 (all_glue _ 864 32 64 96 b3_2_P2_5_D384_j1371_d2_u864 (all_glue _ 896 32 32 64 b3_2_P2_5_D384_j1371_d2_u896 b3_2_P2_5_D384_j1371_d2_u928 rfl) rfl) (all_glue _ 960 64 64 128 (all_glue _ 960 32 32 64 b3_2_P2_5_D384_j1371_d2_u960 b3_2_P2_5_D384_j1371_d2_u992 rfl) (all_glue _ 1024 32 32 64 b3_2_P2_5_D384_j1371_d2_u1024 b3_2_P2_5_D384_j1371_d2_u1056 rfl) rfl) rfl) (all_glue _ 1088 96 128 224 (all_glue _ 1088 32 64 96 b3_2_P2_5_D384_j1371_d2_u1088 (all_glue _ 1120 32 32 64 b3_2_P2_5_D384_j1371_d2_u1120 b3_2_P2_5_D384_j1371_d2_u1152 rfl) rfl) (all_glue _ 1184 64 64 128 (all_glue _ 1184 32 32 64 b3_2_P2_5_D384_j1371_d2_u1184 b3_2_P2_5_D384_j1371_d2_u1216 rfl) (all_glue _ 1248 32 32 64 b3_2_P2_5_D384_j1371_d2_u1248 b3_2_P2_5_D384_j1371_d2_u1280 rfl) rfl) rfl) rfl) (all_glue _ 1312 224 214 438 (all_glue _ 1312 96 128 224 (all_glue _ 1312 32 64 96 b3_2_P2_5_D384_j1371_d2_u1312 (all_glue _ 1344 32 32 64 b3_2_P2_5_D384_j1371_d2_u1344 b3_2_P2_5_D384_j1371_d2_u1376 rfl) rfl) (all_glue _ 1408 64 64 128 (all_glue _ 1408 32 32 64 b3_2_P2_5_D384_j1371_d2_u1408 b3_2_P2_5_D384_j1371_d2_u1440 rfl) (all_glue _ 1472 32 32 64 b3_2_P2_5_D384_j1371_d2_u1472 b3_2_P2_5_D384_j1371_d2_u1504 rfl) rfl) rfl) (all_glue _ 1536 96 118 214 (all_glue _ 1536 32 64 96 b3_2_P2_5_D384_j1371_d2_u1536 (all_glue _ 1568 32 32 64 b3_2_P2_5_D384_j1371_d2_u1568 b3_2_P2_5_D384_j1371_d2_u1600 rfl) rfl) (all_glue _ 1632 64 54 118 (all_glue _ 1632 32 32 64 b3_2_P2_5_D384_j1371_d2_u1632 b3_2_P2_5_D384_j1371_d2_u1664 rfl) (all_glue _ 1696 32 22 54 b3_2_P2_5_D384_j1371_d2_u1696 b3_2_P2_5_D384_j1371_d2_u1728 rfl) rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1371_d3 : (List.range' 3 1).all (detOK b3_2_P2_5_D384_j1371P b3_2_P2_5_D384_j1371C) = true := by
  decide +kernel

end DubC2.Atlas
