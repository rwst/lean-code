/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2764.Part100

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2764`, part 101/143 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2764_d7_u504 : (List.range' 504 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 7 108) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d7_u516 : (List.range' 516 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 7 108) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d7_u528 : (List.range' 528 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 7 108) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d7 : (List.range' 7 1).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 264 276 540 (all_glue _ 0 132 132 264 (all_glue _ 0 60 72 132 (all_glue _ 0 24 36 60 (all_glue _ 0 12 12 24 b3_2_P2_5_D768_j2764_d7_u0 b3_2_P2_5_D768_j2764_d7_u12 rfl) (all_glue _ 24 12 24 36 b3_2_P2_5_D768_j2764_d7_u24 (all_glue _ 36 12 12 24 b3_2_P2_5_D768_j2764_d7_u36 b3_2_P2_5_D768_j2764_d7_u48 rfl) rfl) rfl) (all_glue _ 60 36 36 72 (all_glue _ 60 12 24 36 b3_2_P2_5_D768_j2764_d7_u60 (all_glue _ 72 12 12 24 b3_2_P2_5_D768_j2764_d7_u72 b3_2_P2_5_D768_j2764_d7_u84 rfl) rfl) (all_glue _ 96 12 24 36 b3_2_P2_5_D768_j2764_d7_u96 (all_glue _ 108 12 12 24 b3_2_P2_5_D768_j2764_d7_u108 b3_2_P2_5_D768_j2764_d7_u120 rfl) rfl) rfl) rfl) (all_glue _ 132 60 72 132 (all_glue _ 132 24 36 60 (all_glue _ 132 12 12 24 b3_2_P2_5_D768_j2764_d7_u132 b3_2_P2_5_D768_j2764_d7_u144 rfl) (all_glue _ 156 12 24 36 b3_2_P2_5_D768_j2764_d7_u156 (all_glue _ 168 12 12 24 b3_2_P2_5_D768_j2764_d7_u168 b3_2_P2_5_D768_j2764_d7_u180 rfl) rfl) rfl) (all_glue _ 192 36 36 72 (all_glue _ 192 12 24 36 b3_2_P2_5_D768_j2764_d7_u192 (all_glue _ 204 12 12 24 b3_2_P2_5_D768_j2764_d7_u204 b3_2_P2_5_D768_j2764_d7_u216 rfl) rfl) (all_glue _ 228 12 24 36 b3_2_P2_5_D768_j2764_d7_u228 (all_glue _ 240 12 12 24 b3_2_P2_5_D768_j2764_d7_u240 b3_2_P2_5_D768_j2764_d7_u252 rfl) rfl) rfl) rfl) rfl) (all_glue _ 264 132 144 276 (all_glue _ 264 60 72 132 (all_glue _ 264 24 36 60 (all_glue _ 264 12 12 24 b3_2_P2_5_D768_j2764_d7_u264 b3_2_P2_5_D768_j2764_d7_u276 rfl) (all_glue _ 288 12 24 36 b3_2_P2_5_D768_j2764_d7_u288 (all_glue _ 300 12 12 24 b3_2_P2_5_D768_j2764_d7_u300 b3_2_P2_5_D768_j2764_d7_u312 rfl) rfl) rfl) (all_glue _ 324 36 36 72 (all_glue _ 324 12 24 36 b3_2_P2_5_D768_j2764_d7_u324 (all_glue _ 336 12 12 24 b3_2_P2_5_D768_j2764_d7_u336 b3_2_P2_5_D768_j2764_d7_u348 rfl) rfl) (all_glue _ 360 12 24 36 b3_2_P2_5_D768_j2764_d7_u360 (all_glue _ 372 12 12 24 b3_2_P2_5_D768_j2764_d7_u372 b3_2_P2_5_D768_j2764_d7_u384 rfl) rfl) rfl) rfl) (all_glue _ 396 72 72 144 (all_glue _ 396 36 36 72 (all_glue _ 396 12 24 36 b3_2_P2_5_D768_j2764_d7_u396 (all_glue _ 408 12 12 24 b3_2_P2_5_D768_j2764_d7_u408 b3_2_P2_5_D768_j2764_d7_u420 rfl) rfl) (all_glue _ 432 12 24 36 b3_2_P2_5_D768_j2764_d7_u432 (all_glue _ 444 12 12 24 b3_2_P2_5_D768_j2764_d7_u444 b3_2_P2_5_D768_j2764_d7_u456 rfl) rfl) rfl) (all_glue _ 468 36 36 72 (all_glue _ 468 12 24 36 b3_2_P2_5_D768_j2764_d7_u468 (all_glue _ 480 12 12 24 b3_2_P2_5_D768_j2764_d7_u480 b3_2_P2_5_D768_j2764_d7_u492 rfl) rfl) (all_glue _ 504 12 24 36 b3_2_P2_5_D768_j2764_d7_u504 (all_glue _ 516 12 12 24 b3_2_P2_5_D768_j2764_d7_u516 b3_2_P2_5_D768_j2764_d7_u528 rfl) rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2764_d8 : (List.range' 8 1).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u0 : (List.range' 0 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u12 : (List.range' 12 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u24 : (List.range' 24 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u36 : (List.range' 36 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u48 : (List.range' 48 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u60 : (List.range' 60 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u72 : (List.range' 72 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u84 : (List.range' 84 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d9_u96 : (List.range' 96 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 9 74) = true := by
  decide +kernel

end DubC2.Atlas
