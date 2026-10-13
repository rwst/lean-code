/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D96_j328.Part3

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D96_j328`, part 4/9 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D96_j328_d0_u1008 : (List.range' 1008 22).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 0 206) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 504 526 1030 (all_glue _ 0 224 280 504 (all_glue _ 0 112 112 224 (all_glue _ 0 56 56 112 b3_2_P2_5_D96_j328_d0_u0 b3_2_P2_5_D96_j328_d0_u56 rfl) (all_glue _ 112 56 56 112 b3_2_P2_5_D96_j328_d0_u112 b3_2_P2_5_D96_j328_d0_u168 rfl) rfl) (all_glue _ 224 112 168 280 (all_glue _ 224 56 56 112 b3_2_P2_5_D96_j328_d0_u224 b3_2_P2_5_D96_j328_d0_u280 rfl) (all_glue _ 336 56 112 168 b3_2_P2_5_D96_j328_d0_u336 (all_glue _ 392 56 56 112 b3_2_P2_5_D96_j328_d0_u392 b3_2_P2_5_D96_j328_d0_u448 rfl) rfl) rfl) rfl) (all_glue _ 504 280 246 526 (all_glue _ 504 112 168 280 (all_glue _ 504 56 56 112 b3_2_P2_5_D96_j328_d0_u504 b3_2_P2_5_D96_j328_d0_u560 rfl) (all_glue _ 616 56 112 168 b3_2_P2_5_D96_j328_d0_u616 (all_glue _ 672 56 56 112 b3_2_P2_5_D96_j328_d0_u672 b3_2_P2_5_D96_j328_d0_u728 rfl) rfl) rfl) (all_glue _ 784 112 134 246 (all_glue _ 784 56 56 112 b3_2_P2_5_D96_j328_d0_u784 b3_2_P2_5_D96_j328_d0_u840 rfl) (all_glue _ 896 56 78 134 b3_2_P2_5_D96_j328_d0_u896 (all_glue _ 952 56 22 78 b3_2_P2_5_D96_j328_d0_u952 b3_2_P2_5_D96_j328_d0_u1008 rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D96_j328_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u0 : (List.range' 0 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u56 : (List.range' 56 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u112 : (List.range' 112 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u168 : (List.range' 168 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u224 : (List.range' 224 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u280 : (List.range' 280 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u336 : (List.range' 336 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u392 : (List.range' 392 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

end DubC2.Atlas
