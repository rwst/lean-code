/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D96_j328.Part4

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D96_j328`, part 5/9 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D96_j328_d2_u448 : (List.range' 448 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u504 : (List.range' 504 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u560 : (List.range' 560 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u616 : (List.range' 616 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u672 : (List.range' 672 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u728 : (List.range' 728 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u784 : (List.range' 784 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u840 : (List.range' 840 56).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2_u896 : (List.range' 896 44).all (detRowOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C 2 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j328_d2 : (List.range' 2 1).all (detOK b3_2_P2_5_D96_j328P b3_2_P2_5_D96_j328C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 448 492 940 (all_glue _ 0 224 224 448 (all_glue _ 0 112 112 224 (all_glue _ 0 56 56 112 b3_2_P2_5_D96_j328_d2_u0 b3_2_P2_5_D96_j328_d2_u56 rfl) (all_glue _ 112 56 56 112 b3_2_P2_5_D96_j328_d2_u112 b3_2_P2_5_D96_j328_d2_u168 rfl) rfl) (all_glue _ 224 112 112 224 (all_glue _ 224 56 56 112 b3_2_P2_5_D96_j328_d2_u224 b3_2_P2_5_D96_j328_d2_u280 rfl) (all_glue _ 336 56 56 112 b3_2_P2_5_D96_j328_d2_u336 b3_2_P2_5_D96_j328_d2_u392 rfl) rfl) rfl) (all_glue _ 448 224 268 492 (all_glue _ 448 112 112 224 (all_glue _ 448 56 56 112 b3_2_P2_5_D96_j328_d2_u448 b3_2_P2_5_D96_j328_d2_u504 rfl) (all_glue _ 560 56 56 112 b3_2_P2_5_D96_j328_d2_u560 b3_2_P2_5_D96_j328_d2_u616 rfl) rfl) (all_glue _ 672 112 156 268 (all_glue _ 672 56 56 112 b3_2_P2_5_D96_j328_d2_u672 b3_2_P2_5_D96_j328_d2_u728 rfl) (all_glue _ 784 56 100 156 b3_2_P2_5_D96_j328_d2_u784 (all_glue _ 840 56 44 100 b3_2_P2_5_D96_j328_d2_u840 b3_2_P2_5_D96_j328_d2_u896 rfl) rfl) rfl) rfl) rfl))

end DubC2.Atlas
