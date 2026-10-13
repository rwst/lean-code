/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D96_j343.Part5

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D96_j343`, part 6/9 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D96_j343_d2_u936 : (List.range' 936 34).all (detRowOK b3_2_P2_5_D96_j343P b3_2_P2_5_D96_j343C 2 194) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j343_d2 : (List.range' 2 1).all (detOK b3_2_P2_5_D96_j343P b3_2_P2_5_D96_j343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 468 502 970 (all_glue _ 0 208 260 468 (all_glue _ 0 104 104 208 (all_glue _ 0 52 52 104 b3_2_P2_5_D96_j343_d2_u0 b3_2_P2_5_D96_j343_d2_u52 rfl) (all_glue _ 104 52 52 104 b3_2_P2_5_D96_j343_d2_u104 b3_2_P2_5_D96_j343_d2_u156 rfl) rfl) (all_glue _ 208 104 156 260 (all_glue _ 208 52 52 104 b3_2_P2_5_D96_j343_d2_u208 b3_2_P2_5_D96_j343_d2_u260 rfl) (all_glue _ 312 52 104 156 b3_2_P2_5_D96_j343_d2_u312 (all_glue _ 364 52 52 104 b3_2_P2_5_D96_j343_d2_u364 b3_2_P2_5_D96_j343_d2_u416 rfl) rfl) rfl) rfl) (all_glue _ 468 260 242 502 (all_glue _ 468 104 156 260 (all_glue _ 468 52 52 104 b3_2_P2_5_D96_j343_d2_u468 b3_2_P2_5_D96_j343_d2_u520 rfl) (all_glue _ 572 52 104 156 b3_2_P2_5_D96_j343_d2_u572 (all_glue _ 624 52 52 104 b3_2_P2_5_D96_j343_d2_u624 b3_2_P2_5_D96_j343_d2_u676 rfl) rfl) rfl) (all_glue _ 728 104 138 242 (all_glue _ 728 52 52 104 b3_2_P2_5_D96_j343_d2_u728 b3_2_P2_5_D96_j343_d2_u780 rfl) (all_glue _ 832 52 86 138 b3_2_P2_5_D96_j343_d2_u832 (all_glue _ 884 52 34 86 b3_2_P2_5_D96_j343_d2_u884 b3_2_P2_5_D96_j343_d2_u936 rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D96_j343_d3 : (List.range' 3 1).all (detOK b3_2_P2_5_D96_j343P b3_2_P2_5_D96_j343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j343_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D96_j343P b3_2_P2_5_D96_j343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j343_d5 : (List.range' 5 1).all (detOK b3_2_P2_5_D96_j343P b3_2_P2_5_D96_j343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j343_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D96_j343P b3_2_P2_5_D96_j343C) = true := by
  decide +kernel

end DubC2.Atlas
