/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2764.Part142

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2764`, part 143/143 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2764_d60_u36 : (List.range' 36 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 60 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d60_u48 : (List.range' 48 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 60 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d60_u60 : (List.range' 60 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 60 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d60_u72 : (List.range' 72 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 60 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d60_u84 : (List.range' 84 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 60 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d60_u96 : (List.range' 96 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 60 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d60_u108 : (List.range' 108 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 60 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d60 : (List.range' 60 1).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 60 60 120 (all_glue _ 0 24 36 60 (all_glue _ 0 12 12 24 b3_2_P2_5_D768_j2764_d60_u0 b3_2_P2_5_D768_j2764_d60_u12 rfl) (all_glue _ 24 12 24 36 b3_2_P2_5_D768_j2764_d60_u24 (all_glue _ 36 12 12 24 b3_2_P2_5_D768_j2764_d60_u36 b3_2_P2_5_D768_j2764_d60_u48 rfl) rfl) rfl) (all_glue _ 60 24 36 60 (all_glue _ 60 12 12 24 b3_2_P2_5_D768_j2764_d60_u60 b3_2_P2_5_D768_j2764_d60_u72 rfl) (all_glue _ 84 12 24 36 b3_2_P2_5_D768_j2764_d60_u84 (all_glue _ 96 12 12 24 b3_2_P2_5_D768_j2764_d60_u96 b3_2_P2_5_D768_j2764_d60_u108 rfl) rfl) rfl) rfl))

end DubC2.Atlas
