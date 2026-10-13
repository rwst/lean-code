/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2764.Part136

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2764`, part 137/143 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2764_d39_u84 : (List.range' 84 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 39 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d39_u96 : (List.range' 96 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 39 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d39_u108 : (List.range' 108 7).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 39 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d39 : (List.range' 39 1).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 60 55 115 (all_glue _ 0 24 36 60 (all_glue _ 0 12 12 24 b3_2_P2_5_D768_j2764_d39_u0 b3_2_P2_5_D768_j2764_d39_u12 rfl) (all_glue _ 24 12 24 36 b3_2_P2_5_D768_j2764_d39_u24 (all_glue _ 36 12 12 24 b3_2_P2_5_D768_j2764_d39_u36 b3_2_P2_5_D768_j2764_d39_u48 rfl) rfl) rfl) (all_glue _ 60 24 31 55 (all_glue _ 60 12 12 24 b3_2_P2_5_D768_j2764_d39_u60 b3_2_P2_5_D768_j2764_d39_u72 rfl) (all_glue _ 84 12 19 31 b3_2_P2_5_D768_j2764_d39_u84 (all_glue _ 96 12 7 19 b3_2_P2_5_D768_j2764_d39_u96 b3_2_P2_5_D768_j2764_d39_u108 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2764_d40 : (List.range' 40 3).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d43 : (List.range' 43 2).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true := by
  decide +kernel

end DubC2.Atlas
