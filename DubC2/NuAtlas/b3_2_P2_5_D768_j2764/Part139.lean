/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2764.Part138

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2764`, part 139/143 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2764_d52_u0 : (List.range' 0 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 52 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d52_u12 : (List.range' 12 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 52 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d52_u24 : (List.range' 24 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 52 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d52_u36 : (List.range' 36 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 52 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d52_u48 : (List.range' 48 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 52 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d52_u60 : (List.range' 60 10).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 52 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d52 : (List.range' 52 1).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 36 34 70 (all_glue _ 0 12 24 36 b3_2_P2_5_D768_j2764_d52_u0 (all_glue _ 12 12 12 24 b3_2_P2_5_D768_j2764_d52_u12 b3_2_P2_5_D768_j2764_d52_u24 rfl) rfl) (all_glue _ 36 12 22 34 b3_2_P2_5_D768_j2764_d52_u36 (all_glue _ 48 12 10 22 b3_2_P2_5_D768_j2764_d52_u48 b3_2_P2_5_D768_j2764_d52_u60 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2764_d53 : (List.range' 53 1).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d54 : (List.range' 54 1).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d55_u0 : (List.range' 0 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 55 14) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d55_u12 : (List.range' 12 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 55 14) = true := by
  decide +kernel

end DubC2.Atlas
