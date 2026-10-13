/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2764.Part137

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2764`, part 138/143 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2764_d45 : (List.range' 45 3).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d48_u0 : (List.range' 0 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 48 11) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d48_u12 : (List.range' 12 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 48 11) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d48_u24 : (List.range' 24 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 48 11) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d48_u36 : (List.range' 36 12).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 48 11) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d48_u48 : (List.range' 48 7).all (detRowOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C 48 11) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2764_d48 : (List.range' 48 1).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 24 31 55 (all_glue _ 0 12 12 24 b3_2_P2_5_D768_j2764_d48_u0 b3_2_P2_5_D768_j2764_d48_u12 rfl) (all_glue _ 24 12 19 31 b3_2_P2_5_D768_j2764_d48_u24 (all_glue _ 36 12 7 19 b3_2_P2_5_D768_j2764_d48_u36 b3_2_P2_5_D768_j2764_d48_u48 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2764_d49 : (List.range' 49 3).all (detOK b3_2_P2_5_D768_j2764P b3_2_P2_5_D768_j2764C) = true := by
  decide +kernel

end DubC2.Atlas
