/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2608.Part15

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2608`, part 16/16 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2608_d0_u671 : (List.range' 671 61).all (detRowOK b3_2_P2_5_D768_j2608P b3_2_P2_5_D768_j2608C 0 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2608_d0_u732 : (List.range' 732 61).all (detRowOK b3_2_P2_5_D768_j2608P b3_2_P2_5_D768_j2608C 0 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2608_d0_u793 : (List.range' 793 61).all (detRowOK b3_2_P2_5_D768_j2608P b3_2_P2_5_D768_j2608C 0 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2608_d0_u854 : (List.range' 854 61).all (detRowOK b3_2_P2_5_D768_j2608P b3_2_P2_5_D768_j2608C 0 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2608_d0_u915 : (List.range' 915 25).all (detRowOK b3_2_P2_5_D768_j2608P b3_2_P2_5_D768_j2608C 0 188) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2608_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D768_j2608P b3_2_P2_5_D768_j2608C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 488 452 940 (all_glue _ 0 244 244 488 (all_glue _ 0 122 122 244 (all_glue _ 0 61 61 122 b3_2_P2_5_D768_j2608_d0_u0 b3_2_P2_5_D768_j2608_d0_u61 rfl) (all_glue _ 122 61 61 122 b3_2_P2_5_D768_j2608_d0_u122 b3_2_P2_5_D768_j2608_d0_u183 rfl) rfl) (all_glue _ 244 122 122 244 (all_glue _ 244 61 61 122 b3_2_P2_5_D768_j2608_d0_u244 b3_2_P2_5_D768_j2608_d0_u305 rfl) (all_glue _ 366 61 61 122 b3_2_P2_5_D768_j2608_d0_u366 b3_2_P2_5_D768_j2608_d0_u427 rfl) rfl) rfl) (all_glue _ 488 244 208 452 (all_glue _ 488 122 122 244 (all_glue _ 488 61 61 122 b3_2_P2_5_D768_j2608_d0_u488 b3_2_P2_5_D768_j2608_d0_u549 rfl) (all_glue _ 610 61 61 122 b3_2_P2_5_D768_j2608_d0_u610 b3_2_P2_5_D768_j2608_d0_u671 rfl) rfl) (all_glue _ 732 122 86 208 (all_glue _ 732 61 61 122 b3_2_P2_5_D768_j2608_d0_u732 b3_2_P2_5_D768_j2608_d0_u793 rfl) (all_glue _ 854 61 25 86 b3_2_P2_5_D768_j2608_d0_u854 b3_2_P2_5_D768_j2608_d0_u915 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2608_d1 : (List.range' 1 6).all (detOK b3_2_P2_5_D768_j2608P b3_2_P2_5_D768_j2608C) = true := by
  decide +kernel

end DubC2.Atlas
