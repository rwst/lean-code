/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1381.Part23

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1381`, part 24/68 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1381_d1_u589 : (List.range' 589 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 1 132) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d1_u608 : (List.range' 608 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 1 132) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d1_u627 : (List.range' 627 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 1 132) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d1_u646 : (List.range' 646 14).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 1 132) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 323 337 660 (all_glue _ 0 152 171 323 (all_glue _ 0 76 76 152 (all_glue _ 0 38 38 76 (all_glue _ 0 19 19 38 b3_2_P2_5_D384_j1381_d1_u0 b3_2_P2_5_D384_j1381_d1_u19 rfl) (all_glue _ 38 19 19 38 b3_2_P2_5_D384_j1381_d1_u38 b3_2_P2_5_D384_j1381_d1_u57 rfl) rfl) (all_glue _ 76 38 38 76 (all_glue _ 76 19 19 38 b3_2_P2_5_D384_j1381_d1_u76 b3_2_P2_5_D384_j1381_d1_u95 rfl) (all_glue _ 114 19 19 38 b3_2_P2_5_D384_j1381_d1_u114 b3_2_P2_5_D384_j1381_d1_u133 rfl) rfl) rfl) (all_glue _ 152 76 95 171 (all_glue _ 152 38 38 76 (all_glue _ 152 19 19 38 b3_2_P2_5_D384_j1381_d1_u152 b3_2_P2_5_D384_j1381_d1_u171 rfl) (all_glue _ 190 19 19 38 b3_2_P2_5_D384_j1381_d1_u190 b3_2_P2_5_D384_j1381_d1_u209 rfl) rfl) (all_glue _ 228 38 57 95 (all_glue _ 228 19 19 38 b3_2_P2_5_D384_j1381_d1_u228 b3_2_P2_5_D384_j1381_d1_u247 rfl) (all_glue _ 266 19 38 57 b3_2_P2_5_D384_j1381_d1_u266 (all_glue _ 285 19 19 38 b3_2_P2_5_D384_j1381_d1_u285 b3_2_P2_5_D384_j1381_d1_u304 rfl) rfl) rfl) rfl) rfl) (all_glue _ 323 171 166 337 (all_glue _ 323 76 95 171 (all_glue _ 323 38 38 76 (all_glue _ 323 19 19 38 b3_2_P2_5_D384_j1381_d1_u323 b3_2_P2_5_D384_j1381_d1_u342 rfl) (all_glue _ 361 19 19 38 b3_2_P2_5_D384_j1381_d1_u361 b3_2_P2_5_D384_j1381_d1_u380 rfl) rfl) (all_glue _ 399 38 57 95 (all_glue _ 399 19 19 38 b3_2_P2_5_D384_j1381_d1_u399 b3_2_P2_5_D384_j1381_d1_u418 rfl) (all_glue _ 437 19 38 57 b3_2_P2_5_D384_j1381_d1_u437 (all_glue _ 456 19 19 38 b3_2_P2_5_D384_j1381_d1_u456 b3_2_P2_5_D384_j1381_d1_u475 rfl) rfl) rfl) rfl) (all_glue _ 494 76 90 166 (all_glue _ 494 38 38 76 (all_glue _ 494 19 19 38 b3_2_P2_5_D384_j1381_d1_u494 b3_2_P2_5_D384_j1381_d1_u513 rfl) (all_glue _ 532 19 19 38 b3_2_P2_5_D384_j1381_d1_u532 b3_2_P2_5_D384_j1381_d1_u551 rfl) rfl) (all_glue _ 570 38 52 90 (all_glue _ 570 19 19 38 b3_2_P2_5_D384_j1381_d1_u570 b3_2_P2_5_D384_j1381_d1_u589 rfl) (all_glue _ 608 19 33 52 b3_2_P2_5_D384_j1381_d1_u608 (all_glue _ 627 19 14 33 b3_2_P2_5_D384_j1381_d1_u627 b3_2_P2_5_D384_j1381_d1_u646 rfl) rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1381_d2_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 2 547) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d2_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 2 547) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d2_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 2 547) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d2_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 2 547) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d2_u76 : (List.range' 76 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 2 547) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d2_u95 : (List.range' 95 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 2 547) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d2_u114 : (List.range' 114 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 2 547) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d2_u133 : (List.range' 133 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 2 547) = true := by
  decide +kernel

end DubC2.Atlas
