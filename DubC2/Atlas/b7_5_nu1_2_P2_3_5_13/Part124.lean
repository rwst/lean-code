/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part123

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 124/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d8_u1032 : (List.range' 1032 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 8 109) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d8_u1118 : (List.range' 1118 81).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 8 109) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d8 : (List.range' 8 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 602 597 1199 (all_glue _ 0 258 344 602 (all_glue _ 0 86 172 258 b7_5_nu1_2_P2_3_5_13_d8_u0 (all_glue _ 86 86 86 172 b7_5_nu1_2_P2_3_5_13_d8_u86 b7_5_nu1_2_P2_3_5_13_d8_u172 rfl) rfl) (all_glue _ 258 172 172 344 (all_glue _ 258 86 86 172 b7_5_nu1_2_P2_3_5_13_d8_u258 b7_5_nu1_2_P2_3_5_13_d8_u344 rfl) (all_glue _ 430 86 86 172 b7_5_nu1_2_P2_3_5_13_d8_u430 b7_5_nu1_2_P2_3_5_13_d8_u516 rfl) rfl) rfl) (all_glue _ 602 258 339 597 (all_glue _ 602 86 172 258 b7_5_nu1_2_P2_3_5_13_d8_u602 (all_glue _ 688 86 86 172 b7_5_nu1_2_P2_3_5_13_d8_u688 b7_5_nu1_2_P2_3_5_13_d8_u774 rfl) rfl) (all_glue _ 860 172 167 339 (all_glue _ 860 86 86 172 b7_5_nu1_2_P2_3_5_13_d8_u860 b7_5_nu1_2_P2_3_5_13_d8_u946 rfl) (all_glue _ 1032 86 81 167 b7_5_nu1_2_P2_3_5_13_d8_u1032 b7_5_nu1_2_P2_3_5_13_d8_u1118 rfl) rfl) rfl) rfl))

theorem b7_5_nu1_2_P2_3_5_13_d9_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 9 10) = true := by
  decide +kernel

end DubC2.Atlas
