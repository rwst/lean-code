/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part104

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 105/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d4_u1118 : (List.range' 1118 15).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 4 103) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d4 : (List.range' 4 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 602 531 1133 (all_glue _ 0 258 344 602 (all_glue _ 0 86 172 258 b7_5_nu1_2_P2_3_5_13_d4_u0 (all_glue _ 86 86 86 172 b7_5_nu1_2_P2_3_5_13_d4_u86 b7_5_nu1_2_P2_3_5_13_d4_u172 rfl) rfl) (all_glue _ 258 172 172 344 (all_glue _ 258 86 86 172 b7_5_nu1_2_P2_3_5_13_d4_u258 b7_5_nu1_2_P2_3_5_13_d4_u344 rfl) (all_glue _ 430 86 86 172 b7_5_nu1_2_P2_3_5_13_d4_u430 b7_5_nu1_2_P2_3_5_13_d4_u516 rfl) rfl) rfl) (all_glue _ 602 258 273 531 (all_glue _ 602 86 172 258 b7_5_nu1_2_P2_3_5_13_d4_u602 (all_glue _ 688 86 86 172 b7_5_nu1_2_P2_3_5_13_d4_u688 b7_5_nu1_2_P2_3_5_13_d4_u774 rfl) rfl) (all_glue _ 860 172 101 273 (all_glue _ 860 86 86 172 b7_5_nu1_2_P2_3_5_13_d4_u860 b7_5_nu1_2_P2_3_5_13_d4_u946 rfl) (all_glue _ 1032 86 15 101 b7_5_nu1_2_P2_3_5_13_d4_u1032 b7_5_nu1_2_P2_3_5_13_d4_u1118 rfl) rfl) rfl) rfl))

theorem b7_5_nu1_2_P2_3_5_13_d5_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 5 109) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d5_u86 : (List.range' 86 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 5 109) = true := by
  decide +kernel

end DubC2.Atlas
