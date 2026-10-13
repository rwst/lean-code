/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part118

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 119/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d7_u1032 : (List.range' 1032 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 7 110) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d7_u1118 : (List.range' 1118 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 7 110) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d7_u1204 : (List.range' 1204 6).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 7 110) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d7 : (List.range' 7 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 602 608 1210 (all_glue _ 0 258 344 602 (all_glue _ 0 86 172 258 b7_5_nu1_2_P2_3_5_13_d7_u0 (all_glue _ 86 86 86 172 b7_5_nu1_2_P2_3_5_13_d7_u86 b7_5_nu1_2_P2_3_5_13_d7_u172 rfl) rfl) (all_glue _ 258 172 172 344 (all_glue _ 258 86 86 172 b7_5_nu1_2_P2_3_5_13_d7_u258 b7_5_nu1_2_P2_3_5_13_d7_u344 rfl) (all_glue _ 430 86 86 172 b7_5_nu1_2_P2_3_5_13_d7_u430 b7_5_nu1_2_P2_3_5_13_d7_u516 rfl) rfl) rfl) (all_glue _ 602 344 264 608 (all_glue _ 602 172 172 344 (all_glue _ 602 86 86 172 b7_5_nu1_2_P2_3_5_13_d7_u602 b7_5_nu1_2_P2_3_5_13_d7_u688 rfl) (all_glue _ 774 86 86 172 b7_5_nu1_2_P2_3_5_13_d7_u774 b7_5_nu1_2_P2_3_5_13_d7_u860 rfl) rfl) (all_glue _ 946 172 92 264 (all_glue _ 946 86 86 172 b7_5_nu1_2_P2_3_5_13_d7_u946 b7_5_nu1_2_P2_3_5_13_d7_u1032 rfl) (all_glue _ 1118 86 6 92 b7_5_nu1_2_P2_3_5_13_d7_u1118 b7_5_nu1_2_P2_3_5_13_d7_u1204 rfl) rfl) rfl) rfl))

end DubC2.Atlas
