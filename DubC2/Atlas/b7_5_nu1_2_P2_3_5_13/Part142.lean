/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part141

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 142/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d17_u1118 : (List.range' 1118 26).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 17 104) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d17 : (List.range' 17 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 602 542 1144 (all_glue _ 0 258 344 602 (all_glue _ 0 86 172 258 b7_5_nu1_2_P2_3_5_13_d17_u0 (all_glue _ 86 86 86 172 b7_5_nu1_2_P2_3_5_13_d17_u86 b7_5_nu1_2_P2_3_5_13_d17_u172 rfl) rfl) (all_glue _ 258 172 172 344 (all_glue _ 258 86 86 172 b7_5_nu1_2_P2_3_5_13_d17_u258 b7_5_nu1_2_P2_3_5_13_d17_u344 rfl) (all_glue _ 430 86 86 172 b7_5_nu1_2_P2_3_5_13_d17_u430 b7_5_nu1_2_P2_3_5_13_d17_u516 rfl) rfl) rfl) (all_glue _ 602 258 284 542 (all_glue _ 602 86 172 258 b7_5_nu1_2_P2_3_5_13_d17_u602 (all_glue _ 688 86 86 172 b7_5_nu1_2_P2_3_5_13_d17_u688 b7_5_nu1_2_P2_3_5_13_d17_u774 rfl) rfl) (all_glue _ 860 172 112 284 (all_glue _ 860 86 86 172 b7_5_nu1_2_P2_3_5_13_d17_u860 b7_5_nu1_2_P2_3_5_13_d17_u946 rfl) (all_glue _ 1032 86 26 112 b7_5_nu1_2_P2_3_5_13_d17_u1032 b7_5_nu1_2_P2_3_5_13_d17_u1118 rfl) rfl) rfl) rfl))

theorem b7_5_nu1_2_P2_3_5_13_d18_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 18 104) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d18_u86 : (List.range' 86 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 18 104) = true := by
  decide +kernel

end DubC2.Atlas
