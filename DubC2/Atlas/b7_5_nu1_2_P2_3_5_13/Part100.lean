/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part99

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 100/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d3_u1978 : (List.range' 1978 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 3 195) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d3_u2064 : (List.range' 2064 81).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 3 195) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d3 : (List.range' 3 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 1032 1113 2145 (all_glue _ 0 516 516 1032 (all_glue _ 0 258 258 516 (all_glue _ 0 86 172 258 b7_5_nu1_2_P2_3_5_13_d3_u0 (all_glue _ 86 86 86 172 b7_5_nu1_2_P2_3_5_13_d3_u86 b7_5_nu1_2_P2_3_5_13_d3_u172 rfl) rfl) (all_glue _ 258 86 172 258 b7_5_nu1_2_P2_3_5_13_d3_u258 (all_glue _ 344 86 86 172 b7_5_nu1_2_P2_3_5_13_d3_u344 b7_5_nu1_2_P2_3_5_13_d3_u430 rfl) rfl) rfl) (all_glue _ 516 258 258 516 (all_glue _ 516 86 172 258 b7_5_nu1_2_P2_3_5_13_d3_u516 (all_glue _ 602 86 86 172 b7_5_nu1_2_P2_3_5_13_d3_u602 b7_5_nu1_2_P2_3_5_13_d3_u688 rfl) rfl) (all_glue _ 774 86 172 258 b7_5_nu1_2_P2_3_5_13_d3_u774 (all_glue _ 860 86 86 172 b7_5_nu1_2_P2_3_5_13_d3_u860 b7_5_nu1_2_P2_3_5_13_d3_u946 rfl) rfl) rfl) rfl) (all_glue _ 1032 516 597 1113 (all_glue _ 1032 258 258 516 (all_glue _ 1032 86 172 258 b7_5_nu1_2_P2_3_5_13_d3_u1032 (all_glue _ 1118 86 86 172 b7_5_nu1_2_P2_3_5_13_d3_u1118 b7_5_nu1_2_P2_3_5_13_d3_u1204 rfl) rfl) (all_glue _ 1290 86 172 258 b7_5_nu1_2_P2_3_5_13_d3_u1290 (all_glue _ 1376 86 86 172 b7_5_nu1_2_P2_3_5_13_d3_u1376 b7_5_nu1_2_P2_3_5_13_d3_u1462 rfl) rfl) rfl) (all_glue _ 1548 258 339 597 (all_glue _ 1548 86 172 258 b7_5_nu1_2_P2_3_5_13_d3_u1548 (all_glue _ 1634 86 86 172 b7_5_nu1_2_P2_3_5_13_d3_u1634 b7_5_nu1_2_P2_3_5_13_d3_u1720 rfl) rfl) (all_glue _ 1806 172 167 339 (all_glue _ 1806 86 86 172 b7_5_nu1_2_P2_3_5_13_d3_u1806 b7_5_nu1_2_P2_3_5_13_d3_u1892 rfl) (all_glue _ 1978 86 81 167 b7_5_nu1_2_P2_3_5_13_d3_u1978 b7_5_nu1_2_P2_3_5_13_d3_u2064 rfl) rfl) rfl) rfl) rfl))

theorem b7_5_nu1_2_P2_3_5_13_d4_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 4 103) = true := by
  decide +kernel

end DubC2.Atlas
