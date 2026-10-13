/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part133

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 134/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d12_u946 : (List.range' 946 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 12 99) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d12_u1032 : (List.range' 1032 57).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 12 99) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d12 : (List.range' 12 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 516 573 1089 (all_glue _ 0 258 258 516 (all_glue _ 0 86 172 258 b7_5_nu1_2_P2_3_5_13_d12_u0 (all_glue _ 86 86 86 172 b7_5_nu1_2_P2_3_5_13_d12_u86 b7_5_nu1_2_P2_3_5_13_d12_u172 rfl) rfl) (all_glue _ 258 86 172 258 b7_5_nu1_2_P2_3_5_13_d12_u258 (all_glue _ 344 86 86 172 b7_5_nu1_2_P2_3_5_13_d12_u344 b7_5_nu1_2_P2_3_5_13_d12_u430 rfl) rfl) rfl) (all_glue _ 516 258 315 573 (all_glue _ 516 86 172 258 b7_5_nu1_2_P2_3_5_13_d12_u516 (all_glue _ 602 86 86 172 b7_5_nu1_2_P2_3_5_13_d12_u602 b7_5_nu1_2_P2_3_5_13_d12_u688 rfl) rfl) (all_glue _ 774 172 143 315 (all_glue _ 774 86 86 172 b7_5_nu1_2_P2_3_5_13_d12_u774 b7_5_nu1_2_P2_3_5_13_d12_u860 rfl) (all_glue _ 946 86 57 143 b7_5_nu1_2_P2_3_5_13_d12_u946 b7_5_nu1_2_P2_3_5_13_d12_u1032 rfl) rfl) rfl) rfl))

theorem b7_5_nu1_2_P2_3_5_13_d13_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 13 18) = true := by
  decide +kernel

end DubC2.Atlas
