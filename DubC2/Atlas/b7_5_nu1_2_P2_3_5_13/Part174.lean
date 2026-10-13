/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part173

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 174/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d50_u86 : (List.range' 86 46).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 50 12) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d50 : (List.range' 50 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 86 46 132 b7_5_nu1_2_P2_3_5_13_d50_u0 b7_5_nu1_2_P2_3_5_13_d50_u86 rfl))

theorem b7_5_nu1_2_P2_3_5_13_d51 : (List.range' 51 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d52_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 52 9) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d52_u86 : (List.range' 86 13).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 52 9) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d52 : (List.range' 52 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 86 13 99 b7_5_nu1_2_P2_3_5_13_d52_u0 b7_5_nu1_2_P2_3_5_13_d52_u86 rfl))

end DubC2.Atlas
