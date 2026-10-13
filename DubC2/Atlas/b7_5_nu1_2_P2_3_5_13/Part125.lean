/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part124

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 125/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d9_u86 : (List.range' 86 24).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 9 10) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d9 : (List.range' 9 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 86 24 110 b7_5_nu1_2_P2_3_5_13_d9_u0 b7_5_nu1_2_P2_3_5_13_d9_u86 rfl))

theorem b7_5_nu1_2_P2_3_5_13_d10_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 10 18) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d10_u86 : (List.range' 86 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 10 18) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d10_u172 : (List.range' 172 26).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 10 18) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d10 : (List.range' 10 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 86 112 198 b7_5_nu1_2_P2_3_5_13_d10_u0 (all_glue _ 86 86 26 112 b7_5_nu1_2_P2_3_5_13_d10_u86 b7_5_nu1_2_P2_3_5_13_d10_u172 rfl) rfl))

end DubC2.Atlas
