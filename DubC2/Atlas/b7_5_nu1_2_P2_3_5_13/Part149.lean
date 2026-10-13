/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part148

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 149/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d22_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 22 19) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d22_u86 : (List.range' 86 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 22 19) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d22_u172 : (List.range' 172 37).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 22 19) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d22 : (List.range' 22 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 86 123 209 b7_5_nu1_2_P2_3_5_13_d22_u0 (all_glue _ 86 86 37 123 b7_5_nu1_2_P2_3_5_13_d22_u86 b7_5_nu1_2_P2_3_5_13_d22_u172 rfl) rfl))

end DubC2.Atlas
