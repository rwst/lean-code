/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Part161

/-! Certificate pieces for `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13`, part 162/201 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b7_5_nu1_2_P2_3_5_13_d30_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 30 13) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d30_u86 : (List.range' 86 57).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 30 13) = true := by
  decide +kernel

theorem b7_5_nu1_2_P2_3_5_13_d30 : (List.range' 30 1).all (detOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 86 57 143 b7_5_nu1_2_P2_3_5_13_d30_u0 b7_5_nu1_2_P2_3_5_13_d30_u86 rfl))

theorem b7_5_nu1_2_P2_3_5_13_d31_u0 : (List.range' 0 86).all (detRowOK b7_5_nu1_2_P2_3_5_13P b7_5_nu1_2_P2_3_5_13C 31 13) = true := by
  decide +kernel

end DubC2.Atlas
