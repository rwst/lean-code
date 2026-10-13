/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b3_2_nu0_P3_5_7_11.Part17

/-! Certificate pieces for `DubC2.Atlas.b3_2_nu0_P3_5_7_11`, part 18/35 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_nu0_P3_5_7_11_d7_u173 : (List.range' 173 173).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 7 114) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d7_u346 : (List.range' 346 110).all (detRowOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C 7 114) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d7 : (List.range' 7 1).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 173 283 456 b3_2_nu0_P3_5_7_11_d7_u0 (all_glue _ 173 173 110 283 b3_2_nu0_P3_5_7_11_d7_u173 b3_2_nu0_P3_5_7_11_d7_u346 rfl) rfl))

theorem b3_2_nu0_P3_5_7_11_d8 : (List.range' 8 2).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true := by
  decide +kernel

theorem b3_2_nu0_P3_5_7_11_d10 : (List.range' 10 2).all (detOK b3_2_nu0_P3_5_7_11P b3_2_nu0_P3_5_7_11C) = true := by
  decide +kernel

end DubC2.Atlas
