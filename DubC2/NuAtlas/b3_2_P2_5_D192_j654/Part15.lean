/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j654.Part14

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j654`, part 15/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j654_d8_u132 : (List.range' 132 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 8 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d8_u165 : (List.range' 165 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 8 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d8_u198 : (List.range' 198 7).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 8 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d8 : (List.range' 8 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 99 106 205 (all_glue _ 0 33 66 99 b3_2_P2_5_D192_j654_d8_u0 (all_glue _ 33 33 33 66 b3_2_P2_5_D192_j654_d8_u33 b3_2_P2_5_D192_j654_d8_u66 rfl) rfl) (all_glue _ 99 66 40 106 (all_glue _ 99 33 33 66 b3_2_P2_5_D192_j654_d8_u99 b3_2_P2_5_D192_j654_d8_u132 rfl) (all_glue _ 165 33 7 40 b3_2_P2_5_D192_j654_d8_u165 b3_2_P2_5_D192_j654_d8_u198 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j654_d9 : (List.range' 9 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10_u0 : (List.range' 0 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 10 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10_u33 : (List.range' 33 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 10 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10_u66 : (List.range' 66 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 10 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10_u99 : (List.range' 99 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 10 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10_u132 : (List.range' 132 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 10 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10_u165 : (List.range' 165 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 10 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10_u198 : (List.range' 198 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 10 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10_u231 : (List.range' 231 9).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 10 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d10 : (List.range' 10 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 132 108 240 (all_glue _ 0 66 66 132 (all_glue _ 0 33 33 66 b3_2_P2_5_D192_j654_d10_u0 b3_2_P2_5_D192_j654_d10_u33 rfl) (all_glue _ 66 33 33 66 b3_2_P2_5_D192_j654_d10_u66 b3_2_P2_5_D192_j654_d10_u99 rfl) rfl) (all_glue _ 132 66 42 108 (all_glue _ 132 33 33 66 b3_2_P2_5_D192_j654_d10_u132 b3_2_P2_5_D192_j654_d10_u165 rfl) (all_glue _ 198 33 9 42 b3_2_P2_5_D192_j654_d10_u198 b3_2_P2_5_D192_j654_d10_u231 rfl) rfl) rfl))

end DubC2.Atlas
