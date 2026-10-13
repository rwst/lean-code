/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j654.Part13

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j654`, part 14/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j654_d6_u99 : (List.range' 99 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 6 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d6_u132 : (List.range' 132 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 6 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d6_u165 : (List.range' 165 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 6 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d6_u198 : (List.range' 198 32).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 6 46) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 99 131 230 (all_glue _ 0 33 66 99 b3_2_P2_5_D192_j654_d6_u0 (all_glue _ 33 33 33 66 b3_2_P2_5_D192_j654_d6_u33 b3_2_P2_5_D192_j654_d6_u66 rfl) rfl) (all_glue _ 99 66 65 131 (all_glue _ 99 33 33 66 b3_2_P2_5_D192_j654_d6_u99 b3_2_P2_5_D192_j654_d6_u132 rfl) (all_glue _ 165 33 32 65 b3_2_P2_5_D192_j654_d6_u165 b3_2_P2_5_D192_j654_d6_u198 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j654_d7 : (List.range' 7 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d8_u0 : (List.range' 0 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 8 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d8_u33 : (List.range' 33 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 8 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d8_u66 : (List.range' 66 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 8 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d8_u99 : (List.range' 99 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 8 41) = true := by
  decide +kernel

end DubC2.Atlas
