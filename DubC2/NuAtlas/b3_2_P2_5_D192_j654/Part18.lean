/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j654.Part17

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j654`, part 18/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j654_d18_u132 : (List.range' 132 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 18 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d18_u165 : (List.range' 165 10).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 18 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d18 : (List.range' 18 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 99 76 175 (all_glue _ 0 33 66 99 b3_2_P2_5_D192_j654_d18_u0 (all_glue _ 33 33 33 66 b3_2_P2_5_D192_j654_d18_u33 b3_2_P2_5_D192_j654_d18_u66 rfl) rfl) (all_glue _ 99 33 43 76 b3_2_P2_5_D192_j654_d18_u99 (all_glue _ 132 33 10 43 b3_2_P2_5_D192_j654_d18_u132 b3_2_P2_5_D192_j654_d18_u165 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j654_d19 : (List.range' 19 3).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d22 : (List.range' 22 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d23_u0 : (List.range' 0 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 23 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d23_u33 : (List.range' 33 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 23 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d23_u66 : (List.range' 66 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 23 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d23_u99 : (List.range' 99 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 23 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d23_u132 : (List.range' 132 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 23 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d23_u165 : (List.range' 165 20).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 23 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d23 : (List.range' 23 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 99 86 185 (all_glue _ 0 33 66 99 b3_2_P2_5_D192_j654_d23_u0 (all_glue _ 33 33 33 66 b3_2_P2_5_D192_j654_d23_u33 b3_2_P2_5_D192_j654_d23_u66 rfl) rfl) (all_glue _ 99 33 53 86 b3_2_P2_5_D192_j654_d23_u99 (all_glue _ 132 33 20 53 b3_2_P2_5_D192_j654_d23_u132 b3_2_P2_5_D192_j654_d23_u165 rfl) rfl) rfl))

end DubC2.Atlas
