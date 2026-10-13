/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j654.Part15

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j654`, part 16/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j654_d11 : (List.range' 11 2).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d13 : (List.range' 13 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d14_u0 : (List.range' 0 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d14_u33 : (List.range' 33 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d14_u66 : (List.range' 66 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d14_u99 : (List.range' 99 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d14_u132 : (List.range' 132 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d14_u165 : (List.range' 165 5).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d14 : (List.range' 14 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 99 71 170 (all_glue _ 0 33 66 99 b3_2_P2_5_D192_j654_d14_u0 (all_glue _ 33 33 33 66 b3_2_P2_5_D192_j654_d14_u33 b3_2_P2_5_D192_j654_d14_u66 rfl) rfl) (all_glue _ 99 33 38 71 b3_2_P2_5_D192_j654_d14_u99 (all_glue _ 132 33 5 38 b3_2_P2_5_D192_j654_d14_u132 b3_2_P2_5_D192_j654_d14_u165 rfl) rfl) rfl))

end DubC2.Atlas
