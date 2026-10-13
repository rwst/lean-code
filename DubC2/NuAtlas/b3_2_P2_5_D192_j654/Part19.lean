/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j654.Part18

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j654`, part 19/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j654_d24 : (List.range' 24 2).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d26_u0 : (List.range' 0 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 26 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d26_u33 : (List.range' 33 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 26 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d26_u66 : (List.range' 66 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 26 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d26_u99 : (List.range' 99 33).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 26 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d26_u132 : (List.range' 132 23).all (detRowOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C 26 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j654_d26 : (List.range' 26 1).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 66 89 155 (all_glue _ 0 33 33 66 b3_2_P2_5_D192_j654_d26_u0 b3_2_P2_5_D192_j654_d26_u33 rfl) (all_glue _ 66 33 56 89 b3_2_P2_5_D192_j654_d26_u66 (all_glue _ 99 33 23 56 b3_2_P2_5_D192_j654_d26_u99 b3_2_P2_5_D192_j654_d26_u132 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j654_d27 : (List.range' 27 2).all (detOK b3_2_P2_5_D192_j654P b3_2_P2_5_D192_j654C) = true := by
  decide +kernel

end DubC2.Atlas
