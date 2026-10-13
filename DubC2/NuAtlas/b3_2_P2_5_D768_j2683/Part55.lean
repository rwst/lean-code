/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2683.Part54

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2683`, part 55/63 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2683_d13_u0 : (List.range' 0 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 13 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d13_u18 : (List.range' 18 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 13 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d13_u36 : (List.range' 36 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 13 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d13_u54 : (List.range' 54 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 13 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d13_u72 : (List.range' 72 8).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 13 16) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d13 : (List.range' 13 1).all (detOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 36 44 80 (all_glue _ 0 18 18 36 b3_2_P2_5_D768_j2683_d13_u0 b3_2_P2_5_D768_j2683_d13_u18 rfl) (all_glue _ 36 18 26 44 b3_2_P2_5_D768_j2683_d13_u36 (all_glue _ 54 18 8 26 b3_2_P2_5_D768_j2683_d13_u54 b3_2_P2_5_D768_j2683_d13_u72 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2683_d14_u0 : (List.range' 0 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 14 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d14_u18 : (List.range' 18 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 14 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d14_u36 : (List.range' 36 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 14 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d14_u54 : (List.range' 54 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 14 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d14_u72 : (List.range' 72 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 14 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d14_u90 : (List.range' 90 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 14 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d14_u108 : (List.range' 108 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 14 48) = true := by
  decide +kernel

end DubC2.Atlas
