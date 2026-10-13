/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2683.Part61

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2683`, part 62/63 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2683_d30_u36 : (List.range' 36 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30_u54 : (List.range' 54 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30_u72 : (List.range' 72 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30_u90 : (List.range' 90 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30_u108 : (List.range' 108 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30_u126 : (List.range' 126 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30_u144 : (List.range' 144 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30_u162 : (List.range' 162 18).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30_u180 : (List.range' 180 15).all (detRowOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C 30 39) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2683_d30 : (List.range' 30 1).all (detOK b3_2_P2_5_D768_j2683P b3_2_P2_5_D768_j2683C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 90 105 195 (all_glue _ 0 36 54 90 (all_glue _ 0 18 18 36 b3_2_P2_5_D768_j2683_d30_u0 b3_2_P2_5_D768_j2683_d30_u18 rfl) (all_glue _ 36 18 36 54 b3_2_P2_5_D768_j2683_d30_u36 (all_glue _ 54 18 18 36 b3_2_P2_5_D768_j2683_d30_u54 b3_2_P2_5_D768_j2683_d30_u72 rfl) rfl) rfl) (all_glue _ 90 54 51 105 (all_glue _ 90 18 36 54 b3_2_P2_5_D768_j2683_d30_u90 (all_glue _ 108 18 18 36 b3_2_P2_5_D768_j2683_d30_u108 b3_2_P2_5_D768_j2683_d30_u126 rfl) rfl) (all_glue _ 144 18 33 51 b3_2_P2_5_D768_j2683_d30_u144 (all_glue _ 162 18 15 33 b3_2_P2_5_D768_j2683_d30_u162 b3_2_P2_5_D768_j2683_d30_u180 rfl) rfl) rfl) rfl))

end DubC2.Atlas
