/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D1536_j3408.Part15

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D1536_j3408`, part 16/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D1536_j3408_d0_u365 : (List.range' 365 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 0 156) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d0_u438 : (List.range' 438 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 0 156) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d0_u511 : (List.range' 511 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 0 156) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d0_u584 : (List.range' 584 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 0 156) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d0_u657 : (List.range' 657 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 0 156) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d0_u730 : (List.range' 730 50).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 0 156) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 365 415 780 (all_glue _ 0 146 219 365 (all_glue _ 0 73 73 146 b3_2_P2_5_D1536_j3408_d0_u0 b3_2_P2_5_D1536_j3408_d0_u73 rfl) (all_glue _ 146 73 146 219 b3_2_P2_5_D1536_j3408_d0_u146 (all_glue _ 219 73 73 146 b3_2_P2_5_D1536_j3408_d0_u219 b3_2_P2_5_D1536_j3408_d0_u292 rfl) rfl) rfl) (all_glue _ 365 219 196 415 (all_glue _ 365 73 146 219 b3_2_P2_5_D1536_j3408_d0_u365 (all_glue _ 438 73 73 146 b3_2_P2_5_D1536_j3408_d0_u438 b3_2_P2_5_D1536_j3408_d0_u511 rfl) rfl) (all_glue _ 584 73 123 196 b3_2_P2_5_D1536_j3408_d0_u584 (all_glue _ 657 73 50 123 b3_2_P2_5_D1536_j3408_d0_u657 b3_2_P2_5_D1536_j3408_d0_u730 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D1536_j3408_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d2_u0 : (List.range' 0 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 2 113) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d2_u73 : (List.range' 73 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 2 113) = true := by
  decide +kernel

end DubC2.Atlas
