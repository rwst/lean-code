/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D1536_j3408.Part16

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D1536_j3408`, part 17/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D1536_j3408_d2_u146 : (List.range' 146 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 2 113) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d2_u219 : (List.range' 219 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 2 113) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d2_u292 : (List.range' 292 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 2 113) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d2_u365 : (List.range' 365 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 2 113) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d2_u438 : (List.range' 438 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 2 113) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d2_u511 : (List.range' 511 54).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 2 113) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d2 : (List.range' 2 1).all (detOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 292 273 565 (all_glue _ 0 146 146 292 (all_glue _ 0 73 73 146 b3_2_P2_5_D1536_j3408_d2_u0 b3_2_P2_5_D1536_j3408_d2_u73 rfl) (all_glue _ 146 73 73 146 b3_2_P2_5_D1536_j3408_d2_u146 b3_2_P2_5_D1536_j3408_d2_u219 rfl) rfl) (all_glue _ 292 146 127 273 (all_glue _ 292 73 73 146 b3_2_P2_5_D1536_j3408_d2_u292 b3_2_P2_5_D1536_j3408_d2_u365 rfl) (all_glue _ 438 73 54 127 b3_2_P2_5_D1536_j3408_d2_u438 b3_2_P2_5_D1536_j3408_d2_u511 rfl) rfl) rfl))

theorem b3_2_P2_5_D1536_j3408_d3 : (List.range' 3 1).all (detOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C) = true := by
  decide +kernel

end DubC2.Atlas
