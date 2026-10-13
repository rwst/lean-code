/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D1536_j3408.Part17

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D1536_j3408`, part 18/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D1536_j3408_d5 : (List.range' 5 1).all (detOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d6_u0 : (List.range' 0 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 6 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d6_u73 : (List.range' 73 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 6 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d6_u146 : (List.range' 146 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 6 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d6_u219 : (List.range' 219 73).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 6 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d6_u292 : (List.range' 292 48).all (detRowOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C 6 68) = true := by
  decide +kernel

theorem b3_2_P2_5_D1536_j3408_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 146 194 340 (all_glue _ 0 73 73 146 b3_2_P2_5_D1536_j3408_d6_u0 b3_2_P2_5_D1536_j3408_d6_u73 rfl) (all_glue _ 146 73 121 194 b3_2_P2_5_D1536_j3408_d6_u146 (all_glue _ 219 73 48 121 b3_2_P2_5_D1536_j3408_d6_u219 b3_2_P2_5_D1536_j3408_d6_u292 rfl) rfl) rfl))

theorem b3_2_P2_5_D1536_j3408_d7 : (List.range' 7 2).all (detOK b3_2_P2_5_D1536_j3408P b3_2_P2_5_D1536_j3408C) = true := by
  decide +kernel

end DubC2.Atlas
