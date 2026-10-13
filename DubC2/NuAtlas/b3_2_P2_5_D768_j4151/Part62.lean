/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4151.Part61

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4151`, part 62/69 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4151_d18_u143 : (List.range' 143 7).all (detRowOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C 18 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d18 : (List.range' 18 1).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 78 72 150 (all_glue _ 0 39 39 78 (all_glue _ 0 13 26 39 b3_2_P2_5_D768_j4151_d18_u0 (all_glue _ 13 13 13 26 b3_2_P2_5_D768_j4151_d18_u13 b3_2_P2_5_D768_j4151_d18_u26 rfl) rfl) (all_glue _ 39 13 26 39 b3_2_P2_5_D768_j4151_d18_u39 (all_glue _ 52 13 13 26 b3_2_P2_5_D768_j4151_d18_u52 b3_2_P2_5_D768_j4151_d18_u65 rfl) rfl) rfl) (all_glue _ 78 39 33 72 (all_glue _ 78 13 26 39 b3_2_P2_5_D768_j4151_d18_u78 (all_glue _ 91 13 13 26 b3_2_P2_5_D768_j4151_d18_u91 b3_2_P2_5_D768_j4151_d18_u104 rfl) rfl) (all_glue _ 117 13 20 33 b3_2_P2_5_D768_j4151_d18_u117 (all_glue _ 130 13 7 20 b3_2_P2_5_D768_j4151_d18_u130 b3_2_P2_5_D768_j4151_d18_u143 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4151_d19 : (List.range' 19 1).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d20 : (List.range' 20 1).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d21 : (List.range' 21 2).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d23 : (List.range' 23 1).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

end DubC2.Atlas
