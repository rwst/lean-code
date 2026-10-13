/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4151.Part65

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4151`, part 66/69 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4151_d33_u117 : (List.range' 117 13).all (detRowOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C 33 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d33_u130 : (List.range' 130 13).all (detRowOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C 33 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d33_u143 : (List.range' 143 7).all (detRowOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C 33 30) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d33 : (List.range' 33 1).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 78 72 150 (all_glue _ 0 39 39 78 (all_glue _ 0 13 26 39 b3_2_P2_5_D768_j4151_d33_u0 (all_glue _ 13 13 13 26 b3_2_P2_5_D768_j4151_d33_u13 b3_2_P2_5_D768_j4151_d33_u26 rfl) rfl) (all_glue _ 39 13 26 39 b3_2_P2_5_D768_j4151_d33_u39 (all_glue _ 52 13 13 26 b3_2_P2_5_D768_j4151_d33_u52 b3_2_P2_5_D768_j4151_d33_u65 rfl) rfl) rfl) (all_glue _ 78 39 33 72 (all_glue _ 78 13 26 39 b3_2_P2_5_D768_j4151_d33_u78 (all_glue _ 91 13 13 26 b3_2_P2_5_D768_j4151_d33_u91 b3_2_P2_5_D768_j4151_d33_u104 rfl) rfl) (all_glue _ 117 13 20 33 b3_2_P2_5_D768_j4151_d33_u117 (all_glue _ 130 13 7 20 b3_2_P2_5_D768_j4151_d33_u130 b3_2_P2_5_D768_j4151_d33_u143 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4151_d34 : (List.range' 34 3).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d37 : (List.range' 37 2).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d39 : (List.range' 39 1).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d40_u0 : (List.range' 0 13).all (detRowOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C 40 30) = true := by
  decide +kernel

end DubC2.Atlas
