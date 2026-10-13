/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4151.Part68

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4151`, part 69/69 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4151_d45_u91 : (List.range' 91 13).all (detRowOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C 45 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d45_u104 : (List.range' 104 13).all (detRowOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C 45 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d45_u117 : (List.range' 117 13).all (detRowOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C 45 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d45 : (List.range' 45 1).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 65 65 130 (all_glue _ 0 26 39 65 (all_glue _ 0 13 13 26 b3_2_P2_5_D768_j4151_d45_u0 b3_2_P2_5_D768_j4151_d45_u13 rfl) (all_glue _ 26 13 26 39 b3_2_P2_5_D768_j4151_d45_u26 (all_glue _ 39 13 13 26 b3_2_P2_5_D768_j4151_d45_u39 b3_2_P2_5_D768_j4151_d45_u52 rfl) rfl) rfl) (all_glue _ 65 26 39 65 (all_glue _ 65 13 13 26 b3_2_P2_5_D768_j4151_d45_u65 b3_2_P2_5_D768_j4151_d45_u78 rfl) (all_glue _ 91 13 26 39 b3_2_P2_5_D768_j4151_d45_u91 (all_glue _ 104 13 13 26 b3_2_P2_5_D768_j4151_d45_u104 b3_2_P2_5_D768_j4151_d45_u117 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4151_d46 : (List.range' 46 3).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4151_d49 : (List.range' 49 4).all (detOK b3_2_P2_5_D768_j4151P b3_2_P2_5_D768_j4151C) = true := by
  decide +kernel

end DubC2.Atlas
