/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4147.Part55

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4147`, part 56/60 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4147_d19_u28 : (List.range' 28 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 19 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d19_u42 : (List.range' 42 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 19 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d19_u56 : (List.range' 56 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 19 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d19_u70 : (List.range' 70 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 19 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d19_u84 : (List.range' 84 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 19 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d19_u98 : (List.range' 98 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 19 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d19_u112 : (List.range' 112 13).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 19 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d19 : (List.range' 19 1).all (detOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 69 125 (all_glue _ 0 28 28 56 (all_glue _ 0 14 14 28 b3_2_P2_5_D768_j4147_d19_u0 b3_2_P2_5_D768_j4147_d19_u14 rfl) (all_glue _ 28 14 14 28 b3_2_P2_5_D768_j4147_d19_u28 b3_2_P2_5_D768_j4147_d19_u42 rfl) rfl) (all_glue _ 56 28 41 69 (all_glue _ 56 14 14 28 b3_2_P2_5_D768_j4147_d19_u56 b3_2_P2_5_D768_j4147_d19_u70 rfl) (all_glue _ 84 14 27 41 b3_2_P2_5_D768_j4147_d19_u84 (all_glue _ 98 14 13 27 b3_2_P2_5_D768_j4147_d19_u98 b3_2_P2_5_D768_j4147_d19_u112 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4147_d20 : (List.range' 20 2).all (detOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C) = true := by
  decide +kernel

end DubC2.Atlas
