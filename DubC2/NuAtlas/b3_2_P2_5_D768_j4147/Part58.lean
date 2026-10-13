/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4147.Part57

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4147`, part 58/60 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4147_d25_u126 : (List.range' 126 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 25 28) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d25 : (List.range' 25 1).all (detOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 70 70 140 (all_glue _ 0 28 42 70 (all_glue _ 0 14 14 28 b3_2_P2_5_D768_j4147_d25_u0 b3_2_P2_5_D768_j4147_d25_u14 rfl) (all_glue _ 28 14 28 42 b3_2_P2_5_D768_j4147_d25_u28 (all_glue _ 42 14 14 28 b3_2_P2_5_D768_j4147_d25_u42 b3_2_P2_5_D768_j4147_d25_u56 rfl) rfl) rfl) (all_glue _ 70 28 42 70 (all_glue _ 70 14 14 28 b3_2_P2_5_D768_j4147_d25_u70 b3_2_P2_5_D768_j4147_d25_u84 rfl) (all_glue _ 98 14 28 42 b3_2_P2_5_D768_j4147_d25_u98 (all_glue _ 112 14 14 28 b3_2_P2_5_D768_j4147_d25_u112 b3_2_P2_5_D768_j4147_d25_u126 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4147_d26 : (List.range' 26 2).all (detOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d28 : (List.range' 28 3).all (detOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d31_u0 : (List.range' 0 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 31 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d31_u14 : (List.range' 14 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 31 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d31_u28 : (List.range' 28 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 31 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d31_u42 : (List.range' 42 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 31 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d31_u56 : (List.range' 56 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 31 27) = true := by
  decide +kernel

end DubC2.Atlas
