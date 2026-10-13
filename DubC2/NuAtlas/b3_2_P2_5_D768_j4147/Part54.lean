/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4147.Part53

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4147`, part 54/60 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4147_d11_u126 : (List.range' 126 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 11 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d11_u140 : (List.range' 140 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 11 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d11_u154 : (List.range' 154 1).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 11 31) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d11 : (List.range' 11 1).all (detOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 84 71 155 (all_glue _ 0 42 42 84 (all_glue _ 0 14 28 42 b3_2_P2_5_D768_j4147_d11_u0 (all_glue _ 14 14 14 28 b3_2_P2_5_D768_j4147_d11_u14 b3_2_P2_5_D768_j4147_d11_u28 rfl) rfl) (all_glue _ 42 14 28 42 b3_2_P2_5_D768_j4147_d11_u42 (all_glue _ 56 14 14 28 b3_2_P2_5_D768_j4147_d11_u56 b3_2_P2_5_D768_j4147_d11_u70 rfl) rfl) rfl) (all_glue _ 84 42 29 71 (all_glue _ 84 14 28 42 b3_2_P2_5_D768_j4147_d11_u84 (all_glue _ 98 14 14 28 b3_2_P2_5_D768_j4147_d11_u98 b3_2_P2_5_D768_j4147_d11_u112 rfl) rfl) (all_glue _ 126 14 15 29 b3_2_P2_5_D768_j4147_d11_u126 (all_glue _ 140 14 1 15 b3_2_P2_5_D768_j4147_d11_u140 b3_2_P2_5_D768_j4147_d11_u154 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4147_d12 : (List.range' 12 1).all (detOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d13 : (List.range' 13 2).all (detOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d15_u0 : (List.range' 0 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 15 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d15_u14 : (List.range' 14 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 15 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d15_u28 : (List.range' 28 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 15 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4147_d15_u42 : (List.range' 42 14).all (detRowOK b3_2_P2_5_D768_j4147P b3_2_P2_5_D768_j4147C 15 27) = true := by
  decide +kernel

end DubC2.Atlas
