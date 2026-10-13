/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4146.Part57

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4146`, part 58/58 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4146_d31_u112 : (List.range' 112 14).all (detRowOK b3_2_P2_5_D768_j4146P b3_2_P2_5_D768_j4146C 31 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4146_d31_u126 : (List.range' 126 9).all (detRowOK b3_2_P2_5_D768_j4146P b3_2_P2_5_D768_j4146C 31 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4146_d31 : (List.range' 31 1).all (detOK b3_2_P2_5_D768_j4146P b3_2_P2_5_D768_j4146C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 70 65 135 (all_glue _ 0 28 42 70 (all_glue _ 0 14 14 28 b3_2_P2_5_D768_j4146_d31_u0 b3_2_P2_5_D768_j4146_d31_u14 rfl) (all_glue _ 28 14 28 42 b3_2_P2_5_D768_j4146_d31_u28 (all_glue _ 42 14 14 28 b3_2_P2_5_D768_j4146_d31_u42 b3_2_P2_5_D768_j4146_d31_u56 rfl) rfl) rfl) (all_glue _ 70 28 37 65 (all_glue _ 70 14 14 28 b3_2_P2_5_D768_j4146_d31_u70 b3_2_P2_5_D768_j4146_d31_u84 rfl) (all_glue _ 98 14 23 37 b3_2_P2_5_D768_j4146_d31_u98 (all_glue _ 112 14 9 23 b3_2_P2_5_D768_j4146_d31_u112 b3_2_P2_5_D768_j4146_d31_u126 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4146_d32 : (List.range' 32 6).all (detOK b3_2_P2_5_D768_j4146P b3_2_P2_5_D768_j4146C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4146_d38 : (List.range' 38 6).all (detOK b3_2_P2_5_D768_j4146P b3_2_P2_5_D768_j4146C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4146_d44 : (List.range' 44 5).all (detOK b3_2_P2_5_D768_j4146P b3_2_P2_5_D768_j4146C) = true := by
  decide +kernel

end DubC2.Atlas
