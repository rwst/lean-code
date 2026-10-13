/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2766.Part34

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2766`, part 35/38 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2766_d5_u168 : (List.range' 168 28).all (detRowOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C 5 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d5_u196 : (List.range' 196 4).all (detRowOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C 5 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d5 : (List.range' 5 1).all (detOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 112 88 200 (all_glue _ 0 56 56 112 (all_glue _ 0 28 28 56 b3_2_P2_5_D768_j2766_d5_u0 b3_2_P2_5_D768_j2766_d5_u28 rfl) (all_glue _ 56 28 28 56 b3_2_P2_5_D768_j2766_d5_u56 b3_2_P2_5_D768_j2766_d5_u84 rfl) rfl) (all_glue _ 112 56 32 88 (all_glue _ 112 28 28 56 b3_2_P2_5_D768_j2766_d5_u112 b3_2_P2_5_D768_j2766_d5_u140 rfl) (all_glue _ 168 28 4 32 b3_2_P2_5_D768_j2766_d5_u168 b3_2_P2_5_D768_j2766_d5_u196 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2766_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d7 : (List.range' 7 1).all (detOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d8 : (List.range' 8 1).all (detOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d9_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C 9 26) = true := by
  decide +kernel

end DubC2.Atlas
