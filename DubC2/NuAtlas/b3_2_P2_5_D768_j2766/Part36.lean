/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2766.Part35

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2766`, part 36/38 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2766_d9_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d9_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d9_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d9_u112 : (List.range' 112 18).all (detRowOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d9 : (List.range' 9 1).all (detOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 74 130 (all_glue _ 0 28 28 56 b3_2_P2_5_D768_j2766_d9_u0 b3_2_P2_5_D768_j2766_d9_u28 rfl) (all_glue _ 56 28 46 74 b3_2_P2_5_D768_j2766_d9_u56 (all_glue _ 84 28 18 46 b3_2_P2_5_D768_j2766_d9_u84 b3_2_P2_5_D768_j2766_d9_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2766_d10 : (List.range' 10 1).all (detOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2766_d11 : (List.range' 11 2).all (detOK b3_2_P2_5_D768_j2766P b3_2_P2_5_D768_j2766C) = true := by
  decide +kernel

end DubC2.Atlas
