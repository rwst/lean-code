/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j689.Part26

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j689`, part 27/29 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j689_d32_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 32 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d32_u116 : (List.range' 116 9).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 32 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d32 : (List.range' 32 1).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 58 67 125 (all_glue _ 0 29 29 58 b3_2_P2_5_D192_j689_d32_u0 b3_2_P2_5_D192_j689_d32_u29 rfl) (all_glue _ 58 29 38 67 b3_2_P2_5_D192_j689_d32_u58 (all_glue _ 87 29 9 38 b3_2_P2_5_D192_j689_d32_u87 b3_2_P2_5_D192_j689_d32_u116 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j689_d33 : (List.range' 33 3).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d36 : (List.range' 36 2).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d38 : (List.range' 38 1).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true := by
  decide +kernel

end DubC2.Atlas
