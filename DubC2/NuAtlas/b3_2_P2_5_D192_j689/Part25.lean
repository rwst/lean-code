/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j689.Part24

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j689`, part 25/29 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j689_d23 : (List.range' 23 1).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d24_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 24 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d24_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 24 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d24_u58 : (List.range' 58 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 24 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d24_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 24 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d24_u116 : (List.range' 116 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 24 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d24_u145 : (List.range' 145 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 24 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d24_u174 : (List.range' 174 26).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 24 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d24 : (List.range' 24 1).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 87 113 200 (all_glue _ 0 29 58 87 b3_2_P2_5_D192_j689_d24_u0 (all_glue _ 29 29 29 58 b3_2_P2_5_D192_j689_d24_u29 b3_2_P2_5_D192_j689_d24_u58 rfl) rfl) (all_glue _ 87 58 55 113 (all_glue _ 87 29 29 58 b3_2_P2_5_D192_j689_d24_u87 b3_2_P2_5_D192_j689_d24_u116 rfl) (all_glue _ 145 29 26 55 b3_2_P2_5_D192_j689_d24_u145 b3_2_P2_5_D192_j689_d24_u174 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j689_d25 : (List.range' 25 2).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true := by
  decide +kernel

end DubC2.Atlas
