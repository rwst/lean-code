/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j689.Part17

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j689`, part 18/29 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j689_d6_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 6 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d6_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 6 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d6_u58 : (List.range' 58 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 6 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d6_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 6 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d6_u116 : (List.range' 116 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 6 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d6_u145 : (List.range' 145 25).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 6 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 87 83 170 (all_glue _ 0 29 58 87 b3_2_P2_5_D192_j689_d6_u0 (all_glue _ 29 29 29 58 b3_2_P2_5_D192_j689_d6_u29 b3_2_P2_5_D192_j689_d6_u58 rfl) rfl) (all_glue _ 87 29 54 83 b3_2_P2_5_D192_j689_d6_u87 (all_glue _ 116 29 25 54 b3_2_P2_5_D192_j689_d6_u116 b3_2_P2_5_D192_j689_d6_u145 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j689_d7_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 7 59) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d7_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 7 59) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d7_u58 : (List.range' 58 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 7 59) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d7_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 7 59) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d7_u116 : (List.range' 116 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 7 59) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d7_u145 : (List.range' 145 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 7 59) = true := by
  decide +kernel

end DubC2.Atlas
