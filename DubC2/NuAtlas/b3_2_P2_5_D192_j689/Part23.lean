/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j689.Part22

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j689`, part 23/29 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j689_d17 : (List.range' 17 1).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 18 44) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 18 44) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18_u58 : (List.range' 58 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 18 44) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 18 44) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18_u116 : (List.range' 116 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 18 44) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18_u145 : (List.range' 145 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 18 44) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18_u174 : (List.range' 174 29).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 18 44) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18_u203 : (List.range' 203 17).all (detRowOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C 18 44) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j689_d18 : (List.range' 18 1).all (detOK b3_2_P2_5_D192_j689P b3_2_P2_5_D192_j689C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 116 104 220 (all_glue _ 0 58 58 116 (all_glue _ 0 29 29 58 b3_2_P2_5_D192_j689_d18_u0 b3_2_P2_5_D192_j689_d18_u29 rfl) (all_glue _ 58 29 29 58 b3_2_P2_5_D192_j689_d18_u58 b3_2_P2_5_D192_j689_d18_u87 rfl) rfl) (all_glue _ 116 58 46 104 (all_glue _ 116 29 29 58 b3_2_P2_5_D192_j689_d18_u116 b3_2_P2_5_D192_j689_d18_u145 rfl) (all_glue _ 174 29 17 46 b3_2_P2_5_D192_j689_d18_u174 b3_2_P2_5_D192_j689_d18_u203 rfl) rfl) rfl))

end DubC2.Atlas
