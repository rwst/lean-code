/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j688.Part21

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j688`, part 22/28 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j688_d18_u90 : (List.range' 90 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 18 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d18_u120 : (List.range' 120 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 18 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d18_u150 : (List.range' 150 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 18 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d18_u180 : (List.range' 180 25).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 18 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d18 : (List.range' 18 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 90 115 205 (all_glue _ 0 30 60 90 b3_2_P2_5_D192_j688_d18_u0 (all_glue _ 30 30 30 60 b3_2_P2_5_D192_j688_d18_u30 b3_2_P2_5_D192_j688_d18_u60 rfl) rfl) (all_glue _ 90 60 55 115 (all_glue _ 90 30 30 60 b3_2_P2_5_D192_j688_d18_u90 b3_2_P2_5_D192_j688_d18_u120 rfl) (all_glue _ 150 30 25 55 b3_2_P2_5_D192_j688_d18_u150 b3_2_P2_5_D192_j688_d18_u180 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j688_d19 : (List.range' 19 2).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d21 : (List.range' 21 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true := by
  decide +kernel

end DubC2.Atlas
