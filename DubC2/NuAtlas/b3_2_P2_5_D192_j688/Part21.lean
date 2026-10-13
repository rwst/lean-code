/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j688.Part20

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j688`, part 21/28 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j688_d14_u60 : (List.range' 60 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d14_u90 : (List.range' 90 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d14_u120 : (List.range' 120 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d14_u150 : (List.range' 150 20).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 14 34) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d14 : (List.range' 14 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 90 80 170 (all_glue _ 0 30 60 90 b3_2_P2_5_D192_j688_d14_u0 (all_glue _ 30 30 30 60 b3_2_P2_5_D192_j688_d14_u30 b3_2_P2_5_D192_j688_d14_u60 rfl) rfl) (all_glue _ 90 30 50 80 b3_2_P2_5_D192_j688_d14_u90 (all_glue _ 120 30 20 50 b3_2_P2_5_D192_j688_d14_u120 b3_2_P2_5_D192_j688_d14_u150 rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j688_d15 : (List.range' 15 2).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d17 : (List.range' 17 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d18_u0 : (List.range' 0 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 18 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d18_u30 : (List.range' 30 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 18 41) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d18_u60 : (List.range' 60 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 18 41) = true := by
  decide +kernel

end DubC2.Atlas
