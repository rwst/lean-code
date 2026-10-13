/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j688.Part15

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j688`, part 16/28 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j688_d4_u150 : (List.range' 150 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 4 54) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d4_u180 : (List.range' 180 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 4 54) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d4_u210 : (List.range' 210 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 4 54) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d4_u240 : (List.range' 240 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 4 54) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 120 150 270 (all_glue _ 0 60 60 120 (all_glue _ 0 30 30 60 b3_2_P2_5_D192_j688_d4_u0 b3_2_P2_5_D192_j688_d4_u30 rfl) (all_glue _ 60 30 30 60 b3_2_P2_5_D192_j688_d4_u60 b3_2_P2_5_D192_j688_d4_u90 rfl) rfl) (all_glue _ 120 60 90 150 (all_glue _ 120 30 30 60 b3_2_P2_5_D192_j688_d4_u120 b3_2_P2_5_D192_j688_d4_u150 rfl) (all_glue _ 180 30 60 90 b3_2_P2_5_D192_j688_d4_u180 (all_glue _ 210 30 30 60 b3_2_P2_5_D192_j688_d4_u210 b3_2_P2_5_D192_j688_d4_u240 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j688_d5_u0 : (List.range' 0 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 5 64) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d5_u30 : (List.range' 30 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 5 64) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d5_u60 : (List.range' 60 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 5 64) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d5_u90 : (List.range' 90 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 5 64) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d5_u120 : (List.range' 120 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 5 64) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d5_u150 : (List.range' 150 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 5 64) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d5_u180 : (List.range' 180 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 5 64) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d5_u210 : (List.range' 210 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 5 64) = true := by
  decide +kernel

end DubC2.Atlas
