/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j688.Part8

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j688`, part 9/28 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j688_d1_u90 : (List.range' 90 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u120 : (List.range' 120 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u150 : (List.range' 150 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u180 : (List.range' 180 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u210 : (List.range' 210 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u240 : (List.range' 240 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u270 : (List.range' 270 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u300 : (List.range' 300 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u330 : (List.range' 330 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u360 : (List.range' 360 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u390 : (List.range' 390 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1_u420 : (List.range' 420 20).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 1 88) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 210 230 440 (all_glue _ 0 90 120 210 (all_glue _ 0 30 60 90 b3_2_P2_5_D192_j688_d1_u0 (all_glue _ 30 30 30 60 b3_2_P2_5_D192_j688_d1_u30 b3_2_P2_5_D192_j688_d1_u60 rfl) rfl) (all_glue _ 90 60 60 120 (all_glue _ 90 30 30 60 b3_2_P2_5_D192_j688_d1_u90 b3_2_P2_5_D192_j688_d1_u120 rfl) (all_glue _ 150 30 30 60 b3_2_P2_5_D192_j688_d1_u150 b3_2_P2_5_D192_j688_d1_u180 rfl) rfl) rfl) (all_glue _ 210 120 110 230 (all_glue _ 210 60 60 120 (all_glue _ 210 30 30 60 b3_2_P2_5_D192_j688_d1_u210 b3_2_P2_5_D192_j688_d1_u240 rfl) (all_glue _ 270 30 30 60 b3_2_P2_5_D192_j688_d1_u270 b3_2_P2_5_D192_j688_d1_u300 rfl) rfl) (all_glue _ 330 60 50 110 (all_glue _ 330 30 30 60 b3_2_P2_5_D192_j688_d1_u330 b3_2_P2_5_D192_j688_d1_u360 rfl) (all_glue _ 390 30 20 50 b3_2_P2_5_D192_j688_d1_u390 b3_2_P2_5_D192_j688_d1_u420 rfl) rfl) rfl) rfl))

end DubC2.Atlas
