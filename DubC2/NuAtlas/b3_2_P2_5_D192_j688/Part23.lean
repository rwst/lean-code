/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j688.Part22

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j688`, part 23/28 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j688_d22 : (List.range' 22 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d23 : (List.range' 23 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d24_u0 : (List.range' 0 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 24 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d24_u30 : (List.range' 30 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 24 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d24_u60 : (List.range' 60 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 24 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d24_u90 : (List.range' 90 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 24 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d24_u120 : (List.range' 120 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 24 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d24_u150 : (List.range' 150 30).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 24 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d24_u180 : (List.range' 180 10).all (detRowOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C 24 38) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j688_d24 : (List.range' 24 1).all (detOK b3_2_P2_5_D192_j688P b3_2_P2_5_D192_j688C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 90 100 190 (all_glue _ 0 30 60 90 b3_2_P2_5_D192_j688_d24_u0 (all_glue _ 30 30 30 60 b3_2_P2_5_D192_j688_d24_u30 b3_2_P2_5_D192_j688_d24_u60 rfl) rfl) (all_glue _ 90 60 40 100 (all_glue _ 90 30 30 60 b3_2_P2_5_D192_j688_d24_u90 b3_2_P2_5_D192_j688_d24_u120 rfl) (all_glue _ 150 30 10 40 b3_2_P2_5_D192_j688_d24_u150 b3_2_P2_5_D192_j688_d24_u180 rfl) rfl) rfl))

end DubC2.Atlas
