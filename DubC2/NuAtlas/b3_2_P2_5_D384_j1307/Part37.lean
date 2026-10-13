/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1307.Part36

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1307`, part 37/44 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1307_d15_u0 : (List.range' 0 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 15 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d15_u22 : (List.range' 22 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 15 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d15_u44 : (List.range' 44 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 15 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d15_u66 : (List.range' 66 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 15 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d15_u88 : (List.range' 88 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 15 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d15_u110 : (List.range' 110 5).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 15 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d15 : (List.range' 15 1).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 66 49 115 (all_glue _ 0 22 44 66 b3_2_P2_5_D384_j1307_d15_u0 (all_glue _ 22 22 22 44 b3_2_P2_5_D384_j1307_d15_u22 b3_2_P2_5_D384_j1307_d15_u44 rfl) rfl) (all_glue _ 66 22 27 49 b3_2_P2_5_D384_j1307_d15_u66 (all_glue _ 88 22 5 27 b3_2_P2_5_D384_j1307_d15_u88 b3_2_P2_5_D384_j1307_d15_u110 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1307_d16 : (List.range' 16 1).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d17_u0 : (List.range' 0 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 17 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d17_u22 : (List.range' 22 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 17 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d17_u44 : (List.range' 44 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 17 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d17_u66 : (List.range' 66 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 17 23) = true := by
  decide +kernel

end DubC2.Atlas
