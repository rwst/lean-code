/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1307.Part41

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1307`, part 42/44 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1307_d26_u220 : (List.range' 220 5).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 26 45) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d26 : (List.range' 26 1).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 110 115 225 (all_glue _ 0 44 66 110 (all_glue _ 0 22 22 44 b3_2_P2_5_D384_j1307_d26_u0 b3_2_P2_5_D384_j1307_d26_u22 rfl) (all_glue _ 44 22 44 66 b3_2_P2_5_D384_j1307_d26_u44 (all_glue _ 66 22 22 44 b3_2_P2_5_D384_j1307_d26_u66 b3_2_P2_5_D384_j1307_d26_u88 rfl) rfl) rfl) (all_glue _ 110 66 49 115 (all_glue _ 110 22 44 66 b3_2_P2_5_D384_j1307_d26_u110 (all_glue _ 132 22 22 44 b3_2_P2_5_D384_j1307_d26_u132 b3_2_P2_5_D384_j1307_d26_u154 rfl) rfl) (all_glue _ 176 22 27 49 b3_2_P2_5_D384_j1307_d26_u176 (all_glue _ 198 22 5 27 b3_2_P2_5_D384_j1307_d26_u198 b3_2_P2_5_D384_j1307_d26_u220 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1307_d27_u0 : (List.range' 0 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d27_u22 : (List.range' 22 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d27_u44 : (List.range' 44 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d27_u66 : (List.range' 66 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d27_u88 : (List.range' 88 12).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 27 20) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d27 : (List.range' 27 1).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 44 56 100 (all_glue _ 0 22 22 44 b3_2_P2_5_D384_j1307_d27_u0 b3_2_P2_5_D384_j1307_d27_u22 rfl) (all_glue _ 44 22 34 56 b3_2_P2_5_D384_j1307_d27_u44 (all_glue _ 66 22 12 34 b3_2_P2_5_D384_j1307_d27_u66 b3_2_P2_5_D384_j1307_d27_u88 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1307_d28 : (List.range' 28 2).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d30 : (List.range' 30 3).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true := by
  decide +kernel

end DubC2.Atlas
