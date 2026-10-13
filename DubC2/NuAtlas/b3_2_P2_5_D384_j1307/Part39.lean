/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1307.Part38

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1307`, part 39/44 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1307_d18_u242 : (List.range' 242 18).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 18 52) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d18 : (List.range' 18 1).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 132 128 260 (all_glue _ 0 66 66 132 (all_glue _ 0 22 44 66 b3_2_P2_5_D384_j1307_d18_u0 (all_glue _ 22 22 22 44 b3_2_P2_5_D384_j1307_d18_u22 b3_2_P2_5_D384_j1307_d18_u44 rfl) rfl) (all_glue _ 66 22 44 66 b3_2_P2_5_D384_j1307_d18_u66 (all_glue _ 88 22 22 44 b3_2_P2_5_D384_j1307_d18_u88 b3_2_P2_5_D384_j1307_d18_u110 rfl) rfl) rfl) (all_glue _ 132 66 62 128 (all_glue _ 132 22 44 66 b3_2_P2_5_D384_j1307_d18_u132 (all_glue _ 154 22 22 44 b3_2_P2_5_D384_j1307_d18_u154 b3_2_P2_5_D384_j1307_d18_u176 rfl) rfl) (all_glue _ 198 22 40 62 b3_2_P2_5_D384_j1307_d18_u198 (all_glue _ 220 22 18 40 b3_2_P2_5_D384_j1307_d18_u220 b3_2_P2_5_D384_j1307_d18_u242 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1307_d19 : (List.range' 19 2).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d21 : (List.range' 21 1).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d22 : (List.range' 22 1).all (detOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d23_u0 : (List.range' 0 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 23 54) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d23_u22 : (List.range' 22 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 23 54) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d23_u44 : (List.range' 44 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 23 54) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1307_d23_u66 : (List.range' 66 22).all (detRowOK b3_2_P2_5_D384_j1307P b3_2_P2_5_D384_j1307C 23 54) = true := by
  decide +kernel

end DubC2.Atlas
