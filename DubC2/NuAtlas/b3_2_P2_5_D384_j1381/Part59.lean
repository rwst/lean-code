/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1381.Part58

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1381`, part 59/68 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1381_d28_u95 : (List.range' 95 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 28 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d28_u114 : (List.range' 114 1).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 28 23) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d28 : (List.range' 28 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 57 58 115 (all_glue _ 0 19 38 57 b3_2_P2_5_D384_j1381_d28_u0 (all_glue _ 19 19 19 38 b3_2_P2_5_D384_j1381_d28_u19 b3_2_P2_5_D384_j1381_d28_u38 rfl) rfl) (all_glue _ 57 38 20 58 (all_glue _ 57 19 19 38 b3_2_P2_5_D384_j1381_d28_u57 b3_2_P2_5_D384_j1381_d28_u76 rfl) (all_glue _ 95 19 1 20 b3_2_P2_5_D384_j1381_d28_u95 b3_2_P2_5_D384_j1381_d28_u114 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1381_d29_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 29 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d29_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 29 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d29_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 29 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d29_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 29 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d29_u76 : (List.range' 76 14).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 29 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d29 : (List.range' 29 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 38 52 90 (all_glue _ 0 19 19 38 b3_2_P2_5_D384_j1381_d29_u0 b3_2_P2_5_D384_j1381_d29_u19 rfl) (all_glue _ 38 19 33 52 b3_2_P2_5_D384_j1381_d29_u38 (all_glue _ 57 19 14 33 b3_2_P2_5_D384_j1381_d29_u57 b3_2_P2_5_D384_j1381_d29_u76 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1381_d30 : (List.range' 30 2).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d32_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 32 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d32_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 32 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d32_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 32 35) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d32_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 32 35) = true := by
  decide +kernel

end DubC2.Atlas
