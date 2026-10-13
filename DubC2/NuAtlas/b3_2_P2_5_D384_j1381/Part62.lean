/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1381.Part61

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1381`, part 62/68 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1381_d38_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 38 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d38_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 38 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d38_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 38 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d38_u76 : (List.range' 76 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 38 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d38_u95 : (List.range' 95 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 38 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d38_u114 : (List.range' 114 11).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 38 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d38 : (List.range' 38 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 57 68 125 (all_glue _ 0 19 38 57 b3_2_P2_5_D384_j1381_d38_u0 (all_glue _ 19 19 19 38 b3_2_P2_5_D384_j1381_d38_u19 b3_2_P2_5_D384_j1381_d38_u38 rfl) rfl) (all_glue _ 57 38 30 68 (all_glue _ 57 19 19 38 b3_2_P2_5_D384_j1381_d38_u57 b3_2_P2_5_D384_j1381_d38_u76 rfl) (all_glue _ 95 19 11 30 b3_2_P2_5_D384_j1381_d38_u95 b3_2_P2_5_D384_j1381_d38_u114 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1381_d39_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 39 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d39_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 39 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d39_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 39 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d39_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 39 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d39_u76 : (List.range' 76 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 39 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d39 : (List.range' 39 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 38 57 95 (all_glue _ 0 19 19 38 b3_2_P2_5_D384_j1381_d39_u0 b3_2_P2_5_D384_j1381_d39_u19 rfl) (all_glue _ 38 19 38 57 b3_2_P2_5_D384_j1381_d39_u38 (all_glue _ 57 19 19 38 b3_2_P2_5_D384_j1381_d39_u57 b3_2_P2_5_D384_j1381_d39_u76 rfl) rfl) rfl))

end DubC2.Atlas
