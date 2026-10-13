/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1381.Part60

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1381`, part 61/68 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1381_d35 : (List.range' 35 2).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 37 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 37 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 37 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 37 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37_u76 : (List.range' 76 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 37 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37_u95 : (List.range' 95 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 37 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37_u114 : (List.range' 114 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 37 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37_u133 : (List.range' 133 2).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 37 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d37 : (List.range' 37 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 76 59 135 (all_glue _ 0 38 38 76 (all_glue _ 0 19 19 38 b3_2_P2_5_D384_j1381_d37_u0 b3_2_P2_5_D384_j1381_d37_u19 rfl) (all_glue _ 38 19 19 38 b3_2_P2_5_D384_j1381_d37_u38 b3_2_P2_5_D384_j1381_d37_u57 rfl) rfl) (all_glue _ 76 38 21 59 (all_glue _ 76 19 19 38 b3_2_P2_5_D384_j1381_d37_u76 b3_2_P2_5_D384_j1381_d37_u95 rfl) (all_glue _ 114 19 2 21 b3_2_P2_5_D384_j1381_d37_u114 b3_2_P2_5_D384_j1381_d37_u133 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1381_d38_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 38 25) = true := by
  decide +kernel

end DubC2.Atlas
