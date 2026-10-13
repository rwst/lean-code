/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1381.Part62

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1381`, part 63/68 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1381_d40 : (List.range' 40 3).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d43_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 43 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d43_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 43 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d43_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 43 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d43_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 43 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d43_u76 : (List.range' 76 14).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 43 18) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d43 : (List.range' 43 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 38 52 90 (all_glue _ 0 19 19 38 b3_2_P2_5_D384_j1381_d43_u0 b3_2_P2_5_D384_j1381_d43_u19 rfl) (all_glue _ 38 19 33 52 b3_2_P2_5_D384_j1381_d43_u38 (all_glue _ 57 19 14 33 b3_2_P2_5_D384_j1381_d43_u57 b3_2_P2_5_D384_j1381_d43_u76 rfl) rfl) rfl))

end DubC2.Atlas
