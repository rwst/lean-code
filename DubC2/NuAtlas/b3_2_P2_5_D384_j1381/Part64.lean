/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1381.Part63

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1381`, part 64/68 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1381_d44 : (List.range' 44 3).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d47 : (List.range' 47 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d48_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 48 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d48_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 48 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d48_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 48 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d48_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 48 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d48_u76 : (List.range' 76 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 48 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d48_u95 : (List.range' 95 15).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 48 22) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d48 : (List.range' 48 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 57 53 110 (all_glue _ 0 19 38 57 b3_2_P2_5_D384_j1381_d48_u0 (all_glue _ 19 19 19 38 b3_2_P2_5_D384_j1381_d48_u19 b3_2_P2_5_D384_j1381_d48_u38 rfl) rfl) (all_glue _ 57 19 34 53 b3_2_P2_5_D384_j1381_d48_u57 (all_glue _ 76 19 15 34 b3_2_P2_5_D384_j1381_d48_u76 b3_2_P2_5_D384_j1381_d48_u95 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1381_d49 : (List.range' 49 1).all (detOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1381_d50_u0 : (List.range' 0 19).all (detRowOK b3_2_P2_5_D384_j1381P b3_2_P2_5_D384_j1381C 50 16) = true := by
  decide +kernel

end DubC2.Atlas
