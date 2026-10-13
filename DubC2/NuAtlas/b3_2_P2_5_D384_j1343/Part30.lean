/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1343.Part29

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1343`, part 30/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1343_d30_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 30 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d30_u112 : (List.range' 112 13).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 30 25) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d30 : (List.range' 30 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 69 125 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1343_d30_u0 b3_2_P2_5_D384_j1343_d30_u28 rfl) (all_glue _ 56 28 41 69 b3_2_P2_5_D384_j1343_d30_u56 (all_glue _ 84 28 13 41 b3_2_P2_5_D384_j1343_d30_u84 b3_2_P2_5_D384_j1343_d30_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d31 : (List.range' 31 5).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d36 : (List.range' 36 3).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true := by
  decide +kernel

end DubC2.Atlas
