/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1343.Part27

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1343`, part 28/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1343_d17_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 17 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d17_u112 : (List.range' 112 8).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 17 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d17 : (List.range' 17 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 64 120 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1343_d17_u0 b3_2_P2_5_D384_j1343_d17_u28 rfl) (all_glue _ 56 28 36 64 b3_2_P2_5_D384_j1343_d17_u56 (all_glue _ 84 28 8 36 b3_2_P2_5_D384_j1343_d17_u84 b3_2_P2_5_D384_j1343_d17_u112 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1343_d18 : (List.range' 18 4).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d22 : (List.range' 22 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d23_u0 : (List.range' 0 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 23 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d23_u28 : (List.range' 28 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 23 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d23_u56 : (List.range' 56 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 23 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d23_u84 : (List.range' 84 28).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 23 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d23_u112 : (List.range' 112 23).all (detRowOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C 23 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1343_d23 : (List.range' 23 1).all (detOK b3_2_P2_5_D384_j1343P b3_2_P2_5_D384_j1343C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 79 135 (all_glue _ 0 28 28 56 b3_2_P2_5_D384_j1343_d23_u0 b3_2_P2_5_D384_j1343_d23_u28 rfl) (all_glue _ 56 28 51 79 b3_2_P2_5_D384_j1343_d23_u56 (all_glue _ 84 28 23 51 b3_2_P2_5_D384_j1343_d23_u84 b3_2_P2_5_D384_j1343_d23_u112 rfl) rfl) rfl))

end DubC2.Atlas
