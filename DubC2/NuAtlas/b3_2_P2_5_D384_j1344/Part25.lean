/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1344.Part24

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1344`, part 25/29 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1344_d7 : (List.range' 7 1).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d8_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 8 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d8_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 8 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d8_u58 : (List.range' 58 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 8 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d8_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 8 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d8_u116 : (List.range' 116 4).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 8 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d8 : (List.range' 8 1).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 58 62 120 (all_glue _ 0 29 29 58 b3_2_P2_5_D384_j1344_d8_u0 b3_2_P2_5_D384_j1344_d8_u29 rfl) (all_glue _ 58 29 33 62 b3_2_P2_5_D384_j1344_d8_u58 (all_glue _ 87 29 4 33 b3_2_P2_5_D384_j1344_d8_u87 b3_2_P2_5_D384_j1344_d8_u116 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1344_d9_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d9_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d9_u58 : (List.range' 58 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d9_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d9_u116 : (List.range' 116 14).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 9 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d9 : (List.range' 9 1).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 58 72 130 (all_glue _ 0 29 29 58 b3_2_P2_5_D384_j1344_d9_u0 b3_2_P2_5_D384_j1344_d9_u29 rfl) (all_glue _ 58 29 43 72 b3_2_P2_5_D384_j1344_d9_u58 (all_glue _ 87 29 14 43 b3_2_P2_5_D384_j1344_d9_u87 b3_2_P2_5_D384_j1344_d9_u116 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1344_d10_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 10 29) = true := by
  decide +kernel

end DubC2.Atlas
