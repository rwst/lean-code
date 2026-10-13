/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1344.Part26

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1344`, part 27/29 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1344_d14_u116 : (List.range' 116 14).all (detRowOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C 14 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d14 : (List.range' 14 1).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 58 72 130 (all_glue _ 0 29 29 58 b3_2_P2_5_D384_j1344_d14_u0 b3_2_P2_5_D384_j1344_d14_u29 rfl) (all_glue _ 58 29 43 72 b3_2_P2_5_D384_j1344_d14_u58 (all_glue _ 87 29 14 43 b3_2_P2_5_D384_j1344_d14_u87 b3_2_P2_5_D384_j1344_d14_u116 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1344_d15 : (List.range' 15 2).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d17 : (List.range' 17 1).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d18 : (List.range' 18 4).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1344_d22 : (List.range' 22 1).all (detOK b3_2_P2_5_D384_j1344P b3_2_P2_5_D384_j1344C) = true := by
  decide +kernel

end DubC2.Atlas
