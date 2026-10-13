/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1345.Part25

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1345`, part 26/29 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1345_d10_u116 : (List.range' 116 29).all (detRowOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C 10 29) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1345_d10 : (List.range' 10 1).all (detOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 58 87 145 (all_glue _ 0 29 29 58 b3_2_P2_5_D384_j1345_d10_u0 b3_2_P2_5_D384_j1345_d10_u29 rfl) (all_glue _ 58 29 58 87 b3_2_P2_5_D384_j1345_d10_u58 (all_glue _ 87 29 29 58 b3_2_P2_5_D384_j1345_d10_u87 b3_2_P2_5_D384_j1345_d10_u116 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1345_d11 : (List.range' 11 2).all (detOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1345_d13 : (List.range' 13 1).all (detOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1345_d14_u0 : (List.range' 0 29).all (detRowOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C 14 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1345_d14_u29 : (List.range' 29 29).all (detRowOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C 14 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1345_d14_u58 : (List.range' 58 29).all (detRowOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C 14 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1345_d14_u87 : (List.range' 87 29).all (detRowOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C 14 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1345_d14_u116 : (List.range' 116 14).all (detRowOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C 14 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1345_d14 : (List.range' 14 1).all (detOK b3_2_P2_5_D384_j1345P b3_2_P2_5_D384_j1345C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 58 72 130 (all_glue _ 0 29 29 58 b3_2_P2_5_D384_j1345_d14_u0 b3_2_P2_5_D384_j1345_d14_u29 rfl) (all_glue _ 58 29 43 72 b3_2_P2_5_D384_j1345_d14_u58 (all_glue _ 87 29 14 43 b3_2_P2_5_D384_j1345_d14_u87 b3_2_P2_5_D384_j1345_d14_u116 rfl) rfl) rfl))

end DubC2.Atlas
