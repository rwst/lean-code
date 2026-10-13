/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1316.Part33

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1316`, part 34/42 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1316_d10_u276 : (List.range' 276 9).all (detRowOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C 10 57) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d10 : (List.range' 10 1).all (detOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 138 147 285 (all_glue _ 0 69 69 138 (all_glue _ 0 23 46 69 b3_2_P2_5_D384_j1316_d10_u0 (all_glue _ 23 23 23 46 b3_2_P2_5_D384_j1316_d10_u23 b3_2_P2_5_D384_j1316_d10_u46 rfl) rfl) (all_glue _ 69 23 46 69 b3_2_P2_5_D384_j1316_d10_u69 (all_glue _ 92 23 23 46 b3_2_P2_5_D384_j1316_d10_u92 b3_2_P2_5_D384_j1316_d10_u115 rfl) rfl) rfl) (all_glue _ 138 69 78 147 (all_glue _ 138 23 46 69 b3_2_P2_5_D384_j1316_d10_u138 (all_glue _ 161 23 23 46 b3_2_P2_5_D384_j1316_d10_u161 b3_2_P2_5_D384_j1316_d10_u184 rfl) rfl) (all_glue _ 207 46 32 78 (all_glue _ 207 23 23 46 b3_2_P2_5_D384_j1316_d10_u207 b3_2_P2_5_D384_j1316_d10_u230 rfl) (all_glue _ 253 23 9 32 b3_2_P2_5_D384_j1316_d10_u253 b3_2_P2_5_D384_j1316_d10_u276 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1316_d11 : (List.range' 11 2).all (detOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d13 : (List.range' 13 1).all (detOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d14_u0 : (List.range' 0 23).all (detRowOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C 14 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d14_u23 : (List.range' 23 23).all (detRowOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C 14 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d14_u46 : (List.range' 46 23).all (detRowOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C 14 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d14_u69 : (List.range' 69 23).all (detRowOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C 14 51) = true := by
  decide +kernel

end DubC2.Atlas
