/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1316.Part39

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1316`, part 40/42 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1316_d25_u184 : (List.range' 184 23).all (detRowOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C 25 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d25_u207 : (List.range' 207 23).all (detRowOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C 25 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d25_u230 : (List.range' 230 10).all (detRowOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C 25 48) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d25 : (List.range' 25 1).all (detOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 115 125 240 (all_glue _ 0 46 69 115 (all_glue _ 0 23 23 46 b3_2_P2_5_D384_j1316_d25_u0 b3_2_P2_5_D384_j1316_d25_u23 rfl) (all_glue _ 46 23 46 69 b3_2_P2_5_D384_j1316_d25_u46 (all_glue _ 69 23 23 46 b3_2_P2_5_D384_j1316_d25_u69 b3_2_P2_5_D384_j1316_d25_u92 rfl) rfl) rfl) (all_glue _ 115 69 56 125 (all_glue _ 115 23 46 69 b3_2_P2_5_D384_j1316_d25_u115 (all_glue _ 138 23 23 46 b3_2_P2_5_D384_j1316_d25_u138 b3_2_P2_5_D384_j1316_d25_u161 rfl) rfl) (all_glue _ 184 23 33 56 b3_2_P2_5_D384_j1316_d25_u184 (all_glue _ 207 23 10 33 b3_2_P2_5_D384_j1316_d25_u207 b3_2_P2_5_D384_j1316_d25_u230 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1316_d26 : (List.range' 26 2).all (detOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1316_d28 : (List.range' 28 4).all (detOK b3_2_P2_5_D384_j1316P b3_2_P2_5_D384_j1316C) = true := by
  decide +kernel

end DubC2.Atlas
