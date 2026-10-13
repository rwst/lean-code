/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4144.Part28

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4144`, part 29/31 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4144_d6_u23 : (List.range' 23 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 6 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d6_u46 : (List.range' 46 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 6 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d6_u69 : (List.range' 69 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 6 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d6_u92 : (List.range' 92 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 6 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d6_u115 : (List.range' 115 15).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 6 26) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 69 61 130 (all_glue _ 0 23 46 69 b3_2_P2_5_D768_j4144_d6_u0 (all_glue _ 23 23 23 46 b3_2_P2_5_D768_j4144_d6_u23 b3_2_P2_5_D768_j4144_d6_u46 rfl) rfl) (all_glue _ 69 23 38 61 b3_2_P2_5_D768_j4144_d6_u69 (all_glue _ 92 23 15 38 b3_2_P2_5_D768_j4144_d6_u92 b3_2_P2_5_D768_j4144_d6_u115 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4144_d7 : (List.range' 7 1).all (detOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d8 : (List.range' 8 2).all (detOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C) = true := by
  decide +kernel

end DubC2.Atlas
