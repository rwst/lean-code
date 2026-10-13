/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4144.Part27

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4144`, part 28/31 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4144_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u0 : (List.range' 0 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u23 : (List.range' 23 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u46 : (List.range' 46 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u69 : (List.range' 69 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u92 : (List.range' 92 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u115 : (List.range' 115 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u138 : (List.range' 138 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u161 : (List.range' 161 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5_u184 : (List.range' 184 1).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 5 37) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4144_d5 : (List.range' 5 1).all (detOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 92 93 185 (all_glue _ 0 46 46 92 (all_glue _ 0 23 23 46 b3_2_P2_5_D768_j4144_d5_u0 b3_2_P2_5_D768_j4144_d5_u23 rfl) (all_glue _ 46 23 23 46 b3_2_P2_5_D768_j4144_d5_u46 b3_2_P2_5_D768_j4144_d5_u69 rfl) rfl) (all_glue _ 92 46 47 93 (all_glue _ 92 23 23 46 b3_2_P2_5_D768_j4144_d5_u92 b3_2_P2_5_D768_j4144_d5_u115 rfl) (all_glue _ 138 23 24 47 b3_2_P2_5_D768_j4144_d5_u138 (all_glue _ 161 23 1 24 b3_2_P2_5_D768_j4144_d5_u161 b3_2_P2_5_D768_j4144_d5_u184 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4144_d6_u0 : (List.range' 0 23).all (detRowOK b3_2_P2_5_D768_j4144P b3_2_P2_5_D768_j4144C 6 26) = true := by
  decide +kernel

end DubC2.Atlas
