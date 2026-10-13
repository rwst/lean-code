/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4150.Part60

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4150`, part 61/61 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4150_d45_u84 : (List.range' 84 14).all (detRowOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C 45 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d45_u98 : (List.range' 98 14).all (detRowOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C 45 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d45_u112 : (List.range' 112 8).all (detRowOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C 45 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d45 : (List.range' 45 1).all (detOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 56 64 120 (all_glue _ 0 28 28 56 (all_glue _ 0 14 14 28 b3_2_P2_5_D768_j4150_d45_u0 b3_2_P2_5_D768_j4150_d45_u14 rfl) (all_glue _ 28 14 14 28 b3_2_P2_5_D768_j4150_d45_u28 b3_2_P2_5_D768_j4150_d45_u42 rfl) rfl) (all_glue _ 56 28 36 64 (all_glue _ 56 14 14 28 b3_2_P2_5_D768_j4150_d45_u56 b3_2_P2_5_D768_j4150_d45_u70 rfl) (all_glue _ 84 14 22 36 b3_2_P2_5_D768_j4150_d45_u84 (all_glue _ 98 14 8 22 b3_2_P2_5_D768_j4150_d45_u98 b3_2_P2_5_D768_j4150_d45_u112 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4150_d46 : (List.range' 46 7).all (detOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d53 : (List.range' 53 1).all (detOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C) = true := by
  decide +kernel

end DubC2.Atlas
