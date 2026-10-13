/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4150.Part56

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4150`, part 57/61 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4150_d25_u70 : (List.range' 70 14).all (detRowOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C 25 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d25_u84 : (List.range' 84 14).all (detRowOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C 25 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d25_u98 : (List.range' 98 14).all (detRowOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C 25 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d25_u112 : (List.range' 112 14).all (detRowOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C 25 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d25_u126 : (List.range' 126 9).all (detRowOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C 25 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d25 : (List.range' 25 1).all (detOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 70 65 135 (all_glue _ 0 28 42 70 (all_glue _ 0 14 14 28 b3_2_P2_5_D768_j4150_d25_u0 b3_2_P2_5_D768_j4150_d25_u14 rfl) (all_glue _ 28 14 28 42 b3_2_P2_5_D768_j4150_d25_u28 (all_glue _ 42 14 14 28 b3_2_P2_5_D768_j4150_d25_u42 b3_2_P2_5_D768_j4150_d25_u56 rfl) rfl) rfl) (all_glue _ 70 28 37 65 (all_glue _ 70 14 14 28 b3_2_P2_5_D768_j4150_d25_u70 b3_2_P2_5_D768_j4150_d25_u84 rfl) (all_glue _ 98 14 23 37 b3_2_P2_5_D768_j4150_d25_u98 (all_glue _ 112 14 9 23 b3_2_P2_5_D768_j4150_d25_u112 b3_2_P2_5_D768_j4150_d25_u126 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4150_d26 : (List.range' 26 3).all (detOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4150_d29 : (List.range' 29 4).all (detOK b3_2_P2_5_D768_j4150P b3_2_P2_5_D768_j4150C) = true := by
  decide +kernel

end DubC2.Atlas
