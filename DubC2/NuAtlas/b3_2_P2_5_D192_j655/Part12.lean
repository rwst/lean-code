/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j655.Part11

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j655`, part 12/20 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j655_d2_u1564 : (List.range' 1564 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2_u1598 : (List.range' 1598 17).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 2 323) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d2 : (List.range' 2 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 816 799 1615 (all_glue _ 0 408 408 816 (all_glue _ 0 204 204 408 (all_glue _ 0 102 102 204 (all_glue _ 0 34 68 102 b3_2_P2_5_D192_j655_d2_u0 (all_glue _ 34 34 34 68 b3_2_P2_5_D192_j655_d2_u34 b3_2_P2_5_D192_j655_d2_u68 rfl) rfl) (all_glue _ 102 34 68 102 b3_2_P2_5_D192_j655_d2_u102 (all_glue _ 136 34 34 68 b3_2_P2_5_D192_j655_d2_u136 b3_2_P2_5_D192_j655_d2_u170 rfl) rfl) rfl) (all_glue _ 204 102 102 204 (all_glue _ 204 34 68 102 b3_2_P2_5_D192_j655_d2_u204 (all_glue _ 238 34 34 68 b3_2_P2_5_D192_j655_d2_u238 b3_2_P2_5_D192_j655_d2_u272 rfl) rfl) (all_glue _ 306 34 68 102 b3_2_P2_5_D192_j655_d2_u306 (all_glue _ 340 34 34 68 b3_2_P2_5_D192_j655_d2_u340 b3_2_P2_5_D192_j655_d2_u374 rfl) rfl) rfl) rfl) (all_glue _ 408 204 204 408 (all_glue _ 408 102 102 204 (all_glue _ 408 34 68 102 b3_2_P2_5_D192_j655_d2_u408 (all_glue _ 442 34 34 68 b3_2_P2_5_D192_j655_d2_u442 b3_2_P2_5_D192_j655_d2_u476 rfl) rfl) (all_glue _ 510 34 68 102 b3_2_P2_5_D192_j655_d2_u510 (all_glue _ 544 34 34 68 b3_2_P2_5_D192_j655_d2_u544 b3_2_P2_5_D192_j655_d2_u578 rfl) rfl) rfl) (all_glue _ 612 102 102 204 (all_glue _ 612 34 68 102 b3_2_P2_5_D192_j655_d2_u612 (all_glue _ 646 34 34 68 b3_2_P2_5_D192_j655_d2_u646 b3_2_P2_5_D192_j655_d2_u680 rfl) rfl) (all_glue _ 714 34 68 102 b3_2_P2_5_D192_j655_d2_u714 (all_glue _ 748 34 34 68 b3_2_P2_5_D192_j655_d2_u748 b3_2_P2_5_D192_j655_d2_u782 rfl) rfl) rfl) rfl) rfl) (all_glue _ 816 408 391 799 (all_glue _ 816 204 204 408 (all_glue _ 816 102 102 204 (all_glue _ 816 34 68 102 b3_2_P2_5_D192_j655_d2_u816 (all_glue _ 850 34 34 68 b3_2_P2_5_D192_j655_d2_u850 b3_2_P2_5_D192_j655_d2_u884 rfl) rfl) (all_glue _ 918 34 68 102 b3_2_P2_5_D192_j655_d2_u918 (all_glue _ 952 34 34 68 b3_2_P2_5_D192_j655_d2_u952 b3_2_P2_5_D192_j655_d2_u986 rfl) rfl) rfl) (all_glue _ 1020 102 102 204 (all_glue _ 1020 34 68 102 b3_2_P2_5_D192_j655_d2_u1020 (all_glue _ 1054 34 34 68 b3_2_P2_5_D192_j655_d2_u1054 b3_2_P2_5_D192_j655_d2_u1088 rfl) rfl) (all_glue _ 1122 34 68 102 b3_2_P2_5_D192_j655_d2_u1122 (all_glue _ 1156 34 34 68 b3_2_P2_5_D192_j655_d2_u1156 b3_2_P2_5_D192_j655_d2_u1190 rfl) rfl) rfl) rfl) (all_glue _ 1224 204 187 391 (all_glue _ 1224 102 102 204 (all_glue _ 1224 34 68 102 b3_2_P2_5_D192_j655_d2_u1224 (all_glue _ 1258 34 34 68 b3_2_P2_5_D192_j655_d2_u1258 b3_2_P2_5_D192_j655_d2_u1292 rfl) rfl) (all_glue _ 1326 34 68 102 b3_2_P2_5_D192_j655_d2_u1326 (all_glue _ 1360 34 34 68 b3_2_P2_5_D192_j655_d2_u1360 b3_2_P2_5_D192_j655_d2_u1394 rfl) rfl) rfl) (all_glue _ 1428 102 85 187 (all_glue _ 1428 34 68 102 b3_2_P2_5_D192_j655_d2_u1428 (all_glue _ 1462 34 34 68 b3_2_P2_5_D192_j655_d2_u1462 b3_2_P2_5_D192_j655_d2_u1496 rfl) rfl) (all_glue _ 1530 34 51 85 b3_2_P2_5_D192_j655_d2_u1530 (all_glue _ 1564 34 17 51 b3_2_P2_5_D192_j655_d2_u1564 b3_2_P2_5_D192_j655_d2_u1598 rfl) rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d3_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3_u136 : (List.range' 136 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3_u170 : (List.range' 170 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3_u204 : (List.range' 204 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3_u238 : (List.range' 238 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3_u272 : (List.range' 272 3).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 3 55) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d3 : (List.range' 3 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 136 139 275 (all_glue _ 0 68 68 136 (all_glue _ 0 34 34 68 b3_2_P2_5_D192_j655_d3_u0 b3_2_P2_5_D192_j655_d3_u34 rfl) (all_glue _ 68 34 34 68 b3_2_P2_5_D192_j655_d3_u68 b3_2_P2_5_D192_j655_d3_u102 rfl) rfl) (all_glue _ 136 68 71 139 (all_glue _ 136 34 34 68 b3_2_P2_5_D192_j655_d3_u136 b3_2_P2_5_D192_j655_d3_u170 rfl) (all_glue _ 204 34 37 71 b3_2_P2_5_D192_j655_d3_u204 (all_glue _ 238 34 3 37 b3_2_P2_5_D192_j655_d3_u238 b3_2_P2_5_D192_j655_d3_u272 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d4 : (List.range' 4 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d5_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 5 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d5_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 5 42) = true := by
  decide +kernel

end DubC2.Atlas
