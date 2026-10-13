/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j655.Part6

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j655`, part 7/20 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j655_d0_u1530 : (List.range' 1530 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 0 343) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d0_u1564 : (List.range' 1564 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 0 343) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d0_u1598 : (List.range' 1598 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 0 343) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d0_u1632 : (List.range' 1632 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 0 343) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d0_u1666 : (List.range' 1666 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 0 343) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d0_u1700 : (List.range' 1700 15).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 0 343) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 850 865 1715 (all_glue _ 0 408 442 850 (all_glue _ 0 204 204 408 (all_glue _ 0 102 102 204 (all_glue _ 0 34 68 102 b3_2_P2_5_D192_j655_d0_u0 (all_glue _ 34 34 34 68 b3_2_P2_5_D192_j655_d0_u34 b3_2_P2_5_D192_j655_d0_u68 rfl) rfl) (all_glue _ 102 34 68 102 b3_2_P2_5_D192_j655_d0_u102 (all_glue _ 136 34 34 68 b3_2_P2_5_D192_j655_d0_u136 b3_2_P2_5_D192_j655_d0_u170 rfl) rfl) rfl) (all_glue _ 204 102 102 204 (all_glue _ 204 34 68 102 b3_2_P2_5_D192_j655_d0_u204 (all_glue _ 238 34 34 68 b3_2_P2_5_D192_j655_d0_u238 b3_2_P2_5_D192_j655_d0_u272 rfl) rfl) (all_glue _ 306 34 68 102 b3_2_P2_5_D192_j655_d0_u306 (all_glue _ 340 34 34 68 b3_2_P2_5_D192_j655_d0_u340 b3_2_P2_5_D192_j655_d0_u374 rfl) rfl) rfl) rfl) (all_glue _ 408 204 238 442 (all_glue _ 408 102 102 204 (all_glue _ 408 34 68 102 b3_2_P2_5_D192_j655_d0_u408 (all_glue _ 442 34 34 68 b3_2_P2_5_D192_j655_d0_u442 b3_2_P2_5_D192_j655_d0_u476 rfl) rfl) (all_glue _ 510 34 68 102 b3_2_P2_5_D192_j655_d0_u510 (all_glue _ 544 34 34 68 b3_2_P2_5_D192_j655_d0_u544 b3_2_P2_5_D192_j655_d0_u578 rfl) rfl) rfl) (all_glue _ 612 102 136 238 (all_glue _ 612 34 68 102 b3_2_P2_5_D192_j655_d0_u612 (all_glue _ 646 34 34 68 b3_2_P2_5_D192_j655_d0_u646 b3_2_P2_5_D192_j655_d0_u680 rfl) rfl) (all_glue _ 714 68 68 136 (all_glue _ 714 34 34 68 b3_2_P2_5_D192_j655_d0_u714 b3_2_P2_5_D192_j655_d0_u748 rfl) (all_glue _ 782 34 34 68 b3_2_P2_5_D192_j655_d0_u782 b3_2_P2_5_D192_j655_d0_u816 rfl) rfl) rfl) rfl) rfl) (all_glue _ 850 442 423 865 (all_glue _ 850 204 238 442 (all_glue _ 850 102 102 204 (all_glue _ 850 34 68 102 b3_2_P2_5_D192_j655_d0_u850 (all_glue _ 884 34 34 68 b3_2_P2_5_D192_j655_d0_u884 b3_2_P2_5_D192_j655_d0_u918 rfl) rfl) (all_glue _ 952 34 68 102 b3_2_P2_5_D192_j655_d0_u952 (all_glue _ 986 34 34 68 b3_2_P2_5_D192_j655_d0_u986 b3_2_P2_5_D192_j655_d0_u1020 rfl) rfl) rfl) (all_glue _ 1054 102 136 238 (all_glue _ 1054 34 68 102 b3_2_P2_5_D192_j655_d0_u1054 (all_glue _ 1088 34 34 68 b3_2_P2_5_D192_j655_d0_u1088 b3_2_P2_5_D192_j655_d0_u1122 rfl) rfl) (all_glue _ 1156 68 68 136 (all_glue _ 1156 34 34 68 b3_2_P2_5_D192_j655_d0_u1156 b3_2_P2_5_D192_j655_d0_u1190 rfl) (all_glue _ 1224 34 34 68 b3_2_P2_5_D192_j655_d0_u1224 b3_2_P2_5_D192_j655_d0_u1258 rfl) rfl) rfl) rfl) (all_glue _ 1292 204 219 423 (all_glue _ 1292 102 102 204 (all_glue _ 1292 34 68 102 b3_2_P2_5_D192_j655_d0_u1292 (all_glue _ 1326 34 34 68 b3_2_P2_5_D192_j655_d0_u1326 b3_2_P2_5_D192_j655_d0_u1360 rfl) rfl) (all_glue _ 1394 34 68 102 b3_2_P2_5_D192_j655_d0_u1394 (all_glue _ 1428 34 34 68 b3_2_P2_5_D192_j655_d0_u1428 b3_2_P2_5_D192_j655_d0_u1462 rfl) rfl) rfl) (all_glue _ 1496 102 117 219 (all_glue _ 1496 34 68 102 b3_2_P2_5_D192_j655_d0_u1496 (all_glue _ 1530 34 34 68 b3_2_P2_5_D192_j655_d0_u1530 b3_2_P2_5_D192_j655_d0_u1564 rfl) rfl) (all_glue _ 1598 68 49 117 (all_glue _ 1598 34 34 68 b3_2_P2_5_D192_j655_d0_u1598 b3_2_P2_5_D192_j655_d0_u1632 rfl) (all_glue _ 1666 34 15 49 b3_2_P2_5_D192_j655_d0_u1666 b3_2_P2_5_D192_j655_d0_u1700 rfl) rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D192_j655_d1_u0 : (List.range' 0 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 1 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d1_u34 : (List.range' 34 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 1 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d1_u68 : (List.range' 68 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 1 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d1_u102 : (List.range' 102 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 1 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d1_u136 : (List.range' 136 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 1 51) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j655_d1_u170 : (List.range' 170 34).all (detRowOK b3_2_P2_5_D192_j655P b3_2_P2_5_D192_j655C 1 51) = true := by
  decide +kernel

end DubC2.Atlas
