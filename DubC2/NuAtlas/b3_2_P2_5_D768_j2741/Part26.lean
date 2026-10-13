/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2741.Part25

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2741`, part 26/34 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2741_d0_u1830 : (List.range' 1830 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 0 376) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d0_u1860 : (List.range' 1860 20).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 0 376) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 930 950 1880 (all_glue _ 0 450 480 930 (all_glue _ 0 210 240 450 (all_glue _ 0 90 120 210 (all_glue _ 0 30 60 90 b3_2_P2_5_D768_j2741_d0_u0 (all_glue _ 30 30 30 60 b3_2_P2_5_D768_j2741_d0_u30 b3_2_P2_5_D768_j2741_d0_u60 rfl) rfl) (all_glue _ 90 60 60 120 (all_glue _ 90 30 30 60 b3_2_P2_5_D768_j2741_d0_u90 b3_2_P2_5_D768_j2741_d0_u120 rfl) (all_glue _ 150 30 30 60 b3_2_P2_5_D768_j2741_d0_u150 b3_2_P2_5_D768_j2741_d0_u180 rfl) rfl) rfl) (all_glue _ 210 120 120 240 (all_glue _ 210 60 60 120 (all_glue _ 210 30 30 60 b3_2_P2_5_D768_j2741_d0_u210 b3_2_P2_5_D768_j2741_d0_u240 rfl) (all_glue _ 270 30 30 60 b3_2_P2_5_D768_j2741_d0_u270 b3_2_P2_5_D768_j2741_d0_u300 rfl) rfl) (all_glue _ 330 60 60 120 (all_glue _ 330 30 30 60 b3_2_P2_5_D768_j2741_d0_u330 b3_2_P2_5_D768_j2741_d0_u360 rfl) (all_glue _ 390 30 30 60 b3_2_P2_5_D768_j2741_d0_u390 b3_2_P2_5_D768_j2741_d0_u420 rfl) rfl) rfl) rfl) (all_glue _ 450 240 240 480 (all_glue _ 450 120 120 240 (all_glue _ 450 60 60 120 (all_glue _ 450 30 30 60 b3_2_P2_5_D768_j2741_d0_u450 b3_2_P2_5_D768_j2741_d0_u480 rfl) (all_glue _ 510 30 30 60 b3_2_P2_5_D768_j2741_d0_u510 b3_2_P2_5_D768_j2741_d0_u540 rfl) rfl) (all_glue _ 570 60 60 120 (all_glue _ 570 30 30 60 b3_2_P2_5_D768_j2741_d0_u570 b3_2_P2_5_D768_j2741_d0_u600 rfl) (all_glue _ 630 30 30 60 b3_2_P2_5_D768_j2741_d0_u630 b3_2_P2_5_D768_j2741_d0_u660 rfl) rfl) rfl) (all_glue _ 690 120 120 240 (all_glue _ 690 60 60 120 (all_glue _ 690 30 30 60 b3_2_P2_5_D768_j2741_d0_u690 b3_2_P2_5_D768_j2741_d0_u720 rfl) (all_glue _ 750 30 30 60 b3_2_P2_5_D768_j2741_d0_u750 b3_2_P2_5_D768_j2741_d0_u780 rfl) rfl) (all_glue _ 810 60 60 120 (all_glue _ 810 30 30 60 b3_2_P2_5_D768_j2741_d0_u810 b3_2_P2_5_D768_j2741_d0_u840 rfl) (all_glue _ 870 30 30 60 b3_2_P2_5_D768_j2741_d0_u870 b3_2_P2_5_D768_j2741_d0_u900 rfl) rfl) rfl) rfl) rfl) (all_glue _ 930 480 470 950 (all_glue _ 930 240 240 480 (all_glue _ 930 120 120 240 (all_glue _ 930 60 60 120 (all_glue _ 930 30 30 60 b3_2_P2_5_D768_j2741_d0_u930 b3_2_P2_5_D768_j2741_d0_u960 rfl) (all_glue _ 990 30 30 60 b3_2_P2_5_D768_j2741_d0_u990 b3_2_P2_5_D768_j2741_d0_u1020 rfl) rfl) (all_glue _ 1050 60 60 120 (all_glue _ 1050 30 30 60 b3_2_P2_5_D768_j2741_d0_u1050 b3_2_P2_5_D768_j2741_d0_u1080 rfl) (all_glue _ 1110 30 30 60 b3_2_P2_5_D768_j2741_d0_u1110 b3_2_P2_5_D768_j2741_d0_u1140 rfl) rfl) rfl) (all_glue _ 1170 120 120 240 (all_glue _ 1170 60 60 120 (all_glue _ 1170 30 30 60 b3_2_P2_5_D768_j2741_d0_u1170 b3_2_P2_5_D768_j2741_d0_u1200 rfl) (all_glue _ 1230 30 30 60 b3_2_P2_5_D768_j2741_d0_u1230 b3_2_P2_5_D768_j2741_d0_u1260 rfl) rfl) (all_glue _ 1290 60 60 120 (all_glue _ 1290 30 30 60 b3_2_P2_5_D768_j2741_d0_u1290 b3_2_P2_5_D768_j2741_d0_u1320 rfl) (all_glue _ 1350 30 30 60 b3_2_P2_5_D768_j2741_d0_u1350 b3_2_P2_5_D768_j2741_d0_u1380 rfl) rfl) rfl) rfl) (all_glue _ 1410 240 230 470 (all_glue _ 1410 120 120 240 (all_glue _ 1410 60 60 120 (all_glue _ 1410 30 30 60 b3_2_P2_5_D768_j2741_d0_u1410 b3_2_P2_5_D768_j2741_d0_u1440 rfl) (all_glue _ 1470 30 30 60 b3_2_P2_5_D768_j2741_d0_u1470 b3_2_P2_5_D768_j2741_d0_u1500 rfl) rfl) (all_glue _ 1530 60 60 120 (all_glue _ 1530 30 30 60 b3_2_P2_5_D768_j2741_d0_u1530 b3_2_P2_5_D768_j2741_d0_u1560 rfl) (all_glue _ 1590 30 30 60 b3_2_P2_5_D768_j2741_d0_u1590 b3_2_P2_5_D768_j2741_d0_u1620 rfl) rfl) rfl) (all_glue _ 1650 120 110 230 (all_glue _ 1650 60 60 120 (all_glue _ 1650 30 30 60 b3_2_P2_5_D768_j2741_d0_u1650 b3_2_P2_5_D768_j2741_d0_u1680 rfl) (all_glue _ 1710 30 30 60 b3_2_P2_5_D768_j2741_d0_u1710 b3_2_P2_5_D768_j2741_d0_u1740 rfl) rfl) (all_glue _ 1770 60 50 110 (all_glue _ 1770 30 30 60 b3_2_P2_5_D768_j2741_d0_u1770 b3_2_P2_5_D768_j2741_d0_u1800 rfl) (all_glue _ 1830 30 20 50 b3_2_P2_5_D768_j2741_d0_u1830 b3_2_P2_5_D768_j2741_d0_u1860 rfl) rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2741_d1_u0 : (List.range' 0 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 1 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d1_u30 : (List.range' 30 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 1 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d1_u60 : (List.range' 60 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 1 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d1_u90 : (List.range' 90 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 1 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d1_u120 : (List.range' 120 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 1 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d1_u150 : (List.range' 150 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 1 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d1_u180 : (List.range' 180 20).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 1 40) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 90 110 200 (all_glue _ 0 30 60 90 b3_2_P2_5_D768_j2741_d1_u0 (all_glue _ 30 30 30 60 b3_2_P2_5_D768_j2741_d1_u30 b3_2_P2_5_D768_j2741_d1_u60 rfl) rfl) (all_glue _ 90 60 50 110 (all_glue _ 90 30 30 60 b3_2_P2_5_D768_j2741_d1_u90 b3_2_P2_5_D768_j2741_d1_u120 rfl) (all_glue _ 150 30 20 50 b3_2_P2_5_D768_j2741_d1_u150 b3_2_P2_5_D768_j2741_d1_u180 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2741_d2_u0 : (List.range' 0 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 2 368) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d2_u30 : (List.range' 30 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 2 368) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d2_u60 : (List.range' 60 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 2 368) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d2_u90 : (List.range' 90 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 2 368) = true := by
  decide +kernel

end DubC2.Atlas
