/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2610.Part19

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2610`, part 20/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2610_d0_u1517 : (List.range' 1517 37).all (detRowOK b3_2_P2_5_D768_j2610P b3_2_P2_5_D768_j2610C 0 313) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2610_d0_u1554 : (List.range' 1554 11).all (detRowOK b3_2_P2_5_D768_j2610P b3_2_P2_5_D768_j2610C 0 313) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2610_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D768_j2610P b3_2_P2_5_D768_j2610C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 777 788 1565 (all_glue _ 0 370 407 777 (all_glue _ 0 185 185 370 (all_glue _ 0 74 111 185 (all_glue _ 0 37 37 74 b3_2_P2_5_D768_j2610_d0_u0 b3_2_P2_5_D768_j2610_d0_u37 rfl) (all_glue _ 74 37 74 111 b3_2_P2_5_D768_j2610_d0_u74 (all_glue _ 111 37 37 74 b3_2_P2_5_D768_j2610_d0_u111 b3_2_P2_5_D768_j2610_d0_u148 rfl) rfl) rfl) (all_glue _ 185 74 111 185 (all_glue _ 185 37 37 74 b3_2_P2_5_D768_j2610_d0_u185 b3_2_P2_5_D768_j2610_d0_u222 rfl) (all_glue _ 259 37 74 111 b3_2_P2_5_D768_j2610_d0_u259 (all_glue _ 296 37 37 74 b3_2_P2_5_D768_j2610_d0_u296 b3_2_P2_5_D768_j2610_d0_u333 rfl) rfl) rfl) rfl) (all_glue _ 370 185 222 407 (all_glue _ 370 74 111 185 (all_glue _ 370 37 37 74 b3_2_P2_5_D768_j2610_d0_u370 b3_2_P2_5_D768_j2610_d0_u407 rfl) (all_glue _ 444 37 74 111 b3_2_P2_5_D768_j2610_d0_u444 (all_glue _ 481 37 37 74 b3_2_P2_5_D768_j2610_d0_u481 b3_2_P2_5_D768_j2610_d0_u518 rfl) rfl) rfl) (all_glue _ 555 111 111 222 (all_glue _ 555 37 74 111 b3_2_P2_5_D768_j2610_d0_u555 (all_glue _ 592 37 37 74 b3_2_P2_5_D768_j2610_d0_u592 b3_2_P2_5_D768_j2610_d0_u629 rfl) rfl) (all_glue _ 666 37 74 111 b3_2_P2_5_D768_j2610_d0_u666 (all_glue _ 703 37 37 74 b3_2_P2_5_D768_j2610_d0_u703 b3_2_P2_5_D768_j2610_d0_u740 rfl) rfl) rfl) rfl) rfl) (all_glue _ 777 407 381 788 (all_glue _ 777 185 222 407 (all_glue _ 777 74 111 185 (all_glue _ 777 37 37 74 b3_2_P2_5_D768_j2610_d0_u777 b3_2_P2_5_D768_j2610_d0_u814 rfl) (all_glue _ 851 37 74 111 b3_2_P2_5_D768_j2610_d0_u851 (all_glue _ 888 37 37 74 b3_2_P2_5_D768_j2610_d0_u888 b3_2_P2_5_D768_j2610_d0_u925 rfl) rfl) rfl) (all_glue _ 962 111 111 222 (all_glue _ 962 37 74 111 b3_2_P2_5_D768_j2610_d0_u962 (all_glue _ 999 37 37 74 b3_2_P2_5_D768_j2610_d0_u999 b3_2_P2_5_D768_j2610_d0_u1036 rfl) rfl) (all_glue _ 1073 37 74 111 b3_2_P2_5_D768_j2610_d0_u1073 (all_glue _ 1110 37 37 74 b3_2_P2_5_D768_j2610_d0_u1110 b3_2_P2_5_D768_j2610_d0_u1147 rfl) rfl) rfl) rfl) (all_glue _ 1184 185 196 381 (all_glue _ 1184 74 111 185 (all_glue _ 1184 37 37 74 b3_2_P2_5_D768_j2610_d0_u1184 b3_2_P2_5_D768_j2610_d0_u1221 rfl) (all_glue _ 1258 37 74 111 b3_2_P2_5_D768_j2610_d0_u1258 (all_glue _ 1295 37 37 74 b3_2_P2_5_D768_j2610_d0_u1295 b3_2_P2_5_D768_j2610_d0_u1332 rfl) rfl) rfl) (all_glue _ 1369 111 85 196 (all_glue _ 1369 37 74 111 b3_2_P2_5_D768_j2610_d0_u1369 (all_glue _ 1406 37 37 74 b3_2_P2_5_D768_j2610_d0_u1406 b3_2_P2_5_D768_j2610_d0_u1443 rfl) rfl) (all_glue _ 1480 37 48 85 b3_2_P2_5_D768_j2610_d0_u1480 (all_glue _ 1517 37 11 48 b3_2_P2_5_D768_j2610_d0_u1517 b3_2_P2_5_D768_j2610_d0_u1554 rfl) rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2610_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D768_j2610P b3_2_P2_5_D768_j2610C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2610_d2 : (List.range' 2 2).all (detOK b3_2_P2_5_D768_j2610P b3_2_P2_5_D768_j2610C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2610_d4 : (List.range' 4 2).all (detOK b3_2_P2_5_D768_j2610P b3_2_P2_5_D768_j2610C) = true := by
  decide +kernel

end DubC2.Atlas
