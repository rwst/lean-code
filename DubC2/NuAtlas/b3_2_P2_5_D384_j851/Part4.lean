/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j851.Part3

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j851`, part 4/6 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j851_r54 : (List.range' 54 32).all (roundOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j851_r86 : (List.range' 86 2).all (roundOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j851_d0_u0 : (List.range' 0 103).all (detRowOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C 0 105) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j851_d0_u103 : (List.range' 103 103).all (detRowOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C 0 105) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j851_d0_u206 : (List.range' 206 103).all (detRowOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C 0 105) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j851_d0_u309 : (List.range' 309 103).all (detRowOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C 0 105) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j851_d0_u412 : (List.range' 412 103).all (detRowOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C 0 105) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j851_d0_u515 : (List.range' 515 10).all (detRowOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C 0 105) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j851_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 309 216 525 (all_glue _ 0 103 206 309 b3_2_P2_5_D384_j851_d0_u0 (all_glue _ 103 103 103 206 b3_2_P2_5_D384_j851_d0_u103 b3_2_P2_5_D384_j851_d0_u206 rfl) rfl) (all_glue _ 309 103 113 216 b3_2_P2_5_D384_j851_d0_u309 (all_glue _ 412 103 10 113 b3_2_P2_5_D384_j851_d0_u412 b3_2_P2_5_D384_j851_d0_u515 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j851_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D384_j851P b3_2_P2_5_D384_j851C) = true := by
  decide +kernel

end DubC2.Atlas
