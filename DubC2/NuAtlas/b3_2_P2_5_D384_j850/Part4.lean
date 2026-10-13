/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j850.Part3

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j850`, part 4/6 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j850_r54 : (List.range' 54 32).all (roundOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_r86 : (List.range' 86 26).all (roundOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_d0_u0 : (List.range' 0 111).all (detRowOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C 0 99) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_d0_u111 : (List.range' 111 111).all (detRowOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C 0 99) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_d0_u222 : (List.range' 222 111).all (detRowOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C 0 99) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_d0_u333 : (List.range' 333 111).all (detRowOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C 0 99) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_d0_u444 : (List.range' 444 51).all (detRowOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C 0 99) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 222 273 495 (all_glue _ 0 111 111 222 b3_2_P2_5_D384_j850_d0_u0 b3_2_P2_5_D384_j850_d0_u111 rfl) (all_glue _ 222 111 162 273 b3_2_P2_5_D384_j850_d0_u222 (all_glue _ 333 111 51 162 b3_2_P2_5_D384_j850_d0_u333 b3_2_P2_5_D384_j850_d0_u444 rfl) rfl) rfl))

end DubC2.Atlas
