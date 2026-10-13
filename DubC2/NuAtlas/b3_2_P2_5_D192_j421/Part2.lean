/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D192_j421.Part1

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D192_j421`, part 2/2 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D192_j421_r11 : (List.range' 11 11).all (roundOK b3_2_P2_5_D192_j421P b3_2_P2_5_D192_j421C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j421_r22 : (List.range' 22 36).all (roundOK b3_2_P2_5_D192_j421P b3_2_P2_5_D192_j421C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j421_r58 : (List.range' 58 38).all (roundOK b3_2_P2_5_D192_j421P b3_2_P2_5_D192_j421C) = true := by
  decide +kernel

theorem b3_2_P2_5_D192_j421_d0 : (List.range' 0 5).all (detOK b3_2_P2_5_D192_j421P b3_2_P2_5_D192_j421C) = true := by
  decide +kernel

end DubC2.Atlas
