/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j850.Part1

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j850`, part 2/6 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j850_r6 : (List.range' 6 6).all (roundOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_r12 : (List.range' 12 2).all (roundOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j850_r14 : (List.range' 14 7).all (roundOK b3_2_P2_5_D384_j850P b3_2_P2_5_D384_j850C) = true := by
  decide +kernel

end DubC2.Atlas
