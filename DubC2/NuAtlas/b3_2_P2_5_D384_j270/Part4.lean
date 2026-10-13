/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j270.Part3

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j270`, part 4/5 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j270_r53 : (List.range' 53 40).all (roundOK b3_2_P2_5_D384_j270P b3_2_P2_5_D384_j270C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j270_r93 : (List.range' 93 19).all (roundOK b3_2_P2_5_D384_j270P b3_2_P2_5_D384_j270C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j270_d0 : (List.range' 0 4).all (detOK b3_2_P2_5_D384_j270P b3_2_P2_5_D384_j270C) = true := by
  decide +kernel

end DubC2.Atlas
