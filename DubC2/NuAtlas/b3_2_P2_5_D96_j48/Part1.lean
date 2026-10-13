/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D96_j48.Data

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D96_j48`, part 1/1 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D96_j48_r0 : (List.range' 0 3).all (roundOK b3_2_P2_5_D96_j48P b3_2_P2_5_D96_j48C) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j48_r3 : (List.range' 3 8).all (roundOK b3_2_P2_5_D96_j48P b3_2_P2_5_D96_j48C) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j48_r11 : (List.range' 11 21).all (roundOK b3_2_P2_5_D96_j48P b3_2_P2_5_D96_j48C) = true := by
  decide +kernel

theorem b3_2_P2_5_D96_j48_d0 : (List.range' 0 7).all (detOK b3_2_P2_5_D96_j48P b3_2_P2_5_D96_j48C) = true := by
  decide +kernel

end DubC2.Atlas
