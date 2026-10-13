/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j2074.Part27

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j2074`, part 28/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j2074_d19_u40 : (List.range' 40 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 19 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d19_u60 : (List.range' 60 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 19 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d19_u80 : (List.range' 80 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 19 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d19_u100 : (List.range' 100 5).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 19 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d19 : (List.range' 19 1).all (detOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 60 45 105 (all_glue _ 0 20 40 60 b3_2_P2_5_D384_j2074_d19_u0 (all_glue _ 20 20 20 40 b3_2_P2_5_D384_j2074_d19_u20 b3_2_P2_5_D384_j2074_d19_u40 rfl) rfl) (all_glue _ 60 20 25 45 b3_2_P2_5_D384_j2074_d19_u60 (all_glue _ 80 20 5 25 b3_2_P2_5_D384_j2074_d19_u80 b3_2_P2_5_D384_j2074_d19_u100 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j2074_d20 : (List.range' 20 4).all (detOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d24 : (List.range' 24 1).all (detOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d25_u0 : (List.range' 0 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 25 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d25_u20 : (List.range' 20 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 25 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d25_u40 : (List.range' 40 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 25 21) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d25_u60 : (List.range' 60 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 25 21) = true := by
  decide +kernel

end DubC2.Atlas
