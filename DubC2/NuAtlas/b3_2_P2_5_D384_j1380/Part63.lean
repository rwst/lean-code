/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j1380.Part62

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j1380`, part 63/63 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j1380_d48_u19 : (List.range' 19 19).all (detRowOK b3_2_P2_5_D384_j1380P b3_2_P2_5_D384_j1380C 48 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1380_d48_u38 : (List.range' 38 19).all (detRowOK b3_2_P2_5_D384_j1380P b3_2_P2_5_D384_j1380C 48 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1380_d48_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D384_j1380P b3_2_P2_5_D384_j1380C 48 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1380_d48_u76 : (List.range' 76 9).all (detRowOK b3_2_P2_5_D384_j1380P b3_2_P2_5_D384_j1380C 48 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j1380_d48 : (List.range' 48 1).all (detOK b3_2_P2_5_D384_j1380P b3_2_P2_5_D384_j1380C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 38 47 85 (all_glue _ 0 19 19 38 b3_2_P2_5_D384_j1380_d48_u0 b3_2_P2_5_D384_j1380_d48_u19 rfl) (all_glue _ 38 19 28 47 b3_2_P2_5_D384_j1380_d48_u38 (all_glue _ 57 19 9 28 b3_2_P2_5_D384_j1380_d48_u57 b3_2_P2_5_D384_j1380_d48_u76 rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j1380_d49 : (List.range' 49 2).all (detOK b3_2_P2_5_D384_j1380P b3_2_P2_5_D384_j1380C) = true := by
  decide +kernel

end DubC2.Atlas
