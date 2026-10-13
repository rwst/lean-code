/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2767.Part63

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2767`, part 64/64 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2767_d30_u57 : (List.range' 57 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 30 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d30_u76 : (List.range' 76 19).all (detRowOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C 30 19) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2767_d30 : (List.range' 30 1).all (detOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 38 57 95 (all_glue _ 0 19 19 38 b3_2_P2_5_D768_j2767_d30_u0 b3_2_P2_5_D768_j2767_d30_u19 rfl) (all_glue _ 38 19 38 57 b3_2_P2_5_D768_j2767_d30_u38 (all_glue _ 57 19 19 38 b3_2_P2_5_D768_j2767_d30_u57 b3_2_P2_5_D768_j2767_d30_u76 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2767_d31 : (List.range' 31 2).all (detOK b3_2_P2_5_D768_j2767P b3_2_P2_5_D768_j2767C) = true := by
  decide +kernel

end DubC2.Atlas
