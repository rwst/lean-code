/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2609.Part15

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2609`, part 16/16 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2609_d0_u333 : (List.range' 333 111).all (detRowOK b3_2_P2_5_D768_j2609P b3_2_P2_5_D768_j2609C 0 97) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2609_d0_u444 : (List.range' 444 41).all (detRowOK b3_2_P2_5_D768_j2609P b3_2_P2_5_D768_j2609C 0 97) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2609_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D768_j2609P b3_2_P2_5_D768_j2609C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 222 263 485 (all_glue _ 0 111 111 222 b3_2_P2_5_D768_j2609_d0_u0 b3_2_P2_5_D768_j2609_d0_u111 rfl) (all_glue _ 222 111 152 263 b3_2_P2_5_D768_j2609_d0_u222 (all_glue _ 333 111 41 152 b3_2_P2_5_D768_j2609_d0_u333 b3_2_P2_5_D768_j2609_d0_u444 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2609_d1 : (List.range' 1 3).all (detOK b3_2_P2_5_D768_j2609P b3_2_P2_5_D768_j2609C) = true := by
  decide +kernel

end DubC2.Atlas
