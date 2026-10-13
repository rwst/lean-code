/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2741.Part32

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2741`, part 33/34 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2741_d5_u150 : (List.range' 150 30).all (detRowOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C 5 36) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d5 : (List.range' 5 1).all (detOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 90 90 180 (all_glue _ 0 30 60 90 b3_2_P2_5_D768_j2741_d5_u0 (all_glue _ 30 30 30 60 b3_2_P2_5_D768_j2741_d5_u30 b3_2_P2_5_D768_j2741_d5_u60 rfl) rfl) (all_glue _ 90 30 60 90 b3_2_P2_5_D768_j2741_d5_u90 (all_glue _ 120 30 30 60 b3_2_P2_5_D768_j2741_d5_u120 b3_2_P2_5_D768_j2741_d5_u150 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2741_d6 : (List.range' 6 1).all (detOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d7 : (List.range' 7 2).all (detOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d9 : (List.range' 9 1).all (detOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2741_d10 : (List.range' 10 2).all (detOK b3_2_P2_5_D768_j2741P b3_2_P2_5_D768_j2741C) = true := by
  decide +kernel

end DubC2.Atlas
