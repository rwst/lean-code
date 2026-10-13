/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2765.Part125

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2765`, part 126/126 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2765_d35_u91 : (List.range' 91 13).all (detRowOK b3_2_P2_5_D768_j2765P b3_2_P2_5_D768_j2765C 35 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2765_d35_u104 : (List.range' 104 13).all (detRowOK b3_2_P2_5_D768_j2765P b3_2_P2_5_D768_j2765C 35 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2765_d35_u117 : (List.range' 117 3).all (detRowOK b3_2_P2_5_D768_j2765P b3_2_P2_5_D768_j2765C 35 24) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2765_d35 : (List.range' 35 1).all (detOK b3_2_P2_5_D768_j2765P b3_2_P2_5_D768_j2765C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 65 55 120 (all_glue _ 0 26 39 65 (all_glue _ 0 13 13 26 b3_2_P2_5_D768_j2765_d35_u0 b3_2_P2_5_D768_j2765_d35_u13 rfl) (all_glue _ 26 13 26 39 b3_2_P2_5_D768_j2765_d35_u26 (all_glue _ 39 13 13 26 b3_2_P2_5_D768_j2765_d35_u39 b3_2_P2_5_D768_j2765_d35_u52 rfl) rfl) rfl) (all_glue _ 65 26 29 55 (all_glue _ 65 13 13 26 b3_2_P2_5_D768_j2765_d35_u65 b3_2_P2_5_D768_j2765_d35_u78 rfl) (all_glue _ 91 13 16 29 b3_2_P2_5_D768_j2765_d35_u91 (all_glue _ 104 13 3 16 b3_2_P2_5_D768_j2765_d35_u104 b3_2_P2_5_D768_j2765_d35_u117 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2765_d36 : (List.range' 36 6).all (detOK b3_2_P2_5_D768_j2765P b3_2_P2_5_D768_j2765C) = true := by
  decide +kernel

end DubC2.Atlas
