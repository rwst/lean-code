/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j2692.Part73

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j2692`, part 74/80 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j2692_d18_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 18 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d18_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 18 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d18_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 18 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d18_u80 : (List.range' 80 5).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 18 17) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d18 : (List.range' 18 1).all (detOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 48 37 85 (all_glue _ 0 16 32 48 b3_2_P2_5_D768_j2692_d18_u0 (all_glue _ 16 16 16 32 b3_2_P2_5_D768_j2692_d18_u16 b3_2_P2_5_D768_j2692_d18_u32 rfl) rfl) (all_glue _ 48 16 21 37 b3_2_P2_5_D768_j2692_d18_u48 (all_glue _ 64 16 5 21 b3_2_P2_5_D768_j2692_d18_u64 b3_2_P2_5_D768_j2692_d18_u80 rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j2692_d19 : (List.range' 19 1).all (detOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d20_u0 : (List.range' 0 16).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 20 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d20_u16 : (List.range' 16 16).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 20 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d20_u32 : (List.range' 32 16).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 20 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d20_u48 : (List.range' 48 16).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 20 27) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j2692_d20_u64 : (List.range' 64 16).all (detRowOK b3_2_P2_5_D768_j2692P b3_2_P2_5_D768_j2692C 20 27) = true := by
  decide +kernel

end DubC2.Atlas
