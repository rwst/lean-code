/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D384_j2074.Part19

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D384_j2074`, part 20/30 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D384_j2074_d1_u40 : (List.range' 40 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1_u60 : (List.range' 60 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1_u80 : (List.range' 80 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1_u100 : (List.range' 100 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1_u120 : (List.range' 120 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1_u140 : (List.range' 140 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1_u160 : (List.range' 160 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1_u180 : (List.range' 180 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1_u200 : (List.range' 200 10).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 1 42) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d1 : (List.range' 1 1).all (detOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 100 110 210 (all_glue _ 0 40 60 100 (all_glue _ 0 20 20 40 b3_2_P2_5_D384_j2074_d1_u0 b3_2_P2_5_D384_j2074_d1_u20 rfl) (all_glue _ 40 20 40 60 b3_2_P2_5_D384_j2074_d1_u40 (all_glue _ 60 20 20 40 b3_2_P2_5_D384_j2074_d1_u60 b3_2_P2_5_D384_j2074_d1_u80 rfl) rfl) rfl) (all_glue _ 100 60 50 110 (all_glue _ 100 20 40 60 b3_2_P2_5_D384_j2074_d1_u100 (all_glue _ 120 20 20 40 b3_2_P2_5_D384_j2074_d1_u120 b3_2_P2_5_D384_j2074_d1_u140 rfl) rfl) (all_glue _ 160 20 30 50 b3_2_P2_5_D384_j2074_d1_u160 (all_glue _ 180 20 10 30 b3_2_P2_5_D384_j2074_d1_u180 b3_2_P2_5_D384_j2074_d1_u200 rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D384_j2074_d2_u0 : (List.range' 0 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 2 77) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d2_u20 : (List.range' 20 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 2 77) = true := by
  decide +kernel

theorem b3_2_P2_5_D384_j2074_d2_u40 : (List.range' 40 20).all (detRowOK b3_2_P2_5_D384_j2074P b3_2_P2_5_D384_j2074C 2 77) = true := by
  decide +kernel

end DubC2.Atlas
