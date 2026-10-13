/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuAtlas.b3_2_P2_5_D768_j4145.Part20

/-! Certificate pieces for `DubC2.NuAtlas.b3_2_P2_5_D768_j4145`, part 21/21 — generated; do not edit. -/

namespace DubC2.Atlas

open DubC2.Gen

theorem b3_2_P2_5_D768_j4145_d0_u1188 : (List.range' 1188 44).all (detRowOK b3_2_P2_5_D768_j4145P b3_2_P2_5_D768_j4145C 0 261) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4145_d0_u1232 : (List.range' 1232 44).all (detRowOK b3_2_P2_5_D768_j4145P b3_2_P2_5_D768_j4145C 0 261) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4145_d0_u1276 : (List.range' 1276 29).all (detRowOK b3_2_P2_5_D768_j4145P b3_2_P2_5_D768_j4145C 0 261) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4145_d0 : (List.range' 0 1).all (detOK b3_2_P2_5_D768_j4145P b3_2_P2_5_D768_j4145C) = true :=
  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (all_glue _ 0 660 645 1305 (all_glue _ 0 308 352 660 (all_glue _ 0 132 176 308 (all_glue _ 0 44 88 132 b3_2_P2_5_D768_j4145_d0_u0 (all_glue _ 44 44 44 88 b3_2_P2_5_D768_j4145_d0_u44 b3_2_P2_5_D768_j4145_d0_u88 rfl) rfl) (all_glue _ 132 88 88 176 (all_glue _ 132 44 44 88 b3_2_P2_5_D768_j4145_d0_u132 b3_2_P2_5_D768_j4145_d0_u176 rfl) (all_glue _ 220 44 44 88 b3_2_P2_5_D768_j4145_d0_u220 b3_2_P2_5_D768_j4145_d0_u264 rfl) rfl) rfl) (all_glue _ 308 176 176 352 (all_glue _ 308 88 88 176 (all_glue _ 308 44 44 88 b3_2_P2_5_D768_j4145_d0_u308 b3_2_P2_5_D768_j4145_d0_u352 rfl) (all_glue _ 396 44 44 88 b3_2_P2_5_D768_j4145_d0_u396 b3_2_P2_5_D768_j4145_d0_u440 rfl) rfl) (all_glue _ 484 88 88 176 (all_glue _ 484 44 44 88 b3_2_P2_5_D768_j4145_d0_u484 b3_2_P2_5_D768_j4145_d0_u528 rfl) (all_glue _ 572 44 44 88 b3_2_P2_5_D768_j4145_d0_u572 b3_2_P2_5_D768_j4145_d0_u616 rfl) rfl) rfl) rfl) (all_glue _ 660 308 337 645 (all_glue _ 660 132 176 308 (all_glue _ 660 44 88 132 b3_2_P2_5_D768_j4145_d0_u660 (all_glue _ 704 44 44 88 b3_2_P2_5_D768_j4145_d0_u704 b3_2_P2_5_D768_j4145_d0_u748 rfl) rfl) (all_glue _ 792 88 88 176 (all_glue _ 792 44 44 88 b3_2_P2_5_D768_j4145_d0_u792 b3_2_P2_5_D768_j4145_d0_u836 rfl) (all_glue _ 880 44 44 88 b3_2_P2_5_D768_j4145_d0_u880 b3_2_P2_5_D768_j4145_d0_u924 rfl) rfl) rfl) (all_glue _ 968 176 161 337 (all_glue _ 968 88 88 176 (all_glue _ 968 44 44 88 b3_2_P2_5_D768_j4145_d0_u968 b3_2_P2_5_D768_j4145_d0_u1012 rfl) (all_glue _ 1056 44 44 88 b3_2_P2_5_D768_j4145_d0_u1056 b3_2_P2_5_D768_j4145_d0_u1100 rfl) rfl) (all_glue _ 1144 88 73 161 (all_glue _ 1144 44 44 88 b3_2_P2_5_D768_j4145_d0_u1144 b3_2_P2_5_D768_j4145_d0_u1188 rfl) (all_glue _ 1232 44 29 73 b3_2_P2_5_D768_j4145_d0_u1232 b3_2_P2_5_D768_j4145_d0_u1276 rfl) rfl) rfl) rfl) rfl))

theorem b3_2_P2_5_D768_j4145_d1 : (List.range' 1 3).all (detOK b3_2_P2_5_D768_j4145P b3_2_P2_5_D768_j4145C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4145_d4 : (List.range' 4 5).all (detOK b3_2_P2_5_D768_j4145P b3_2_P2_5_D768_j4145C) = true := by
  decide +kernel

theorem b3_2_P2_5_D768_j4145_d9 : (List.range' 9 3).all (detOK b3_2_P2_5_D768_j4145P b3_2_P2_5_D768_j4145C) = true := by
  decide +kernel

end DubC2.Atlas
