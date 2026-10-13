/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas.b7_5_nu1_2_P2_3_5_13.Main

/-!
# The `(p/q, ν, 𝒫)` divisor-set atlas of plan-dubC2 (M2)

Every entry is a machine-checked theorem of the form: for every real `ξ ≠ 0`, infinitely many
of `⌊ξ(p/q)ⁿ + ν⌋` are divisible by a member of `𝒫`.  The entries form one linear import
chain (see `DubC2/gencert.py`), so importing the last one imports them all:

* `DubC2.Atlas.b3_2_nu1_2_P2_5` — Base 3/2, ν = 1/2, 𝒫 = {2,5} (machine re-check of T1)
* `DubC2.Atlas.b7_5_nu1_2_P2_3_5_11` — Base 7/5, ν = 1/2, 𝒫 = {2,3,5,11} ([DN05] Thm 4(iii), machine re-check)
* `DubC2.Atlas.b3_2_num1_P2_3` — Base 3/2, ν = −1, 𝒫 = {2,3}
* `DubC2.Atlas.b4_3_num1_P2_3` — Base 4/3, ν = −1, 𝒫 = {2,3}
* `DubC2.Atlas.b3_2_num1_P2_7` — Base 3/2, ν = −1, 𝒫 = {2,7}
* `DubC2.Atlas.b6_5_num1_P2_3_5` — Base 6/5, ν = −1, 𝒫 = {2,3,5} ([DN05] Thm 3, [Nov12] Thm 1.4, machine re-check)
* `DubC2.Atlas.b4_3_nu0_P2_3_5` — Base 4/3, floor, 𝒫 = {2,3,5} ([FS67], [DN05] Thm 1, machine re-check)
* `DubC2.Atlas.b5_2_num1_P2_3_5` — Base 5/2, ν = −1, 𝒫 = {2,3,5} ([DN05] Thm 3, [Nov12] Thm 1.4, machine re-check)
* `DubC2.Atlas.b4_3_nu1_2_P2_5` — Base 4/3, ν = 1/2, 𝒫 = {2,5}
* `DubC2.Atlas.b5_3_nu1_2_P2_3` — Base 5/3, ν = 1/2, 𝒫 = {2,3} ([DN05] Thm 4(ii), machine re-check)
* `DubC2.Atlas.b5_3_nu1_2_P2_5` — Base 5/3, ν = 1/2, 𝒫 = {2,5}
* `DubC2.Atlas.b3_2_nu0_P2_5_7_11` — Base 3/2, floor, 𝒫 = {2,5,7,11} ([FS67], [DN05] Thm 1, machine re-check)
* `DubC2.Atlas.b5_2_nu1_2_P2_3_7_11` — Base 5/2, ν = 1/2, 𝒫 = {2,3,7,11}
* `DubC2.Atlas.b3_2_nu0_P2_7_11_13` — Base 3/2, floor, 𝒫 = {2,7,11,13}
* `DubC2.Atlas.b3_2_nu0_P3_5_7_11` — Base 3/2, floor, 𝒫 = {3,5,7,11}
* `DubC2.Atlas.b7_5_nu1_2_P2_3_5_13` — Base 7/5, ν = 1/2, 𝒫 = {2,3,5,13}
-/
