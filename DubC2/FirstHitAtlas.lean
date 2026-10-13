/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Atlas
import DubC2.FirstHit

/-!
# Effective first-hit bounds for the sixteen atlas cells (T4(a), per cell)

`Gen.first_hit_rank` instantiated at every certificate of `DubC2/Atlas/`: for every `ξ ≠ 0` and
every `N`, a term of `⌊ξ(p/q)ⁿ + ν⌋` divisible by a member of the cell's set occurs at some
`n ≤ γ^(R+1)(N + J + (R+1)(|det| + K(ξ) + 1)) + J + 2`, with `γ = 1 + log_q(p/q)`,
`K(ξ) = Params.kξ` and the certificate's peel depth `J`, det-state count `|det|` and rank depth
`R` (rank of the root det state) read off the certificate by `rfl`:

| cell | `J` | `|det|` | `R` |
|---|---|---|---|
| `b3_2_nu1_2_P2_5` | 6 | 7 | 3 |
| `b7_5_nu1_2_P2_3_5_11` | 21 | 75 | 44 |
| `b3_2_num1_P2_3` | 1 | 1 | 0 |
| `b4_3_num1_P2_3` | 1 | 2 | 1 |
| `b3_2_num1_P2_7` | 3 | 12 | 8 |
| `b6_5_num1_P2_3_5` | 1 | 6 | 5 |
| `b4_3_nu0_P2_3_5` | 4 | 7 | 5 |
| `b5_2_num1_P2_3_5` | 2 | 4 | 3 |
| `b4_3_nu1_2_P2_5` | 2 | 37 | 32 |
| `b5_3_nu1_2_P2_3` | 3 | 7 | 2 |
| `b5_3_nu1_2_P2_5` | 3 | 7 | 2 |
| `b3_2_nu0_P2_5_7_11` | 13 | 53 | 30 |
| `b5_2_nu1_2_P2_3_7_11` | 12 | 133 | 110 |
| `b3_2_nu0_P2_7_11_13` | 28 | 33 | 17 |
| `b3_2_nu0_P3_5_7_11` | 17 | 269 | 215 |
| `b7_5_nu1_2_P2_3_5_13` | 22 | 153 | 98 |

[Oda26] Thm 27 has the vertex count in the exponent instead of `R`.
-/

namespace DubC2.Atlas

open DubC2.Gen

/-- Base 3/2, ν = 1/2, 𝒫 = {2,5} (machine re-check of T1): the effective first hit (`J = 6`, `|det| = 7`, `R = 3`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b3_2_nu1_2_P2_5_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 ((3 : ℝ) / 2)) ^ 4 *
        ((N : ℝ) + 6 + 4 * (7 + b3_2_nu1_2_P2_5P.kξ ξ + 1)) + 6 + 2 ∧
      ∃ ℓ ∈ b3_2_nu1_2_P2_5P.PM ++ b3_2_nu1_2_P2_5P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b3_2_nu1_2_P2_5P.p b3_2_nu1_2_P2_5P.q ξ ((b3_2_nu1_2_P2_5P.a : ℝ) / b3_2_nu1_2_P2_5P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b3_2_nu1_2_P2_5_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b3_2_nu1_2_P2_5C.J = 6 := rfl
  have hS : b3_2_nu1_2_P2_5C.sets.length = 7 := rfl
  have hR : b3_2_nu1_2_P2_5C.depth = 3 := rfl
  have hg : b3_2_nu1_2_P2_5P.gamma = 1 + Real.logb 2 ((3 : ℝ) / 2) := by
    simp [Params.gamma, b3_2_nu1_2_P2_5P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 7/5, ν = 1/2, 𝒫 = {2,3,5,11} ([DN05] Thm 4(iii), machine re-check): the effective first hit (`J = 21`, `|det| = 75`, `R = 44`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b7_5_nu1_2_P2_3_5_11_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 5 ((7 : ℝ) / 5)) ^ 45 *
        ((N : ℝ) + 21 + 45 * (75 + b7_5_nu1_2_P2_3_5_11P.kξ ξ + 1)) + 21 + 2 ∧
      ∃ ℓ ∈ b7_5_nu1_2_P2_3_5_11P.PM ++ b7_5_nu1_2_P2_3_5_11P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b7_5_nu1_2_P2_3_5_11P.p b7_5_nu1_2_P2_3_5_11P.q ξ ((b7_5_nu1_2_P2_3_5_11P.a : ℝ) / b7_5_nu1_2_P2_3_5_11P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b7_5_nu1_2_P2_3_5_11_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b7_5_nu1_2_P2_3_5_11C.J = 21 := rfl
  have hS : b7_5_nu1_2_P2_3_5_11C.sets.length = 75 := rfl
  have hR : b7_5_nu1_2_P2_3_5_11C.depth = 44 := rfl
  have hg : b7_5_nu1_2_P2_3_5_11P.gamma = 1 + Real.logb 5 ((7 : ℝ) / 5) := by
    simp [Params.gamma, b7_5_nu1_2_P2_3_5_11P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 3/2, ν = −1, 𝒫 = {2,3}: the effective first hit (`J = 1`, `|det| = 1`, `R = 0`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b3_2_num1_P2_3_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 ((3 : ℝ) / 2)) ^ 1 *
        ((N : ℝ) + 1 + 1 * (1 + b3_2_num1_P2_3P.kξ ξ + 1)) + 1 + 2 ∧
      ∃ ℓ ∈ b3_2_num1_P2_3P.PM ++ b3_2_num1_P2_3P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b3_2_num1_P2_3P.p b3_2_num1_P2_3P.q ξ ((b3_2_num1_P2_3P.a : ℝ) / b3_2_num1_P2_3P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b3_2_num1_P2_3_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b3_2_num1_P2_3C.J = 1 := rfl
  have hS : b3_2_num1_P2_3C.sets.length = 1 := rfl
  have hR : b3_2_num1_P2_3C.depth = 0 := rfl
  have hg : b3_2_num1_P2_3P.gamma = 1 + Real.logb 2 ((3 : ℝ) / 2) := by
    simp [Params.gamma, b3_2_num1_P2_3P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 4/3, ν = −1, 𝒫 = {2,3}: the effective first hit (`J = 1`, `|det| = 2`, `R = 1`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b4_3_num1_P2_3_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 3 ((4 : ℝ) / 3)) ^ 2 *
        ((N : ℝ) + 1 + 2 * (2 + b4_3_num1_P2_3P.kξ ξ + 1)) + 1 + 2 ∧
      ∃ ℓ ∈ b4_3_num1_P2_3P.PM ++ b4_3_num1_P2_3P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b4_3_num1_P2_3P.p b4_3_num1_P2_3P.q ξ ((b4_3_num1_P2_3P.a : ℝ) / b4_3_num1_P2_3P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b4_3_num1_P2_3_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b4_3_num1_P2_3C.J = 1 := rfl
  have hS : b4_3_num1_P2_3C.sets.length = 2 := rfl
  have hR : b4_3_num1_P2_3C.depth = 1 := rfl
  have hg : b4_3_num1_P2_3P.gamma = 1 + Real.logb 3 ((4 : ℝ) / 3) := by
    simp [Params.gamma, b4_3_num1_P2_3P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 3/2, ν = −1, 𝒫 = {2,7}: the effective first hit (`J = 3`, `|det| = 12`, `R = 8`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b3_2_num1_P2_7_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 ((3 : ℝ) / 2)) ^ 9 *
        ((N : ℝ) + 3 + 9 * (12 + b3_2_num1_P2_7P.kξ ξ + 1)) + 3 + 2 ∧
      ∃ ℓ ∈ b3_2_num1_P2_7P.PM ++ b3_2_num1_P2_7P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b3_2_num1_P2_7P.p b3_2_num1_P2_7P.q ξ ((b3_2_num1_P2_7P.a : ℝ) / b3_2_num1_P2_7P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b3_2_num1_P2_7_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b3_2_num1_P2_7C.J = 3 := rfl
  have hS : b3_2_num1_P2_7C.sets.length = 12 := rfl
  have hR : b3_2_num1_P2_7C.depth = 8 := rfl
  have hg : b3_2_num1_P2_7P.gamma = 1 + Real.logb 2 ((3 : ℝ) / 2) := by
    simp [Params.gamma, b3_2_num1_P2_7P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 6/5, ν = −1, 𝒫 = {2,3,5} ([DN05] Thm 3, [Nov12] Thm 1.4, machine re-check): the effective first hit (`J = 1`, `|det| = 6`, `R = 5`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b6_5_num1_P2_3_5_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 5 ((6 : ℝ) / 5)) ^ 6 *
        ((N : ℝ) + 1 + 6 * (6 + b6_5_num1_P2_3_5P.kξ ξ + 1)) + 1 + 2 ∧
      ∃ ℓ ∈ b6_5_num1_P2_3_5P.PM ++ b6_5_num1_P2_3_5P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b6_5_num1_P2_3_5P.p b6_5_num1_P2_3_5P.q ξ ((b6_5_num1_P2_3_5P.a : ℝ) / b6_5_num1_P2_3_5P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b6_5_num1_P2_3_5_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b6_5_num1_P2_3_5C.J = 1 := rfl
  have hS : b6_5_num1_P2_3_5C.sets.length = 6 := rfl
  have hR : b6_5_num1_P2_3_5C.depth = 5 := rfl
  have hg : b6_5_num1_P2_3_5P.gamma = 1 + Real.logb 5 ((6 : ℝ) / 5) := by
    simp [Params.gamma, b6_5_num1_P2_3_5P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 4/3, floor, 𝒫 = {2,3,5} ([FS67], [DN05] Thm 1, machine re-check): the effective first hit (`J = 4`, `|det| = 7`, `R = 5`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b4_3_nu0_P2_3_5_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 3 ((4 : ℝ) / 3)) ^ 6 *
        ((N : ℝ) + 4 + 6 * (7 + b4_3_nu0_P2_3_5P.kξ ξ + 1)) + 4 + 2 ∧
      ∃ ℓ ∈ b4_3_nu0_P2_3_5P.PM ++ b4_3_nu0_P2_3_5P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b4_3_nu0_P2_3_5P.p b4_3_nu0_P2_3_5P.q ξ ((b4_3_nu0_P2_3_5P.a : ℝ) / b4_3_nu0_P2_3_5P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b4_3_nu0_P2_3_5_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b4_3_nu0_P2_3_5C.J = 4 := rfl
  have hS : b4_3_nu0_P2_3_5C.sets.length = 7 := rfl
  have hR : b4_3_nu0_P2_3_5C.depth = 5 := rfl
  have hg : b4_3_nu0_P2_3_5P.gamma = 1 + Real.logb 3 ((4 : ℝ) / 3) := by
    simp [Params.gamma, b4_3_nu0_P2_3_5P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 5/2, ν = −1, 𝒫 = {2,3,5} ([DN05] Thm 3, [Nov12] Thm 1.4, machine re-check): the effective first hit (`J = 2`, `|det| = 4`, `R = 3`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b5_2_num1_P2_3_5_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 ((5 : ℝ) / 2)) ^ 4 *
        ((N : ℝ) + 2 + 4 * (4 + b5_2_num1_P2_3_5P.kξ ξ + 1)) + 2 + 2 ∧
      ∃ ℓ ∈ b5_2_num1_P2_3_5P.PM ++ b5_2_num1_P2_3_5P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b5_2_num1_P2_3_5P.p b5_2_num1_P2_3_5P.q ξ ((b5_2_num1_P2_3_5P.a : ℝ) / b5_2_num1_P2_3_5P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b5_2_num1_P2_3_5_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b5_2_num1_P2_3_5C.J = 2 := rfl
  have hS : b5_2_num1_P2_3_5C.sets.length = 4 := rfl
  have hR : b5_2_num1_P2_3_5C.depth = 3 := rfl
  have hg : b5_2_num1_P2_3_5P.gamma = 1 + Real.logb 2 ((5 : ℝ) / 2) := by
    simp [Params.gamma, b5_2_num1_P2_3_5P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 4/3, ν = 1/2, 𝒫 = {2,5}: the effective first hit (`J = 2`, `|det| = 37`, `R = 32`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b4_3_nu1_2_P2_5_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 3 ((4 : ℝ) / 3)) ^ 33 *
        ((N : ℝ) + 2 + 33 * (37 + b4_3_nu1_2_P2_5P.kξ ξ + 1)) + 2 + 2 ∧
      ∃ ℓ ∈ b4_3_nu1_2_P2_5P.PM ++ b4_3_nu1_2_P2_5P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b4_3_nu1_2_P2_5P.p b4_3_nu1_2_P2_5P.q ξ ((b4_3_nu1_2_P2_5P.a : ℝ) / b4_3_nu1_2_P2_5P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b4_3_nu1_2_P2_5_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b4_3_nu1_2_P2_5C.J = 2 := rfl
  have hS : b4_3_nu1_2_P2_5C.sets.length = 37 := rfl
  have hR : b4_3_nu1_2_P2_5C.depth = 32 := rfl
  have hg : b4_3_nu1_2_P2_5P.gamma = 1 + Real.logb 3 ((4 : ℝ) / 3) := by
    simp [Params.gamma, b4_3_nu1_2_P2_5P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 5/3, ν = 1/2, 𝒫 = {2,3} ([DN05] Thm 4(ii), machine re-check): the effective first hit (`J = 3`, `|det| = 7`, `R = 2`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b5_3_nu1_2_P2_3_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 3 ((5 : ℝ) / 3)) ^ 3 *
        ((N : ℝ) + 3 + 3 * (7 + b5_3_nu1_2_P2_3P.kξ ξ + 1)) + 3 + 2 ∧
      ∃ ℓ ∈ b5_3_nu1_2_P2_3P.PM ++ b5_3_nu1_2_P2_3P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b5_3_nu1_2_P2_3P.p b5_3_nu1_2_P2_3P.q ξ ((b5_3_nu1_2_P2_3P.a : ℝ) / b5_3_nu1_2_P2_3P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b5_3_nu1_2_P2_3_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b5_3_nu1_2_P2_3C.J = 3 := rfl
  have hS : b5_3_nu1_2_P2_3C.sets.length = 7 := rfl
  have hR : b5_3_nu1_2_P2_3C.depth = 2 := rfl
  have hg : b5_3_nu1_2_P2_3P.gamma = 1 + Real.logb 3 ((5 : ℝ) / 3) := by
    simp [Params.gamma, b5_3_nu1_2_P2_3P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 5/3, ν = 1/2, 𝒫 = {2,5}: the effective first hit (`J = 3`, `|det| = 7`, `R = 2`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b5_3_nu1_2_P2_5_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 3 ((5 : ℝ) / 3)) ^ 3 *
        ((N : ℝ) + 3 + 3 * (7 + b5_3_nu1_2_P2_5P.kξ ξ + 1)) + 3 + 2 ∧
      ∃ ℓ ∈ b5_3_nu1_2_P2_5P.PM ++ b5_3_nu1_2_P2_5P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b5_3_nu1_2_P2_5P.p b5_3_nu1_2_P2_5P.q ξ ((b5_3_nu1_2_P2_5P.a : ℝ) / b5_3_nu1_2_P2_5P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b5_3_nu1_2_P2_5_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b5_3_nu1_2_P2_5C.J = 3 := rfl
  have hS : b5_3_nu1_2_P2_5C.sets.length = 7 := rfl
  have hR : b5_3_nu1_2_P2_5C.depth = 2 := rfl
  have hg : b5_3_nu1_2_P2_5P.gamma = 1 + Real.logb 3 ((5 : ℝ) / 3) := by
    simp [Params.gamma, b5_3_nu1_2_P2_5P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 3/2, floor, 𝒫 = {2,5,7,11} ([FS67], [DN05] Thm 1, machine re-check): the effective first hit (`J = 13`, `|det| = 53`, `R = 30`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b3_2_nu0_P2_5_7_11_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 ((3 : ℝ) / 2)) ^ 31 *
        ((N : ℝ) + 13 + 31 * (53 + b3_2_nu0_P2_5_7_11P.kξ ξ + 1)) + 13 + 2 ∧
      ∃ ℓ ∈ b3_2_nu0_P2_5_7_11P.PM ++ b3_2_nu0_P2_5_7_11P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b3_2_nu0_P2_5_7_11P.p b3_2_nu0_P2_5_7_11P.q ξ ((b3_2_nu0_P2_5_7_11P.a : ℝ) / b3_2_nu0_P2_5_7_11P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b3_2_nu0_P2_5_7_11_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b3_2_nu0_P2_5_7_11C.J = 13 := rfl
  have hS : b3_2_nu0_P2_5_7_11C.sets.length = 53 := rfl
  have hR : b3_2_nu0_P2_5_7_11C.depth = 30 := rfl
  have hg : b3_2_nu0_P2_5_7_11P.gamma = 1 + Real.logb 2 ((3 : ℝ) / 2) := by
    simp [Params.gamma, b3_2_nu0_P2_5_7_11P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 5/2, ν = 1/2, 𝒫 = {2,3,7,11}: the effective first hit (`J = 12`, `|det| = 133`, `R = 110`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b5_2_nu1_2_P2_3_7_11_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 ((5 : ℝ) / 2)) ^ 111 *
        ((N : ℝ) + 12 + 111 * (133 + b5_2_nu1_2_P2_3_7_11P.kξ ξ + 1)) + 12 + 2 ∧
      ∃ ℓ ∈ b5_2_nu1_2_P2_3_7_11P.PM ++ b5_2_nu1_2_P2_3_7_11P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b5_2_nu1_2_P2_3_7_11P.p b5_2_nu1_2_P2_3_7_11P.q ξ ((b5_2_nu1_2_P2_3_7_11P.a : ℝ) / b5_2_nu1_2_P2_3_7_11P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b5_2_nu1_2_P2_3_7_11_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b5_2_nu1_2_P2_3_7_11C.J = 12 := rfl
  have hS : b5_2_nu1_2_P2_3_7_11C.sets.length = 133 := rfl
  have hR : b5_2_nu1_2_P2_3_7_11C.depth = 110 := rfl
  have hg : b5_2_nu1_2_P2_3_7_11P.gamma = 1 + Real.logb 2 ((5 : ℝ) / 2) := by
    simp [Params.gamma, b5_2_nu1_2_P2_3_7_11P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 3/2, floor, 𝒫 = {2,7,11,13}: the effective first hit (`J = 28`, `|det| = 33`, `R = 17`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b3_2_nu0_P2_7_11_13_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 ((3 : ℝ) / 2)) ^ 18 *
        ((N : ℝ) + 28 + 18 * (33 + b3_2_nu0_P2_7_11_13P.kξ ξ + 1)) + 28 + 2 ∧
      ∃ ℓ ∈ b3_2_nu0_P2_7_11_13P.PM ++ b3_2_nu0_P2_7_11_13P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b3_2_nu0_P2_7_11_13P.p b3_2_nu0_P2_7_11_13P.q ξ ((b3_2_nu0_P2_7_11_13P.a : ℝ) / b3_2_nu0_P2_7_11_13P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b3_2_nu0_P2_7_11_13_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b3_2_nu0_P2_7_11_13C.J = 28 := rfl
  have hS : b3_2_nu0_P2_7_11_13C.sets.length = 33 := rfl
  have hR : b3_2_nu0_P2_7_11_13C.depth = 17 := rfl
  have hg : b3_2_nu0_P2_7_11_13P.gamma = 1 + Real.logb 2 ((3 : ℝ) / 2) := by
    simp [Params.gamma, b3_2_nu0_P2_7_11_13P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 3/2, floor, 𝒫 = {3,5,7,11}: the effective first hit (`J = 17`, `|det| = 269`, `R = 215`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b3_2_nu0_P3_5_7_11_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 ((3 : ℝ) / 2)) ^ 216 *
        ((N : ℝ) + 17 + 216 * (269 + b3_2_nu0_P3_5_7_11P.kξ ξ + 1)) + 17 + 2 ∧
      ∃ ℓ ∈ b3_2_nu0_P3_5_7_11P.PM ++ b3_2_nu0_P3_5_7_11P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b3_2_nu0_P3_5_7_11P.p b3_2_nu0_P3_5_7_11P.q ξ ((b3_2_nu0_P3_5_7_11P.a : ℝ) / b3_2_nu0_P3_5_7_11P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b3_2_nu0_P3_5_7_11_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b3_2_nu0_P3_5_7_11C.J = 17 := rfl
  have hS : b3_2_nu0_P3_5_7_11C.sets.length = 269 := by
    set_option maxRecDepth 4000 in rfl
  have hR : b3_2_nu0_P3_5_7_11C.depth = 215 := rfl
  have hg : b3_2_nu0_P3_5_7_11P.gamma = 1 + Real.logb 2 ((3 : ℝ) / 2) := by
    simp [Params.gamma, b3_2_nu0_P3_5_7_11P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

/-- Base 7/5, ν = 1/2, 𝒫 = {2,3,5,13}: the effective first hit (`J = 22`, `|det| = 153`, `R = 98`). -/
@[category research solved, AMS 11 37, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem b7_5_nu1_2_P2_3_5_13_first_hit {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 5 ((7 : ℝ) / 5)) ^ 99 *
        ((N : ℝ) + 22 + 99 * (153 + b7_5_nu1_2_P2_3_5_13P.kξ ξ + 1)) + 22 + 2 ∧
      ∃ ℓ ∈ b7_5_nu1_2_P2_3_5_13P.PM ++ b7_5_nu1_2_P2_3_5_13P.Pq,
        (ℓ : ℤ) ∣ Z32.xInt b7_5_nu1_2_P2_3_5_13P.p b7_5_nu1_2_P2_3_5_13P.q ξ ((b7_5_nu1_2_P2_3_5_13P.a : ℝ) / b7_5_nu1_2_P2_3_5_13P.b) n := by
  obtain ⟨n, hn, hb, hd⟩ := first_hit_rank b7_5_nu1_2_P2_3_5_13_checked hξ N
  refine ⟨n, hn, ?_, hd⟩
  have hJ : b7_5_nu1_2_P2_3_5_13C.J = 22 := rfl
  have hS : b7_5_nu1_2_P2_3_5_13C.sets.length = 153 := rfl
  have hR : b7_5_nu1_2_P2_3_5_13C.depth = 98 := rfl
  have hg : b7_5_nu1_2_P2_3_5_13P.gamma = 1 + Real.logb 5 ((7 : ℝ) / 5) := by
    simp [Params.gamma, b7_5_nu1_2_P2_3_5_13P]
  simp only [firstHitBound, hJ, hS, hR, hg] at hb
  push_cast at hb
  linarith

end DubC2.Atlas
