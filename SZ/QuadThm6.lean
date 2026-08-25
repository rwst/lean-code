/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `1 + √3 ∈ 𝒵`: the confinement cell, made explicit

The one quadratic Pisot cell that the trace-parity design of `SZ/PellDesign.lean` cannot
reach, and the last piece of the classification in `SZ/Classification.lean`.

`α = 1 + √3` has minimal polynomial `x² - 2x - 2`, so `a = 2` is even but `b = 2` is
**even too**: mod `2` the recurrence degenerates to `T_{n+2} ≡ 0`, the whole trace is
eventually even, and neither sign of `ξ'` can produce even floors.  Equivalently
`(x+1)² ∤ x² + 1 · x + 0` — the lattice criterion fails.  [Dub06EO] covers this `α` by
Theorem 1(iv) instead, `P_α(1) = -3 ≤ -3`, quoting the Dubickas–Zaimi confinement of
[DubA06]: `ξ = 1/(P'_α(α)(α-1))` has `{ξ αⁿ} → 1/|P_α(1)| = 1/3 < 1/2`.

At this `α` that construction is completely explicit, and needs no limit at all.  With
`P'_α(α)(α-1) = 2√3 · √3 = 6` the Dubickas–Zaimi multiplier is `ξ = 1/6`; in the even
integral-part normalisation (`ξ ↦ 2ξ`) it is **`ξ = 1/3`**.  The trace
`S_n = αⁿ + ᾱⁿ` satisfies `S_{n+2} = 2S_{n+1} + 2S_n` from `S₀ = S₁ = 2`, hence

> `S_n ≡ 2 (mod 6)` for every `n`,

and `ᾱ = 1 - √3 ∈ (-1,0)` gives `(2 - ᾱⁿ)/3 ∈ [1/3, 1)`.  Writing `S_n = 6m + 2`,

> `αⁿ/3 = 2m + (2 - ᾱⁿ)/3`,  so  `⌊αⁿ/3⌋ = 2m`  — even, for every `n ≥ 0`.

## Main results

* `SZ.strace_emod` — `S_n ≡ 2 (mod 6)`.
* `SZ.floor_oneAddSqrtThree` — `3 ⌊αⁿ/3⌋ = S_n - 2`.
* `SZ.oneAddSqrtThree_mem_MahlerZ` — `1 + √3 ∈ 𝒵`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336, Theorem 1(iv).
* [DubA06] A. Dubickas, *Arithmetical properties of linear recurrent sequences*, Archivum
  Mathematicum **42** (2006) — the `ξ = 1/(P'(α)(α-1))` confinement.
-/

namespace SZ

open Real

private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

private theorem one_lt_sqrt_three : 1 < Real.sqrt 3 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]

private theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]

/-- `1 + √3` and `1 - √3` are the two roots of `x² = 2x + 2`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem sqrtThree_pair : Pair (1 + Real.sqrt 3) (1 - Real.sqrt 3) 2 2 where
  one_lt := by linarith [sqrt_three_pos]
  absLt := by
    rw [abs_lt]
    constructor <;> [linarith [sqrt_three_lt_two]; linarith [one_lt_sqrt_three]]
  sum := by push_cast; ring
  prod := by push_cast; nlinarith [sqrt_three_sq]

/-- **The trace is `≡ 2` modulo `6`.**  `S_{n+2} = 2S_{n+1} + 2S_n` with `S₀ = S₁ = 2`
propagates `2 · 2 + 2 · 2 = 8 ≡ 2`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem strace_emod (n : ℕ) : rec2 2 2 2 2 n % 6 = 2 := by
  induction n using SZ.twoStep with
  | h0 => decide
  | h1 => decide
  | hs n ih1 ih2 => rw [rec2_add_two]; omega

/-- The trace identity: `(1+√3)ⁿ + (1-√3)ⁿ = S_n`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem strace_real (n : ℕ) :
    (1 + Real.sqrt 3) ^ n + (1 - Real.sqrt 3) ^ n = (rec2 2 2 2 2 n : ℝ) := by
  have h := rec2_real (A := 2) (B := 2) (t₀ := 2) (t₁ := 2) (u := (1 : ℝ)) (v := (1 : ℝ))
    sqrtThree_pair.sq_alpha sqrtThree_pair.sq_beta (by norm_num) (by push_cast; ring) n
  simpa using h

private theorem conj_pow_lt (n : ℕ) : (1 - Real.sqrt 3) ^ n ≤ 1 := by
  have h := abs_le.mp (sqrtThree_pair.abs_pow_le n)
  exact h.2

private theorem neg_one_lt_conj_pow (n : ℕ) : -1 < (1 - Real.sqrt 3) ^ n := by
  cases n with
  | zero => norm_num
  | succ k =>
    have h1 : |(1 - Real.sqrt 3) ^ (k + 1)| = |1 - Real.sqrt 3| ^ (k + 1) := abs_pow _ _
    have h2 : |1 - Real.sqrt 3| ^ (k + 1) < 1 :=
      pow_lt_one₀ (abs_nonneg _) sqrtThree_pair.absLt (Nat.succ_ne_zero k)
    have h3 : |(1 - Real.sqrt 3) ^ (k + 1)| < 1 := by rw [h1]; exact h2
    linarith [(abs_lt.mp h3).1]

/-- **The exact orbit at `ξ = 1/3`.**  `3 ⌊(1+√3)ⁿ/3⌋ = S_n - 2` for every `n ≥ 0`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem floor_oneAddSqrtThree (n : ℕ) :
    3 * ⌊(1 / 3 : ℝ) * (1 + Real.sqrt 3) ^ n⌋ = rec2 2 2 2 2 n - 2 := by
  obtain ⟨m, hm⟩ : (6 : ℤ) ∣ (rec2 2 2 2 2 n - 2) := by
    have := strace_emod n; omega
  have hfl : ⌊(1 / 3 : ℝ) * (1 + Real.sqrt 3) ^ n⌋ = 2 * m := by
    have hval : (1 / 3 : ℝ) * (1 + Real.sqrt 3) ^ n
        = (2 * m : ℤ) + (2 - (1 - Real.sqrt 3) ^ n) / 3 := by
      have h := strace_real n
      have hc : ((rec2 2 2 2 2 n : ℤ) : ℝ) = 6 * (m : ℝ) + 2 := by
        have : (rec2 2 2 2 2 n : ℤ) = 6 * m + 2 := by omega
        rw [this]; push_cast; ring
      push_cast
      linarith [h, hc]
    rw [Int.floor_eq_iff, hval]
    have h1 := conj_pow_lt n
    have h2 := neg_one_lt_conj_pow n
    push_cast
    constructor <;> linarith
  rw [hfl]; omega

/-- **[Dub06EO] Theorem 1(iv) at `α = 1 + √3`.**  Every `⌊(1+√3)ⁿ/3⌋` is even, so
`1 + √3 ∈ 𝒵`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem oneAddSqrtThree_mem_MahlerZ : (1 + Real.sqrt 3) ∈ MahlerZ := by
  refine ⟨sqrtThree_pair.one_lt, 1 / 3, by norm_num, fun n _ => ?_⟩
  obtain ⟨m, hm⟩ : (6 : ℤ) ∣ (rec2 2 2 2 2 n - 2) := by
    have := strace_emod n; omega
  have := floor_oneAddSqrtThree n
  exact ⟨m, by omega⟩

end SZ
