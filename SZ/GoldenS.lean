/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime

/-!
# The golden mean lies in `𝒮`

[Dub06EO] Theorem 2(ii) at `d = 2`, `r = 1`: `φ = (1+√5)/2` is a root of `x² - x - 1`, so
*no* nonzero `ξ` makes every `⌊ξ φⁿ⌋` even.

The mechanism is the exact mirror of `SZ/PellDesign.lean`.  Because `φ² = φ + 1`, the
orbit satisfies `ξ φ^{n+2} = ξ φ^{n+1} + ξ φⁿ`, so the *carry*
`c_n = x_{n+1} + x_n - x_{n+2} = y_{n+2} - y_{n+1} - y_n` is an integer in `(-2, 1)`,
hence `0` or `-1`.  If every `x_n` is even then every `c_n` is even, so `c_n = 0` and the
**fractional parts themselves obey the Fibonacci recurrence** `y_{n+2} = y_{n+1} + y_n`.
A non-negative Fibonacci-like sequence either vanishes identically or doubles every two
steps, and `y_n < 1` forbids doubling — so all `y_n = 0`, `ξ` and `ξ φ` are integers, and
`φ` is rational.

Equivalently, in the language of `SZ/Trace.lean`: mod `2` the recurrence at `(a,b) = (1,1)`
is Fibonacci, of period `3`, and the alternating pattern `(1,0)^∞` is not one of its
orbits — `(x+1)² ∤ x² + x + 1` in `𝔽₂[x]`.  For `1 + √2` the coefficient `a = 2` is even
and the pattern *is* admissible.  **The method knows where it must fail.**

## Main result

* `SZ.golden_mem_S` — `(1+√5)/2 ∈ 𝒮`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336, Theorem 2(ii).
-/

namespace SZ

open Real

/-- The golden mean. -/
noncomputable def golden : ℝ := (1 + Real.sqrt 5) / 2

private theorem sqrt_five_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private theorem sqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

private theorem two_lt_sqrt_five : 2 < Real.sqrt 5 := by
  nlinarith [sqrt_five_sq, sqrt_five_pos]

@[category API, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem one_lt_golden : 1 < golden := by
  rw [golden]; linarith [two_lt_sqrt_five]

@[category API, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem golden_sq : golden ^ 2 = golden + 1 := by
  rw [golden]; nlinarith [sqrt_five_sq]

@[category API, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem irrational_sqrt_five : Irrational (Real.sqrt 5) := by
  have h := (by norm_num : Nat.Prime 5).irrational_sqrt
  simpa using h

/-- **[Dub06EO] Theorem 2(ii), `d = 2`.**  The golden mean lies in `𝒮`: for *every* nonzero
real `ξ` the sequence `⌊ξ φⁿ⌋` contains odd terms. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem golden_mem_S : golden ∈ S := by
  refine ⟨one_lt_golden, ?_⟩
  rintro ⟨-, ξ, hξ, heven⟩
  -- the orbit and its fractional parts
  set y : ℕ → ℝ := fun k => Int.fract (ξ * golden ^ (k + 1)) with hydef
  have hy0 : ∀ k, 0 ≤ y k := fun k => Int.fract_nonneg _
  have hy1 : ∀ k, y k < 1 := fun k => Int.fract_lt_one _
  have hx : ∀ k : ℕ, Even ⌊ξ * golden ^ (k + 1)⌋ := fun k => heven (k + 1) (by omega)
  -- the orbit obeys the Fibonacci recurrence
  have hpow : ∀ k : ℕ, golden ^ (k + 3) = golden ^ (k + 2) + golden ^ (k + 1) := by
    intro k
    have h2 : golden ^ (k + 3) = golden ^ (k + 1) * golden ^ 2 := by ring
    rw [h2, golden_sq]; ring
  have horb : ∀ k : ℕ, ξ * golden ^ (k + 3)
      = ξ * golden ^ (k + 2) + ξ * golden ^ (k + 1) := by
    intro k; rw [hpow k]; ring
  -- hence so do the fractional parts: the carry is an even integer in `(-2,1)`
  have hcarry : ∀ k : ℕ, y (k + 2) = y (k + 1) + y k := by
    intro k
    set c : ℤ := ⌊ξ * golden ^ (k + 2)⌋ + ⌊ξ * golden ^ (k + 1)⌋
      - ⌊ξ * golden ^ (k + 3)⌋ with hcdef
    have hreal : (c : ℝ) = y (k + 2) - y (k + 1) - y k := by
      simp only [hcdef, hydef, Int.fract]
      push_cast
      have := horb k
      have e1 : k + 2 + 1 = k + 3 := by omega
      have e2 : k + 1 + 1 = k + 2 := by omega
      rw [e1, e2]
      linarith
    have hlt : c < 1 := by
      have : (c : ℝ) < 1 := by
        rw [hreal]; linarith [hy0 (k + 1), hy0 k, hy1 (k + 2)]
      exact_mod_cast this
    have hgt : (-2 : ℤ) < c := by
      have : (-2 : ℝ) < (c : ℝ) := by
        rw [hreal]; linarith [hy1 (k + 1), hy1 k, hy0 (k + 2)]
      exact_mod_cast this
    have hev : Even c := by
      simp only [hcdef]
      exact ((hx (k + 1)).add (hx k)).sub (hx (k + 2))
    obtain ⟨m, hm⟩ := hev
    have hc0 : c = 0 := by omega
    have : (0 : ℝ) = y (k + 2) - y (k + 1) - y k := by rw [← hreal, hc0]; norm_num
    linarith
  -- a non-negative Fibonacci-like sequence bounded by `1` must vanish
  have hstep2 : ∀ m : ℕ, 2 * y (m + 1) ≤ y (m + 3) := by
    intro m
    have h1 : y (m + 3) = y (m + 2) + y (m + 1) := by
      have := hcarry (m + 1)
      have e1 : m + 1 + 2 = m + 3 := by omega
      have e2 : m + 1 + 1 = m + 2 := by omega
      rw [e1, e2] at this; exact this
    have h2 : y (m + 2) = y (m + 1) + y m := hcarry m
    linarith [hy0 m]
  have hgrow : ∀ i : ℕ, ∀ j : ℕ, 2 ^ j * y (i + 1) ≤ y (2 * j + i + 1) := by
    intro i j
    induction j with
    | zero => simp
    | succ j ih =>
      have hs := hstep2 (2 * j + i)
      have e1 : 2 * j + i + 1 = 2 * j + i + 1 := rfl
      have e2 : 2 * j + i + 3 = 2 * (j + 1) + i + 1 := by omega
      rw [e2] at hs
      calc (2 : ℝ) ^ (j + 1) * y (i + 1) = 2 * (2 ^ j * y (i + 1)) := by ring
        _ ≤ 2 * y (2 * j + i + 1) := by linarith
        _ ≤ y (2 * (j + 1) + i + 1) := hs
  have hvanish : ∀ i : ℕ, y (i + 1) = 0 := by
    intro i
    by_contra hne
    have hpos : 0 < y (i + 1) := lt_of_le_of_ne (hy0 _) (Ne.symm hne)
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (1 / 2 : ℝ) ^ j < y (i + 1) :=
      exists_pow_lt_of_lt_one hpos (by norm_num)
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have hone : (1 : ℝ) < 2 ^ j * y (i + 1) := by
      have e : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [div_pow]; norm_num
      rw [e] at hj
      have := mul_lt_mul_of_pos_left hj h2j
      rwa [mul_one_div, div_self (ne_of_gt h2j)] at this
    linarith [hgrow i j, hy1 (2 * j + i + 1)]
  -- so `ξ φ` and `ξ φ²` are integers, and `φ` is rational
  -- `y 0` is recovered from the recurrence, so `ξ φ` and `ξ φ²` are both integers
  have hy1z : y 1 = 0 := by simpa using hvanish 0
  have hy2z : y 2 = 0 := by simpa using hvanish 1
  have hy00 : y 0 = 0 := by
    have h0 : y 2 = y 1 + y 0 := by simpa using hcarry 0
    linarith
  have hz0 : ξ * golden = (⌊ξ * golden⌋ : ℝ) := by
    have h : Int.fract (ξ * golden ^ 1) = 0 := by simpa [hydef] using hy00
    rw [Int.fract, pow_one] at h
    linarith
  have hz1 : ξ * golden ^ 2 = (⌊ξ * golden ^ 2⌋ : ℝ) := by
    have h : Int.fract (ξ * golden ^ 2) = 0 := by simpa [hydef] using hy1z
    rw [Int.fract] at h
    linarith
  set p : ℤ := ⌊ξ * golden⌋ with hp
  set q : ℤ := ⌊ξ * golden ^ 2⌋ with hq
  have hsplit : ξ * golden ^ 2 = ξ * golden + ξ := by rw [golden_sq]; ring
  have hxi : ξ = ((q - p : ℤ) : ℝ) := by push_cast; linarith
  have hd : ((q - p : ℤ) : ℝ) ≠ 0 := by rw [← hxi]; exact hξ
  have hgold : golden = (p : ℝ) / ((q - p : ℤ) : ℝ) := by
    rw [eq_div_iff hd, ← hxi]
    linarith
  refine irrational_sqrt_five ⟨2 * (p : ℚ) / ((q - p : ℤ) : ℚ) - 1, ?_⟩
  have hgg : Real.sqrt 5 = 2 * golden - 1 := by rw [golden]; ring
  rw [hgg, hgold]
  push_cast
  ring

end SZ
