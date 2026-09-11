/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Int.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Rational algebraic integers are rational integers

`ℤ` is integrally closed in its fraction field `ℚ`, so an element of `ℚ` that is integral over
`ℤ` is the image of an integer.  Transported along the (injective) embedding `ℚ → ℝ` this says:
a *real* algebraic integer that happens to be rational is an ordinary integer.

The consequence used downstream is the negative one: **no algebraic integer is a
half-odd-integer** (`IsIntegral.ne_intCast_add_half`), because `k + 1/2` is rational with
denominator two.  That single fact is the whole arithmetic of the non-vanishing argument for
Erdős products `∏ ((1-p) + p e(x_j))` whose ladder `(x_j)` consists of algebraic integers: such
a product has no zero factor, since `(1-p) + p e(x) = 0` forces `p = 1/2` and `x ∈ 1/2 + ℤ`.

## Main results

* `exists_int_of_isIntegral_ratCast` — a rational algebraic integer is a rational integer;
* `IsIntegral.ne_intCast_add_half` — an algebraic integer is never `k + 1/2`;
* `IsIntegral.cos_pi_ne_zero` — hence `cos (π x) ≠ 0` for every real algebraic integer `x`.
-/

/-- **A rational algebraic integer is a rational integer.**  `ℤ` is integrally closed in `ℚ`
(`IsIntegrallyClosed.isIntegral_iff`), and `ℚ → ℝ` is injective, so integrality over `ℤ` descends
from `ℝ` to `ℚ` (`IsIntegral.tower_bot`). -/
theorem exists_int_of_isIntegral_ratCast {q : ℚ} (h : IsIntegral ℤ ((q : ℝ))) : ∃ n : ℤ, q = n := by
  have h1 : IsIntegral ℤ q := by
    refine IsIntegral.tower_bot (A := ℚ) (B := ℝ) ?_ ?_
    · exact fun a b hab => by exact_mod_cast hab
    · simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact ⟨n, by rw [← hn]; simp⟩

/-- **No algebraic integer is a half-odd-integer.**  If `x = k + 1/2` were integral over `ℤ`,
then `x` would be a rational algebraic integer, hence an integer `n` with `2n = 2k + 1`. -/
theorem IsIntegral.ne_intCast_add_half {x : ℝ} (hx : IsIntegral ℤ x) (k : ℤ) :
    x ≠ (k : ℝ) + 1 / 2 := by
  intro hxk
  have hI : IsIntegral ℤ (((((2 * k + 1 : ℤ) : ℚ) / 2 : ℚ) : ℝ)) := by
    have h : ((((2 * k + 1 : ℤ) : ℚ) / 2 : ℚ) : ℝ) = x := by rw [hxk]; push_cast; ring
    rw [h]; exact hx
  obtain ⟨n, hn⟩ := exists_int_of_isIntegral_ratCast hI
  have h2 : (2 * n : ℤ) = 2 * k + 1 := by
    have h3 : ((2 * n : ℤ) : ℚ) = ((2 * k + 1 : ℤ) : ℚ) := by
      push_cast; push_cast at hn; linarith [hn]
    exact_mod_cast h3
  omega

/-- `cos (π x) ≠ 0` for every real algebraic integer `x`: the zeros of `cos (π ·)` are exactly
the half-odd-integers, and `IsIntegral.ne_intCast_add_half` excludes those. -/
theorem IsIntegral.cos_pi_ne_zero {x : ℝ} (hx : IsIntegral ℤ x) : Real.cos (Real.pi * x) ≠ 0 := by
  rw [Ne, Real.cos_eq_zero_iff]
  rintro ⟨n, hn⟩
  have hpi := Real.pi_pos
  have hx2 : x = (n : ℝ) + 1 / 2 := by
    have h : Real.pi * x = Real.pi * ((n : ℝ) + 1 / 2) := by rw [hn]; ring
    exact mul_left_cancel₀ (ne_of_gt hpi) h
  exact hx.ne_intCast_add_half n hx2
