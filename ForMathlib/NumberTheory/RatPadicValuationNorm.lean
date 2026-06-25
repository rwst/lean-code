/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers

@[expose] public section
/-!
# The `p`-adic valuation and the `p`-adic norm on `ℚ` share a unit ball

The `ℤᵐ⁰`-valued `p`-adic valuation `Rat.padicValuation p` and the real-valued `p`-adic norm
`padicNorm p` cut out the same closed unit ball of `ℚ`: both `Rat.padicValuation p x ≤ 1` and
`(padicNorm p x : ℝ) ≤ 1` are equivalent to `0 ≤ padicValRat p x`.

## Main statements

* `Rat.padicValuation_le_one_iff_padicNorm`: `Rat.padicValuation p x ≤ 1 ↔ (padicNorm p x : ℝ) ≤ 1`.
-/

namespace Rat

/-- **The `p`-adic valuation and the `p`-adic norm of a rational determine the same unit ball.**
Both `Rat.padicValuation p x ≤ 1` and `(padicNorm p x : ℝ) ≤ 1` say `0 ≤ padicValRat p x`. -/
theorem padicValuation_le_one_iff_padicNorm (p : ℕ) [Fact p.Prime] (x : ℚ) :
    Rat.padicValuation p x ≤ 1 ↔ (padicNorm p x : ℝ) ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Rat.padicValuation]
    simp only [Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hx]
    rw [padicNorm.eq_zpow_of_nonzero hx,
        show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from (WithZero.exp_zero).symm,
        WithZero.exp_le_exp]
    push_cast
    rw [zpow_le_one_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt : (1 : ℝ) < p)]

end Rat
