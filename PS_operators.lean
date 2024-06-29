import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Fib.Basic

set_option autoImplicit false

namespace PowerSeries
open Nat Finset PowerSeries
macro "R" : term => `(ℚ)

noncomputable def inv_one_minus (f : R⟦X⟧) : R⟦X⟧ :=
  if (constantCoeff R f = 1) then 0 else
    mk fun j => coeff R j (f ^ j)

noncomputable def exp' (f : R⟦X⟧) : R⟦X⟧ :=
  if (constantCoeff R f ≠ 0) then 0 else
    mk fun j => coeff R j (rescale (j ! : R)⁻¹ (f ^ j))

noncomputable def log (f : R⟦X⟧) : R⟦X⟧ :=
  if (constantCoeff R f ≠ 1) then 0 else
    mk fun j => coeff R j (rescale (((-1) ^ j : R) * ((j + 1) : R)⁻¹)
      (((mk fun p => coeff R (p + 1) f) * X) ^ (j + 1)))

/-- Shows that `inv_one_minus X` and `invUnitsSub 1` generate the same series. -/
lemma inv_one_minus_eq_invUnitsSub : inv_one_minus X = invUnitsSub 1 := by
  ext n
  unfold inv_one_minus
  simp

/-- Shows that `1 / (1 - X)^2` generates the series `1 + 2*X + 3*X^2 + 4*X^3 + ...` -/
lemma inv_one_minus_eq_n : (inv_one_minus X) ^ 2 = (mk fun j => (j + 1 : R)) := by
  ext n
  unfold inv_one_minus
  simp only [constantCoeff_X, zero_ne_one, ↓reduceIte, coeff_X_pow_self, coeff_mk]
  rw [pow_two, coeff_mul]
  simp

/-- Shows that $e^{af} * e^{bf} = e^{(a + b)f}$ -/
@[simp]
theorem exp_mul_exp_eq_exp_add' (a b : R) (f : R⟦X⟧) (hC : constantCoeff R f = 0) :
    rescale a (exp' f) * rescale b (exp' f) = rescale (a + b) (exp' f) := by
  ext n
  unfold exp'
  simp only [ne_eq, map_pow, ite_not, hC, ↓reduceIte, coeff_mk, coeff_rescale]
  simp only [coeff_mul, exp, rescale, coeff_mk, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.coe_mk,
    factorial, Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul]
  apply sum_congr rfl
  rintro x hx
  sorry

/-- Shows that $e^{f} * e^{-f} = 1$ -/
@[simp]
theorem exp_mul_exp_neg_eq_one' (f : R⟦X⟧) (hC : constantCoeff R f = 0) :
    exp' f * evalNegHom (exp' f) = 1 := by
  sorry

/-- Shows that the derivative of the `exp` operator equals itself. -/
theorem deriv_exp_self (f : R⟦X⟧) (hC : constantCoeff R f = 0) :
    d⁄dX R (exp' f) = exp' f := by
  ext n
  unfold exp'
  simp only [ne_eq, map_pow, hC, ↓reduceIte, ite_not, coeff_mk]
  sorry

theorem deriv_log_eq_deriv_mul_inv (f : R⟦X⟧) (hC : constantCoeff R f = 0) :
    d⁄dX R (-log (1 - f)) = (d⁄dX R f) * inv_one_minus f := by
  ext n
  unfold log inv_one_minus
  simp only [map_sub, map_one, ne_eq, sub_eq_self, coeff_one, add_eq_zero,
             one_ne_zero, and_false, hC, ↓reduceIte, zero_sub, map_pow, map_mul,
             rescale_X, map_neg, ite_not, mul_ite, mul_zero]
  sorry

@[simp]
theorem log_exp_cancel (f : R⟦X⟧) (hC : constantCoeff R f = 0) : log (exp' f) = f := by
  ext n
  unfold log exp'
  simp only [ne_eq, map_pow, hC, ↓reduceIte, ite_not, map_mul, rescale_X, map_neg,
    map_one]
  sorry

@[simp]
theorem exp_log_cancel (f : R⟦X⟧) (hC : constantCoeff R f = 1) : exp' (log f) = f := by
  ext n
  unfold log exp'
  simp only [ne_eq, map_pow, map_mul, rescale_X, map_neg, map_one, ite_not,
    ite_pow, coeff_rescale, hC, ↓reduceIte, inv_pow]
  sorry

/-- Shows that `X / (1 - X - X^2)` generates the series with Fibonacci coefficients. -/
lemma inv_one_minus_eq_fib : X * inv_one_minus (X + X ^ 2) = (mk fun j => (fib j : R)) := by
  ext n
  unfold inv_one_minus fib
  simp only [map_add, constantCoeff_X, map_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, zero_ne_one, ↓reduceIte, coeff_mk]
  sorry
