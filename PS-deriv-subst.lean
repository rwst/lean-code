/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Algebra.Polynomial.Derivation

@[expose] public section

namespace PowerSeries

variable (A : Type*) [CommRing A]

open Nat

/-- The derivative of g^n equals n * g^(n-1) * g'.
    This is the power rule for formal power series, proved by induction. -/
theorem derivative_pow (g : A⟦X⟧) (n : ℕ) :
    d⁄dX A (g ^ n) = n * g ^ (n - 1) * d⁄dX A g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, (derivative A).leibniz, ih, smul_eq_mul, add_tsub_cancel_right]
    rcases n with _ | m
    · simp
    · simp only [add_tsub_cancel_right, pow_succ]; push_cast; ring

/-- Chain rule for monomials: d/dX(X^n.subst g) = (d/dX X^n).subst g * d/dX g.
    Since X^n.subst g = g^n and d/dX(X^n) = n * X^(n-1), this reduces to
    showing d/dX(g^n) = n * g^(n-1) * d/dX g, which is `derivative_pow`. -/
theorem derivative_subst_X_pow {g : A⟦X⟧} (hg : HasSubst g) (n : ℕ) :
    d⁄dX A ((X : A⟦X⟧) ^ n |>.subst g) = (d⁄dX A ((X : A⟦X⟧) ^ n)).subst g * d⁄dX A g := by
  simp only [subst_pow hg, subst_X hg, derivative_pow, derivative_X, mul_one,
    subst_mul hg, ← coe_substAlgHom hg, map_natCast]

/-- Chain rule for polynomials viewed as power series. -/
theorem derivative_subst_coe (p : Polynomial A) {g : A⟦X⟧} (hg : HasSubst g) :
    d⁄dX A ((p : A⟦X⟧).subst g) = (d⁄dX A (p : A⟦X⟧)).subst g * d⁄dX A g := by
  rw [subst_coe hg, derivative_coe, subst_coe hg]
  rw [Derivation.comp_aeval_eq (a := g) (derivative A) p, smul_eq_mul]

/-- Chain rule for formal power series substitution:
    d/dX (f.subst g) = (f'.subst g) * g'
    where f' denotes the derivative of f.

    This is the formal power series analogue of the calculus chain rule
    (f ∘ g)' = (f' ∘ g) · g'. -/
theorem derivative_subst {f g : A⟦X⟧} (hg0 : g.constantCoeff = 0) :
    d⁄dX A (f.subst g) = (d⁄dX A f).subst g * d⁄dX A g := by
  have hg : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  ext n
  have key : ∀ m, coeff m (f.subst g) = coeff m ((↑(trunc (m + 1) f) : A⟦X⟧).subst g) := fun m => by
    rw [coeff_subst' hg, coeff_subst' hg]
    apply finsum_congr
    intro d
    by_cases hd : d ≤ m
    · rw [coeff_coe_trunc_of_lt (Nat.lt_succ_of_le hd)]
    · push_neg at hd
      have hord : m < (g ^ d).order :=
        (le_order_pow_of_constantCoeff_eq_zero d hg0).trans_lt' (by exact_mod_cast hd)
      rw [coeff_of_lt_order _ hord]
      simp
  rw [coeff_derivative, key (n + 1), ← coeff_derivative]
  conv_lhs => rw [derivative_subst_coe (A := A) (trunc (n + 2) f) hg]
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  have hi : i ≤ n := by simp only [Finset.mem_antidiagonal] at hij; omega
  congr 1
  rw [coeff_subst' hg, coeff_subst' hg]
  apply finsum_congr
  intro d
  by_cases hd : d ≤ i
  · congr 1
    rw [coeff_derivative, coeff_derivative, coeff_coe_trunc_of_lt]
    omega
  · push_neg at hd
    have hord : i < (g ^ d).order :=
      (le_order_pow_of_constantCoeff_eq_zero d hg0).trans_lt' (by exact_mod_cast hd)
    rw [coeff_of_lt_order _ hord]
    simp
