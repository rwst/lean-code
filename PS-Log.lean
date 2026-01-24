/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

@[expose] public section

namespace PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

open Nat

/-- Power series for log(1 + X). -/
def log : PowerSeries A :=
  mk fun n => if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / n)

variable {A}

@[simp]
theorem coeff_log (n : ℕ) :
    coeff n (log A) = if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / n) :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_log : constantCoeff (log A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_log]
  simp

variable (A) in
@[simp]
theorem map_log {A' : Type*} [CommRing A'] [Algebra ℚ A'] (f : A →+* A') :
    map f (log A) = log A' := by
  ext n
  simp only [coeff_map, coeff_log]
  split_ifs <;> simp

/-- The derivative of `log(1+X)` is `1/(1+X) = 1 - X + X² - X³ + ⋯`. -/
theorem deriv_log : d⁄dX A (log A) = mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n) := by
  ext n
  rw [coeff_derivative, coeff_log, coeff_mk]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have : (↑n + 1 : A) = algebraMap ℚ A (n + 1) := by simp
  rw [this, ← map_mul]
  congr 1
  have h1 : (-1 : ℚ) ^ (n + 1 + 1) = (-1) ^ n := by ring
  field_simp
  rw [h1]
  push_cast
  ring

/-! ## Substitution -/

variable (A) in
theorem HasSubst.log : HasSubst (log A) :=
  HasSubst.of_constantCoeff_zero' constantCoeff_log

variable (A) in
theorem HasSubst.exp_sub_one : HasSubst (exp A - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [constantCoeff_exp])

variable (A) in
/-- `logOf f` is `log(f)` when `constantCoeff f = 1`, defined as `log(1+X)` substituted at `f-1`. -/
noncomputable def logOf (f : A⟦X⟧) : A⟦X⟧ :=
  (log A).subst (f - 1)

-- Helper: A power series g with g' * (1+X) = g and constantCoeff g = c equals c * (1 + X)
private theorem eq_of_deriv_mul_one_add_X_eq_self [IsAddTorsionFree A]
    {g : A⟦X⟧} (hderiv : d⁄dX A g * (1 + X) = g) (hconst : constantCoeff g = c) :
    g = c • (1 + X) := by
  -- Prove by showing all coefficients match
  ext n
  induction n with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff, hconst, map_add, map_one,
      constantCoeff_X, add_zero, smul_eq_mul, mul_one]
  | succ n ih =>
    -- From g' * (1+X) = g, extract coefficient relations
    have hcoeff : ∀ m, coeff m (d⁄dX A g * (1 + X)) = coeff m g := fun m => by rw [hderiv]
    -- coeff n of (g' * (1+X)) = coeff n g' + coeff (n-1) g' (when n ≥ 1)
    -- This gives: (n+1) * a_{n+1} + n * a_n = a_n for coeff n, so (n+1) * a_{n+1} = (1-n) * a_n
    sorry

variable (A) in
/-- exp(log(1+X)) = 1 + X -/
theorem exp_subst_log : (exp A).subst (log A) = 1 + X := by
  sorry

variable (A) in
/-- log(exp(X)) = X (via substituting exp-1 into log) -/
theorem log_subst_exp_sub_one : (log A).subst (exp A - 1) = X := by
  sorry

variable (A) in
/-- logOf(exp A) = X -/
theorem logOf_exp : logOf A (exp A) = X :=
  log_subst_exp_sub_one A

theorem constantCoeff_logOf (f : A⟦X⟧) (hf : constantCoeff f = 1) :
    constantCoeff (logOf A f) = 0 := by
  unfold logOf
  have h : constantCoeff (f - 1) = 0 := by simp only [map_sub, hf, map_one, sub_self]
  exact constantCoeff_subst_eq_zero h (log A) constantCoeff_log

variable (A) in
@[simp]
theorem logOf_one_add_X : logOf A (1 + X) = log A := by
  simp only [logOf, add_sub_cancel_left]
  rw [← map_algebraMap_eq_subst_X (S := A), Algebra.algebraMap_self, map_id]
  rfl

end PowerSeries

end
