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

theorem HasSubst.log : HasSubst (log A) :=
  HasSubst.of_constantCoeff_zero' constantCoeff_log

theorem HasSubst.exp_sub_one : HasSubst (exp A - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [constantCoeff_exp])

/-- `logOf f` is `log(f)` when `constantCoeff f = 1`, defined as `log(1+X)` substituted at `f-1`. -/
noncomputable def logOf (f : A⟦X⟧) : A⟦X⟧ :=
  (log A).subst (f - 1)

-- Helper: A power series g with g' * (1+X) = g and constantCoeff g = c equals c * (1 + X)
omit [Algebra ℚ A] in
private theorem eq_of_deriv_mul_one_add_X_eq_self [IsAddTorsionFree A]
    {g : A⟦X⟧} (hderiv : d⁄dX A g * (1 + X) = g) (hconst : constantCoeff g = c) :
    g = c • (1 + X) := by
  -- From g' * (1+X) = g, comparing coeff n gives: (n+1) * a_{n+1} + n * a_n = a_n
  -- So (n+1) * a_{n+1} = (1-n) * a_n
  -- This determines: a_0 = c (given), a_1 = c, a_n = 0 for n ≥ 2
  have hcoeff : ∀ n, coeff n (d⁄dX A g * (1 + X)) = coeff n g := fun n => by rw [hderiv]
  -- Recurrence: (n+2) * a_{n+2} = -n * a_{n+1}
  have hrec : ∀ n : ℕ, (↑(n + 2) : A) * coeff (n + 2) g = -↑n * coeff (n + 1) g := fun n => by
    have h := hcoeff (n + 1)
    rw [mul_add, mul_one, map_add, coeff_succ_mul_X, coeff_derivative, coeff_derivative] at h
    simp only [show n + 1 + 1 = n + 2 from rfl] at h
    calc (↑(n + 2) : A) * coeff (n + 2) g
        = coeff (n + 2) g * (↑(n + 1) + 1) := by push_cast; ring
      _ = coeff (n + 1) g - coeff (n + 1) g * (↑n + 1) := by linear_combination h
      _ = -↑n * coeff (n + 1) g := by ring
  -- First: coeff 1 g = c (from hcoeff at 0)
  have h1 : coeff 1 g = c := by
    have h := hcoeff 0
    rw [mul_add, mul_one, map_add, coeff_zero_mul_X, add_zero, coeff_derivative] at h
    simp only [Nat.cast_zero, zero_add, mul_one] at h
    rw [← hconst, ← coeff_zero_eq_constantCoeff, h]
  -- Second: coeff n g = 0 for n ≥ 2 (by strong induction using hrec)
  have h2 : ∀ n : ℕ, coeff (n + 2) g = 0 := by
    intro n
    induction n with
    | zero =>
      -- coeff 2 g = 0 from hrec 0: 2 * a_2 = -0 * a_1 = 0
      have h := hrec 0
      simp only [Nat.cast_zero, neg_zero, zero_mul] at h
      -- h: ↑2 * coeff 2 g = 0, rewrite as 2 • coeff 2 g = 0
      rw [← nsmul_eq_mul] at h
      exact (nsmul_eq_zero_iff_right (by omega : (2 : ℕ) ≠ 0)).mp h
    | succ m ih =>
      -- coeff (m+3) g = 0 from hrec (m+1): (m+3) * a_{m+3} = -(m+1) * a_{m+2}
      -- By ih, a_{m+2} = 0, so (m+3) * a_{m+3} = 0
      have h := hrec (m + 1)
      simp only [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at h
      rw [ih, mul_zero] at h
      -- h: ↑(m+3) * coeff (m+3) g = 0
      rw [← nsmul_eq_mul] at h
      -- Goal: coeff (m + 1 + 2) g = 0, which is coeff (m + 3) g = 0
      exact (nsmul_eq_zero_iff_right (by omega : (m + 3 : ℕ) ≠ 0)).mp h
  -- Now prove coefficient by coefficient
  ext n
  match n with
  | 0 =>
    simp only [coeff_zero_eq_constantCoeff, hconst, LinearMap.map_smul, smul_eq_mul,
      map_add, map_one, constantCoeff_X, add_zero, mul_one]
  | 1 =>
    -- Goal: coeff 1 g = coeff 1 (c • (1 + X))
    -- LHS = c (by h1)
    -- RHS = c * coeff 1 (1 + X) = c * (0 + 1) = c
    rw [h1, LinearMap.map_smul, smul_eq_mul, map_add, coeff_one, coeff_X]
    simp
  | n + 2 =>
    -- Goal: coeff (n+2) g = coeff (n+2) (c • (1 + X))
    -- LHS = 0 (by h2)
    -- RHS = c * coeff (n+2) (1 + X) = c * 0 = 0
    rw [h2 n, LinearMap.map_smul, smul_eq_mul, map_add, coeff_one, coeff_X]
    simp

/-- Chain rule for formal power series substitution:
    d/dX (f.subst g) = (f'.subst g) * g'
    where f' denotes the derivative of f.

    This is the formal power series analogue of the calculus chain rule
    (f ∘ g)' = (f' ∘ g) · g'. -/
theorem derivative_subst {f g : A⟦X⟧} (hg0 : g.constantCoeff = 0) :
    d⁄dX A (f.subst g) = (d⁄dX A f).subst g * d⁄dX A g := by
    sorry

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
