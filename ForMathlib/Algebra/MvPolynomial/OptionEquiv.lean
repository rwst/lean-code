/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Degrees

@[expose] public section

/-!
# `MvPolynomial (Option σ) R ≃ MvPolynomial σ R[X]`: coefficients, degrees, evaluation

Mathlib's `MvPolynomial.optionEquivRight R σ` is the algebra isomorphism that reads the
distinguished variable `X none` as the polynomial variable of the coefficient ring:

`MvPolynomial (Option σ) R ≃ₐ[R] MvPolynomial σ R[X]`.

It comes with the three defining equations (`optionEquivRight_X_none`, `optionEquivRight_X_some`,
`optionEquivRight_C`) and nothing else.  Its left-handed twin `optionEquivLeft`, by contrast, has
a full coefficient and degree API (`optionEquivLeft_coeff_coeff`, `support_optionEquivLeft`,
`natDegree_optionEquivLeft`, …).  This file supplies the missing right-handed half:

* `MvPolynomial.optionEquivRight_monomial` — the image of a monomial, the analogue of
  `optionEquivLeft_monomial`;
* `MvPolynomial.coeff_coeff_optionEquivRight`, `MvPolynomial.coeff_optionEquivRight_symm` — the
  coefficient dictionary, in both directions: a coefficient of `Q : MvPolynomial (Option σ) R` at
  `μ` is the coefficient at `μ none` of the coefficient at `μ.some` of its image;
* `MvPolynomial.degreeOf_some_optionEquivRight_symm_le`,
  `MvPolynomial.degreeOf_none_optionEquivRight_symm_le` — the two degree bounds that follow: the
  degree in `X (some s)` is at most the degree of `P` in `X s`, and the degree in `X none` is at
  most any bound for the degrees of the coefficients of `P`;
* `MvPolynomial.eval_optionEquivRight_symm` — evaluating in `Option σ` variables is evaluating
  the coefficients at the value of the `none` variable.

The degree bounds are the point: they are what turns a bidegree bound «degree `≤ u` in each `Y`,
coefficients of degree `≤ v` in `z`» for `P : MvPolynomial σ R[X]` into the per-variable degree
bounds that `Height.logHeight₁_eval_le_of_degreeOf` wants for the corresponding polynomial in
`Option σ` variables.
-/

open scoped Polynomial

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {σ : Type*}

/-- The image of a monomial under `MvPolynomial.optionEquivRight`: the exponent of `X none`
becomes the degree of the coefficient.  The analogue of `MvPolynomial.optionEquivLeft_monomial`. -/
theorem optionEquivRight_monomial (μ : Option σ →₀ ℕ) (r : R) :
    optionEquivRight R σ (monomial μ r) = monomial μ.some (Polynomial.monomial (μ none) r) := by
  rw [optionEquivRight_apply, aeval_monomial, Finsupp.prod_option_index, MvPolynomial.monomial_eq,
    ← mul_assoc]
  · congr 1
    simp only [Option.elim_none, algebraMap_apply, Polynomial.algebraMap_eq, ← C_pow, ← map_mul,
      Polynomial.C_mul_X_pow_eq_monomial]
  · simp
  · intros; rw [pow_add]

/-- **The coefficient dictionary.**  The coefficient of `Q : MvPolynomial (Option σ) R` at `μ` is
read off the image `optionEquivRight R σ Q` as the coefficient at `μ none` of its coefficient at
`μ.some`.  The analogue of `MvPolynomial.optionEquivLeft_coeff_coeff`. -/
theorem coeff_coeff_optionEquivRight (Q : MvPolynomial (Option σ) R) (ν : σ →₀ ℕ) (a : ℕ) :
    ((optionEquivRight R σ Q).coeff ν).coeff a = Q.coeff (ν.optionElim a) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial μ r =>
      rw [optionEquivRight_monomial, coeff_monomial, coeff_monomial]
      by_cases hν : μ.some = ν
      · subst hν
        rw [if_pos rfl, Polynomial.coeff_monomial]
        by_cases ha : μ none = a
        · subst ha
          rw [if_pos rfl, if_pos (Finsupp.optionElim_some μ).symm]
        · rw [if_neg ha, if_neg]
          intro h
          exact ha (by rw [h, Finsupp.optionElim_apply_none])
      · rw [if_neg hν, Polynomial.coeff_zero, eq_comm, if_neg]
        intro h
        exact hν (by rw [h, Finsupp.some_optionElim])
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

/-- The coefficient dictionary read backwards: a coefficient of the polynomial in `Option σ`
variables attached to `P : MvPolynomial σ R[X]`. -/
theorem coeff_optionEquivRight_symm (P : MvPolynomial σ R[X]) (μ : Option σ →₀ ℕ) :
    ((optionEquivRight R σ).symm P).coeff μ = (P.coeff μ.some).coeff (μ none) := by
  have h := coeff_coeff_optionEquivRight ((optionEquivRight R σ).symm P) μ.some (μ none)
  rw [AlgEquiv.apply_symm_apply, Finsupp.optionElim_some] at h
  exact h.symm

/-- **The degree in a `some` variable does not grow.**  If `P` has degree at most `u` in `X s`,
then its `Option σ`-avatar has degree at most `u` in `X (some s)`. -/
theorem degreeOf_some_optionEquivRight_symm_le (P : MvPolynomial σ R[X]) (s : σ) :
    ((optionEquivRight R σ).symm P).degreeOf (some s) ≤ P.degreeOf s := by
  classical
  rw [degreeOf_le_iff]
  intro μ hμ
  rw [mem_support_iff, coeff_optionEquivRight_symm] at hμ
  have hcoeff : P.coeff μ.some ≠ 0 := fun h => hμ (by rw [h, Polynomial.coeff_zero])
  have := monomial_le_degreeOf s (mem_support_iff.2 hcoeff)
  rwa [Finsupp.some_apply] at this

/-- **The degree in the `none` variable is the degree of the coefficients.**  If every coefficient
of `P` has degree at most `v`, then the `Option σ`-avatar of `P` has degree at most `v` in
`X none`. -/
theorem degreeOf_none_optionEquivRight_symm_le {P : MvPolynomial σ R[X]} {v : ℕ}
    (hv : ∀ ν, (P.coeff ν).natDegree ≤ v) :
    ((optionEquivRight R σ).symm P).degreeOf none ≤ v := by
  classical
  rw [degreeOf_le_iff]
  intro μ hμ
  rw [mem_support_iff, coeff_optionEquivRight_symm] at hμ
  exact le_trans (Polynomial.le_natDegree_of_ne_zero hμ) (hv _)

/-- **Evaluation, forwards.**  Evaluating `Q` in `Option σ` variables is evaluating its image
with the coefficients specialized at the value of the `none` variable. -/
theorem eval₂_optionEquivRight (x : Option σ → R) (Q : MvPolynomial (Option σ) R) :
    eval₂ (Polynomial.evalRingHom (x none)) (fun s => x (some s)) (optionEquivRight R σ Q) =
      eval x Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => rw [optionEquivRight_C, eval₂_C, eval_C]; simp
  | add p q hp hq => rw [map_add, eval₂_add, hp, hq, map_add]
  | mul_X p o hp =>
      have ho : eval₂ (Polynomial.evalRingHom (x none)) (fun s => x (some s))
          (optionEquivRight R σ (X o)) = x o := by
        cases o with
        | none => rw [optionEquivRight_X_none, eval₂_C]; simp
        | some s => rw [optionEquivRight_X_some, eval₂_X]
      rw [map_mul, eval₂_mul, hp, ho, map_mul, eval_X]

/-- **Evaluation.**  Evaluating the `Option σ`-avatar of `P` at a point `x` is evaluating `P` with
its coefficients specialized at `x none`. -/
theorem eval_optionEquivRight_symm (x : Option σ → R) (P : MvPolynomial σ R[X]) :
    eval x ((optionEquivRight R σ).symm P) =
      eval₂ (Polynomial.evalRingHom (x none)) (fun s => x (some s)) P := by
  have h := eval₂_optionEquivRight x ((optionEquivRight R σ).symm P)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end MvPolynomial
