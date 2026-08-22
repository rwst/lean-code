/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

/-!
# Liouville's inequality, and the height of a polynomial value

Mathlib's `NumberTheory/Height` develops the Weil height of an element of a field carrying an
admissible family of absolute values: `Height.mulHeight₁`, `Height.logHeight₁`, together with
the arithmetic inequalities `logHeight₁_mul_le`, `logHeight₁_add_le`, `logHeight₁_pow`,
`logHeight₁_prod_le`, `logHeight₁_sum_le`, and the projective evaluation bound
`Height.mulHeight_eval_le` for *homogeneous* polynomials.

This file adds the two facts that are missing for Diophantine work:

* **Liouville's inequality** — for `x ≠ 0` and any absolute value `v` of the family,
  `(mulHeight₁ x)⁻¹ ≤ v x`, i.e. `-logHeight₁ x ≤ log (v x)`
  (`Height.inv_mulHeight₁_le_of_mem_archAbsVal`, `Height.neg_logHeight₁_le_log_of_mem_archAbsVal`
  and the nonarchimedean twins).  Over a number field this is the classical statement
  `log |β| ≥ -[k : ℚ] · h(β)` of [Wal00, p. 82], because `logHeight₁ = [k : ℚ] · h` — see
  `NumberField.totalWeight_eq_finrank` for the normalisation.  The version at a complex embedding
  is `NumberField.inv_mulHeight₁_le_norm`.

* **The affine evaluation bound** — the height of `p(x)` for a not necessarily homogeneous
  multivariate polynomial (`Height.logHeight₁_eval_le`), and its univariate form
  (`Height.logHeight₁_eval_le_of_polynomial`).

The proof of Liouville's inequality does not touch the product formula directly: the whole of it
is already packaged in `Height.mulHeight₁_inv`, `H(x⁻¹) = H(x)`.  What remains is the observation
that a *single* absolute value of the family is bounded by the height, because the height is a
product of factors that are all `≥ 1`.

## References

* [Wal00] M. Waldschmidt, *Diophantine approximation on linear algebraic groups*, Grundlehren
  der math. Wiss. 326, Springer 2000; Ch. 3 and p. 82 (Liouville's inequality).
-/

namespace Height

open AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-! ### A single absolute value is bounded by the height -/

/-- Every archimedean absolute value of the family is bounded by the multiplicative height:
the height is a product of factors `max (v x) 1`, all of which are `≥ 1`. -/
theorem apply_le_mulHeight₁_of_mem_archAbsVal {v : AbsoluteValue K ℝ}
    (hv : v ∈ archAbsVal (K := K)) (x : K) : v x ≤ mulHeight₁ x := by
  have hG : (1 : ℝ) ≤ ∏ᶠ w : nonarchAbsVal (K := K), max (w.val x) 1 :=
    one_le_finprod fun _ ↦ le_max_right ..
  classical
  have hP : max (v x) 1 ≤ (archAbsVal.map fun w : AbsoluteValue K ℝ ↦ max (w x) 1).prod := by
    conv_rhs => rw [← Multiset.cons_erase hv]
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_right _ _))
      (Multiset.one_le_prod_map fun _ _ ↦ le_max_right ..)
  have hP0 : (0 : ℝ) ≤ (archAbsVal.map fun w : AbsoluteValue K ℝ ↦ max (w x) 1).prod :=
    le_trans (le_trans zero_le_one (le_max_right (v x) 1)) hP
  rw [mulHeight₁_eq]
  exact le_trans (le_max_left _ _) (le_trans hP (le_mul_of_one_le_right hP0 hG))

/-- Every nonarchimedean absolute value of the family is bounded by the multiplicative height. -/
theorem apply_le_mulHeight₁_of_mem_nonarchAbsVal {v : AbsoluteValue K ℝ}
    (hv : v ∈ nonarchAbsVal (K := K)) (x : K) : v x ≤ mulHeight₁ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hP : (1 : ℝ) ≤ (archAbsVal.map fun w : AbsoluteValue K ℝ ↦ max (w x) 1).prod :=
    Multiset.one_le_prod_map fun _ _ ↦ le_max_right ..
  classical
  set g : nonarchAbsVal (K := K) → ℝ :=
    fun w ↦ if w = (⟨v, hv⟩ : nonarchAbsVal (K := K)) then max (v x) 1 else 1 with hg
  have hgs : Function.HasFiniteMulSupport g := by
    refine Set.Finite.subset (Set.finite_singleton (⟨v, hv⟩ : nonarchAbsVal (K := K))) ?_
    intro w hw
    simp only [Function.mem_mulSupport, hg] at hw
    by_contra hne
    exact hw (ite_eq_right hne)
  have hfs : Function.HasFiniteMulSupport
      fun w : nonarchAbsVal (K := K) ↦ max (w.val x) 1 := by
    refine Set.Finite.subset (AdmissibleAbsValues.hasFiniteMulSupport hx) fun w hw ↦ ?_
    simp only [Function.mem_mulSupport] at hw ⊢
    intro h
    exact hw (by rw [h, max_self])
  have hG : max (v x) 1 ≤ ∏ᶠ w : nonarchAbsVal (K := K), max (w.val x) 1 := by
    have hsingle : (∏ᶠ w : nonarchAbsVal (K := K), g w) = max (v x) 1 := by
      rw [finprod_eq_single g ⟨v, hv⟩ fun w hw ↦ ite_eq_right hw]
      simp [hg]
    rw [← hsingle]
    refine finprod_le_finprod hgs (fun w ↦ ?_) hfs fun w ↦ ?_
    · simp only [hg]; split <;> positivity
    · simp only [hg]
      split
      · next h => subst h; exact le_rfl
      · exact le_max_right ..
  have hG0 : (0 : ℝ) ≤ ∏ᶠ w : nonarchAbsVal (K := K), max (w.val x) 1 :=
    le_trans (le_trans zero_le_one (le_max_right (v x) 1)) hG
  rw [mulHeight₁_eq]
  exact le_trans (le_max_left _ _) (le_trans hG (le_mul_of_one_le_left hG0 hP))

/-! ### Liouville's inequality -/

/-- **Liouville's inequality**, archimedean form: a nonzero element of `K` cannot be too small at
any archimedean absolute value of the family, `v x ≥ H(x)⁻¹`.

Over a number field this is `|β| ≥ H(β)^{-1}`, i.e. `log |β| ≥ -[k : ℚ] h(β)` in the
normalisation of [Wal00, p. 82], since `logHeight₁ = [k : ℚ] * h`. -/
theorem inv_mulHeight₁_le_of_mem_archAbsVal {v : AbsoluteValue K ℝ}
    (hv : v ∈ archAbsVal (K := K)) {x : K} (hx : x ≠ 0) : (mulHeight₁ x)⁻¹ ≤ v x := by
  have h := apply_le_mulHeight₁_of_mem_archAbsVal hv x⁻¹
  rw [map_inv₀, mulHeight₁_inv] at h
  rwa [inv_le_comm₀ (mulHeight₁_pos x) (v.pos hx)]

/-- **Liouville's inequality**, nonarchimedean form. -/
theorem inv_mulHeight₁_le_of_mem_nonarchAbsVal {v : AbsoluteValue K ℝ}
    (hv : v ∈ nonarchAbsVal (K := K)) {x : K} (hx : x ≠ 0) : (mulHeight₁ x)⁻¹ ≤ v x := by
  have h := apply_le_mulHeight₁_of_mem_nonarchAbsVal hv x⁻¹
  rw [map_inv₀, mulHeight₁_inv] at h
  rwa [inv_le_comm₀ (mulHeight₁_pos x) (v.pos hx)]

/-- **Liouville's inequality**, logarithmic form: `log (v x) ≥ -h(x)`. -/
theorem neg_logHeight₁_le_log_of_mem_archAbsVal {v : AbsoluteValue K ℝ}
    (hv : v ∈ archAbsVal (K := K)) {x : K} (hx : x ≠ 0) : -logHeight₁ x ≤ log (v x) := by
  rw [logHeight₁_eq_log_mulHeight₁, ← Real.log_inv]
  exact Real.log_le_log (by positivity) (inv_mulHeight₁_le_of_mem_archAbsVal hv hx)

/-- **Liouville's inequality**, logarithmic nonarchimedean form. -/
theorem neg_logHeight₁_le_log_of_mem_nonarchAbsVal {v : AbsoluteValue K ℝ}
    (hv : v ∈ nonarchAbsVal (K := K)) {x : K} (hx : x ≠ 0) : -logHeight₁ x ≤ log (v x) := by
  rw [logHeight₁_eq_log_mulHeight₁, ← Real.log_inv]
  exact Real.log_le_log (by positivity) (inv_mulHeight₁_le_of_mem_nonarchAbsVal hv hx)

/-- The logarithm of any archimedean absolute value of a nonzero element is squeezed between
`±h(x)`. -/
theorem abs_log_le_logHeight₁_of_mem_archAbsVal {v : AbsoluteValue K ℝ}
    (hv : v ∈ archAbsVal (K := K)) {x : K} (hx : x ≠ 0) : |log (v x)| ≤ logHeight₁ x := by
  rw [abs_le]
  refine ⟨neg_logHeight₁_le_log_of_mem_archAbsVal hv hx, ?_⟩
  rw [logHeight₁_eq_log_mulHeight₁]
  exact Real.log_le_log (v.pos hx) (apply_le_mulHeight₁_of_mem_archAbsVal hv x)

/-! ### The height of a polynomial value -/

open Finset in
/-- The height of the value of a (not necessarily homogeneous) multivariate polynomial: the
affine companion of Mathlib's projective `Height.logHeight_eval_le`. -/
theorem logHeight₁_eval_le {ι : Type*} [DecidableEq ι] (x : ι → K) (p : MvPolynomial ι K) :
    logHeight₁ (MvPolynomial.eval x p) ≤
      totalWeight K * log #p.support
        + ∑ m ∈ p.support, (logHeight₁ (MvPolynomial.coeff m p)
            + ∑ i ∈ m.support, m i * logHeight₁ (x i)) := by
  rw [MvPolynomial.eval_eq]
  refine le_trans (logHeight₁_sum_le _ _) ?_
  gcongr with m hm
  refine le_trans (logHeight₁_mul_le _ _) ?_
  gcongr
  refine le_trans (logHeight₁_prod_le _ _) ?_
  gcongr with i hi
  exact le_of_eq (logHeight₁_pow _ _)

open Finset in
/-- The height of the value of a univariate polynomial. -/
theorem logHeight₁_eval_le_of_polynomial (x : K) (p : Polynomial K) :
    logHeight₁ (p.eval x) ≤
      totalWeight K * log #p.support
        + ∑ n ∈ p.support, (logHeight₁ (p.coeff n) + n * logHeight₁ x) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine le_trans (logHeight₁_sum_le _ _) ?_
  gcongr with n hn
  refine le_trans (logHeight₁_mul_le _ _) ?_
  gcongr
  exact le_of_eq (logHeight₁_pow _ _)

end Height

/-! ### Number fields -/

namespace NumberField

open Height

variable {K : Type*} [Field K] [NumberField K]

/-- **Liouville's inequality** at an infinite place of a number field: `v x ≥ H(x)⁻¹`. -/
theorem inv_mulHeight₁_le_infinitePlace (v : InfinitePlace K) {x : K} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ v x :=
  inv_mulHeight₁_le_of_mem_archAbsVal (mem_multisetInfinitePlace.mpr v.isInfinitePlace) hx

/-- **Liouville's inequality** at an infinite place, logarithmic form. -/
theorem neg_logHeight₁_le_log_infinitePlace (v : InfinitePlace K) {x : K} (hx : x ≠ 0) :
    -logHeight₁ x ≤ Real.log (v x) :=
  neg_logHeight₁_le_log_of_mem_archAbsVal (mem_multisetInfinitePlace.mpr v.isInfinitePlace) hx

/-- **Liouville's inequality** at a complex embedding: a nonzero algebraic number is at least
`H(x)⁻¹` in absolute value.  Since `logHeight₁ = [K : ℚ] * h`
(`NumberField.totalWeight_eq_finrank`), this is the inequality `log |β| ≥ -[k : ℚ] h(β)`
of [Wal00, p. 82]. -/
theorem inv_mulHeight₁_le_norm (φ : K →+* ℂ) {x : K} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ‖φ x‖ := by
  have := inv_mulHeight₁_le_infinitePlace (InfinitePlace.mk φ) hx
  rwa [InfinitePlace.apply] at this

/-- **Liouville's inequality** at a complex embedding, logarithmic form. -/
theorem neg_logHeight₁_le_log_norm (φ : K →+* ℂ) {x : K} (hx : x ≠ 0) :
    -logHeight₁ x ≤ Real.log ‖φ x‖ := by
  have := neg_logHeight₁_le_log_infinitePlace (InfinitePlace.mk φ) hx
  rwa [InfinitePlace.apply] at this

/-- The inequality is sharp: over `ℚ` it is an equality at every `1 / n`. -/
example (n : ℕ) (hn : 0 < n) :
    (mulHeight₁ ((n : ℚ)⁻¹))⁻¹ = ‖(Rat.castHom ℂ) ((n : ℚ)⁻¹)‖ := by
  rw [mulHeight₁_inv, Rat.mulHeight₁_eq_max]
  simp [Rat.num_natCast, Rat.den_natCast, Nat.max_eq_left hn]

end NumberField
