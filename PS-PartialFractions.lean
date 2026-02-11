import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Tactic

noncomputable section

open scoped Classical
open Polynomial

variable {K : Type*} [Field K]

/-! This code bridges the gap between RatFunc (where partial fractions happen) and PowerSeries
(where you want the coefficients), and introduces the specific polynomials required for
the "coefficient formula."
-/

open RatFunc

/-!
### 1. Reverse Partial Fractions Structure
Mathlib has partial fractions, but not specifically optimized for the form
c / (1 - αX)^k, which is the "generating function friendly" format.
-/

/-- A single term in the partial fraction decomposition: c / (1 - αX)^k -/
structure GenFuncPartialFraction (L : Type*) [Field L] where
  c     : L  -- The numerator coefficient
  alpha : L  -- The reciprocal of the root (i.e., the base of the geometric series)
  k     : ℕ  -- The multiplicity/power (must be ≥ 1)

/-!
### 2. Standard Partial Fractions Structure

A term in the classical partial fraction decomposition: c / (X - r)^k
-/

/-- A single term in the standard partial fraction decomposition: c / (X - r)^k -/
structure StandardPartialFraction (L : Type*) [Field L] where
  c : L      -- The numerator coefficient
  root : L   -- The root r
  k : ℕ      -- The multiplicity/power (k ≥ 1)

/-!
### 3. Missing Infrastructure Lemmas

These lemmas bridge standard partial fractions to the generating function form.
-/

/--
Standard partial fraction decomposition exists:
For any polynomial Q that splits completely over L, 1/Q can be written as
a sum of terms c / (X - r)^k.
-/
theorem standard_partial_fractions_exists
    (Q : Polynomial K) (hQ_ne : Q ≠ 0) (hQ_const : Q.coeff 0 ≠ 0)
    (L : Type*) [Field L] [Algebra K L] [IsSplittingField K L Q] :
    ∃ (terms : List (StandardPartialFraction L)),
      -- All roots in the decomposition are roots of Q
      (∀ t ∈ terms, (Q.map (algebraMap K L)).IsRoot t.root) ∧
      -- All multiplicities are positive
      (∀ t ∈ terms, t.k ≥ 1) ∧
      -- The decomposition holds
      (1 : RatFunc L) / (Q.map (algebraMap K L) : RatFunc L) =
      (terms.map fun (t : StandardPartialFraction L) =>
        RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k
      ).sum := by
  sorry

/-!
#### Helper lemmas for RatFunc algebra

TODO:   What would make this easier in mathlib/tactics:
  1. Better ring tactic integration with RatFunc.C - currently ring doesn't simplify
   expressions involving the embedding
  2. Direct simp lemmas like RatFunc.neg_C_eq without needing to use map_neg
  3. A unified approach for 1/r vs r⁻¹ - these are definitionally equal but don't always unify
   in rewrites
-/

/-- C(a) * C(b) = C(a * b) -/
lemma RatFunc.C_mul_C (L : Type*) [Field L] (a b : L) :
    RatFunc.C a * RatFunc.C b = RatFunc.C (a * b) := by
  rw [← map_mul]

/-- X ≠ C(r) for any r (X has degree 1, C(r) has degree 0) -/
lemma RatFunc.X_ne_C (L : Type*) [Field L] (r : L) : (RatFunc.X : RatFunc L) ≠ RatFunc.C r := by
  intro heq
  have := congrArg RatFunc.num heq
  simp only [RatFunc.num_X, RatFunc.num_C] at this
  have hdeg : (Polynomial.X : L[X]).natDegree = (Polynomial.C r).natDegree := by rw [this]
  simp at hdeg

/-- (X - C(r))^k ≠ 0 -/
lemma RatFunc.X_sub_C_pow_ne_zero (L : Type*) [Field L] (r : L) (k : ℕ) :
    (RatFunc.X - RatFunc.C r) ^ k ≠ 0 := by
  apply pow_ne_zero
  intro h
  exact RatFunc.X_ne_C L r (sub_eq_zero.mp h)

/-- (1 - C(r⁻¹) * X)^k ≠ 0 when r ≠ 0 -/
lemma RatFunc.one_sub_C_inv_mul_X_pow_ne_zero (L : Type*) [Field L] (r : L) (hr : r ≠ 0) (k : ℕ) :
    (1 - RatFunc.C r⁻¹ * RatFunc.X) ^ k ≠ 0 := by
  apply pow_ne_zero
  intro h
  have h1 : (1 : RatFunc L) = RatFunc.C r⁻¹ * RatFunc.X := sub_eq_zero.mp h
  have : RatFunc.X = RatFunc.C r := by
    calc RatFunc.X = RatFunc.C r * (RatFunc.C r⁻¹ * RatFunc.X) := by
           rw [← mul_assoc, RatFunc.C_mul_C, mul_inv_cancel₀ hr, map_one, one_mul]
      _ = RatFunc.C r * 1 := by rw [← h1]
      _ = RatFunc.C r := mul_one _
  exact RatFunc.X_ne_C L r this

/-- Key factorization: X - C(r) = -C(r) * (1 - C(r⁻¹) * X) -/
lemma RatFunc.X_sub_C_factor (L : Type*) [Field L] (r : L) (hr : r ≠ 0) :
    RatFunc.X - RatFunc.C r = -RatFunc.C r * (1 - RatFunc.C r⁻¹ * RatFunc.X) := by
  have h1 : RatFunc.C r * RatFunc.C r⁻¹ = (1 : RatFunc L) := by
    rw [RatFunc.C_mul_C, mul_inv_cancel₀ hr, map_one]
  calc RatFunc.X - RatFunc.C r
      = RatFunc.X + (-RatFunc.C r) := sub_eq_add_neg _ _
    _ = 1 * RatFunc.X + (-RatFunc.C r) * 1 := by ring
    _ = (RatFunc.C r * RatFunc.C r⁻¹) * RatFunc.X + (-RatFunc.C r) * 1 := by rw [h1]
    _ = -RatFunc.C r * (1 - RatFunc.C r⁻¹ * RatFunc.X) := by ring

/--
Conversion from standard form to generating function form:
  1 / (X - r)^k = (-1/r)^k / (1 - (1/r)X)^k
for r ≠ 0.

Proof idea: Factor (X - r) = -r * (1 - r⁻¹ * X), raise to power k, invert.
-/
theorem inv_linear_pow_eq_geom_series_term (L : Type*) [Field L]
    (r : L) (hr : r ≠ 0) (k : ℕ) :
    (1 : RatFunc L) / (RatFunc.X - RatFunc.C r) ^ k =
    RatFunc.C ((-1 / r) ^ k) / (1 - RatFunc.C (1 / r) * RatFunc.X) ^ k := by
  have hXr_ne := RatFunc.X_sub_C_pow_ne_zero L r k
  have h1r_ne : (1 - RatFunc.C (1 / r) * RatFunc.X) ^ k ≠ 0 := by
    convert RatFunc.one_sub_C_inv_mul_X_pow_ne_zero L r hr k using 2
    rw [one_div]
  have factor : RatFunc.X - RatFunc.C r = -RatFunc.C r * (1 - RatFunc.C (1/r) * RatFunc.X) := by
    convert RatFunc.X_sub_C_factor L r hr using 2
    rw [one_div]
  have hcoef : ((-1 / r) ^ k : L) * (-r) ^ k = 1 := by
    rw [← mul_pow]
    have h_base : (-1 / r) * (-r) = (1 : L) := by field_simp
    rw [h_base, one_pow]
  have neg_C_pow : (-RatFunc.C r) ^ k = RatFunc.C ((-r) ^ k) := by
    have h1 : -RatFunc.C r = RatFunc.C (-r) := by simp [map_neg]
    rw [h1, ← map_pow]
  have inv_neg_pow : ((-r) ^ k)⁻¹ = ((-1 / r) ^ k : L) := by
    have h1 : -1 / r = (-r)⁻¹ := by field_simp
    rw [h1, ← inv_pow]
  calc (1 : RatFunc L) / (RatFunc.X - RatFunc.C r) ^ k
      = 1 / (-RatFunc.C r * (1 - RatFunc.C (1/r) * RatFunc.X)) ^ k := by rw [factor]
    _ = 1 / ((-RatFunc.C r) ^ k * (1 - RatFunc.C (1/r) * RatFunc.X) ^ k) := by rw [mul_pow]
    _ = 1 / (-RatFunc.C r) ^ k / (1 - RatFunc.C (1/r) * RatFunc.X) ^ k := by rw [div_div]
    _ = 1 / (RatFunc.C ((-r) ^ k)) / (1 - RatFunc.C (1/r) * RatFunc.X) ^ k := by rw [neg_C_pow]
    _ = RatFunc.C (((-r) ^ k)⁻¹) / (1 - RatFunc.C (1/r) * RatFunc.X) ^ k := by
        rw [one_div, map_inv₀]
    _ = RatFunc.C ((-1 / r) ^ k) / (1 - RatFunc.C (1/r) * RatFunc.X) ^ k := by rw [inv_neg_pow]

/--
Induction principle for rational functions of the form 1 / ∏(X - rᵢ):
If a property P holds for 1 (empty product) and is preserved when multiplying
the denominator by a new linear factor (X - r), then P holds for any such product.
-/
theorem inv_prod_linear_induction (L : Type*) [Field L]
    (P : RatFunc L → Prop)
    (h_one : P 1)
    (h_step : ∀ (f : RatFunc L) (r : L), P f → P (f / (RatFunc.X - RatFunc.C r))) :
    ∀ (roots : List L),
      P ((roots.map fun r => RatFunc.X - RatFunc.C r).prod⁻¹) := by
  intro roots
  induction roots with
  | nil =>
    simp only [List.map_nil, List.prod_nil, inv_one]
    exact h_one
  | cons r tail ih =>
    simp only [List.map_cons, List.prod_cons]
    have h_linear_ne : RatFunc.X - RatFunc.C r ≠ 0 := by
      intro h
      exact RatFunc.X_ne_C L r (sub_eq_zero.mp h)
    rw [mul_inv, mul_comm, ← div_eq_mul_inv]
    exact h_step _ r ih

/-!
### 4. Main Theorem

The missing existence theorem:
Any inverse of a polynomial Q (with Q(0) ≠ 0) decomposes into a sum of
terms of the form c / (1 - αX)^k in the splitting field.
-/
/-- Helper: if Q(0) ≠ 0, then 0 is not a root of Q -/
lemma root_ne_zero_of_coeff_zero_ne_zero (Q : Polynomial K) (hQ_const : Q.coeff 0 ≠ 0)
    (L : Type*) [Field L] [Algebra K L]
    (r : L) (hr : (Q.map (algebraMap K L)).IsRoot r) :
    r ≠ 0 := by
  intro h_r_zero
  rw [h_r_zero, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_zero] at hr
  rw [map_eq_zero_iff _ (algebraMap K L).injective] at hr
  exact hQ_const hr

/-- Convert a standard partial fraction term to generating function form -/
def standardToGenFunc {L : Type*} [Field L] (t : StandardPartialFraction L) (_hr : t.root ≠ 0) :
    GenFuncPartialFraction L :=
  ⟨t.c * ((-1 / t.root) ^ t.k), 1 / t.root, t.k⟩

/-- The conversion preserves the rational function value -/
lemma standardToGenFunc_eq (L : Type*) [Field L] (t : StandardPartialFraction L) (hr : t.root ≠ 0) :
    RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k =
    (let g := standardToGenFunc t hr
     RatFunc.C g.c / (1 - RatFunc.C g.alpha * RatFunc.X) ^ g.k) := by
  unfold standardToGenFunc
  have h := inv_linear_pow_eq_geom_series_term L t.root hr t.k
  calc RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k
      = RatFunc.C t.c * (1 / (RatFunc.X - RatFunc.C t.root) ^ t.k) := by rw [mul_one_div]
    _ = RatFunc.C t.c * (RatFunc.C ((-1 / t.root) ^ t.k) /
          (1 - RatFunc.C (1 / t.root) * RatFunc.X) ^ t.k) := by rw [h]
    _ = (RatFunc.C t.c * RatFunc.C ((-1 / t.root) ^ t.k)) /
          (1 - RatFunc.C (1 / t.root) * RatFunc.X) ^ t.k := by rw [mul_div_assoc]
    _ = RatFunc.C (t.c * (-1 / t.root) ^ t.k) /
          (1 - RatFunc.C (1 / t.root) * RatFunc.X) ^ t.k := by rw [RatFunc.C_mul_C]

theorem exists_partial_fraction_form_inv_poly
    (Q : Polynomial K) (hQ_const : Q.coeff 0 ≠ 0)
    (L : Type*) [Field L] [Algebra K L] [IsSplittingField K L Q] :
    ∃ (terms : List (GenFuncPartialFraction L)),
      (1 : RatFunc L) / (Q.map (algebraMap K L) : RatFunc L) =
      (terms.map fun (t : GenFuncPartialFraction L) =>
        (RatFunc.C t.c) / ((1 : RatFunc L) - RatFunc.C t.alpha * RatFunc.X) ^ t.k
      ).sum := by
  have hQ_ne : Q ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hQ_const
    exact hQ_const rfl
  obtain ⟨std_terms, h_roots, _, h_decomp⟩ :=
    standard_partial_fractions_exists Q hQ_ne hQ_const L
  have h_roots_ne : ∀ t ∈ std_terms, t.root ≠ 0 := fun t ht =>
    root_ne_zero_of_coeff_zero_ne_zero Q hQ_const L t.root (h_roots t ht)
  let toGenFunc : StandardPartialFraction L → GenFuncPartialFraction L := fun t =>
    if hr : t.root ≠ 0 then standardToGenFunc t hr
    else ⟨0, 0, 0⟩
  use std_terms.map toGenFunc
  rw [h_decomp, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hr : t.root ≠ 0 := h_roots_ne t ht
  simp only [toGenFunc, dif_pos hr, Function.comp_apply]
  exact standardToGenFunc_eq L t hr
