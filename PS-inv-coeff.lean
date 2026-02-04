import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer


noncomputable section

open scoped Classical
open Polynomial PowerSeries BigOperators

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

/--
The missing existence theorem:
Any inverse of a polynomial Q (with Q(0) ≠ 0) decomposes into a sum of
terms of the form c / (1 - αX)^k in the splitting field.
-/
theorem exists_partial_fraction_form_inv_poly
    (Q : Polynomial K) (hQ_const : Q.coeff 0 ≠ 0)
    (L : Type*) [Field L] [Algebra K L] [IsSplittingField K L Q] :
    ∃ (terms : List (GenFuncPartialFraction L)),
      -- The decomposition holds in the Rational Function field
      (1 : RatFunc L) / (Q.map (algebraMap K L) : RatFunc L) =
      (terms.map fun (t : GenFuncPartialFraction L) =>
        (RatFunc.C t.c) / ((1 : RatFunc L) - RatFunc.C t.alpha * RatFunc.X) ^ t.k
      ).sum := by
  sorry

/-!
### 2. Binomial Coefficient Polynomials
We need to treat the binomial coefficient `(n + k - 1).choose (k - 1)`
as a polynomial in `n` over the field K.
-/

/--
Constructs the polynomial P_k(X) such that P_k(n) = (n + k - 1) choose (k - 1).
This is related to the Pochhammer symbol or rising factorial.
-/
def binomialCoefPoly (k : ℕ) : Polynomial K :=
  if k = 0 then 0 else
  -- P_k(X) = (X + 1)(X + 2)...(X + k - 1) / (k-1)!
  Polynomial.C (((k - 1).factorial : K)⁻¹) * (ascPochhammer K (k - 1)).comp (Polynomial.X + 1)

/--
Lemma stating that this polynomial actually computes the integer binomial coefficient
when evaluated at a natural number n (cast to K).
-/
theorem binomialCoefPoly_eval_eq [CharZero K] (k : ℕ) (n : ℕ) (hk : k ≥ 1) :
    (binomialCoefPoly k).eval (n : K) = (Nat.choose (n + k - 1) (k - 1) : K) := by
  -- Unfold the definition and use hk to take the else branch
  have hk' : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  simp only [binomialCoefPoly, if_neg hk']
  -- Simplify evaluation of C * p.comp q
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
             Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  -- Normalize ↑n + 1 to ↑(n + 1)
  have cast_eq : (n : K) + 1 = ((n + 1 : ℕ) : K) := by push_cast; ring
  rw [cast_eq]
  -- Use the mathlib theorem connecting choose to ascPochhammer
  rw [Nat.cast_choose_eq_ascPochhammer_div, div_eq_mul_inv, mul_comm]
  congr 1
  -- Show the arguments match: (n + k - 1) - (k - 1 - 1) = n + 1
  -- First handle the k = 1 case separately where ascPochhammer K 0 = 1
  rcases k with _ | k'
  · omega  -- k = 0 contradicts hk
  · simp only [Nat.add_sub_cancel]
    cases k' with
    | zero => simp [ascPochhammer_zero]  -- k = 1: both sides = 1
    | succ k'' =>
      -- k = k'' + 2, so k - 1 = k'' + 1
      simp only [Nat.succ_sub_one]
      -- Need: n + k'' + 1 - k'' = n + 1
      norm_cast
      congr 1
      omega

/-!
### 3. Expansion of Inverse Powers (Generalized Binomial Thm)
Mathlib knows geometric series, but the specific formula for 1/(1-x)^k
is often derived rather than available as a single rewrite.
-/

/--
The coefficient of x^n in the expansion of 1 / (1 - aX)^k is (n+k-1 choose k-1) * a^n.
-/
theorem coeff_inv_one_sub_smul_pow (a : K) (k : ℕ) (hk : k ≥ 1) (n : ℕ) :
    (PowerSeries.coeff n) ((1 - PowerSeries.C a * PowerSeries.X)⁻¹ ^ k : K⟦X⟧) =
    (Nat.choose (n + k - 1) (k - 1) : K) * a ^ n := by
  sorry

/-!
### 4. The RatFunc to PowerSeries Bridge
We need to legally transport the equality from RatFunc (step 1) to PowerSeries (step 3).
-/

/--
A helper definition to coerce a valid Rational Function to a Power Series.
Valid means the denominator has a non-zero constant term (is a unit in PowerSeries).
-/
def ratFuncToPowerSeries (f : RatFunc K) (h_denom : (denom f).coeff 0 ≠ 0) : PowerSeries K :=
  (denom f : PowerSeries K)⁻¹ * (num f : PowerSeries K)

/--
The Commutation Lemma:
If a RatFunc decomposition holds, the PowerSeries decomposition holds.
This allows us to sum the series of the parts to get the series of the whole.
-/
theorem ratFunc_decomposition_implies_series_sum
    (terms : List (GenFuncPartialFraction K))
    (Q : Polynomial K) (hQ : Q.coeff 0 ≠ 0) :
    -- If the decomposition holds in RatFunc...
    (1 : RatFunc K) / (Q : RatFunc K) =
      (terms.map fun (t : GenFuncPartialFraction K) =>
        RatFunc.C t.c / ((1 : RatFunc K) - RatFunc.C t.alpha * RatFunc.X) ^ t.k).sum
    →
    -- ...then it holds in PowerSeries (implying coefficient equality)
    (Q : PowerSeries K)⁻¹ =
      (terms.map fun (t : GenFuncPartialFraction K) =>
        PowerSeries.C t.c * ((1 - PowerSeries.C t.alpha * PowerSeries.X)⁻¹ ^ t.k)
      ).sum := by
  sorry

theorem inverse_series_coefficient_repeated_roots
    (Q : Polynomial K)
    (h_const : Q.coeff 0 ≠ 0) : -- Ensure Q is invertible
    -- Existence of Splitting Field L
    ∃ (L : Type*) (_ : Field L) (_ : Algebra K L),
    let Q_L := Q.map (algebraMap K L)
    let roots := Q_L.roots
    let unique_roots := roots.toFinset

    -- EXISTENCE CLAIM:
    -- For every unique root 'r', there exists a helper polynomial 'P_r'
    ∃ (poly_map : L → Polynomial L),

    -- CONSTRAINT 1:
    -- For each root r, the degree of its helper polynomial P_r
    -- must be less than the multiplicity of r in Q
    (∀ r ∈ unique_roots, (poly_map r).degree < roots.count r)

    ∧

    -- CONSTRAINT 2:
    -- The coefficient formula holds for all n
    ∀ (n : ℕ),
      (PowerSeries.coeff n) ((Polynomial.map (algebraMap K L) Q : PowerSeries L)⁻¹) =
      -- Sum over unique roots: P_r(n) * (1/r)^n
      ∑ r ∈ unique_roots,
        ((poly_map r).eval (n : L)) * (1 / r) ^ n :=
by
  sorry

-- The statement for 1/(1-2x)
example (n : ℕ) : (PowerSeries.coeff n) ((1 - (PowerSeries.C (2 : ℚ)) * PowerSeries.X)⁻¹) = 2 ^ n := by
  sorry

-- Define the Fibonacci Power Series: ∑ F_n * X^n
def fibSeries : PowerSeries ℚ := PowerSeries.mk (fun n => (Nat.fib n : ℚ))

-- The Polynomial: 1 - X - X^2
def fibDenom : PowerSeries ℚ := 1 - PowerSeries.X - PowerSeries.X ^ 2

theorem fib_generating_function : fibSeries = PowerSeries.X * fibDenom⁻¹ := by
  sorry
