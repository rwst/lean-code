/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Polynomial.BigOperators
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Stanley's closure property: the proof

The machinery discharging `Stanley.pRecursive_of_isAlgebraic` — see `CITED.Stanley` for the
statement, its provenance, and why *this* closure property and not Carlson's theorem.  Until
2026-09-06 that statement was the one cited axiom of plan-B1E2's eventual-periodicity engine;
this file makes it a theorem, over any field of characteristic zero, with footprint `std3`.

## The proof

[Sta80] Thm 2.1 says: over a field of characteristic `0`, a power series `f` algebraic over `K[X]`
is *D-finite*.  The argument is one line of algebra — `K(X)(f)` is a **finite** extension of
`K(X)`, and it is **closed under `d/dX`** (differentiate the minimal polynomial: `f' =
-P_X(X,f)/P_Y(X,f)`, which lives in `K(X)(f)` because `P_Y(X,f) ≠ 0` by separability), so among
`f, f', …, f^(d)` there must be a `K(X)`-linear relation; clearing denominators makes it a
`K[X]`-linear one, i.e. an ODE.  [Sta80] Thm 1.5 then reads the recurrence off the ODE
coefficient by coefficient.

The load-bearing step — *a finite intermediate field is stable under the ambient derivation* — is
**already in Mathlib**, as a by-product of the Liouville-theorem differential-field development:
`instance (B : IntermediateField F K) [FiniteDimensional F B] : DifferentialAlgebra B K` in
`Mathlib/FieldTheory/Differential/Basic.lean`, whose standing `[CharZero F]` is where separability
enters.  So this file supplies only what surrounds it:

* **`fracDeriv`** (§1) — Mathlib relates `Derivation` to `IsLocalization` *nowhere*, so a
  derivation of a domain is extended to its fraction field here, by the dual-numbers trick:
  `r ↦ (r, D r)` is a ring hom into `S[ε] = TrivSqZeroExt S S` precisely because `D` is Leibniz,
  and `IsLocalization.lift` applies because `(u, b)` is a unit of `S[ε]` as soon as `u ≠ 0`.
  Uniqueness is `eq_of_leibniz_of_isFractionRing`.  This section is Stanley-free and is the
  natural Mathlib contribution.
* **The differential fields** (§2) — `Differential (RatFunc K)` and `Differential K⸨X⸩` from §1,
  and `DifferentialAlgebra (RatFunc K) K⸨X⸩` from its uniqueness clause.  Note `toIntDerivation`:
  `Differential` wants a `Derivation ℤ A A` over `Ring.toIntAlgebra`, while `restrictScalars ℤ`
  produces one over whatever `Algebra ℤ A` is ambient (for `K⟦X⟧`, `MvPowerSeries.instAlgebra`) —
  equal instances, not syntactically equal, and Lean cares.
* **`exists_ode`** (§3) = [Sta80] Thm 2.1: transport into `K⸨X⸩`, adjoin, apply the Mathlib
  instance, count dimensions, clear denominators, descend along `HahnSeries.ofPowerSeries`.
* **`sum_recCoeff_eq_zero` and `exists_recCoeff_ne_zero`** (§4) = the half of [Sta80] Thm 1.5 that
  is needed.  Mathlib has no `holonomic`/`DFinite`/`PRecursive` anything, so the extraction is
  built from scratch on `PowerSeries.coeff_iterate_derivative`.

## References

* [Sta80] R. P. Stanley. *Differentiably finite power series.* European J. Combin. **1** (1980),
  175–188.  (**Thm 2.1**, **Thm 1.5**.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): WP6.
-/

namespace Stanley

open scoped Differential
open Polynomial

/-- Any derivation of a commutative ring into itself is a `ℤ`-derivation — in the exact shape the
`Differential` class expects, i.e. over `Ring.toIntAlgebra` rather than whatever `Algebra ℤ A`
instance happens to be ambient (for `K⟦X⟧` that would be `MvPowerSeries.instAlgebra`). -/
def toIntDerivation {A : Type*} [CommRing A] {R : Type*} [CommSemiring R] [Algebra R A]
    (d : Derivation R A A) : Derivation ℤ A A where
  toLinearMap := AddMonoidHom.toIntLinearMap d.toLinearMap.toAddMonoidHom
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' := d.leibniz

@[simp] lemma toIntDerivation_apply {A : Type*} [CommRing A] {R : Type*} [CommSemiring R]
    [Algebra R A] (d : Derivation R A A) (a : A) : toIntDerivation d a = d a := rfl

/-! ## §1. Derivations extend to the fraction field

Mathlib relates `Derivation` to `IsLocalization` nowhere; this section supplies the missing
existence-and-uniqueness, by the dual-numbers trick: a derivation `D : R → R` is the same thing as
a ring hom `r ↦ (r, D r)` into the square-zero extension `S[ε]`, and *that* extends to `Frac R` by
`IsLocalization.lift` because `(u, b)` is a unit of `S[ε]` as soon as `u ≠ 0`. -/

section FractionField

variable {R : Type*} [CommRing R] [IsDomain R] {S : Type*} [Field S] [Algebra R S]
  [IsFractionRing R S]

/-- `r ↦ (r, D r) : R → S[ε]`, the dual-numbers form of a derivation: the Leibniz rule *is*
multiplicativity of this map. -/
noncomputable def dualHom (D : Derivation ℤ R R) : R →+* TrivSqZeroExt S S where
  toFun r := (algebraMap R S r, algebraMap R S (D r))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp <;> rfl
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show algebraMap R S (a * b) = algebraMap R S a * algebraMap R S b
      exact map_mul _ _ _
    · show algebraMap R S (D (a * b))
        = algebraMap R S a * algebraMap R S (D b) + algebraMap R S (D a) * algebraMap R S b
      simp [Derivation.leibniz, smul_eq_mul, mul_comm]

lemma isUnit_dualHom (D : Derivation ℤ R R) (y : nonZeroDivisors R) :
    IsUnit (dualHom (S := S) D y) := by
  have h : (dualHom (S := S) D y).fst ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  exact ⟨⟨_, (dualHom (S := S) D y)⁻¹, TrivSqZeroExt.mul_inv_cancel h,
    TrivSqZeroExt.inv_mul_cancel h⟩, rfl⟩

/-- The dual-numbers hom, lifted to the fraction field. -/
noncomputable def fracLift (D : Derivation ℤ R R) : S →+* TrivSqZeroExt S S :=
  IsLocalization.lift (M := nonZeroDivisors R) (isUnit_dualHom D)

@[simp] lemma fracLift_algebraMap (D : Derivation ℤ R R) (r : R) :
    fracLift (S := S) D (algebraMap R S r) = (algebraMap R S r, algebraMap R S (D r)) :=
  IsLocalization.lift_eq _ r

lemma fst_fracLift (D : Derivation ℤ R R) (s : S) : (fracLift (S := S) D s).fst = s := by
  have h : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (fracLift (S := S) D) = RingHom.id S := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) ?_
    ext r
    simp
    rfl
  exact congrArg (fun f => f s) h

/-- The extension of `D` to the fraction field. -/
@[category API, AMS 11 68 05, ref "Sta80", group "stanley_closure"]
noncomputable def fracDeriv (D : Derivation ℤ R R) : Derivation ℤ S S :=
  Derivation.mk'
    (AddMonoidHom.toIntLinearMap
      (((TrivSqZeroExt.sndHom S S).toAddMonoidHom).comp (fracLift (S := S) D).toAddMonoidHom))
    (fun a b => by
      have h : ∀ s : S, (AddMonoidHom.toIntLinearMap
          (((TrivSqZeroExt.sndHom S S).toAddMonoidHom).comp
            (fracLift (S := S) D).toAddMonoidHom)) s = (fracLift (S := S) D s).snd :=
        fun _ => rfl
      rw [h, h, h, map_mul, TrivSqZeroExt.snd_mul, fst_fracLift, fst_fracLift]
      simp [smul_eq_mul, mul_comm])

@[simp] lemma fracDeriv_algebraMap (D : Derivation ℤ R R) (r : R) :
    fracDeriv (S := S) D (algebraMap R S r) = algebraMap R S (D r) := by
  simp [fracDeriv]
  rfl

/-- **Uniqueness**: a Leibniz map out of a fraction field is determined by its values on the base.

Stated for bare functions rather than for `Derivation`: the two maps compared in the application
below live over *equal but not syntactically equal* `Algebra ℤ` instances (`Ring.toIntAlgebra`
against `HahnSeries.powerSeriesAlgebra`), where the bundled form would only get in the way. -/
@[category API, AMS 11 68 05, ref "Sta80", group "stanley_closure"]
theorem eq_of_leibniz_of_isFractionRing {N : Type*} [AddCommGroup N] [Module S N] (d₁ d₂ : S → N)
    (hl₁ : ∀ a b : S, d₁ (a * b) = a • d₁ b + b • d₁ a)
    (hl₂ : ∀ a b : S, d₂ (a * b) = a • d₂ b + b • d₂ a)
    (h : ∀ r : R, d₁ (algebraMap R S r) = d₂ (algebraMap R S r)) (s : S) : d₁ s = d₂ s := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) s
  set t : S := algebraMap R S x / algebraMap R S y with ht
  have hy0 : algebraMap R S y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hts : t * algebraMap R S y = algebraMap R S x := div_mul_cancel₀ _ hy0
  have key : ∀ d : S → N, (∀ a b : S, d (a * b) = a • d b + b • d a) →
      (algebraMap R S y) • d t = d (algebraMap R S x) - t • d (algebraMap R S y) := by
    intro d hd
    have hL := hd t (algebraMap R S y)
    rw [hts] at hL
    rw [hL]; abel
  have hkey : (algebraMap R S y) • d₁ t = (algebraMap R S y) • d₂ t := by
    rw [key d₁ hl₁, key d₂ hl₂, h x, h y]
  have := congrArg (fun z => (algebraMap R S y)⁻¹ • z) hkey
  simpa [inv_smul_smul₀ hy0] using this

end FractionField

/-! ## §2. The differential fields `K(X)` and `K⸨X⸩`

Mathlib has no derivation on either.  Both are fraction fields of a differential domain, so the
previous section supplies one, and its uniqueness clause makes the two agree along
`K(X) → K⸨X⸩`. -/

section DifferentialFields

open scoped RatFunc

variable (K : Type*) [Field K]

/-- `d/dX` on `K(X)`: the unique derivation extending `Polynomial.derivative`. -/
noncomputable scoped instance ratFuncDifferential : Differential (RatFunc K) :=
  ⟨fracDeriv (toIntDerivation (Polynomial.derivative' (R := K)))⟩

/-- `d/dX` on `K⸨X⸩`: the unique derivation extending `PowerSeries.derivative`. -/
noncomputable scoped instance laurentDifferential : Differential (LaurentSeries K) :=
  ⟨fracDeriv (toIntDerivation (PowerSeries.derivative K))⟩

@[simp] lemma deriv_algebraMap_polynomial (p : K[X]) :
    (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) (Polynomial.derivative p) :=
  fracDeriv_algebraMap _ _

@[simp] lemma deriv_algebraMap_powerSeries (f : PowerSeries K) :
    (algebraMap (PowerSeries K) (LaurentSeries K) f)′
      = algebraMap (PowerSeries K) (LaurentSeries K) (PowerSeries.derivative K f) :=
  fracDeriv_algebraMap _ _

scoped instance : DifferentialAlgebra (RatFunc K) (LaurentSeries K) := by
  refine ⟨fun a => eq_of_leibniz_of_isFractionRing (R := K[X])
    (fun x => (algebraMap (RatFunc K) (LaurentSeries K) x)′)
    (fun x => algebraMap (RatFunc K) (LaurentSeries K) x′) ?_ ?_ ?_ a⟩
  · intro u v
    simp [Algebra.smul_def, Derivation.leibniz]
  · intro u v
    simp [Algebra.smul_def, Derivation.leibniz]
  · intro p
    rw [deriv_algebraMap_polynomial, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    show (algebraMap (PowerSeries K) (LaurentSeries K) (algebraMap K[X] (PowerSeries K) p))′
      = algebraMap (PowerSeries K) (LaurentSeries K)
          (algebraMap K[X] (PowerSeries K) (Polynomial.derivative p))
    rw [deriv_algebraMap_powerSeries]
    exact congrArg _ (PowerSeries.derivative_coe p)

end DifferentialFields

/-! ## §3. Algebraic ⇒ D-finite

[Sta80] Thm 2.1.  The mathematical core — *a finite intermediate field is stable under the ambient
derivation* — is Mathlib's `Differential` instance for `IntermediateField`s, which is where
separability (hence `CharZero`) enters.  What is left here is transport: into `K⸨X⸩` and back, and
clearing denominators to turn a `K(X)`-linear relation into a `K[X]`-linear one. -/

section DFinite

open scoped RatFunc

variable {K : Type*} [Field K] [CharZero K]

/-- `d/dX` on `K⸨X⸩` as a plain function, so that it can be iterated. -/
noncomputable def lderiv (K : Type*) [Field K] : LaurentSeries K → LaurentSeries K := fun x => x′

omit [CharZero K] in
lemma lderiv_algebraMap (u : PowerSeries K) :
    lderiv K (algebraMap (PowerSeries K) (LaurentSeries K) u)
      = algebraMap (PowerSeries K) (LaurentSeries K) (PowerSeries.derivative K u) :=
  deriv_algebraMap_powerSeries K u

omit [CharZero K] in
lemma lderiv_iterate_algebraMap (i : ℕ) (u : PowerSeries K) :
    (lderiv K)^[i] (algebraMap (PowerSeries K) (LaurentSeries K) u)
      = algebraMap (PowerSeries K) (LaurentSeries K) ((PowerSeries.derivative K)^[i] u) := by
  induction i generalizing u with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, lderiv_algebraMap, ih, ← Function.iterate_succ_apply]

/-- The tower `K[X] → K⟦X⟧ → K⸨X⸩`, which Mathlib does not record. -/
scoped instance : IsScalarTower K[X] (PowerSeries K) (LaurentSeries K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **[Sta80] Thm 2.1**: an algebraic power series is *D-finite* — it satisfies a nontrivial
linear ODE with polynomial coefficients. -/
@[category research solved, AMS 11 68 05, ref "Sta80", group "stanley_closure"]
theorem exists_ode {f : PowerSeries K} (hf : IsAlgebraic K[X] f) :
    ∃ (r : ℕ) (p : Fin (r + 1) → K[X]), (∃ i, p i ≠ 0) ∧
      ∑ i : Fin (r + 1), (p i : PowerSeries K) * (PowerSeries.derivative K)^[(i : ℕ)] f = 0 := by
  set g : LaurentSeries K := algebraMap (PowerSeries K) (LaurentSeries K) f with hg
  -- `g` is algebraic over the *field* `K(X)`, hence generates a finite extension
  have halg : IsAlgebraic (RatFunc K) g :=
    (IsFractionRing.isAlgebraic_iff K[X] (RatFunc K) (LaurentSeries K)).mp hf.algebraMap
  have hint : IsIntegral (RatFunc K) g := isAlgebraic_iff_isIntegral.mp halg
  set B : IntermediateField (RatFunc K) (LaurentSeries K) :=
    IntermediateField.adjoin (RatFunc K) {g} with hB
  have : FiniteDimensional (RatFunc K) B := IntermediateField.adjoin.finiteDimensional hint
  -- ... and `B` is stable under `d/dX`, by Mathlib's differential-field machinery
  have hclosed : ∀ x ∈ B, lderiv K x ∈ B := by
    intro x hx
    have hx' : algebraMap B (LaurentSeries K) ⟨x, hx⟩ = x := rfl
    have h2 := DifferentialAlgebra.deriv_algebraMap (A := B) (B := LaurentSeries K) ⟨x, hx⟩
    rw [hx'] at h2
    show (x)′ ∈ B
    rw [h2]
    exact ((⟨x, hx⟩ : B)′).2
  have hmem : ∀ i : ℕ, (lderiv K)^[i] g ∈ B := by
    intro i
    induction i with
    | zero => simpa using IntermediateField.mem_adjoin_simple_self (RatFunc K) g
    | succ n ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
  -- `finrank + 1` iterated derivatives are `K(X)`-linearly dependent
  set d := Module.finrank (RatFunc K) B with hd
  set v : Fin (d + 1) → B := fun i => ⟨(lderiv K)^[(i : ℕ)] g, hmem i⟩ with hv
  have hnli : ¬ LinearIndependent (RatFunc K) v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp [← hd] at hcard
  obtain ⟨c, hc0, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hnli
  have hsumL : ∑ i : Fin (d + 1), c i • (lderiv K)^[(i : ℕ)] g = 0 := by
    have h : ((∑ i : Fin (d + 1), c i • v i : B) : LaurentSeries K) = 0 := by rw [hc0]; rfl
    rw [AddSubmonoidClass.coe_finsetSum] at h
    exact h
  -- clear denominators: an `K(X)`-relation becomes a `K[X]`-relation
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors K[X]) Finset.univ c
  have hq : ∀ i, ∃ y : K[X], algebraMap K[X] (RatFunc K) y = (b : K[X]) • c i :=
    fun i => hb i (Finset.mem_univ i)
  choose q hqs using hq
  have hb0 : algebraMap K[X] (RatFunc K) (b : K[X]) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨d, q, ⟨i₀, ?_⟩, ?_⟩
  · intro h0
    have h1 := hqs i₀
    rw [h0, map_zero, Algebra.smul_def, eq_comm, mul_eq_zero] at h1
    exact h1.elim hb0 hi₀
  · have key : ∑ i : Fin (d + 1),
        algebraMap K[X] (LaurentSeries K) (q i) * (lderiv K)^[(i : ℕ)] g = 0 := by
      have hstep : ∀ i : Fin (d + 1),
          algebraMap K[X] (LaurentSeries K) (q i) * (lderiv K)^[(i : ℕ)] g
            = algebraMap K[X] (LaurentSeries K) (b : K[X]) * (c i • (lderiv K)^[(i : ℕ)] g) := by
        intro i
        rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) (LaurentSeries K), hqs i,
          Algebra.smul_def (R := K[X]) (A := RatFunc K), map_mul,
          ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) (LaurentSeries K),
          Algebra.smul_def (R := RatFunc K) (A := LaurentSeries K), mul_assoc]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, ← Finset.mul_sum, hsumL,
        mul_zero]
    have hdesc : algebraMap (PowerSeries K) (LaurentSeries K)
        (∑ i : Fin (d + 1), (q i : PowerSeries K)
          * (PowerSeries.derivative K)^[(i : ℕ)] f) = 0 := by
      rw [map_sum]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key
      rw [map_mul, hg, lderiv_iterate_algebraMap]
      rfl
    have h0 : algebraMap (PowerSeries K) (LaurentSeries K)
        (∑ i : Fin (d + 1), (q i : PowerSeries K) * (PowerSeries.derivative K)^[(i : ℕ)] f)
        = algebraMap (PowerSeries K) (LaurentSeries K) 0 := by rw [hdesc, map_zero]
    exact HahnSeries.ofPowerSeries_injective h0

end DFinite

/-! ## §4. D-finite ⇒ P-recursive

[Sta80] Thm 1.5, the half that is needed here.  Taking the `(n+N)`-th coefficient of the ODE turns
`p i * D^[i] f` into a finite sum over pairs `(i, k)` — derivative order and index of a coefficient
of `p i` — of `(p i).coeff k * (n + (N-k) + 1).ascFactorial i * coeff (n + (N-k+i)) f`.  Grouping
those pairs by the shift `j = N - k + i` is the recurrence, whose coefficients are the polynomials
`recCoeff` below.  Reading the `(n+N)`-th coefficient rather than the `n`-th is what makes every
shift nonnegative, as `IsPRecursive` demands. -/

section PRecursive

variable {K : Type*} [Field K]

/-- `ascPoly K a i = (X + a)(X + a + 1) ⋯ (X + a + i - 1)`: the polynomial whose value at `n` is
the ascending factorial `(n + a).ascFactorial i` that `i`-fold differentiation produces. -/
noncomputable def ascPoly (K : Type*) [Field K] (a i : ℕ) : K[X] :=
  ∏ t ∈ Finset.range i, (X + C ((a + t : ℕ) : K))

@[simp] lemma ascPoly_eval (a i n : ℕ) :
    (ascPoly K a i).eval (n : K) = ((n + a).ascFactorial i : K) := by
  rw [ascPoly, Nat.ascFactorial_eq_prod_range, eval_prod, Nat.cast_prod]
  exact Finset.prod_congr rfl fun _ _ => by simp only [eval_add, eval_X, eval_C]; push_cast; ring

lemma ascPoly_monic (a i : ℕ) : (ascPoly K a i).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

lemma ascPoly_natDegree (a i : ℕ) : (ascPoly K a i).natDegree = i := by
  rw [ascPoly, natDegree_prod _ _ fun t _ => (monic_X_add_C ((a + t : ℕ) : K)).ne_zero]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma ascPoly_degree (a i : ℕ) : (ascPoly K a i).degree = (i : ℕ) := by
  rw [degree_eq_natDegree (ascPoly_monic a i).ne_zero, ascPoly_natDegree]

/-- The pairs `(i, k)` the extraction sums over: `i` the order of the derivative, `k` the index of
a coefficient of `p i`. -/
def recPairs (r N : ℕ) : Finset (Fin (r + 1) × ℕ) := Finset.univ ×ˢ Finset.range (N + 1)

/-- The shift of the coefficient of `f` contributed by the pair `(i, k)`. -/
def recShift {r : ℕ} (N : ℕ) (ik : Fin (r + 1) × ℕ) : ℕ := N - ik.2 + (ik.1 : ℕ)

/-- The coefficient of `w (n + j)` in the recurrence extracted from a linear ODE of order `r`
whose coefficients have degree at most `N`. -/
@[category API, AMS 11 68 05, ref "Sta80", group "stanley_closure"]
noncomputable def recCoeff {r : ℕ} (p : Fin (r + 1) → K[X]) (N j : ℕ) : K[X] :=
  ∑ ik ∈ (recPairs r N).filter (fun ik => recShift N ik = j),
    C ((p ik.1).coeff ik.2) * ascPoly K (N - ik.2 + 1) (ik.1 : ℕ)

lemma coeff_coe_mul (q : K[X]) (u : PowerSeries K) (N n : ℕ) (hq : q.natDegree ≤ N) :
    PowerSeries.coeff (n + N) ((q : PowerSeries K) * u)
      = ∑ k ∈ Finset.range (N + 1), q.coeff k * PowerSeries.coeff (n + N - k) u := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe]
  have hsub : Finset.range (N + 1) ⊆ Finset.range (n + N).succ := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  refine (Finset.sum_subset hsub ?_).symm
  intro k _ hk
  have hk' : N < k := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hk'), zero_mul]

/-- The recurrence extracted from the ODE holds at every index. -/
@[category API, AMS 11 68 05, ref "Sta80", group "stanley_closure"]
theorem sum_recCoeff_eq_zero {f : PowerSeries K} {r N : ℕ} {p : Fin (r + 1) → K[X]}
    (hN : ∀ i, (p i).natDegree ≤ N)
    (hode : ∑ i : Fin (r + 1), (p i : PowerSeries K) * (PowerSeries.derivative K)^[(i : ℕ)] f = 0)
    (n : ℕ) :
    ∑ j ∈ Finset.range (N + r + 1),
      (recCoeff p N j).eval (n : K) * PowerSeries.coeff (n + j) f = 0 := by
  have h0 : ∑ i : Fin (r + 1),
      PowerSeries.coeff (n + N) ((p i : PowerSeries K) * (PowerSeries.derivative K)^[(i : ℕ)] f)
      = 0 := by rw [← map_sum, hode, map_zero]
  have hexp : ∀ i : Fin (r + 1),
      PowerSeries.coeff (n + N) ((p i : PowerSeries K) * (PowerSeries.derivative K)^[(i : ℕ)] f)
      = ∑ k ∈ Finset.range (N + 1),
          (C ((p i).coeff k) * ascPoly K (N - k + 1) (i : ℕ)).eval (n : K)
            * PowerSeries.coeff (n + recShift N (i, k)) f := by
    intro i
    rw [coeff_coe_mul _ _ _ _ (hN i)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    have e1 : n + N - k = n + (N - k) := by omega
    have e2 : n + (N - k) + (i : ℕ) = n + recShift N (i, k) := by simp only [recShift]; omega
    have e3 : n + (N - k) + 1 = n + (N - k + 1) := by omega
    rw [e1, PowerSeries.coeff_iterate_derivative, e2, e3, eval_mul, eval_C, ascPoly_eval]
    ring
  have hpairs : ∑ ik ∈ recPairs r N,
      (C ((p ik.1).coeff ik.2) * ascPoly K (N - ik.2 + 1) (ik.1 : ℕ)).eval (n : K)
        * PowerSeries.coeff (n + recShift N ik) f = 0 := by
    rw [recPairs, Finset.sum_product, ← h0]
    exact (Finset.sum_congr rfl fun i _ => hexp i).symm
  have hmaps : ∀ ik ∈ recPairs r N, recShift N ik ∈ Finset.range (N + r + 1) := by
    rintro ⟨i, k⟩ hik
    simp only [recPairs, Finset.mem_product, Finset.mem_range] at hik
    simp only [recShift, Finset.mem_range]
    omega
  rw [← hpairs, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [recCoeff, eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ik hik => ?_
  rw [(Finset.mem_filter.mp hik).2]

lemma mem_recPairs {r N : ℕ} {ik : Fin (r + 1) × ℕ} : ik ∈ recPairs r N ↔ ik.2 ≤ N := by
  simp [recPairs, Finset.mem_product, Finset.mem_range]

/-- The extracted recurrence is **nontrivial**: at the largest shift that any nonzero coefficient
of the ODE reaches, the largest derivative order occurring there contributes a term of strictly
top degree, which therefore cannot cancel. -/
@[category API, AMS 11 68 05, ref "Sta80", group "stanley_closure"]
theorem exists_recCoeff_ne_zero {r N : ℕ} {p : Fin (r + 1) → K[X]}
    (hN : ∀ i, (p i).natDegree ≤ N) (hp : ∃ i, p i ≠ 0) :
    ∃ j ∈ Finset.range (N + r + 1), recCoeff p N j ≠ 0 := by
  classical
  obtain ⟨i₁, hi₁⟩ := hp
  set S : Finset (Fin (r + 1) × ℕ) :=
    (recPairs r N).filter (fun ik => (p ik.1).coeff ik.2 ≠ 0) with hSdef
  have hmemS : ∀ ik : Fin (r + 1) × ℕ, ik ∈ S ↔ (ik.2 ≤ N ∧ (p ik.1).coeff ik.2 ≠ 0) := by
    intro ik; rw [hSdef, Finset.mem_filter, mem_recPairs]
  have hSne : S.Nonempty := by
    refine ⟨(i₁, (p i₁).natDegree), (hmemS _).mpr ⟨hN i₁, ?_⟩⟩
    exact Polynomial.leadingCoeff_ne_zero.mpr hi₁
  obtain ⟨w, hwS, hwmax⟩ := S.exists_max_image (recShift N) hSne
  set j₀ := recShift N w with hj₀
  set F : Finset (Fin (r + 1) × ℕ) :=
    (recPairs r N).filter (fun ik => recShift N ik = j₀) with hFdef
  set T : Finset (Fin (r + 1) × ℕ) := S.filter (fun ik => recShift N ik = j₀) with hTdef
  obtain ⟨t, htT, htmax⟩ :=
    T.exists_max_image (fun ik => (ik.1 : ℕ)) ⟨w, Finset.mem_filter.mpr ⟨hwS, rfl⟩⟩
  have htS : t ∈ S := (Finset.mem_filter.mp htT).1
  have htshift : recShift N t = j₀ := (Finset.mem_filter.mp htT).2
  have htc : (p t.1).coeff t.2 ≠ 0 := ((hmemS t).mp htS).2
  have ht2 : t.2 ≤ N := ((hmemS t).mp htS).1
  have htF : t ∈ F := Finset.mem_filter.mpr ⟨mem_recPairs.mpr ht2, htshift⟩
  refine ⟨j₀, ?_, ?_⟩
  · have hw2 : w.2 ≤ N := ((hmemS w).mp hwS).1
    have hw1 : (w.1 : ℕ) < r + 1 := w.1.2
    simp only [hj₀, recShift, Finset.mem_range]
    omega
  · have hsplit : recCoeff p N j₀
        = C ((p t.1).coeff t.2) * ascPoly K (N - t.2 + 1) (t.1 : ℕ)
          + ∑ ik ∈ F.erase t, C ((p ik.1).coeff ik.2) * ascPoly K (N - ik.2 + 1) (ik.1 : ℕ) :=
      (Finset.add_sum_erase F _ htF).symm
    have hdeg_main : (C ((p t.1).coeff t.2) * ascPoly K (N - t.2 + 1) (t.1 : ℕ)).degree
        = ((t.1 : ℕ) : WithBot ℕ) := by
      rw [degree_mul, degree_C htc, ascPoly_degree, zero_add]
    have hdeg_rest : (∑ ik ∈ F.erase t, C ((p ik.1).coeff ik.2)
          * ascPoly K (N - ik.2 + 1) (ik.1 : ℕ)).degree < ((t.1 : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro ik hik
      obtain ⟨hik_ne, hikF⟩ := Finset.mem_erase.mp hik
      have hik2 : ik.2 ≤ N := mem_recPairs.mp (Finset.mem_filter.mp hikF).1
      have hikshift : recShift N ik = j₀ := (Finset.mem_filter.mp hikF).2
      by_cases hc : (p ik.1).coeff ik.2 = 0
      · simp only [hc, map_zero, zero_mul, degree_zero]
        exact WithBot.bot_lt_coe _
      · have hikT : ik ∈ T :=
          Finset.mem_filter.mpr ⟨(hmemS ik).mpr ⟨hik2, hc⟩, hikshift⟩
        have h1 : (ik.1 : ℕ) ≤ (t.1 : ℕ) := htmax ik hikT
        have h2 : (ik.1 : ℕ) ≠ (t.1 : ℕ) := by
          intro heq
          refine hik_ne (Prod.ext (Fin.val_injective heq) ?_)
          simp only [recShift] at hikshift htshift
          omega
        rw [degree_mul, degree_C hc, ascPoly_degree, zero_add]
        exact_mod_cast lt_of_le_of_ne h1 h2
    have hd : (recCoeff p N j₀).degree = ((t.1 : ℕ) : WithBot ℕ) := by
      rw [hsplit, degree_add_eq_left_of_degree_lt (by rw [hdeg_main]; exact hdeg_rest), hdeg_main]
    intro hzero
    rw [hzero, degree_zero] at hd
    exact WithBot.bot_ne_coe hd

end PRecursive

/-! ## §5. The theorem -/

section Assembly

variable {K : Type*} [Field K] [CharZero K]

/-- **[Sta80] Thm 2.1 + Thm 1.5**: the coefficient sequence of a power series algebraic over `K[X]`
satisfies a nontrivial linear recurrence with polynomial coefficients.

This is the unfolded form of `Stanley.pRecursive_of_isAlgebraic` (see `CITED.Stanley`), stated for
any field of characteristic zero. -/
@[category research solved, AMS 11 68 05, ref "Sta80", group "stanley_closure"]
theorem exists_polynomial_recurrence {f : PowerSeries K} (hf : IsAlgebraic K[X] f) :
    ∃ (s : ℕ) (Q : Fin (s + 1) → K[X]), (∃ j, Q j ≠ 0) ∧
      ∀ n : ℕ, ∑ j : Fin (s + 1), (Q j).eval (n : K) * PowerSeries.coeff (n + (j : ℕ)) f = 0 := by
  obtain ⟨r, p, hp, hode⟩ := exists_ode hf
  set N := Finset.univ.sup fun i => (p i).natDegree with hNdef
  have hN : ∀ i, (p i).natDegree ≤ N := fun i => by
    rw [hNdef]; exact Finset.le_sup (f := fun i => (p i).natDegree) (Finset.mem_univ i)
  refine ⟨N + r, fun j => recCoeff p N (j : ℕ), ?_, fun n => ?_⟩
  · obtain ⟨j, hjmem, hjne⟩ := exists_recCoeff_ne_zero hN hp
    exact ⟨⟨j, Finset.mem_range.mp hjmem⟩, hjne⟩
  · rw [Fin.sum_univ_eq_sum_range
      (fun j => (recCoeff p N j).eval (n : K) * PowerSeries.coeff (n + j) f) (N + r + 1)]
    exact sum_recCoeff_eq_zero hN hode n

end Assembly

end Stanley
