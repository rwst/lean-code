/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonFreeSplit
import Mathlib.RingTheory.PowerSeries.Expand
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Mahler data in the ambient field of §2.2

plan-formalize-AF17's **WP20**, first instalment of the second half of gap (6).

`AF.exists_lift_of_eventually_formVal_eq_zero` (WP19) consumes the Mahler system *in the ambient
field* `Ω` of [AF22] §2.2, in its `k₀`-th iterated form

  `f_i = ∑_j A_{k₀}(z)_{ij}·σ(f_j)`,   `σ` = the substitution `z ↦ z^{q^{k₀}}` on `Ω`,

and it needs `σ` as an honest ring endomorphism of `Ω`, because [AF22] (2.37) applies it to a whole
relation (`AF.relation_subst`).  The data the corpus starts from is an *analytic* system on a disc
together with power-series solutions.  This file is the passage between the two, and it is entirely
`std3`.

## The substitution exists, and the type synonym is what makes it exist

There is no substitution `z ↦ z^n` on an abstract algebraically closed field; it has to be built,
and the construction is the only place where the shape of `Ω` matters:

* on `K⟦z⟧` it is Mathlib's `PowerSeries.expand`;
* on `K⸨z⸩` it is that extended to the fraction field — `AF.laurentExpand`, by
  `IsFractionRing.lift`, which needs `PowerSeries.expand` to be injective (`AF.expand_injective`);
* on `Ω`, an algebraic closure of `K⸨z⸩`, it is the lift of the previous one along
  `IsAlgClosed.lift`.

That last step is where a subtlety sits.  `IsAlgClosed.lift` produces `S →ₐ[R] M` from *two*
`R`-algebra structures, one on the source and one on the target, and here they are the two
different structures on the same type `Ω` — the given one, and the one twisted by the substitution.
Two instances on one type is exactly what a type synonym is for: `AF.Twisted` carries the twisted
structure, is definitionally `Ω`, and `AF.ambientSubst` is the lift read back through it.

## What the substitution has to satisfy, and why each clause is needed

* `AF.ambientSubst_algebraMap` — it *is* the substitution on `K(z)`, i.e. `AF.substPowRat`.  This
  single equation gives the other two: constants are fixed (`AF.ambientSubst_ambC`, the hypothesis
  `hσC` of WP19), and elements algebraic over `K(z)` stay algebraic
  (`AF.isIntegral_of_ringHom_comp`, the hypothesis `hσint`) — the minimal polynomial is transported
  by `Polynomial.map`, and monicity survives.

## From the analytic system to the ambient one

[AF17]'s data is `AF.IsMahlerSolution` — an identity of functions on a disc — plus power series
summing to them.  `AF.isFormalMahlerSolution_of_isMahlerSolution` turns it into
`AF.IsFormalMahlerSolution`, by the uniqueness of Taylor coefficients already in the corpus
(`AF.eq_zero_of_isSumOnBall_zero`); the one new ingredient is that `z ↦ z^q` is compatible with
`PowerSeries.expand` on the analytic side (`AF.IsSumOnBall.expand`), for which `r ≤ 1` is what keeps
`z^q` in the disc.

`AF.isFormalMahlerSolution_iter` then iterates the system `k` times — this is [AF22] (2.1)'s
`A_k(z) = A(z)A(z^q)⋯A(z^{q^{k-1}})` on the solutions — and `AF.ambient_mahler_iter` reads the
result in `Ω`.  Only the iterated form is used downstream: §2.4 substitutes once, at the exponent
`q^{k₀}` chosen by Lemma 2.8.

## Contents

* `AF.expand_injective`, `AF.coe_expand`, `AF.laurentExpand` — the substitution on `K⸨z⸩`;
* `AF.Twisted`, **`AF.ambientSubst`**, `AF.ambientSubst_algebraMap`, `AF.ambientSubst_ambC`,
  `AF.isIntegral_ambientSubst` — the substitution on `Ω`;
* `AF.IsSumOnBall.expand`, **`AF.isFormalMahlerSolution_of_isMahlerSolution`** — analytic to formal;
* `AF.isFormalMahlerSolution_iter`, **`AF.ambient_mahler_iter`** — the iterated system, in `Ω`.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.2, (2.1), (2.6), (2.37).
* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* arXiv:1508.07158v2, (1.2).
* [AF17f] `plans/plan-formalize-AF17.html`: WP20, gap (6) of Stage 2, milestone M4.
-/

open Filter Topology

open scoped Polynomial LaurentSeries RatFunc nonZeroDivisors

namespace AF

/-! ## The substitution `z ↦ z^n` on Laurent series -/

section Laurent

variable (K : Type*) [Field K]

/-- **`PowerSeries.expand` is injective.**  The coefficients of `expand n f` at the multiples of
`n` are all of the coefficients of `f`.  This is what lets the substitution be extended to the
fraction field. -/
@[category API, AMS 13, ref "AF22", group "af_mahler_alternative"]
theorem expand_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (PowerSeries.expand (R := K) n hn) := by
  intro f g h
  ext m
  have hm := congrArg (PowerSeries.coeff (n * m)) h
  rwa [PowerSeries.coeff_expand, PowerSeries.coeff_expand, ite_eq_left ⟨m, rfl⟩, ite_eq_left ⟨m, rfl⟩,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)] at hm

variable {K}

/-- On polynomials the two substitutions agree: `AF.substPow` is `Polynomial.expand`, and
`PowerSeries.expand` extends it. -/
@[category API, AMS 13, ref "AF22", group "af_mahler_alternative"]
theorem coe_expand {n : ℕ} (hn : n ≠ 0) (p : K[X]) :
    PowerSeries.expand n hn (p : PowerSeries K) = ((substPow K n p : K[X]) : PowerSeries K) := by
  ext m
  simp only [substPow_eq_expand, PowerSeries.coeff_expand, Polynomial.coeff_coe,
    Polynomial.coeff_expand (Nat.pos_of_ne_zero hn)]

variable (K)

/-- **The substitution `z ↦ z^n` on `K⸨z⸩`**, the fraction field of `K⟦z⟧`. -/
@[category API, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def laurentExpand {n : ℕ} (hn : n ≠ 0) : LaurentSeries K →+* LaurentSeries K :=
  IsFractionRing.lift (A := PowerSeries K) (K := LaurentSeries K) (L := LaurentSeries K)
    (g := (algebraMap (PowerSeries K) (LaurentSeries K)).comp
      (PowerSeries.expand n hn).toRingHom)
    (fun _ _ h => expand_injective K hn
      ((IsFractionRing.injective (PowerSeries K) (LaurentSeries K)) h))

variable {K}

@[category API, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem laurentExpand_coe {n : ℕ} (hn : n ≠ 0) (f : PowerSeries K) :
    laurentExpand K hn (algebraMap (PowerSeries K) (LaurentSeries K) f)
      = algebraMap (PowerSeries K) (LaurentSeries K) (PowerSeries.expand n hn f) :=
  IsFractionRing.lift_algebraMap _ f

/-- A polynomial, read in `K⸨z⸩` through `K(z)`, is its own image as a power series. -/
@[category API, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem algebraMap_ratFunc_laurent (p : K[X]) :
    algebraMap (RatFunc K) (LaurentSeries K) (algebraMap K[X] (RatFunc K) p)
      = algebraMap (PowerSeries K) (LaurentSeries K) (p : PowerSeries K) := by
  rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) (LaurentSeries K)]
  rfl

/-- **The substitution on `K⸨z⸩` restricts to `AF.substPowRat` on `K(z)`.**  Both sides are ring
homomorphisms out of the localization `K(z)` of `K[z]`, so it is enough to check it on `K[z]`. -/
@[category research solved, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem laurentExpand_ratFunc {n : ℕ} (hn : 0 < n) (c : RatFunc K) :
    laurentExpand K hn.ne' (algebraMap (RatFunc K) (LaurentSeries K) c)
      = algebraMap (RatFunc K) (LaurentSeries K) (substPowRat K hn c) := by
  have key : (laurentExpand K hn.ne').comp (algebraMap (RatFunc K) (LaurentSeries K))
      = (algebraMap (RatFunc K) (LaurentSeries K)).comp (substPowRat K hn) := by
    refine IsLocalization.ringHom_ext (K[X])⁰ (RingHom.ext fun p => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      algebraMap_ratFunc_laurent, laurentExpand_coe, coe_expand, substPowRat_algebraMap,
      algebraMap_ratFunc_laurent]
  exact DFunLike.congr_fun key c

end Laurent

/-! ## Integrality survives a substitution -/

section Integral

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- **A ring endomorphism of `Ω` compatible with one of the base field preserves integrality.**
If `σ` restricts to `ρ` on `F`, then a monic vanishing polynomial for `x` is carried by
`Polynomial.map ρ` to one for `σ x` — this is WP19's hypothesis `hσint`, for which no more than
this is needed. -/
@[category research solved, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem isIntegral_of_ringHom_comp {σ : Ω →+* Ω} {ρ : F →+* F}
    (hσ : ∀ c : F, σ (algebraMap F Ω c) = algebraMap F Ω (ρ c)) {x : Ω}
    (hx : IsIntegral F x) : IsIntegral F (σ x) := by
  obtain ⟨p, hpm, hp⟩ := hx
  refine ⟨p.map ρ, hpm.map ρ, ?_⟩
  have h := congrArg σ hp
  rw [map_zero, Polynomial.hom_eval₂] at h
  rwa [Polynomial.eval₂_map, show (algebraMap F Ω).comp ρ = σ.comp (algebraMap F Ω) from
    RingHom.ext fun c => (hσ c).symm]

end Integral

/-! ## The substitution on the ambient field -/

section Ambient

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω]

/-- **`Ω` with its `K⸨z⸩`-algebra structure twisted by the substitution.**  `IsAlgClosed.lift`
needs two algebra structures over the same base, one on the source and one on the target; they are
here two structures on one type, so one of them has to be carried by a synonym. -/
@[category API, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
def Twisted (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra (LaurentSeries K) Ω]
    {n : ℕ} (_ : n ≠ 0) : Type _ := Ω

variable [Algebra (LaurentSeries K) Ω]

noncomputable instance {n : ℕ} (hn : n ≠ 0) : Field (Twisted K Ω hn) := ‹Field Ω›

noncomputable instance {n : ℕ} (hn : n ≠ 0) [IsAlgClosed Ω] : IsAlgClosed (Twisted K Ω hn) :=
  ‹IsAlgClosed Ω›

noncomputable instance {n : ℕ} (hn : n ≠ 0) : Algebra (LaurentSeries K) (Twisted K Ω hn) :=
  ((algebraMap (LaurentSeries K) Ω).comp (laurentExpand K hn)).toAlgebra

variable [IsAlgClosed Ω] [Algebra.IsAlgebraic (LaurentSeries K) Ω]

/-- **The substitution `z ↦ z^n` on the ambient field** ([AF22] §2.2's `A`, here any algebraically
closed algebraic extension of `K⸨z⸩`).  It exists because `Ω` is algebraic over `K⸨z⸩` and
algebraically closed, so `IsAlgClosed.lift` extends the substitution of `AF.laurentExpand` — the
target being `Ω` with the twisted structure. -/
@[category research solved, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def ambientSubst (K : Type*) [Field K] {Ω : Type*} [Field Ω]
    [Algebra (LaurentSeries K) Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic (LaurentSeries K) Ω]
    {n : ℕ} (hn : n ≠ 0) : Ω →+* Ω :=
  (IsAlgClosed.lift (R := LaurentSeries K) (S := Ω) (M := Twisted K Ω hn)).toRingHom

@[category API, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem ambientSubst_algebraMap {n : ℕ} (hn : n ≠ 0) (x : LaurentSeries K) :
    ambientSubst K (Ω := Ω) hn (algebraMap (LaurentSeries K) Ω x)
      = algebraMap (LaurentSeries K) Ω (laurentExpand K hn x) :=
  (IsAlgClosed.lift (R := LaurentSeries K) (S := Ω) (M := Twisted K Ω hn)).commutes x

variable [Algebra (RatFunc K) Ω] [IsScalarTower (RatFunc K) (LaurentSeries K) Ω]

/-- **The substitution restricts to `AF.substPowRat` on `K(z)`** — the one equation the assembly
uses, `AF.laurentExpand_ratFunc` read in `Ω`. -/
@[category research solved, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem ambientSubst_ratFunc {n : ℕ} (hn : 0 < n) (c : RatFunc K) :
    ambientSubst K (Ω := Ω) hn.ne' (algebraMap (RatFunc K) Ω c)
      = algebraMap (RatFunc K) Ω (substPowRat K hn c) := by
  rw [IsScalarTower.algebraMap_apply (RatFunc K) (LaurentSeries K) Ω,
    IsScalarTower.algebraMap_apply (RatFunc K) (LaurentSeries K) Ω, ambientSubst_algebraMap,
    laurentExpand_ratFunc]

/-- The substitution fixes the constants — WP19's hypothesis `hσC`. -/
@[category research solved, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem ambientSubst_ambC {n : ℕ} (hn : 0 < n) (a : K) :
    ambientSubst K (Ω := Ω) hn.ne' (ambC K Ω a) = ambC K Ω a := by
  rw [ambC, RingHom.comp_apply, toAmbient_apply, ambientSubst_ratFunc hn,
    substPowRat_algebraMap, substPow_eq_expand, Polynomial.expand_C]

/-- Elements algebraic over `K(z)` stay algebraic under the substitution — WP19's `hσint`. -/
@[category research solved, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem isIntegral_ambientSubst {n : ℕ} (hn : 0 < n) {x : Ω} (hx : IsIntegral (RatFunc K) x) :
    IsIntegral (RatFunc K) (ambientSubst K (Ω := Ω) hn.ne' x) :=
  isIntegral_of_ringHom_comp (ambientSubst_ratFunc hn) hx

end Ambient

/-! ## From the analytic Mahler system to the formal one -/

section Formal

variable {K : Type*} [Field K] {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Algebra K 𝕜]

/-- **`PowerSeries.expand` on the analytic side.**  If `H` is the sum of `f` on the disc of radius
`r ≤ 1`, then `z ↦ H (z^n)` is the sum of `expand n f` there — the disc being stable under
`z ↦ z^n` is exactly what `r ≤ 1` buys. -/
@[category research solved, AMS 30 40, ref "AF17", group "af_mahler_alternative"]
theorem IsSumOnBall.expand {r : ℝ} (hr1 : r ≤ 1) {f : PowerSeries K} {H : 𝕜 → 𝕜}
    (h : IsSumOnBall r f H) {n : ℕ} (hn : n ≠ 0) :
    IsSumOnBall r (PowerSeries.expand n hn f) (fun z => H (z ^ n)) := by
  intro z hz
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hzn : ‖z ^ n‖ < r := by
    rw [norm_pow]
    rcases eq_or_lt_of_le (norm_nonneg z) with h0 | h0
    · rw [← h0, zero_pow hn]
      exact lt_of_le_of_lt (le_of_eq rfl) (by rw [← h0] at hz; exact hz)
    · calc ‖z‖ ^ n ≤ ‖z‖ ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg z) (le_trans hz.le hr1) hn0
        _ = ‖z‖ := pow_one _
        _ < r := hz
  have hinj : Function.Injective (fun m : ℕ => n * m) := fun a b hab => by
    simpa [Nat.mul_left_cancel_iff hn0] using hab
  have hzero : ∀ m : ℕ, m ∉ Set.range (fun k : ℕ => n * k) →
      algebraMap K 𝕜 (PowerSeries.coeff m (PowerSeries.expand n hn f)) * z ^ m = 0 := by
    intro m hm
    have hnd : ¬ n ∣ m := fun ⟨c, hc⟩ => hm ⟨c, hc.symm⟩
    rw [PowerSeries.coeff_expand, ite_eq_right hnd, map_zero, zero_mul]
  rw [← hinj.hasSum_iff hzero]
  have he : ((fun m => algebraMap K 𝕜 (PowerSeries.coeff m (PowerSeries.expand n hn f)) * z ^ m) ∘
      fun k : ℕ => n * k)
      = fun k => algebraMap K 𝕜 (PowerSeries.coeff k f) * (z ^ n) ^ k := by
    funext k
    rw [Function.comp_apply, PowerSeries.coeff_expand, ite_eq_left ⟨k, rfl⟩,
      Nat.mul_div_cancel_left _ hn0, ← pow_mul]
  rw [he]
  exact h (z ^ n) hzn

/-- The formal shadow of a function on a disc is unique. -/
@[category API, AMS 30 40, ref "AF17", group "af_mahler_alternative"]
theorem IsSumOnBall.unique {r : ℝ} (hr : 0 < r) {g₁ g₂ : PowerSeries K} {H : 𝕜 → 𝕜}
    (h₁ : IsSumOnBall r g₁ H) (h₂ : IsSumOnBall r g₂ H) : g₁ = g₂ := by
  have h : IsSumOnBall (𝕜 := 𝕜) r (g₁ - g₂) (fun _ => 0) := by
    intro z hz
    have hs := (h₁ z hz).sub (h₂ z hz)
    rw [sub_self] at hs
    simpa only [map_sub, sub_mul] using hs
  exact sub_eq_zero.1 (eq_zero_of_isSumOnBall_zero hr h)

@[category API, AMS 13, ref "AF22", group "af_mahler_alternative"]
theorem substPowSeries_eq_expand {q : ℕ} (hq0 : q ≠ 0) (g : PowerSeries K) :
    substPowSeries q g = PowerSeries.expand q hq0 g := by
  ext m
  rw [substPowSeries, PowerSeries.coeff_mk, PowerSeries.coeff_expand]

variable {ι : Type*} [Fintype ι]

/-- **The analytic Mahler system is the formal one.**  The two sides have the same sum on the disc,
so they are the same power series — the uniqueness of Taylor coefficients that
`AF.relation_formal_of_functional` uses, applied to the system itself rather than to a lifted
relation.  `r ≤ 1` enters only through `AF.IsSumOnBall.expand`. -/
@[category research solved, AMS 11 30 39, ref "AF17", group "af_mahler_alternative"]
theorem isFormalMahlerSolution_of_isMahlerSolution {q : ℕ} (hq0 : q ≠ 0) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) {A : Matrix ι ι K[X]} {F : ι → 𝕜 → 𝕜}
    (hF : IsMahlerSolution q A F (Metric.ball 0 r)) {f : ι → PowerSeries K}
    (hf : ∀ i, IsSumOnBall r (f i) (F i)) : IsFormalMahlerSolution q A f := by
  intro i
  have hsub : ∀ j, IsSumOnBall (𝕜 := 𝕜) r (substPowSeries q (f j)) (fun z => F j (z ^ q)) := by
    intro j
    rw [substPowSeries_eq_expand hq0]
    exact (hf j).expand hr1 hq0
  refine IsSumOnBall.unique hr0 (hf i) fun z hz => ?_
  have h1 := IsSumOnBall.finsetSum (𝕜 := 𝕜) (r := r) Finset.univ
    (fun j _ => (hsub j).polyMul (A i j)) z hz
  rw [hF z (by simpa only [Metric.mem_ball, dist_zero_right] using hz) i]
  exact h1

end Formal

/-! ## The iterated system, formally and in the ambient field -/

section Iterate

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] (2.1) on the solutions**: iterating `f = A(z)f(z^q)` gives `f = A_k(z)f(z^{q^k})`,
with `A_k` the corpus's `AF.iterMatrix`.  This is the shape [AF22] §2.4 substitutes into, at the
`k₀` produced by Lemma 2.8. -/
@[category research solved, AMS 11 13 39, ref "AF22", group "af_mahler_alternative"]
theorem isFormalMahlerSolution_iter {q : ℕ} (hq0 : q ≠ 0) {A : Matrix ι ι K[X]}
    {f : ι → PowerSeries K} (hF : IsFormalMahlerSolution q A f) (k : ℕ) (i : ι) :
    f i = ∑ j, ((iterMatrix q A k i j : K[X]) : PowerSeries K) *
      PowerSeries.expand (q ^ k) (pow_ne_zero k hq0) (f j) := by
  induction k generalizing i with
  | zero =>
      have h1 : ∀ j, PowerSeries.expand (q ^ 0) (pow_ne_zero 0 hq0) (f j) = f j :=
        fun j => PowerSeries.expand_one_apply (f j)
      rw [Finset.sum_eq_single i]
      · rw [h1, iterMatrix_zero, Matrix.one_apply_eq, Polynomial.coe_one, one_mul]
      · intro j _ hj
        rw [iterMatrix_zero, Matrix.one_apply_ne (Ne.symm hj), Polynomial.coe_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
  | succ k ih =>
      have hqk : q ^ k ≠ 0 := pow_ne_zero k hq0
      have hcast : ∀ (m m' : ℕ) (hm : m ≠ 0) (hm' : m' ≠ 0), m = m' →
          ∀ x : PowerSeries K, PowerSeries.expand m hm x = PowerSeries.expand m' hm' x := by
        rintro m m' hm hm' rfl x
        rfl
      have hexpmul : ∀ x : PowerSeries K,
          PowerSeries.expand q hq0 (PowerSeries.expand (q ^ k) hqk x)
            = PowerSeries.expand (q ^ (k + 1)) (pow_ne_zero (k + 1) hq0) x := by
        intro x
        rw [← PowerSeries.expand_mul q hq0 (q ^ k) hqk x]
        exact hcast _ _ _ _ (by rw [pow_succ]; ring) x
      have hstep : ∀ j, PowerSeries.expand q hq0 (f j)
          = ∑ l, ((substPow K q (iterMatrix q A k j l) : K[X]) : PowerSeries K) *
              PowerSeries.expand (q ^ (k + 1)) (pow_ne_zero (k + 1) hq0) (f l) := by
        intro j
        rw [ih j, map_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [map_mul, coe_expand, hexpmul]
      rw [hF i]
      calc ∑ j, ((A i j : K[X]) : PowerSeries K) * substPowSeries q (f j)
          = ∑ j, ∑ l, (((A i j * substPow K q (iterMatrix q A k j l) : K[X])) : PowerSeries K) *
              PowerSeries.expand (q ^ (k + 1)) (pow_ne_zero (k + 1) hq0) (f l) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [substPowSeries_eq_expand hq0, hstep j, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by rw [Polynomial.coe_mul, mul_assoc]
        _ = ∑ l, ((iterMatrix q A (k + 1) i l : K[X]) : PowerSeries K) *
              PowerSeries.expand (q ^ (k + 1)) (pow_ne_zero (k + 1) hq0) (f l) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [← Finset.sum_mul]
            congr 1
            rw [iterMatrix_succ, Matrix.mul_apply,
              ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
            exact Finset.sum_congr rfl fun j _ => by
              rw [Polynomial.coeToPowerSeries.ringHom_apply, Matrix.map_apply]

variable {Ω : Type*} [Field Ω] [Algebra (LaurentSeries K) Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic (LaurentSeries K) Ω] [Algebra (RatFunc K) Ω]
  [IsScalarTower (RatFunc K) (LaurentSeries K) Ω]

/-- The solutions, read in the ambient field of [AF22] §2.2. -/
@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def toAmbientSeries (K : Type*) [Field K] (Ω : Type*) [Field Ω]
    [Algebra (LaurentSeries K) Ω] : PowerSeries K →+* Ω :=
  (algebraMap (LaurentSeries K) Ω).comp (algebraMap (PowerSeries K) (LaurentSeries K))

omit [IsAlgClosed Ω] [Algebra.IsAlgebraic (LaurentSeries K) Ω] [Algebra (RatFunc K) Ω]
  [IsScalarTower (RatFunc K) (LaurentSeries K) Ω] in
/-- The solutions keep their identity there: `K⟦z⟧ → K⸨z⸩ → Ω` is injective. -/
@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem toAmbientSeries_injective : Function.Injective (toAmbientSeries K Ω) :=
  (algebraMap (LaurentSeries K) Ω).injective.comp
    (IsFractionRing.injective (PowerSeries K) (LaurentSeries K))

omit [IsAlgClosed Ω] [Algebra.IsAlgebraic (LaurentSeries K) Ω] in
@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem toAmbientSeries_poly (p : K[X]) :
    toAmbientSeries K Ω (p : PowerSeries K) = toAmbient K Ω p := by
  rw [toAmbientSeries, RingHom.comp_apply, toAmbient_apply,
    IsScalarTower.algebraMap_apply (RatFunc K) (LaurentSeries K) Ω, algebraMap_ratFunc_laurent]

/-- **[AF22] (2.6) in the ambient field**, in its `k`-th iterated form: the shape WP19's
`AF.exists_lift_of_eventually_formVal_eq_zero` consumes as its hypothesis `hf`. -/
@[category research solved, AMS 11 12 13 39, ref "AF22", group "af_mahler_alternative"]
theorem ambient_mahler_iter {q : ℕ} (hq0 : q ≠ 0) {A : Matrix ι ι K[X]}
    {f : ι → PowerSeries K} (hF : IsFormalMahlerSolution q A f) (k : ℕ) (i : ι) :
    toAmbientSeries K Ω (f i) = ∑ j, toAmbient K Ω (iterMatrix q A k i j) *
      ambientSubst K (Ω := Ω) (pow_ne_zero k hq0) (toAmbientSeries K Ω (f j)) := by
  have hsub : ∀ g : PowerSeries K, ambientSubst K (Ω := Ω) (pow_ne_zero k hq0)
      (toAmbientSeries K Ω g)
      = toAmbientSeries K Ω (PowerSeries.expand (q ^ k) (pow_ne_zero k hq0) g) := by
    intro g
    simp only [toAmbientSeries, RingHom.comp_apply]
    rw [ambientSubst_algebraMap, laurentExpand_coe]
  rw [isFormalMahlerSolution_iter hq0 hF k i, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hsub, toAmbientSeries_poly]

end Iterate

end AF
