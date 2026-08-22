/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.MahlerSystem
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Tactic.NormNum
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Regular points of a Mahler system: `2/3`, and the inverse-integrality criterion
(plan-B1E2 WP10/T2, plan-B1E2b WP7, WP8)

**If `σ(·,0)` is a permutation of the kernel, then `2/3` and every `(2/3)^{k^m}` is a *regular*
point of the Mahler system** — `det M` does not vanish there (`regular_two_thirds`) — and more
generally **every point whose inverse is not an algebraic integer is regular**
(`regular_of_not_isIntegral_inv`), a criterion that is sharp
(`singular_sqrt_two_inv_example`).  WP8 then removes the hypothesis on `σ` altogether:
**a point is regular as soon as the constant term of its primitive minimal polynomial fails to
divide the lowest nonzero coefficient of `det M`** (`regular_of_not_dvd_lowest_coeff`).

Unconditional, elementary, and of independent interest: [AF17] stress that *no* condition in the
literature rules out the exceptional branch of their Cor 1.8, and this is a checkable sufficient
condition at rational points.

## The lever

The whole proof is three lines of mathematics, and it turns on our point being **rational**:

1. `M(0) = P₀` (`RB.mahlerMatrix_map_eval_zero`), so if `σ(·,0)` is a permutation then `M(0)` is
   a permutation matrix and **`det M(0) = ±1`** (`det_eval_zero_eq_pm_one`).
2. `det M ∈ ℤ[z]`, so `det M(0) = ±1` *is* its constant coefficient.
3. **Rational-root theorem**: a rational root of an integer polynomial has numerator dividing the
   constant coefficient. Dividing `±1` forces numerator `±1`. But `(2/3)^N = 2^N/3^N` has
   numerator `2^N ≥ 2` for `N ≥ 1`. ∎ (`not_root_of_coeff_zero_pm_one`)

Since `k^m ≥ 1` for every `m ≥ 0` whenever `k ≥ 1`, **all** the iterates `(2/3)^{k^m}` are covered
at once — including `m = 0`, i.e. `2/3` itself.

## The general form of the lever, and how far it reaches ([B1E2b] WP7)

The rational-root theorem says nothing at algebraic irrationals, but the *lever* does, once it is
stated correctly.  `det M(0) = ±1` is a statement about the constant coefficient, and reversing
coefficients turns it into a statement about the **leading** coefficient:

  **`inv_isIntegral_of_root_of_coeff_zero_pm_one`** — if `P ∈ ℤ[X]` has `P(0) = ±1` then `±P.reverse`
  is *monic*, so for every nonzero root `α` of `P` the inverse `α⁻¹` is an **algebraic integer**.

Contraposed, that is the criterion `regular_of_not_isIntegral_inv`: *`α⁻¹ ∉ 𝒪 ⇒ α` is regular*,
with the iterates `α^N` free by integral closure (`regular_of_not_isIntegral_inv_pow`).  At
`α = (2/3)^N` it reproduces `regular_two_thirds` (`(3/2)^N` is not an integer); the specialised
rational-root proof is kept because it is shorter, not because it is needed.

**The criterion is sharp, and the natural strengthening is false.**  It is tempting to conclude
that every root of `det M` is an algebraic *unit* — `α` and `α⁻¹` both integral.  That is **not**
true, and `singular_sqrt_two_inv_example` is a counterexample inside the very class the lever
covers: `k = 3`, `σ(0,·) = (0,0,1)`, `σ(1,·) = (1,2,0)`, `σ(2,·) = (2,1,1)`, whose `σ(·,0)` is the
identity and whose determinant is

  `det M(z) = 1 + z − z² − 2z³ − 2z⁴ = −(2z² − 1)(z² + z + 1)`.

Its root `α = 1/√2` is singular, `α⁻¹ = √2` is an algebraic integer (as the criterion promises),
and `α` itself is **not** one.  So `regular_of_not_isIntegral_inv` cannot be improved to
"non-integral points are regular": the room in which non-units live is the *leading* coefficient
of `det M`, which the permutation hypothesis does not constrain.

Two things still lie outside: `φ` and its `3ˡ`-th roots ([AF17] §8.1's counterexample, where `φ⁻¹`
*is* an algebraic integer, so the criterion is silent — as it must be), and points `1/b` for
algebraic integers `b`.  In particular **plan-B1E2's E.2 case 2, whose evaluation point `1/σβ` is
an algebraic irrational, does not automatically inherit regularity** ([B1E2] §5); the criterion
turns that into a concrete, checkable question about `(σβ)` rather than an open-ended one.

## Dropping the hypothesis: the lowest coefficient ([B1E2b] WP8)

Both levers above read `det M` at `0`, so both die when `det M(0) = 0` — and `det M(0) = 0`
happens exactly when `σ(·,0)` is not injective, i.e. off WP7's hypothesis.  **Deflation** repairs
this without any hypothesis at all.  Write

  `det M = z^e · D₁`,   `e = (det M).natTrailingDegree`,   `c = D₁(0) = (det M).trailingCoeff`,

the *lowest nonzero* coefficient (`exists_deflation`).  A nonzero root of `det M` is a root of
`D₁` (`exists_deflation_of_aeval_eq_zero`), and the divisibility tests then run against `c`:

* rational `α`: `α.num ∣ c` (`num_dvd_trailingCoeff_of_aeval_eq_zero`) — the checkable form, two
  integers computed from `σ`;
* algebraic `α` with primitive minimal polynomial `P`: `P(0) ∣ c`
  (`coeff_zero_dvd_trailingCoeff_of_aeval_eq_zero`), by Gauss's lemma in annihilator form
  (`dvd_of_isPrimitive_irreducible`).

Contrapositives: `regular_of_not_dvd_lowest_coeff` and `regular_of_not_dvd_lowest_coeff_rat`.  The
plan's non-degeneracy hypothesis `det M ≠ 0` is **not needed** — `det M = 0` gives `c = 0`, and
everything divides `0`, so the divisibility hypothesis already excludes it.

WP7 is the special case `c = ±1` (`trailingCoeff_det_eq_pm_one_of_perm`), and `±1` is used only
through its *parity*: an odd `c` alone gives back all of `regular_two_thirds`
(`regular_two_thirds_of_odd_lowest_coeff`), since the numerator `2^{k^m}` is even.  The refinement
is not vacuous: `nonPermSigma` (`k = 2`, both states decimating to state `0`) has
`det M = z(1+z)`, so `det M(0) = 0` and WP7 says nothing, while `c = 1` makes every `(2/3)^{2^m}`
regular (`regular_two_thirds_nonPermSigma`).

### What the row-sum factor is for (review item F7c)

`(1 + z + ⋯ + z^{k-1}) ∣ det M` (`RB.rowSum_dvd_det`) is now proved, and it justifies the shape of
the hypothesis: for `k ≥ 2` every Mahler determinant *has* singular points — all `k`-th roots of
unity except `1` (`aeval_det_eq_zero_of_pow_eq_one`) — so `det M ≠ 0` is the strongest
non-degeneracy available.  Those forced singularities are harmless: the factor is `≥ 1` at every
`α ≥ 0` (`aeval_rowSum_pos`), so it is never the reason a positive rational is singular.

**Refuted:** the plan's claim that the factor forces `det M(1) = 0`.  `z = 1` is the one `k`-th
root of unity where `1 + z + ⋯ + z^{k-1} = k ≠ 0`.  The WP7 sharpness system is a counterexample
with `σ(·,0)` even a permutation — `det M(1) = -3` (`eval_one_det_sharpSigma`,
`exists_det_eval_one_ne_zero`) — and so is [AF17] §8.1's own `det A = (1+z-z²)(1+z+z²)`, where
`det A(1) = 3`.

## Status of the debt this discharges

Rev. 1 of [B1E2] filed regularity as "known technical debt … one hard sub-lemma". Gate 0 showed
it was the *whole* difference between Track I working and not. It is now a theorem in the main
case, and an exhaustive search (all systems with `k ∈ {2,3}`, `d ∈ {2,3,4}`, `m < 4`) found
**zero** genuine singularities at `(2/3)^{k^m}`: 39130 systems have `det M((2/3)^{k^m}) = 0`, but
every one of them has `det M ≡ 0` — degenerate, every point singular, `2/3` not special — and
none has `det P₀ ≠ 0`, confirming the lever. **So Track I is blocked on exactly one input: the
`p`-adic port (WP5), which does not exist in the literature.** Regularity is *not* the blocker.

## Contents

* **`RB.not_root_of_coeff_zero_pm_one`** — the arithmetic core: an integer polynomial with
  constant coefficient `±1` has no root `(2/3)^N`, `N ≥ 1`.
* **`RB.det_eval_zero_eq_pm_one`** — `σ(·,0)` a permutation ⇒ `det M(0) = ±1`.
* **`RB.regular_two_thirds`** — the regularity lemma (T2).
* **`RB.inv_isIntegral_of_root_of_coeff_zero_pm_one`** — the general lever: roots have integral
  inverses.
* **`RB.regular_of_not_isIntegral_inv`**, `RB.regular_of_not_isIntegral_inv_pow` — the criterion,
  and its iterates.
* `RB.sharpSigma`, `RB.det_mahlerMatrix_sharpSigma`, `RB.aeval_det_sharpSigma_inv_sqrt_two`,
  `RB.not_isIntegral_inv_sqrt_two`, **`RB.singular_sqrt_two_inv_example`** — the sharpness system.
* `RB.exists_deflation`, `RB.exists_deflation_of_aeval_eq_zero` — the `X^e` split (ForMathlib
  candidates); `RB.dvd_of_isPrimitive_irreducible` — Gauss in annihilator form.
* `RB.num_dvd_trailingCoeff_of_aeval_eq_zero`,
  `RB.coeff_zero_dvd_trailingCoeff_of_aeval_eq_zero` — the divisibility tests.
* **`RB.regular_of_not_dvd_lowest_coeff`**, `RB.regular_of_not_dvd_lowest_coeff_rat`,
  `RB.regular_two_thirds_of_odd_lowest_coeff` — the hypothesis-free criterion (WP8), and
  `RB.trailingCoeff_det_eq_pm_one_of_perm` placing WP7 inside it.
* `RB.nonPermSigma`, `RB.eval_zero_det_nonPermSigma`, **`RB.regular_two_thirds_nonPermSigma`** —
  a system with `det M(0) = 0` that WP8 decides and WP7 cannot.
* `RB.aeval_det_eq_zero_of_pow_eq_one`, `RB.aeval_rowSum_pos`, `RB.eval_one_det_sharpSigma`,
  **`RB.exists_det_eval_one_ne_zero`** — the job of the row-sum factor, and the refutation of
  "`det M(1) = 0`".

## References

* [AF17] Adamczewski, Faverjon. *Méthode de Mahler …* Proc. LMS **115** (2017), 55–90.  (Thm 1.4
  = the regular-point transcendence theorem this feeds; §8.1 = the counterexample, at algebraic
  *irrationals*.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.2 (this lemma, worked out), §5 (why E.2
  does not inherit it), WP10.
* [B1E2b] `plans/plan-B1E2b.html` (2026-07-28): WP7 (the criterion and its sharpness; the
  "every singular point is a unit" claim it refutes), WP8 = review items B7 and F7c (the
  hypothesis-free refinement, and the job of the row-sum factor).
-/

namespace RB

open Polynomial

/-! ## The arithmetic core -/

/-- **The rational-root lever** ([B1E2] §0.2(4)): an integer polynomial whose constant
coefficient is `±1` has no root of the form `(2/3)^N` with `N ≥ 1`.

The numerator of `(2/3)^N` is `2^N`, which would have to divide `±1`. -/
@[category research solved, AMS 11 68, ref "B1E2", group "rb_mahler_system"]
theorem not_root_of_coeff_zero_pm_one {P : Polynomial ℤ} (hP : P.coeff 0 = 1 ∨ P.coeff 0 = -1)
    {N : ℕ} (hN : 0 < N) : ¬ (Polynomial.aeval ((2 / 3 : ℚ) ^ N) P = 0) := by
  intro hroot
  have h1 : IsFractionRing.num ℤ ((2 / 3 : ℚ) ^ N) ∣ P.coeff 0 := num_dvd_of_is_root hroot
  have h2 : Associated (IsFractionRing.num ℤ ((2 / 3 : ℚ) ^ N) : ℤ) (((2 / 3 : ℚ) ^ N).num) :=
    Rat.isFractionRingNum _
  have h3 : ((2 / 3 : ℚ) ^ N).num ∣ P.coeff 0 := (h2.dvd_iff_dvd_left).mp h1
  have hnum : ((2 / 3 : ℚ) ^ N).num = 2 ^ N := by
    rw [Rat.num_pow]
    norm_num [Rat.num]
  rw [hnum] at h3
  have h2N : (2 : ℤ) ^ N ∣ 1 := by
    rcases hP with h | h
    · rwa [h] at h3
    · rw [h] at h3; exact dvd_neg.mp h3
  have hle := Int.le_of_dvd one_pos h2N
  have h2le : (2 : ℤ) ≤ 2 ^ N := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  omega

/-! ## `det M(0) = ±1` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The lever's hypothesis, discharged** ([B1E2] §0.2(2)+(4)): if `σ(·,0)` is a permutation of
the index set, then `M(0)` is its permutation matrix, so `det M(0) = sign = ±1`.

(The plan reaches this via the permutation expansion of `det M` — §0.2(3), "the all-zeros tuple
contributes `z⁰` with coefficient `±1`".  Going through `M(0) = P₀` is the same fact and is
shorter in Lean, so the expansion is not formalized separately.) -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2", group "rb_mahler_system"]
lemma det_eval_zero_eq_pm_one (k : ℕ) (hk : 0 < k) (σ : ι → Fin k → ι)
    (e : Equiv.Perm ι) (he : ∀ i, e i = σ i ⟨0, hk⟩) :
    (mahlerMatrix k σ).det.eval 0 = 1 ∨ (mahlerMatrix k σ).det.eval 0 = -1 := by
  have hmap : (Polynomial.evalRingHom 0).mapMatrix (mahlerMatrix k σ) = e.permMatrix ℤ := by
    have h1 : (Polynomial.evalRingHom (0 : ℤ)).mapMatrix (mahlerMatrix k σ)
        = (mahlerMatrix k σ).map (Polynomial.eval 0) := rfl
    rw [h1, mahlerMatrix_map_eval_zero k hk σ]
    ext i j
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, he i]
  have hdet : (mahlerMatrix k σ).det.eval 0 = (e.permMatrix ℤ).det := by
    have h := RingHom.map_det (Polynomial.evalRingHom (0 : ℤ)) (mahlerMatrix k σ)
    rw [hmap] at h
    exact h
  rw [hdet, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]

/-! ## The regularity lemma -/

/-- **T2 — the regularity lemma** ([B1E2] §0.2): if `σ(·,0)` is a permutation of the index set,
then **`2/3` is a regular point**: `det M` vanishes at none of the iterates `(2/3)^{k^m}`.

All iterates are covered at once, `m = 0` (i.e. `2/3` itself) included, because `k^m ≥ 1`.

Unconditional and elementary. It works *because* the point is rational; see the module doc for
where it stops. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2", group "rb_mahler_system"]
theorem regular_two_thirds (k : ℕ) (hk : 0 < k) (σ : ι → Fin k → ι)
    (e : Equiv.Perm ι) (he : ∀ i, e i = σ i ⟨0, hk⟩) (m : ℕ) :
    Polynomial.aeval ((2 / 3 : ℚ) ^ (k ^ m)) (mahlerMatrix k σ).det ≠ 0 := by
  refine not_root_of_coeff_zero_pm_one ?_ (pow_pos hk m)
  simpa [Polynomial.coeff_zero_eq_eval_zero] using det_eval_zero_eq_pm_one k hk σ e he

/-! ## The general criterion: inverse-integrality ([B1E2b] WP7) -/

/-- **The inverse-integrality lever** ([B1E2b] WP7): if an integer polynomial has constant
coefficient `±1`, then the *inverse* of every nonzero root is an **algebraic integer**.

Reversing the coefficients turns `P` into `±P.reverse`, whose leading coefficient is `P.coeff 0`,
i.e. `±1`; so `±P.reverse` is monic, and `α⁻¹` is one of its roots
(`Polynomial.eval₂_reverse_eq_zero_iff`).

This is the correct general form of the rational-root lever above: at `α = (2/3)^N` it says
`(3/2)^N` is an algebraic integer, which is false, recovering `not_root_of_coeff_zero_pm_one`.
Unlike that lever it also bites at *irrational* `α` — which is where [AF17] §8.1's counterexample
lives.  It does **not** say the roots are algebraic units; see `singular_sqrt_two_inv_example`. -/
@[category research solved, AMS 11 68 12, ref "B1E2b", group "rb_mahler_system"]
theorem inv_isIntegral_of_root_of_coeff_zero_pm_one {K : Type*} [Field K] {P : Polynomial ℤ}
    (hP : P.coeff 0 = 1 ∨ P.coeff 0 = -1) {α : K} (hα : α ≠ 0)
    (h : Polynomial.aeval α P = 0) : IsIntegral ℤ α⁻¹ := by
  have : Invertible α := invertibleOfNonzero hα
  have hc0 : P.coeff 0 ≠ 0 := by rcases hP with h | h <;> simp [h]
  have htrail : P.reverse.leadingCoeff = P.coeff 0 := by
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff,
      Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hc0)]
  have hroot : Polynomial.aeval α⁻¹ P.reverse = 0 := by
    rw [Polynomial.aeval_def, ← invOf_eq_inv]
    exact (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℤ K) α P).mpr
      (by rwa [Polynomial.aeval_def] at h)
  rcases hP with h1 | h1
  · exact ⟨P.reverse, by rw [Polynomial.Monic, htrail, h1], by
      rwa [Polynomial.aeval_def] at hroot⟩
  · refine ⟨-P.reverse, ?_, ?_⟩
    · rw [Polynomial.Monic, Polynomial.leadingCoeff_neg, htrail, h1, neg_neg]
    · rw [← Polynomial.aeval_def]
      simp [hroot]

/-- **The regularity criterion** ([B1E2b] WP7): if `σ(·,0)` is a permutation, then every point
whose *inverse* is not an algebraic integer is a **regular** point of the Mahler system.

At rational points this specialises to `regular_two_thirds` (`(3/2)^N ∉ ℤ`), but it applies
verbatim at algebraic irrationals, where the rational-root argument says nothing. -/
@[category research solved, AMS 11 68 12, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem regular_of_not_isIntegral_inv {K : Type*} [Field K] (k : ℕ) (hk : 0 < k)
    (σ : ι → Fin k → ι) (e : Equiv.Perm ι) (he : ∀ i, e i = σ i ⟨0, hk⟩)
    {α : K} (hα : α ≠ 0) (hint : ¬ IsIntegral ℤ α⁻¹) :
    Polynomial.aeval α (mahlerMatrix k σ).det ≠ 0 := fun hroot =>
  hint (inv_isIntegral_of_root_of_coeff_zero_pm_one
    (by simpa [Polynomial.coeff_zero_eq_eval_zero] using det_eval_zero_eq_pm_one k hk σ e he)
    hα hroot)

/-- **The iterates come for free** ([B1E2b] WP7): `α⁻¹` not an algebraic integer makes *every*
power `α^N`, `N ≥ 1`, a regular point — because `(α^N)⁻¹ = (α⁻¹)^N` integral would force `α⁻¹`
integral (`IsIntegral.of_pow`, i.e. integral closure).

This is the shape the Mahler iteration needs: the transcendence theorem tests `α, α^k, α^{k²}, …`
all at once. -/
@[category research solved, AMS 11 68 12, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem regular_of_not_isIntegral_inv_pow {K : Type*} [Field K] (k : ℕ) (hk : 0 < k)
    (σ : ι → Fin k → ι) (e : Equiv.Perm ι) (he : ∀ i, e i = σ i ⟨0, hk⟩)
    {α : K} (hα : α ≠ 0) (hint : ¬ IsIntegral ℤ α⁻¹) {N : ℕ} (hN : 0 < N) :
    Polynomial.aeval (α ^ N) (mahlerMatrix k σ).det ≠ 0 := by
  refine regular_of_not_isIntegral_inv k hk σ e he (pow_ne_zero N hα) fun hpow => hint ?_
  refine IsIntegral.of_pow hN ?_
  rwa [inv_pow]

/-! ## Sharpness: a singular point need not be an algebraic unit ([B1E2b] WP7) -/

/-- The decimation of the **sharpness system** ([B1E2b] WP7): `k = 3`, three states,
`σ(0,·) = (0,0,1)`, `σ(1,·) = (1,2,0)`, `σ(2,·) = (2,1,1)`. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
def sharpSigma : Fin 3 → Fin 3 → Fin 3 := ![![0, 0, 1], ![1, 2, 0], ![2, 1, 1]]

/-- In the sharpness system `σ(·,0)` is the identity, so `det M(0) = ±1` applies to it. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
lemma sharpSigma_zero (i : Fin 3) :
    (Equiv.refl (Fin 3)) i = sharpSigma i ⟨0, by norm_num⟩ := by
  revert i; decide

/-- The determinant of the sharpness system:
`det M = 1 + z − z² − 2z³ − 2z⁴ = −(2z² − 1)(z² + z + 1)`. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
theorem det_mahlerMatrix_sharpSigma :
    (mahlerMatrix 3 sharpSigma).det = -((2 * X ^ 2 - 1) * (X ^ 2 + X + 1)) := by
  rw [Matrix.det_fin_three]
  simp [mahlerMatrix, sharpSigma, Fin.sum_univ_three]
  ring

/-- `1/√2` is a **singular** point of the sharpness system: it is a root of `2z² − 1`. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
theorem aeval_det_sharpSigma_inv_sqrt_two :
    Polynomial.aeval ((Real.sqrt 2)⁻¹) (mahlerMatrix 3 sharpSigma).det = 0 := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [det_mahlerMatrix_sharpSigma]
  simp only [map_neg, map_mul, map_sub, map_add, map_pow, map_one, map_ofNat,
    Polynomial.aeval_X]
  linear_combination (-2 : ℝ) * ((Real.sqrt 2)⁻¹ ^ 2 + (Real.sqrt 2)⁻¹ + 1) * h2

/-- `√2` is an algebraic integer (root of the monic `X² − 2`). -/
@[category API, AMS 11 12, ref "B1E2b", group "rb_mahler_system"]
lemma isIntegral_sqrt_two : IsIntegral ℤ (Real.sqrt 2) :=
  ⟨X ^ 2 - Polynomial.C 2, Polynomial.monic_X_pow_sub_C 2 (by norm_num), by
    simp [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]⟩

/-- `1/√2` is **not** an algebraic integer: its square `1/2` would then be an integer. -/
@[category research solved, AMS 11 12, ref "B1E2b", group "rb_mahler_system"]
theorem not_isIntegral_inv_sqrt_two : ¬ IsIntegral ℤ ((Real.sqrt 2)⁻¹ : ℝ) := by
  intro hint
  have hsq : IsIntegral ℤ ((algebraMap ℚ ℝ) (1 / 2 : ℚ)) := by
    have h := hint.pow 2
    rwa [show ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = (algebraMap ℚ ℝ) (1 / 2 : ℚ) by
      rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num] at h
  have hQ : IsIntegral ℤ (1 / 2 : ℚ) :=
    isIntegral_algebraMap_iff.mp hsq
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hQ
  have hy' : (y : ℚ) = 1 / 2 := by simpa using hy
  have h2 : (2 : ℤ) * y = 1 := by
    have : (2 : ℚ) * (y : ℚ) = 1 := by rw [hy']; norm_num
    exact_mod_cast this
  omega

/-- **Sharpness** ([B1E2b] WP7): `det M(0) = ±1` forces the *inverses* of the roots of `det M` to
be algebraic integers — and no more.  It does **not** force the roots themselves to be algebraic
integers, so "every singular point is an algebraic unit" is false.

The witness is `RB.sharpSigma`: `σ(·,0) = id` is a permutation, `det M = −(2z²−1)(z²+z+1)`, and
`α = 1/√2` is a root with `α⁻¹ = √2` an algebraic integer but `α` itself not one.  So the criterion
`regular_of_not_isIntegral_inv` is exactly as strong as it can be. -/
@[category research solved, AMS 11 68 12, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem singular_sqrt_two_inv_example :
    ∃ (σ : Fin 3 → Fin 3 → Fin 3) (e : Equiv.Perm (Fin 3)) (α : ℝ),
      (∀ i, e i = σ i ⟨0, by norm_num⟩) ∧ α ≠ 0 ∧
        Polynomial.aeval α (mahlerMatrix 3 σ).det = 0 ∧
        IsIntegral ℤ α⁻¹ ∧ ¬ IsIntegral ℤ α := by
  refine ⟨sharpSigma, Equiv.refl _, (Real.sqrt 2)⁻¹, sharpSigma_zero, ?_,
    aeval_det_sharpSigma_inv_sqrt_two, ?_, not_isIntegral_inv_sqrt_two⟩
  · simp [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2) |>.ne']
  · rw [inv_inv]; exact isIntegral_sqrt_two

/-! ## Deflation: the lowest nonzero coefficient ([B1E2b] WP8)

Two general polynomial facts, both absent from Mathlib and both ForMathlib candidates: splitting
off the `X^e` factor of an integer polynomial, and Gauss's lemma in the form "a primitive
irreducible integer annihilator of `α` divides every integer annihilator of `α`". -/

/-- **Deflation** ([B1E2b] WP8): every polynomial factors as `X^e · D₁` with `e` its trailing
degree, and the constant coefficient of `D₁` is the *lowest nonzero* coefficient of `D`.

(For `D = 0` this is `0 = X^0 · 0` and the trailing coefficient is `0`; the statement is
degenerate but true, which is what keeps `hne : det M ≠ 0` out of the theorems below.) -/
@[category API, AMS 12, ref "B1E2b", group "rb_mahler_system"]
lemma exists_deflation {R : Type*} [CommRing R] (D : Polynomial R) :
    ∃ D₁ : Polynomial R, D = X ^ D.natTrailingDegree * D₁ ∧ D₁.coeff 0 = D.trailingCoeff := by
  obtain ⟨D₁, hD₁⟩ : (X : Polynomial R) ^ D.natTrailingDegree ∣ D :=
    Polynomial.X_pow_dvd_iff.mpr fun d hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  refine ⟨D₁, hD₁, ?_⟩
  have h : (X ^ D.natTrailingDegree * D₁).coeff D.natTrailingDegree = D₁.coeff 0 := by
    simpa using Polynomial.coeff_X_pow_mul D₁ D.natTrailingDegree 0
  rw [Polynomial.trailingCoeff]
  nth_rewrite 1 [hD₁]
  exact h.symm

/-- **Deflation at a nonzero root** ([B1E2b] WP8): a nonzero root of `D` is a root of the deflated
polynomial `D₁ = D / X^e`, whose constant coefficient is `D.trailingCoeff`.

This is what makes the whole section hypothesis-free: the `X^e` factor of `det M` carries only the
root `0`, so it can be discarded, and the divisibility tests below run against the lowest
*nonzero* coefficient rather than against `det M(0)`, which may well be `0`. -/
@[category API, AMS 12, ref "B1E2b", group "rb_mahler_system"]
lemma exists_deflation_of_aeval_eq_zero {K : Type*} [Field K] {D : Polynomial ℤ} {α : K}
    (hα : α ≠ 0) (h : Polynomial.aeval α D = 0) :
    ∃ D₁ : Polynomial ℤ, D₁.coeff 0 = D.trailingCoeff ∧ Polynomial.aeval α D₁ = 0 := by
  obtain ⟨D₁, hD₁, hc⟩ := exists_deflation D
  refine ⟨D₁, hc, ?_⟩
  rw [hD₁] at h
  simp only [map_mul, map_pow, Polynomial.aeval_X] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (pow_eq_zero_iff' .. |>.mp h').1 hα
  · exact h'

/-- Evaluating an integer polynomial at `α` in a field of characteristic `0` is the same as
evaluating its rational image — the bridge into Gauss's lemma. -/
@[category API, AMS 12, ref "B1E2b", group "rb_mahler_system"]
lemma aeval_map_cast_eq_zero {K : Type*} [Field K] [CharZero K] {P : Polynomial ℤ} {α : K}
    (h : Polynomial.aeval α P = 0) : Polynomial.aeval α (P.map (Int.castRingHom ℚ)) = 0 := by
  rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
  exact h

/-- **Gauss's lemma in annihilator form** ([B1E2b] WP8): a *primitive irreducible* integer
polynomial `P` annihilating `α` divides every integer polynomial annihilating `α`.

`P` is the primitive minimal polynomial of `α` (unique up to sign): primitivity plus irreducibility
over `ℤ` is exactly that.  Over `ℚ` this is `minpoly.dvd`; Gauss
(`Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`) brings the divisibility back to
`ℤ[X]`, which is what turns it into a statement about *integer* coefficients. -/
@[category research solved, AMS 11 12, ref "B1E2b", group "rb_mahler_system"]
theorem dvd_of_isPrimitive_irreducible {K : Type*} [Field K] [CharZero K] {D P : Polynomial ℤ}
    (hprim : P.IsPrimitive) (hirr : Irreducible P) {α : K} (hP : Polynomial.aeval α P = 0)
    (hD : Polynomial.aeval α D = 0) : P ∣ D := by
  rw [Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast P D hprim]
  set PQ := P.map (Int.castRingHom ℚ)
  have hirrQ : Irreducible PQ :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hirr
  obtain ⟨u, hu⟩ : minpoly ℚ α ∣ PQ := minpoly.dvd ℚ α (aeval_map_cast_eq_zero hP)
  have hunit : IsUnit u :=
    (hirrQ.isUnit_or_isUnit hu).resolve_left (minpoly.not_isUnit ℚ α)
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit
  have hback : PQ ∣ minpoly ℚ α := ⟨v, by rw [hu, mul_assoc, hv, mul_one]⟩
  exact hback.trans (minpoly.dvd ℚ α (aeval_map_cast_eq_zero hD))

/-! ## The divisibility test on the lowest coefficient ([B1E2b] WP8) -/

/-- **The rational-root theorem in `Rat.num` form**: a rational root of an integer polynomial has
numerator dividing the constant coefficient.  (Mathlib's `num_dvd_of_is_root` is stated for
`IsFractionRing.num`, which is only *associated* to `Rat.num`.) -/
@[category API, AMS 11 12, ref "B1E2b", group "rb_mahler_system"]
lemma num_dvd_coeff_zero {D : Polynomial ℤ} {α : ℚ} (h : Polynomial.aeval α D = 0) :
    α.num ∣ D.coeff 0 :=
  ((Rat.isFractionRingNum α).dvd_iff_dvd_left).mp (num_dvd_of_is_root h)

/-- **The rational test** ([B1E2b] WP8): if a nonzero rational `α` is a root of `D ∈ ℤ[X]`, then
its numerator divides the **lowest nonzero coefficient** `c = D.trailingCoeff` — not merely
`D.coeff 0`, which may vanish.

This is the rational-root theorem applied after deflation, and it needs no hypothesis on `D`
whatsoever: when `D = 0` we have `c = 0` and everything divides `0`. -/
@[category research solved, AMS 11 12, ref "B1E2b", group "rb_mahler_system"]
theorem num_dvd_trailingCoeff_of_aeval_eq_zero {D : Polynomial ℤ} {α : ℚ} (hα : α ≠ 0)
    (h : Polynomial.aeval α D = 0) : α.num ∣ D.trailingCoeff := by
  obtain ⟨D₁, hc, h₁⟩ := exists_deflation_of_aeval_eq_zero hα h
  exact hc ▸ num_dvd_coeff_zero h₁

/-- **The algebraic test** ([B1E2b] WP8, review item B7): if `α` is a root of `D ∈ ℤ[X]` and `P` is
the primitive minimal polynomial of `α`, then `P(0)` divides the lowest nonzero coefficient of `D`.

At `α = a/b` in lowest terms `P = bX - a` and `P(0) = -a`, so this says exactly what
`num_dvd_trailingCoeff_of_aeval_eq_zero` says, up to the sign that divisibility ignores. -/
@[category research solved, AMS 11 12, ref "B1E2b", group "rb_mahler_system"]
theorem coeff_zero_dvd_trailingCoeff_of_aeval_eq_zero {K : Type*} [Field K] [CharZero K]
    {D P : Polynomial ℤ} (hprim : P.IsPrimitive) (hirr : Irreducible P) {α : K} (hα : α ≠ 0)
    (hP : Polynomial.aeval α P = 0) (h : Polynomial.aeval α D = 0) :
    P.coeff 0 ∣ D.trailingCoeff := by
  obtain ⟨D₁, hc, h₁⟩ := exists_deflation_of_aeval_eq_zero hα h
  obtain ⟨g, hg⟩ := dvd_of_isPrimitive_irreducible hprim hirr hP h₁
  exact hc ▸ ⟨g.coeff 0, by rw [hg, Polynomial.mul_coeff_zero]⟩

/-! ## The hypothesis-free regularity criterion ([B1E2b] WP8) -/

/-- **The refinement** ([B1E2b] WP8, review item B7): *no hypothesis on `σ` at all*.  If the
primitive minimal polynomial of `α` has a constant term that does **not** divide the lowest nonzero
coefficient `c` of `det M`, then `α` is a regular point.

This strictly contains the permutation criterion of WP7: when `σ(·,0)` is a permutation,
`det M(0) = ±1`, so `c = ±1` (`trailingCoeff_det_eq_pm_one_of_perm`) and *every* `α` whose minimal
polynomial has non-unit constant term passes the test.  Dropping the permutation hypothesis costs
only the replacement of `±1` by the computable integer `c`.

The plan's non-degeneracy hypothesis `det M ≠ 0` is **not needed**: if `det M = 0` then `c = 0`,
everything divides `0`, and the hypothesis `hdvd` is already false. -/
@[category research solved, AMS 11 68 12, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem regular_of_not_dvd_lowest_coeff {K : Type*} [Field K] [CharZero K] (k : ℕ)
    (σ : ι → Fin k → ι) {P : Polynomial ℤ} (hprim : P.IsPrimitive) (hirr : Irreducible P)
    {α : K} (hα : α ≠ 0) (hP : Polynomial.aeval α P = 0)
    (hdvd : ¬ (P.coeff 0 ∣ (mahlerMatrix k σ).det.trailingCoeff)) :
    Polynomial.aeval α (mahlerMatrix k σ).det ≠ 0 := fun h =>
  hdvd (coeff_zero_dvd_trailingCoeff_of_aeval_eq_zero hprim hirr hα hP h)

/-- **The checkable form** ([B1E2b] WP8): at a rational point the test is "does the numerator of
`α` divide the lowest nonzero coefficient of `det M`?" — a divisibility of two integers, both of
which a machine computes from `σ`. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem regular_of_not_dvd_lowest_coeff_rat (k : ℕ) (σ : ι → Fin k → ι) {α : ℚ} (hα : α ≠ 0)
    (hdvd : ¬ (α.num ∣ (mahlerMatrix k σ).det.trailingCoeff)) :
    Polynomial.aeval α (mahlerMatrix k σ).det ≠ 0 := fun h =>
  hdvd (num_dvd_trailingCoeff_of_aeval_eq_zero hα h)

/-- **`2/3` again, without the permutation hypothesis** ([B1E2b] WP8): an *odd* lowest coefficient
of `det M` already makes every iterate `(2/3)^{k^m}` regular, because the numerator `2^{k^m}` is
even and cannot divide it.

Compare `regular_two_thirds`, which assumes `σ(·,0)` is a permutation in order to get `c = ±1`.
Oddness is all that was ever used. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem regular_two_thirds_of_odd_lowest_coeff (k : ℕ) (hk : 0 < k) (σ : ι → Fin k → ι)
    (hodd : Odd (mahlerMatrix k σ).det.trailingCoeff) (m : ℕ) :
    Polynomial.aeval ((2 / 3 : ℚ) ^ (k ^ m)) (mahlerMatrix k σ).det ≠ 0 := by
  have hpos : 0 < k ^ m := pow_pos hk m
  refine regular_of_not_dvd_lowest_coeff_rat k σ (by positivity) ?_
  have hnum : ((2 / 3 : ℚ) ^ (k ^ m)).num = 2 ^ (k ^ m) := by
    rw [Rat.num_pow]; norm_num [Rat.num]
  rw [hnum]
  intro hdvd
  obtain ⟨t, ht⟩ := hodd
  obtain ⟨u, hu⟩ := dvd_trans (dvd_pow_self (2 : ℤ) hpos.ne') hdvd
  omega

/-- **WP7 is the case `c = ±1`** ([B1E2b] WP8): if `σ(·,0)` is a permutation then `det M` has
nonzero constant term, so its trailing degree is `0` and its lowest coefficient is `±1`.

So `regular_of_not_dvd_lowest_coeff` really does contain `regular_two_thirds`: `±1` is odd, and
`2^N ∤ ±1`. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem trailingCoeff_det_eq_pm_one_of_perm (k : ℕ) (hk : 0 < k) (σ : ι → Fin k → ι)
    (e : Equiv.Perm ι) (he : ∀ i, e i = σ i ⟨0, hk⟩) :
    (mahlerMatrix k σ).det.natTrailingDegree = 0 ∧
      ((mahlerMatrix k σ).det.trailingCoeff = 1 ∨ (mahlerMatrix k σ).det.trailingCoeff = -1) := by
  have h0 : (mahlerMatrix k σ).det.coeff 0 = 1 ∨ (mahlerMatrix k σ).det.coeff 0 = -1 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using det_eval_zero_eq_pm_one k hk σ e he
  have hne : (mahlerMatrix k σ).det.coeff 0 ≠ 0 := by rcases h0 with h | h <;> simp [h]
  have htd : (mahlerMatrix k σ).det.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hne)
  exact ⟨htd, by rwa [Polynomial.trailingCoeff, htd]⟩

/-! ## The refinement is not vacuous: a system with `det M(0) = 0` ([B1E2b] WP8) -/

/-- A decimation whose `σ(·,0)` is **not** injective, let alone a permutation: `k = 2`,
`σ(0,·) = (0,0)`, `σ(1,·) = (0,1)`, so both states decimate to state `0` at `r = 0`. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
def nonPermSigma : Fin 2 → Fin 2 → Fin 2 := ![![0, 0], ![0, 1]]

/-- `σ(·,0)` collapses the two states, so WP7's permutation hypothesis fails. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
lemma not_injective_nonPermSigma :
    ¬ Function.Injective fun i => nonPermSigma i ⟨0, by norm_num⟩ := by decide

/-- `M(z) = ![![1 + z, 0], ![1, z]]`, so `det M = z(1 + z)`. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
theorem det_mahlerMatrix_nonPermSigma :
    (mahlerMatrix 2 nonPermSigma).det = X * (1 + X) := by
  rw [Matrix.det_fin_two]
  simp [mahlerMatrix, nonPermSigma, Fin.sum_univ_two]
  ring

/-- **The WP7 lever is unavailable here**: the constant coefficient of `det M` is `0`, not `±1`, so
`det M(0) = ±1` fails as badly as it can.  Deflation is not a convenience — it is what makes the
test exist at all. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
theorem eval_zero_det_nonPermSigma : (mahlerMatrix 2 nonPermSigma).det.eval 0 = 0 := by
  rw [det_mahlerMatrix_nonPermSigma]; simp

/-- The lowest *nonzero* coefficient is `1`: `det M = z(1+z)` has trailing degree `1`. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
theorem trailingCoeff_det_nonPermSigma :
    (mahlerMatrix 2 nonPermSigma).det.trailingCoeff = 1 := by
  rw [det_mahlerMatrix_nonPermSigma, Polynomial.trailingCoeff_mul]
  have hX : (X : Polynomial ℤ).trailingCoeff = 1 := by
    simp [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X]
  have h1 : (1 + X : Polynomial ℤ).trailingCoeff = 1 := by
    rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simp))]
    simp
  rw [hX, h1, mul_one]

/-- **The refinement decides a system WP7 cannot touch** ([B1E2b] WP8): `σ(·,0)` is not a
permutation and `det M(0) = 0`, yet `2/3` and all its `2^m`-th powers are regular points, because
the lowest nonzero coefficient is odd. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem regular_two_thirds_nonPermSigma (m : ℕ) :
    Polynomial.aeval ((2 / 3 : ℚ) ^ (2 ^ m)) (mahlerMatrix 2 nonPermSigma).det ≠ 0 :=
  regular_two_thirds_of_odd_lowest_coeff 2 (by norm_num) nonPermSigma
    (by rw [trailingCoeff_det_nonPermSigma]; exact odd_one) m

/-! ## What the row-sum factor forces, and what it does not ([B1E2b] WP8, review item F7c)

`(1 + z + ⋯ + z^{k-1}) ∣ det M` (`RB.rowSum_dvd_det`) is the corpus's oldest structural fact about
`M`; here is the job it can do.  It says a Mahler determinant with `k ≥ 2` **always** has singular
points — every `k`-th root of unity other than `1` — so the strongest non-degeneracy one may ask
for is `det M ≠ 0` as a polynomial.  And it says those forced singularities are *harmless*: they
sit on `|z| = 1`, while the row-sum factor is `≥ 1` at every point `α ≥ 0`, so it can never be the
reason a positive rational such as `2/3` is singular.

**The plan's claim that the factor forces `det M(1) = 0` is false** — `1` is the one `k`-th root of
unity that is *not* a root of `1 + z + ⋯ + z^{k-1}`, where the value is `k`.  The sharpness system
of WP7 refutes it outright: `det M(1) = -3` (`eval_one_det_sharpSigma`), and so does [AF17] §8.1's
own example, `det A = (1+z-z²)(1+z+z²)` with `det A(1) = 3`. -/

/-- Every `k`-th root of unity other than `1` kills the row-sum factor. -/
@[category research solved, AMS 11 12, ref "B1E2b", group "rb_mahler_system"]
lemma aeval_rowSum_eq_zero_of_pow_eq_one {K : Type*} [Field K] (k : ℕ) {ζ : K} (hζ : ζ ^ k = 1)
    (hne : ζ ≠ 1) : Polynomial.aeval ζ (∑ r : Fin k, (X : Polynomial ℤ) ^ (r : ℕ)) = 0 := by
  have h1 : Polynomial.aeval ζ (∑ r : Fin k, (X : Polynomial ℤ) ^ (r : ℕ))
      = ∑ i ∈ Finset.range k, ζ ^ i := by
    simp [Fin.sum_univ_eq_sum_range (fun i => ζ ^ i)]
  have h2 : (∑ i ∈ Finset.range k, ζ ^ i) * (ζ - 1) = ζ ^ k - 1 := geom_sum_mul ζ k
  rw [hζ, sub_self] at h2
  rw [h1]
  exact (mul_eq_zero.mp h2).resolve_right fun h => hne (sub_eq_zero.mp h)

/-- **Forced singularities** ([B1E2b] WP8): every `k`-th root of unity other than `1` is a singular
point of *every* Mahler system on a nonempty index set.

Hence "`det M` has no roots" is never available, and `det M ≠ 0` is the right non-degeneracy
hypothesis — the one used in `regular_of_not_dvd_lowest_coeff`, where it is not even needed as a
hypothesis. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem aeval_det_eq_zero_of_pow_eq_one {K : Type*} [Field K] [Nonempty ι] (k : ℕ)
    (σ : ι → Fin k → ι) {ζ : K} (hζ : ζ ^ k = 1) (hne : ζ ≠ 1) :
    Polynomial.aeval ζ (mahlerMatrix k σ).det = 0 := by
  obtain ⟨g, hg⟩ := rowSum_dvd_det k σ
  rw [hg, map_mul, aeval_rowSum_eq_zero_of_pow_eq_one k hζ hne, zero_mul]

/-- **The forced singularities are harmless** ([B1E2b] WP8): the row-sum factor is `≥ 1` at every
nonnegative point, so it never vanishes at `2/3`, at any positive rational, or anywhere in
`[0,1)` — the region the Mahler method evaluates in.  A singular point `α ≥ 0` must come from the
complementary factor `det M / (1 + z + ⋯ + z^{k-1})`. -/
@[category research solved, AMS 11 12, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem aeval_rowSum_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {k : ℕ}
    (hk : 0 < k) {α : K} (hα : 0 ≤ α) :
    0 < Polynomial.aeval α (∑ r : Fin k, (X : Polynomial ℤ) ^ (r : ℕ)) := by
  have h1 : Polynomial.aeval α (∑ r : Fin k, (X : Polynomial ℤ) ^ (r : ℕ))
      = ∑ i ∈ Finset.range k, α ^ i := by
    simp [Fin.sum_univ_eq_sum_range (fun i => α ^ i)]
  rw [h1]
  exact Finset.sum_pos' (fun i _ => by positivity) ⟨0, Finset.mem_range.mpr hk, by simp⟩

/-- The sharpness system evaluated at `1`: `det M(1) = -(2-1)(1+1+1) = -3`. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
theorem eval_one_det_sharpSigma : (mahlerMatrix 3 sharpSigma).det.eval 1 = -3 := by
  rw [det_mahlerMatrix_sharpSigma]; norm_num

/-- **The plan's `det M(1) = 0` is false** ([B1E2b] WP8, review item F7c): the row-sum factor
`1 + z + ⋯ + z^{k-1}` takes the value `k ≠ 0` at `z = 1`, so it forces nothing there.  Witness:
the WP7 sharpness system, whose `σ(·,0)` is even a permutation and whose determinant is `-3` at
`1`. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_system"]
theorem exists_det_eval_one_ne_zero :
    ∃ (k : ℕ) (σ : Fin 3 → Fin k → Fin 3), (mahlerMatrix k σ).det.eval 1 ≠ 0 :=
  ⟨3, sharpSigma, by rw [eval_one_det_sharpSigma]; norm_num⟩

end RB
