/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Analysis.Complex.HardySpace
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.Meromorphic.Basic
import ForMathlib.RingTheory.PowerSeries.Rationality
import ForMathlib.Analysis.InnerProductSpace.Hadamard
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Nevanlinna-class factorization on the unit disk (Bertin §1.2) — literature axioms

This file records the §1.2 results of Bertin, *Pisot and Salem Numbers* ("Criteria of rationality
in ℂ"): three Nevanlinna-class factorization results (Propositions 1.2.1–1.2.3), the bridge Lemma
1.2.1 to the §1.1 Kronecker machinery, the headline rationality Theorem 1.2.1, and two sufficient
conditions for bounded characteristic (Propositions 1.2.4–1.2.5). Propositions 1.2.1, 1.2.2, 1.2.4
and Lemma 1.2.1 are recorded as **literature axioms**; Propositions 1.2.3, 1.2.5 and Theorem 1.2.1
are **proved** from them.

* `Complex.hasBoundedCharacteristic_iff_isBoundedAnalyticQuotient` — **Proposition 1.2.1**
  (Tsuji): a meromorphic function on `D(0,1)` has *bounded characteristic* iff it is a quotient
  of two analytic and bounded functions. This is Nevanlinna's characterization of the class `N`
  of functions of bounded type.
* `Complex.memHardy_isBoundedAnalyticQuotient` — **Proposition 1.2.2** (Bertin): every Hardy-space
  function `Hᵖ` (`p ∈ ℝ⁺`) is such a bounded-analytic quotient, i.e. `Hᵖ ⊆ N`.
* `Complex.hasBoundedCharacteristic_iff_isHardyQuotient` — **Proposition 1.2.3** (Bertin): bounded
  characteristic is equivalent to being a quotient of two `Hᵖ` functions (any `p > 0`, e.g. `H²`).
  This is **proved** from 1.2.1 and 1.2.2 (its only non-standard axioms), using `H^∞ ⊆ Hᵖ` and the
  identity principle to reconcile the two notions of quotient.
* `Complex.boundedCharacteristic_kroneckerDet_root_tendsto_zero` — **Lemma 1.2.1** (Bertin): for `f`
  of bounded characteristic with no pole at `0`, the Kronecker/Hankel determinants `Dₙ(S(f))` of its
  Taylor series satisfy `‖Dₙ‖ ^ (1/n) → 0`. A literature axiom (its published proof uses the Hardy
  `ℓ²` coefficients of a quotient representation and Hadamard's inequality); the bridge from the
  factorization results to the §1.1 Kronecker determinants.
* `Complex.isRationalSeries_of_boundedCharacteristic_intCoeffs` — **Theorem 1.2.1** (Bertin): a
  function of bounded characteristic with no pole at `0` whose Taylor coefficients are **integers**
  is a rational function — its Taylor series `S(f)` is a rational series. **Proved** from Lemma 1.2.1
  and Kronecker's criterion: the integer determinants `Dₙ` have modulus `< 1` from some index on,
  hence vanish, forcing rationality.
* `Complex.hasBoundedCharacteristic_of_bddAway` — **Proposition 1.2.4** (Bertin): if `f` is
  meromorphic on `D(0,1)` and stays bounded away from some value `α` on an annulus `η ≤ |z| < 1` near
  the boundary (`|f - α| ≥ δ > 0`), then `f` has bounded characteristic. A literature axiom (its proof
  applies the disk Nevanlinna characteristic and the First Main Theorem to `1/(f - α)`).
* `Complex.hasBoundedCharacteristic_of_re_le` — **Proposition 1.2.5** (Bertin): if `Re f ≤ k` near
  the boundary (on an annulus `η ≤ |z| < 1`), then `f` has bounded characteristic. **Proved** from
  1.2.4 by avoiding `α = k + 1` with margin `δ = 1`.

The first two results' published proofs run through the Poisson–Jensen formula, the Nevanlinna
characteristic, and
Blaschke/canonical factorization — machinery only partly present in Mathlib (the planar value-
distribution functions `ValueDistribution.{proximity, logCounting, characteristic}` exist, and the
individual disk Blaschke factor `Complex.canonicalFactor`, but the disk class `N`, the factorization
theorems, and the full canonical decomposition do not). The results are therefore asserted on the
authority of their citations rather than left as `sorry`s; `#print axioms` surfaces the dependency
in every downstream proof. The supporting notions `HasBoundedCharacteristic` /
`IsBoundedAnalyticQuotient` are given as clean definitions, reusing Mathlib's characteristic
function. The Hardy-space membership `Complex.MemHardy` is from `ForMathlib`.

## References
* [Tsu59] Tsuji, Masatsugu. *Potential Theory in Modern Function Theory.* Maruzen, 1959.
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

/-! ## Informal-result registry

The general results these (published) proofs rely on that are **not** in Mathlib, recorded at the
level of "what notion the proof needs". Registry-keyed so the `informal_uses` edges below share
canonical nodes. -/

informal_result "poisson-jensen"
  latex "Poisson-Jensen formula: the value of a meromorphic function at an interior point of a disk is recovered from its boundary values via the Poisson kernel, corrected by the logarithmic potentials of its zeros and poles; the basis of Jensen's inequality bounding the Nevanlinna characteristic."
  refs "Tsu59"

informal_result "nevanlinna-characteristic"
  latex "Nevanlinna characteristic T(r,f) = m(r,f) + N(r,f): the proximity function (logarithmic average of log+ of the modulus on the circle of radius r) plus the integrated pole-counting function; a meromorphic function is of bounded type exactly when T(r,f) stays bounded as r tends to 1."
  refs "Tsu59"

informal_result "blaschke-canonical-factorization"
  latex "Blaschke and canonical factorization on the unit disk: a function of bounded type factors as a Blaschke product over its zeros and poles times a quotient of zero-free bounded analytic functions, the canonical factors having modulus one on the boundary circle."
  refs "Tsu59"

namespace Complex

open Metric Set ValueDistribution

/-- A meromorphic function on the unit disk `D(0,1)` **has bounded characteristic** (equivalently,
lies in the *Nevanlinna class* `N` of functions of bounded type) when its Nevanlinna characteristic
`T(r, f) = m(r, f) + N(r, f)` stays bounded as `r → 1⁻`. Here `T(r, f)` is
`ValueDistribution.characteristic f ⊤ r`: the proximity function (the logarithmic average of
`log⁺ ‖f‖` on the circle `|z| = r`) plus the integrated counting function of the poles. -/
@[category API, AMS 30, ref "Ber92"]
def HasBoundedCharacteristic (f : ℂ → ℂ) : Prop :=
  MeromorphicOn f (ball 0 1) ∧ BddAbove (characteristic f ⊤ '' Ico 0 1)

/-- `f` is a **quotient of two bounded analytic functions** on the unit disk: there exist `g, h`
analytic and bounded on `D(0,1)`, with `h` not identically zero, such that `f = g / h` wherever
`h ≠ 0`. -/
@[category API, AMS 30, ref "Ber92"]
def IsBoundedAnalyticQuotient (f : ℂ → ℂ) : Prop :=
  ∃ g h : ℂ → ℂ,
    AnalyticOnNhd ℂ g (ball 0 1) ∧ (∃ C, ∀ z ∈ ball 0 1, ‖g z‖ ≤ C) ∧
      AnalyticOnNhd ℂ h (ball 0 1) ∧ (∃ C, ∀ z ∈ ball 0 1, ‖h z‖ ≤ C) ∧
        (∃ z ∈ ball 0 1, h z ≠ 0) ∧ ∀ z ∈ ball 0 1, h z ≠ 0 → f z = g z / h z

/-- **Proposition 1.2.1** (Tsuji). A meromorphic function `f` on the unit disk `D(0,1)` has bounded
characteristic if and only if it is the quotient of two analytic and bounded functions on `D(0,1)`.
This is Nevanlinna's characterization of the class `N` of functions of bounded type. Its proof rests
on the Poisson–Jensen formula, the Nevanlinna characteristic, and Blaschke/canonical factorization;
recorded here as a literature axiom on the authority of [Tsu59] (see also [Ber92], Proposition
1.2.1). -/
@[category research solved, AMS 30, ref "Tsu59",
  informal_uses "poisson-jensen" "nevanlinna-characteristic" "blaschke-canonical-factorization"]
axiom hasBoundedCharacteristic_iff_isBoundedAnalyticQuotient (f : ℂ → ℂ) :
    HasBoundedCharacteristic f ↔ IsBoundedAnalyticQuotient f

/-- **Proposition 1.2.2** (Bertin). Every function of the Hardy space `Hᵖ` (`p ∈ ℝ⁺`) can be written
as `f = f₁ / f₂` with `f₁, f₂` analytic and bounded on `D(0,1)`; that is, `Hᵖ ⊆ N`. The published
proof shows an `Hᵖ` function has bounded characteristic (via the Poisson–Jensen formula and the
Nevanlinna characteristic) and then applies Proposition 1.2.1; recorded as a literature axiom on the
authority of [Ber92], Proposition 1.2.2. -/
@[category research solved, AMS 30, ref "Ber92",
  informal_uses "poisson-jensen" "nevanlinna-characteristic" "blaschke-canonical-factorization",
  formal_uses hasBoundedCharacteristic_iff_isBoundedAnalyticQuotient]
axiom memHardy_isBoundedAnalyticQuotient {p : ℝ} (hp : 0 < p) {f : ℂ → ℂ}
    (hf : MemHardy p f) : IsBoundedAnalyticQuotient f

/-- A function analytic and bounded on the disk lies in every Hardy space `Hᵖ` (`H^∞ ⊆ Hᵖ`):
its integral means are bounded by the supremum bound to the power `p`. -/
private lemma memHardy_of_analyticOn_bounded {p : ℝ} (hp : 0 ≤ p) {g : ℂ → ℂ} {C : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hgC : ∀ z ∈ ball 0 1, ‖g z‖ ≤ C) :
    MemHardy p g := by
  refine ⟨hg, C ^ p, ?_⟩
  rintro _ ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hsub : Metric.sphere (0 : ℂ) |r| ⊆ ball 0 1 := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right, hz, abs_of_nonneg hr0]
    exact hr1
  have hcont : ContinuousOn (fun z => ‖g z‖ ^ p) (Metric.sphere (0 : ℂ) |r|) :=
    ((hg.continuousOn.mono hsub).norm).rpow_const fun _ _ => Or.inr hp
  show Real.circleAverage (fun z => ‖g z‖ ^ p) 0 r ≤ C ^ p
  refine Real.circleAverage_mono_on_of_le_circle hcont.circleIntegrable' fun z hz => ?_
  exact Real.rpow_le_rpow (norm_nonneg _) (hgC z (hsub hz)) hp

/-- Identity principle on the disk: analytic functions `a`, `b` that agree wherever the analytic
function `c` is nonzero agree on all of `D(0,1)`. -/
private lemma eqOn_ball_of_eqOn_ne {a b c : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a (ball 0 1))
    (hb : AnalyticOnNhd ℂ b (ball 0 1)) (hc : AnalyticOnNhd ℂ c (ball 0 1)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ ball 0 1) (hcz₀ : c z₀ ≠ 0) (hab : ∀ z ∈ ball 0 1, c z ≠ 0 → a z = b z) :
    Set.EqOn a b (ball 0 1) := by
  refine ha.eqOn_of_preconnected_of_eventuallyEq hb (convex_ball (0 : ℂ) 1).isPreconnected hz₀ ?_
  filter_upwards [(hc z₀ hz₀).continuousAt.eventually_ne hcz₀, isOpen_ball.mem_nhds hz₀]
    with z hz1 hz2 using hab z hz2 hz1

/-- On the disk, the product of two analytic functions, each nonzero somewhere, is nonzero
somewhere. -/
private lemma exists_mem_ball_mul_ne_zero {a b : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a (ball 0 1))
    (hb : AnalyticOnNhd ℂ b (ball 0 1)) {za zb : ℂ} (hza : za ∈ ball 0 1) (haz : a za ≠ 0)
    (hzb : zb ∈ ball 0 1) (hbz : b zb ≠ 0) : ∃ z ∈ ball 0 1, a z * b z ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  have hb0 : Set.EqOn b (fun _ => (0 : ℂ)) (ball 0 1) := by
    refine eqOn_ball_of_eqOn_ne hb analyticOnNhd_const ha hza haz fun z hz haz' => ?_
    rcases mul_eq_zero.mp (hcon z hz) with h | h
    · exact absurd h haz'
    · exact h
  exact hbz (by simpa using hb0 hzb)

/-- `f` is a **quotient of two `Hᵖ` functions** on the unit disk: there exist `f₁, f₂ ∈ Hᵖ` with
`f₂` not identically zero such that `f = f₁ / f₂` wherever `f₂ ≠ 0`. -/
@[category API, AMS 30, ref "Ber92"]
def IsHardyQuotient (p : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ f₁ f₂ : ℂ → ℂ, MemHardy p f₁ ∧ MemHardy p f₂ ∧
    (∃ z ∈ ball 0 1, f₂ z ≠ 0) ∧ ∀ z ∈ ball 0 1, f₂ z ≠ 0 → f z = f₁ z / f₂ z

/-- **Proposition 1.2.3** (Bertin). A meromorphic function `f` on `D(0,1)` has bounded
characteristic if and only if it is the quotient of two functions of the Hardy space `Hᵖ`
(any `p > 0`; in particular `H²`). This is a **corollary of Propositions 1.2.1 and 1.2.2**: the
bounded analytic functions of 1.2.1 lie in every `Hᵖ` (`H^∞ ⊆ Hᵖ`), and conversely 1.2.2 rewrites
each `Hᵖ` factor as a quotient of bounded analytic functions, so the two notions of quotient agree.
The Lean proof reduces, via the identity principle, the ratio algebra to the bounded-analytic
case. -/
@[category research solved, AMS 30, ref "Ber92", formal_uses
  hasBoundedCharacteristic_iff_isBoundedAnalyticQuotient memHardy_isBoundedAnalyticQuotient]
theorem hasBoundedCharacteristic_iff_isHardyQuotient {p : ℝ} (hp : 0 < p) (f : ℂ → ℂ) :
    HasBoundedCharacteristic f ↔ IsHardyQuotient p f := by
  rw [hasBoundedCharacteristic_iff_isBoundedAnalyticQuotient]
  constructor
  · rintro ⟨g, h, hgan, ⟨Cg, hCg⟩, hhan, ⟨Ch, hCh⟩, hhne, hagree⟩
    exact ⟨g, h, memHardy_of_analyticOn_bounded hp.le hgan hCg,
      memHardy_of_analyticOn_bounded hp.le hhan hCh, hhne, hagree⟩
  · rintro ⟨f₁, f₂, hf₁, hf₂, ⟨w, hw, hf₂w⟩, hfeq⟩
    obtain ⟨g₁, h₁, hg₁an, ⟨Cg₁, hCg₁⟩, hh₁an, ⟨Ch₁, hCh₁⟩, ⟨u₁, hu₁, hh₁u₁⟩, heq₁⟩ :=
      memHardy_isBoundedAnalyticQuotient hp hf₁
    obtain ⟨g₂, h₂, hg₂an, ⟨Cg₂, hCg₂⟩, hh₂an, ⟨Ch₂, hCh₂⟩, ⟨u₂, hu₂, hh₂u₂⟩, heq₂⟩ :=
      memHardy_isBoundedAnalyticQuotient hp hf₂
    have key₁ : Set.EqOn g₁ (fun z => f₁ z * h₁ z) (ball 0 1) := by
      refine eqOn_ball_of_eqOn_ne hg₁an (hf₁.1.mul hh₁an) hh₁an hu₁ hh₁u₁ fun z hz hhz => ?_
      show g₁ z = f₁ z * h₁ z
      rw [heq₁ z hz hhz]; field_simp
    have key₂ : Set.EqOn g₂ (fun z => f₂ z * h₂ z) (ball 0 1) := by
      refine eqOn_ball_of_eqOn_ne hg₂an (hf₂.1.mul hh₂an) hh₂an hu₂ hh₂u₂ fun z hz hhz => ?_
      show g₂ z = f₂ z * h₂ z
      rw [heq₂ z hz hhz]; field_simp
    obtain ⟨zg, hzg, hg₂zg⟩ : ∃ z ∈ ball 0 1, g₂ z ≠ 0 := by
      obtain ⟨z, hz, hz0⟩ := exists_mem_ball_mul_ne_zero hf₂.1 hh₂an hw hf₂w hu₂ hh₂u₂
      exact ⟨z, hz, by rw [key₂ hz]; exact hz0⟩
    have hHne : ∃ z ∈ ball 0 1, h₁ z * g₂ z ≠ 0 :=
      exists_mem_ball_mul_ne_zero hh₁an hg₂an hu₁ hh₁u₁ hzg hg₂zg
    refine ⟨fun z => g₁ z * h₂ z, fun z => h₁ z * g₂ z, hg₁an.mul hh₂an, ⟨Cg₁ * Ch₂, ?_⟩,
      hh₁an.mul hg₂an, ⟨Ch₁ * Cg₂, ?_⟩, hHne, ?_⟩
    · intro z hz
      rw [norm_mul]
      exact mul_le_mul (hCg₁ z hz) (hCh₂ z hz) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hCg₁ z hz))
    · intro z hz
      rw [norm_mul]
      exact mul_le_mul (hCh₁ z hz) (hCg₂ z hz) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hCh₁ z hz))
    · intro z hz hH
      obtain ⟨hh₁z, hg₂z⟩ := mul_ne_zero_iff.mp hH
      have hfac : g₂ z = f₂ z * h₂ z := key₂ hz
      have hf₂z : f₂ z ≠ 0 := fun hh => hg₂z (by rw [hfac, hh, zero_mul])
      have hh₂z : h₂ z ≠ 0 := fun hh => hg₂z (by rw [hfac, hh, mul_zero])
      show f z = g₁ z * h₂ z / (h₁ z * g₂ z)
      rw [hfeq z hz hf₂z, heq₁ z hz hh₁z, heq₂ z hz hh₂z]
      field_simp

/-- **Lemma 1.2.1** (Bertin). If `f` is meromorphic with bounded characteristic on `D(0,1)` and has
no pole at the origin — so near `0` it is analytic with Taylor coefficients `a`, i.e. power series
`S(f) = ∑ aₖ Xᵏ` — then the Kronecker/Hankel determinants `Dₙ(S(f)) = kroneckerDet (mk a) n` satisfy
`‖Dₙ(S(f))‖ ^ (1/n) → 0`.

This is the bridge from the §1.2 Hardy/Nevanlinna factorization to the §1.1 Kronecker-determinant
machinery. Recorded as a literature axiom: the proof factors `f = g/h` with `g, h ∈ H²`
(`hasBoundedCharacteristic_iff_isHardyQuotient`), whose Taylor coefficients are then `ℓ²`
(`memHardy_two_iff_summable`); the multiplier/Toeplitz determinant identity (`kroneckerDet_step`)
rewrites `Dₙ` as a determinant of the `ℓ²` numerator coefficients, bounded via Hadamard's inequality
(`OrthonormalBasis.norm_det_le_prod_norm`), whose geometric mean tends to `0`. -/
@[category research solved, AMS 30, ref "Ber92", formal_uses
  hasBoundedCharacteristic_iff_isHardyQuotient memHardy_two_iff_summable
  OrthonormalBasis.norm_det_le_prod_norm]
axiom boundedCharacteristic_kroneckerDet_root_tendsto_zero {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ : ENNReal}
    (hf : HasBoundedCharacteristic f)
    (hfp : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 ρ) :
    Filter.Tendsto (fun n => ‖kroneckerDet (PowerSeries.mk a) n‖ ^ (n : ℝ)⁻¹)
      Filter.atTop (nhds 0)

/-- **Theorem 1.2.1** (Bertin). A meromorphic function `f` on the unit disk `D(0,1)` with bounded
characteristic and no pole at the origin — so near `0` it is analytic with Taylor series
`S(f) = ∑ aₖ Xᵏ` — whose Taylor coefficients are **integers** (`a k ∈ ℤ`) is a *rational function*:
its Taylor series `S(f)` is a rational series (`IsRationalSeries`, the power-series expansion of a
ratio of polynomials; over the field `ℂ` this is exactly "the expansion of a rational function").

Proof (Bertin). The Kronecker/Hankel determinants `Dₙ(S(f)) = kroneckerDet (mk a) n` are integers,
being determinants of integer Hankel matrices. By **Lemma 1.2.1**
(`boundedCharacteristic_kroneckerDet_root_tendsto_zero`) their geometric means `‖Dₙ‖ ^ (1/n)` tend to
`0`, so `‖Dₙ‖ < 1` from some index on; an integer of modulus `< 1` is `0`, hence `Dₙ = 0` eventually,
and the **Kronecker criterion** (`isRationalSeries_iff_kroneckerDet_eventually_zero`) makes `S(f)`
rational. This is the rationality criterion the whole section builds toward; its only non-standard
axiom is Lemma 1.2.1. -/
@[category research solved, AMS 30, ref "Ber92", formal_uses
  boundedCharacteristic_kroneckerDet_root_tendsto_zero
  isRationalSeries_iff_kroneckerDet_eventually_zero]
theorem isRationalSeries_of_boundedCharacteristic_intCoeffs {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ : ENNReal}
    (hf : HasBoundedCharacteristic f)
    (hfp : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 ρ)
    (hint : ∀ n, ∃ m : ℤ, a n = (m : ℂ)) :
    IsRationalSeries (PowerSeries.mk a) := by
  classical
  choose b hb using hint
  -- The Kronecker determinants of `S(f)` are integers: casts of the integer Hankel determinants.
  have hcast : ∀ n, kroneckerDet (PowerSeries.mk a) n
      = ((kroneckerDet (PowerSeries.mk b) n : ℤ) : ℂ) := by
    intro n
    have hmap : hankelMatrix (PowerSeries.mk a) n
        = (hankelMatrix (PowerSeries.mk b) n).map (Int.castRingHom ℂ) := by
      ext i j
      simp only [hankelMatrix_apply, PowerSeries.coeff_mk, Matrix.map_apply, Int.coe_castRingHom, hb]
    show (hankelMatrix (PowerSeries.mk a) n).det
        = (((hankelMatrix (PowerSeries.mk b) n).det : ℤ) : ℂ)
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Int.coe_castRingHom]
  -- By Lemma 1.2.1 the integer determinants have modulus `< 1` eventually, hence vanish.
  have hev : ∀ᶠ n : ℕ in Filter.atTop, kroneckerDet (PowerSeries.mk a) n = 0 := by
    have hroot := boundedCharacteristic_kroneckerDet_root_tendsto_zero hf hfp
    have h1 : ∀ᶠ n : ℕ in Filter.atTop,
        ‖kroneckerDet (PowerSeries.mk a) n‖ ^ (n : ℝ)⁻¹ < 1 :=
      hroot.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [h1, Filter.eventually_ge_atTop 1] with n hn1 hn
    have hne : n ≠ 0 := by omega
    have hx0 : (0 : ℝ) ≤ ‖kroneckerDet (PowerSeries.mk a) n‖ := norm_nonneg _
    have hnorm : ‖kroneckerDet (PowerSeries.mk a) n‖ < 1 :=
      calc ‖kroneckerDet (PowerSeries.mk a) n‖
          = (‖kroneckerDet (PowerSeries.mk a) n‖ ^ (n : ℝ)⁻¹) ^ n :=
            (Real.rpow_inv_natCast_pow hx0 hne).symm
        _ < 1 := pow_lt_one₀ (Real.rpow_nonneg hx0 _) hn1 hne
    have hzero : kroneckerDet (PowerSeries.mk b) n = 0 := by
      rw [hcast n, Complex.norm_intCast] at hnorm
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast hnorm)
    rw [hcast n, hzero, Int.cast_zero]
  exact (isRationalSeries_iff_kroneckerDet_eventually_zero (PowerSeries.mk a)).mpr
    (Filter.eventually_atTop.mp hev)

/-- **Proposition 1.2.4** (Bertin). Let `f` be meromorphic on the unit disk `D(0,1)`. If `f` stays
bounded away from some value `α ∈ ℂ` on an annulus `η ≤ |z| < 1` near the boundary — there are
`η ∈ [0,1)` and `δ > 0` with `|f(z) - α| ≥ δ` for every `z` with `η ≤ |z| < 1` — then `f` has bounded
characteristic.

The published proof passes to `g = 1 / (f - α)`, which is analytic and bounded (`|g| ≤ 1/δ`) on the
annulus, hence of bounded proximity there; its counting function is controlled by the finitely many
poles of `f` inside `|z| ≤ η`, so `T(r, g)` stays bounded, and the First Main Theorem gives
`T(r, f) = T(r, g) + O(1)`. The Nevanlinna machinery this needs — the characteristic on the disk and
the First Main Theorem near the boundary — is not in Mathlib, so the result is recorded as a
literature axiom on the authority of [Ber92], Proposition 1.2.4. -/
@[category research solved, AMS 30, ref "Ber92",
  informal_uses "poisson-jensen" "nevanlinna-characteristic"]
axiom hasBoundedCharacteristic_of_bddAway {f : ℂ → ℂ} (hf : MeromorphicOn f (ball 0 1))
    {α : ℂ} {η δ : ℝ} (hη : η ∈ Ico (0 : ℝ) 1) (hδ : 0 < δ)
    (hbound : ∀ z : ℂ, η ≤ ‖z‖ → ‖z‖ < 1 → δ ≤ ‖f z - α‖) :
    HasBoundedCharacteristic f

/-- **Proposition 1.2.5** (Bertin). Let `f` be meromorphic on the unit disk `D(0,1)`. If the real
part of `f` is bounded above near the boundary — there are `k ∈ ℝ` and `η ∈ [0,1)` with
`Re f(z) ≤ k` for every `z` with `η ≤ |z| < 1` — then `f` has bounded characteristic.

This is a **corollary of Proposition 1.2.4**: with the real part bounded by `k`, the value
`α = k + 1` is avoided with margin `δ = 1`, since
`|f(z) - α| ≥ |Re(f(z) - α)| = (k + 1) - Re f(z) ≥ 1` on the annulus. Geometrically, `f` maps the
annulus into the half-plane `{Re w ≤ k}`, which stays a fixed distance from `k + 1`. -/
@[category research solved, AMS 30, ref "Ber92", formal_uses hasBoundedCharacteristic_of_bddAway]
theorem hasBoundedCharacteristic_of_re_le {f : ℂ → ℂ} (hf : MeromorphicOn f (ball 0 1))
    {k η : ℝ} (hη : η ∈ Ico (0 : ℝ) 1)
    (hbound : ∀ z : ℂ, η ≤ ‖z‖ → ‖z‖ < 1 → (f z).re ≤ k) :
    HasBoundedCharacteristic f := by
  refine hasBoundedCharacteristic_of_bddAway hf hη (α := (k : ℂ) + 1) (δ := 1) one_pos ?_
  intro z hz1 hz2
  have hre : (f z - ((k : ℂ) + 1)).re ≤ -1 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith [hbound z hz1 hz2]
  calc (1 : ℝ) = -(-1) := by ring
    _ ≤ -(f z - ((k : ℂ) + 1)).re := by linarith
    _ ≤ |(f z - ((k : ℂ) + 1)).re| := neg_le_abs _
    _ ≤ ‖f z - ((k : ℂ) + 1)‖ := Complex.abs_re_le_norm _

end Complex
