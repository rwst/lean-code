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

This file records three classical factorization results from Bertin, *Pisot and Salem Numbers*,
§1.2 ("Criteria of rationality in ℂ"). The first two are recorded as **literature axioms**; the
third is **proved** here as a corollary of them.

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

end Complex
