/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.DistributionModOneBasics
import ForMathlib.Analysis.Equidistribution.IntegralCriterion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Eval.Defs
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Uniform distribution of sequences (Bertin §4.2–4.4)

Bertin's **Definition 4.2** of uniform distribution modulo one, phrased via the centered
fractional part `ε` (Bertin's convention, see `BertinPisot.DistributionModOneBasics`) and the
counting function `ν(a, b, N)` — the number of indices `n < N` with `ε(xₙ) ∈ [a, b)` — together
with the distribution criteria of §4.3 and the theorems of §4.4:

* **Theorem 4.3.1** (`uniformlyDistributedModOne_iff_integralCriterion`): u.d. mod 1 ⟺ every
  Riemann-integrable `f` satisfies `(1/N) Σ f(ε xₙ) → ∫ f` (the analytic engine lives axiom-free in
  `ForMathlib.Analysis.Equidistribution.IntegralCriterion`). Riemann-integrability is essential
  (`average_epsRangeIndicator_eq_one`).
* **Theorem 4.3.2** (`uniformlyDistributedModOne_iff_weylCriterion`): Weyl's criterion — u.d. mod 1
  ⟺ the Weyl sums `σ_h(N) = (1/N) Σ exp(2πi h xₙ) → 0` for every `h ∈ ℤ*`. The forward direction is
  proved (via 4.3.1 applied to `cos`/`sin`); the converse is cited.
* **Corollary** (`uniformlyDistributedModOne_nα_iff_irrational`): `(nα)` is u.d. mod 1 ⟺ `α` is
  irrational. Both halves are proved here from Weyl's criterion — the irrational case via the
  geometric Weyl-sum bound `weylCriterion_nα_of_irrational`.
* **Theorem 4.3.3** (`uniformlyDistributedModOne_comp_continuous_iff`): for continuous `φ`, the image
  `(φ(ε xₙ))` of a u.d. sequence is u.d. ⟺ `∫_{-1/2}^{1/2} exp(2πi h φ) = 0` for all `h ∈ ℤ*` (via
  the proved displayed limit `tendsto_average_exp_comp`; the iff is cited through 4.3.2).
* **§4.4** — **Van der Corput's theorem** (`vanDerCorput_theorem_4_4_1`: all difference sequences
  `(xₙ₊ₖ − xₙ)` u.d. ⟹ `(xₙ)` u.d.) and **Fejér's theorem** (`fejer_theorem_4_4_2`: smooth `g` with
  the stated growth of `g'` makes `(g(n))` u.d.), both cited (van der Corput inequality / lemma — not
  in Mathlib).

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §4.2–4.4.
  - [vdC31] van der Corput, J. G. "Diophantische Ungleichungen. I. Zur Gleichverteilung modulo
    Eins." *Acta Math.* 56 (1931), 373–456.
-/

namespace Bertin

open Filter MeasureTheory
open scoped Topology

open Classical in
/-- `ν(a, b, N)`: the number of indices `n < N` for which `ε(xₙ)` lies in the interval `[a, b)`
(intended for `-1/2 ≤ a < b ≤ 1/2`). -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def countModOne (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => ε (x n) ∈ Set.Ico a b)).card

/-- **Definition 4.2** (Bertin). The sequence `(xₙ)` is *uniformly distributed modulo one*
(u.d. mod 1) if for every pair `a < b` of reals with `-1/2 ≤ a < b ≤ 1/2`, the proportion of
indices `n < N` with `ε(xₙ) ∈ [a, b)` tends to the length of the interval:
`ν(a, b, N) / N → b - a` as `N → ∞`. -/
@[category API, AMS 11, ref "Ber92"]
def UniformlyDistributedModOne (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, -(1/2) ≤ a → a < b → b ≤ 1/2 →
    Tendsto (fun N : ℕ => (countModOne x a b N : ℝ) / N) atTop (𝓝 (b - a))

/-- Sanity check: the count `ν(a, b, N)` never exceeds `N`. -/
@[category test, AMS 11, ref "Ber92"]
theorem countModOne_le (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : countModOne x a b N ≤ N := by
  rw [countModOne]
  calc ((Finset.range N).filter (fun n => ε (x n) ∈ Set.Ico a b)).card
      ≤ (Finset.range N).card := Finset.card_filter_le _ _
    _ = N := Finset.card_range N

/-- **Bertin's example**: `(log n)_{n ≥ 1}` is *dense* modulo one
(`Bertin.dense_eps_log`) yet **not** uniformly distributed modulo one — density does not imply
uniform distribution.

Taking `a = 0` and any `0 < b ≤ 1/2`: `ε(log n) ∈ [0, b)` iff `n ∈ [eᵐ, e^{m+b})` for some
integer `m`, so along the subsequence `N = E(e^{m+b})` the count is
`ν(0, b, N) = Σ_{k=0}^{m} (e^{k+b} - eᵏ) + O(m) = (e^b - 1)(e^{m+1} - 1)/(e - 1) + O(m)`.
Since `E(e^{m+b})/e^{m+b} → 1`, the ratio `ν(0,b,N)/N → (e^b - 1)·e^{1-b}/(e - 1) ≠ b`, so the
defining limit `ν(0,b,N)/N → b` fails. This is an asymptotic density computation (geometric sums
with floor error terms and a subsequence limit), beyond what is convenient to formalize here, so
it is recorded as a cited result. -/
@[category textbook, AMS 11, ref "Ber92"]
axiom not_uniformlyDistributedModOne_log :
    ¬ UniformlyDistributedModOne (fun n => Real.log n)

/-! ### Theorem 4.3.1 — the Riemann-integral criterion -/

/-- Lebesgue's criterion for Riemann-integrability on a set `s`: `f` is bounded on `s` and its
set of discontinuities within `s` is Lebesgue-null. (Mathlib has no standalone Riemann-integral
predicate, so we use this characterisation.) -/
@[category API, AMS 11, ref "Ber92"]
def IsRiemannIntegrableOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∃ C, ∀ t ∈ s, |f t| ≤ C) ∧ volume {t ∈ s | ¬ ContinuousAt f t} = 0

/-- The Riemann-integral criterion for `(xₙ)`: for every Riemann-integrable `f` on `[-1/2, 1/2]`,
the average `(1/N) Σ_{n<N} f(ε xₙ)` converges to `∫_{-1/2}^{1/2} f`. -/
@[category API, AMS 11, ref "Ber92"]
def IntegralCriterion (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, IsRiemannIntegrableOn f (Set.Icc (-(1/2) : ℝ) (1/2)) →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (ε (x n))) / N) atTop
      (𝓝 (∫ t in (-(1/2) : ℝ)..(1/2), f t))

/-- The easy direction of Theorem 4.3.1: the integral criterion implies uniform distribution.
Apply the criterion to the indicator `𝟙_{[a,b)}` (Riemann-integrable, with integral `b - a`),
whose average is exactly `ν(a,b,N)/N`. -/
@[category research solved, AMS 11, ref "Ber92"]
theorem uniformlyDistributedModOne_of_integralCriterion (x : ℕ → ℝ)
    (h : IntegralCriterion x) : UniformlyDistributedModOne x := by
  intro a b ha hab hb
  set g : ℝ → ℝ := Set.indicator (Set.Ico a b) (fun _ => 1) with hg
  -- `g = 𝟙_{[a,b)}` is Riemann-integrable: bounded by `1`, discontinuous only at `{a, b}`.
  have hRI : IsRiemannIntegrableOn g (Set.Icc (-(1/2) : ℝ) (1/2)) := by
    refine ⟨⟨1, fun t _ => by rw [hg, Set.indicator_apply]; split <;> simp⟩, ?_⟩
    have hsub : {t ∈ Set.Icc (-(1/2) : ℝ) (1/2) | ¬ ContinuousAt g t} ⊆ ({a, b} : Set ℝ) := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      have hc0 : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t := continuousAt_const
      have hc1 : ContinuousAt (fun _ : ℝ => (1 : ℝ)) t := continuousAt_const
      rcases lt_trichotomy t a with hta | hta | hta
      · refine absurd ?_ ht.2; rw [hg]; refine hc0.congr ?_
        filter_upwards [Iio_mem_nhds hta] with s hs
        rw [Set.indicator_apply, if_neg (fun hm => absurd hm.1 (not_le.mpr hs))]
      · exact Set.mem_insert_iff.mpr (Or.inl hta)
      · rcases lt_trichotomy t b with htb | htb | htb
        · refine absurd ?_ ht.2; rw [hg]; refine hc1.congr ?_
          filter_upwards [Ioo_mem_nhds hta htb] with s hs
          rw [Set.indicator_apply, if_pos ⟨hs.1.le, hs.2⟩]
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr htb))
        · refine absurd ?_ ht.2; rw [hg]; refine hc0.congr ?_
          filter_upwards [Ioi_mem_nhds htb] with s hs
          rw [Set.indicator_apply, if_neg (fun hm => absurd hm.2 (not_lt.mpr hs.le))]
    exact measure_mono_null hsub (((Set.finite_singleton b).insert a).measure_zero volume)
  have hcrit := h g hRI
  -- `∫_{-1/2}^{1/2} 𝟙_{[a,b)} = b - a`.
  have hint : (∫ t in (-(1/2) : ℝ)..(1/2), g t) = b - a := by
    have hvol : volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico a b) = ENNReal.ofReal (b - a) := by
      apply le_antisymm
      · calc volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico a b)
            ≤ volume (Set.Icc a b) := measure_mono (fun t ht => Set.Ico_subset_Icc_self ht.2)
          _ = ENNReal.ofReal (b - a) := Real.volume_Icc
      · calc ENNReal.ofReal (b - a) = volume (Set.Ioo a b) := (Real.volume_Ioo).symm
          _ ≤ volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico a b) :=
              measure_mono (fun t ht => ⟨Set.mem_Ioc.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩,
                Set.Ioo_subset_Ico_self ht⟩)
    rw [hg, intervalIntegral.integral_of_le (by linarith : (-(1/2) : ℝ) ≤ 1/2),
      setIntegral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def, hvol, ENNReal.toReal_ofReal (by linarith)]
  rw [hint] at hcrit
  -- and `Σ_{n<N} 𝟙_{[a,b)}(ε xₙ) = ν(a,b,N)`.
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, g (ε (x n))) = (countModOne x a b N : ℝ) := by
    intro N
    simp only [hg, Set.indicator_apply, countModOne]
    rw [Finset.sum_boole]
  simp_rw [hsum] at hcrit
  exact hcrit

/-- The hard direction of Theorem 4.3.1: uniform distribution implies the integral criterion.
Its proof approximates a Riemann-integrable `f` from below and above by dyadic step functions and
uses the interval case (uniform distribution) together with a squeeze. The general analytic engine
— the Riemann/Darboux step-function approximation — is formalised (axiom-free) in
`ForMathlib.Analysis.Equidistribution.IntegralCriterion`; here we instantiate it at the centered
fractional parts `yₙ = ε(xₙ) ∈ [-1/2, 1/2)` of the sequence. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses tendsto_average_of_indicator_equidistributed]
theorem integralCriterion_of_uniformlyDistributedModOne (x : ℕ → ℝ)
    (h : UniformlyDistributedModOne x) : IntegralCriterion x := by
  intro f hf
  obtain ⟨hbdd, hae⟩ := hf
  -- The interval-indicator equidistribution hypothesis, read off from `UniformlyDistributedModOne`.
  have hH : ∀ a b : ℝ, -(1/2) ≤ a → a < b → b ≤ 1/2 →
      Tendsto (fun N => (∑ m ∈ Finset.range N,
        (Set.Ico a b).indicator (fun _ => (1:ℝ)) (ε (x m))) / N) atTop
        (𝓝 ((b - a) / (1/2 - -(1/2)))) := by
    intro a b ha hab hb
    have hcount : ∀ N : ℕ,
        (∑ m ∈ Finset.range N, (Set.Ico a b).indicator (fun _ => (1:ℝ)) (ε (x m)))
          = (countModOne x a b N : ℝ) := by
      intro N; simp only [Set.indicator_apply, countModOne]; rw [Finset.sum_boole]
    simp_rw [hcount]
    rw [show (b - a) / (1/2 - -(1/2)) = b - a by norm_num]
    exact h a b ha hab hb
  have key := tendsto_average_of_indicator_equidistributed (c := -(1/2)) (d := 1/2)
    (by norm_num) hbdd hae (fun n => ε (x n)) (fun n => ε_mem_Ico (x n)) hH
  -- Convert the `Set.Icc` integral (length-one interval) to the interval integral of `IntegralCriterion`.
  have hconv : ∫ t in (-(1/2):ℝ)..(1/2), f t
      = (∫ t in Set.Icc (-(1/2):ℝ) (1/2), f t) / (1/2 - -(1/2)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2),
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    norm_num
  rw [hconv]
  exact key

/-- **Theorem 4.3.1** (Bertin). A sequence `(xₙ)` is uniformly distributed modulo one **iff**, for
every Riemann-integrable `f` on `[-1/2, 1/2]`, `(1/N) Σ_{n<N} f(ε xₙ) → ∫_{-1/2}^{1/2} f`. The
forward direction is cited (`integralCriterion_of_uniformlyDistributedModOne`); the reverse is
proved (`uniformlyDistributedModOne_of_integralCriterion`). -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses integralCriterion_of_uniformlyDistributedModOne
    uniformlyDistributedModOne_of_integralCriterion]
theorem uniformlyDistributedModOne_iff_integralCriterion (x : ℕ → ℝ) :
    UniformlyDistributedModOne x ↔ IntegralCriterion x :=
  ⟨integralCriterion_of_uniformlyDistributedModOne x,
    uniformlyDistributedModOne_of_integralCriterion x⟩

/-! ### Example: Riemann-integrability is essential -/

/-- **Bertin's example** (§4.2): the characteristic function `χ = 𝟙_J` of the set
`J = {ε(xₙ) : n}` of centered fractional parts of an arbitrary real sequence `(xₙ)`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def epsRangeIndicator (x : ℕ → ℝ) : ℝ → ℝ :=
  (Set.range fun m => ε (x m)).indicator (fun _ => 1)

/-- The set `J = {ε(xₙ) : n}` is countable, so `χ = 𝟙_J` is Lebesgue-integrable on `[-1/2, 1/2]`. -/
@[category textbook, AMS 11, ref "Ber92"]
theorem integrableOn_epsRangeIndicator (x : ℕ → ℝ) :
    IntegrableOn (epsRangeIndicator x) (Set.Icc (-(1/2) : ℝ) (1/2)) := by
  have hfin : volume (Set.Icc (-(1/2) : ℝ) (1/2)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  rw [epsRangeIndicator]
  exact (integrableOn_const hfin).indicator (Set.countable_range _).measurableSet

/-- The integral of `χ = 𝟙_J` over `[-1/2, 1/2]` is `0`: the set `J = {ε(xₙ) : n}` is countable,
hence Lebesgue-null. -/
@[category textbook, AMS 11, ref "Ber92"]
theorem integral_epsRangeIndicator_eq_zero (x : ℕ → ℝ) :
    ∫ t in (-(1/2) : ℝ)..(1/2), epsRangeIndicator x t = 0 := by
  have hnull : volume (Set.range fun m => ε (x m)) = 0 :=
    (Set.countable_range _).measure_zero volume
  rw [epsRangeIndicator, intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
      setIntegral_indicator (Set.countable_range _).measurableSet, setIntegral_const, smul_eq_mul,
      mul_one, measureReal_def, measure_mono_null Set.inter_subset_right hnull, ENNReal.toReal_zero]

/-- **Bertin's example** (§4.2). Riemann-integrability cannot be relaxed to mere
Lebesgue-integrability in the integral criterion (Theorem 4.3.1): for the characteristic function
`χ = 𝟙_J` of `J = {ε(xₙ) : n}` — Lebesgue-integrable with integral `0`
(`integral_epsRangeIndicator_eq_zero`) — every sample `ε(xₙ)` lies in `J`, so `χ(ε xₙ) = 1` for all
`n` and the averages are constantly `1`: `(1/N) Σ_{n<N} χ(ε xₙ) = 1` for every `N ≥ 1`. This does
**not** converge to `∫ χ = 0`, so `χ` violates the criterion's conclusion. -/
@[category textbook, AMS 11, ref "Ber92"]
theorem average_epsRangeIndicator_eq_one (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Finset.range N, epsRangeIndicator x (ε (x n))) / N = 1 := by
  have hone : ∀ n, epsRangeIndicator x (ε (x n)) = 1 := fun n => by
    rw [epsRangeIndicator]; exact Set.indicator_of_mem (Set.mem_range_self n) _
  simp only [hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [div_self (by exact_mod_cast hN.ne')]

/-! ### Theorem 4.3.2 — Weyl's criterion (exponential sums) -/

/-- **Weyl's criterion** condition: the exponential sums `(1/N) Σ_{n<N} exp(2πi h xₙ)` vanish in the
limit, for every non-zero integer `h`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def WeylCriterion (x : ℕ → ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * h * x n)) / N) atTop (𝓝 0)

/-- A continuous function bounded by `1` is Riemann-integrable on `[-1/2, 1/2]` (its discontinuity
set is empty). -/
private theorem isRiemann_trig {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ t, |g t| ≤ 1) :
    IsRiemannIntegrableOn g (Set.Icc (-(1/2) : ℝ) (1/2)) := by
  refine ⟨⟨1, fun t _ => hb t⟩, ?_⟩
  have hempty : {t ∈ Set.Icc (-(1/2) : ℝ) (1/2) | ¬ ContinuousAt g t} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]; exact fun t ht => ht.2 hg.continuousAt
  rw [hempty, measure_empty]

/-- `∫_{-1/2}^{1/2} cos(2πh t) dt = 0` for a non-zero integer `h`. -/
private theorem integral_cos_eq_zero (h : ℤ) (hh : h ≠ 0) :
    ∫ t in (-(1/2) : ℝ)..(1/2), Real.cos (2 * Real.pi * h * t) = 0 := by
  have hne : (2 * Real.pi * (h : ℝ)) ≠ 0 := by
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have hderiv : ∀ t ∈ Set.uIcc (-(1/2) : ℝ) (1/2),
      HasDerivAt (fun t => Real.sin (2 * Real.pi * h * t) / (2 * Real.pi * h))
        (Real.cos (2 * Real.pi * h * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * (h : ℝ) * t) (2 * Real.pi * h) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi * (h : ℝ))
    have h2 := ((Real.hasDerivAt_sin (2 * Real.pi * h * t)).comp t h1).div_const (2 * Real.pi * h)
    convert h2 using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _)]
  have e1 : (2 * Real.pi * (h : ℝ) * (1/2)) = ((h : ℤ) : ℝ) * Real.pi := by ring
  have e2 : (2 * Real.pi * (h : ℝ) * (-(1/2))) = ((-h : ℤ) : ℝ) * Real.pi := by push_cast; ring
  rw [e1, e2, Real.sin_int_mul_pi, Real.sin_int_mul_pi]; simp

/-- `∫_{-1/2}^{1/2} sin(2πh t) dt = 0` for a non-zero integer `h`. -/
private theorem integral_sin_eq_zero (h : ℤ) (hh : h ≠ 0) :
    ∫ t in (-(1/2) : ℝ)..(1/2), Real.sin (2 * Real.pi * h * t) = 0 := by
  have hne : (2 * Real.pi * (h : ℝ)) ≠ 0 := by
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have hderiv : ∀ t ∈ Set.uIcc (-(1/2) : ℝ) (1/2),
      HasDerivAt (fun t => -Real.cos (2 * Real.pi * h * t) / (2 * Real.pi * h))
        (Real.sin (2 * Real.pi * h * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * (h : ℝ) * t) (2 * Real.pi * h) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi * (h : ℝ))
    have h2 := (((Real.hasDerivAt_cos (2 * Real.pi * h * t)).comp t h1).neg).div_const (2 * Real.pi * h)
    convert h2 using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_sin.comp (by fun_prop)).intervalIntegrable _ _)]
  have e1 : (2 * Real.pi * (h : ℝ) * (1/2)) = ((h : ℤ) : ℝ) * Real.pi := by ring
  have e2 : (2 * Real.pi * (h : ℝ) * (-(1/2))) = -(((h : ℤ) : ℝ) * Real.pi) := by ring
  rw [e1, e2, Real.cos_neg]; ring

/-- `exp(2πi h z) = cos(2πh e) + i·sin(2πh e)` when `z = k + e` with `k` an integer: the
exponential depends only on the fractional part `e`. -/
private theorem weyl_term (h : ℤ) (z e : ℝ) (k : ℤ) (hz : z = (k : ℝ) + e) :
    Complex.exp (2 * Real.pi * Complex.I * h * z)
      = ↑(Real.cos (2 * Real.pi * h * e)) + ↑(Real.sin (2 * Real.pi * h * e)) * Complex.I := by
  have hsplit : (2 * Real.pi * Complex.I * h * z : ℂ)
      = (↑(h * k) * (2 * ↑Real.pi * Complex.I)) + ↑(2 * Real.pi * (h : ℝ) * e) * Complex.I := by
    rw [hz]; push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]

/-- The forward direction of **Theorem 4.3.2** (Weyl): u.d. mod 1 implies the exponential sums
vanish. By Theorem 4.3.1 the averages `(1/N) Σ cos(2πh ε xₙ)` and `(1/N) Σ sin(2πh ε xₙ)` converge
to `∫ cos = 0` and `∫ sin = 0` (for `h ≠ 0`); recombining the real and imaginary parts, and using
`exp(2πi h xₙ) = exp(2πi h ε xₙ)`, gives the complex exponential sum `→ 0`. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses integralCriterion_of_uniformlyDistributedModOne]
theorem weylCriterion_of_uniformlyDistributedModOne (x : ℕ → ℝ)
    (h : UniformlyDistributedModOne x) : WeylCriterion x := by
  intro m hm
  have hcrit := integralCriterion_of_uniformlyDistributedModOne x h
  have hcos := hcrit (fun t => Real.cos (2 * Real.pi * m * t))
    (isRiemann_trig (by fun_prop) (fun t => Real.abs_cos_le_one _))
  have hsin := hcrit (fun t => Real.sin (2 * Real.pi * m * t))
    (isRiemann_trig (by fun_prop) (fun t => Real.abs_sin_le_one _))
  rw [integral_cos_eq_zero m hm] at hcos
  rw [integral_sin_eq_zero m hm] at hsin
  have hrw : ∀ N : ℕ, (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * m * x n)) / N
      = Complex.ofReal ((∑ n ∈ Finset.range N, Real.cos (2 * Real.pi * m * ε (x n))) / (N : ℝ))
        + Complex.ofReal ((∑ n ∈ Finset.range N, Real.sin (2 * Real.pi * m * ε (x n))) / (N : ℝ))
          * Complex.I := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ =>
          weyl_term m (x n) (ε (x n)) (round (x n)) (self_eq_round_add_ε (x n))),
        Finset.sum_add_distrib, ← Finset.sum_mul]
    push_cast; ring
  rw [tendsto_congr hrw]
  have ha : Tendsto (fun N : ℕ => Complex.ofReal
      ((∑ n ∈ Finset.range N, Real.cos (2 * Real.pi * m * ε (x n))) / (N : ℝ))) atTop (𝓝 0) := by
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hcos
    rwa [Complex.ofReal_zero] at hc
  have hb : Tendsto (fun N : ℕ => Complex.ofReal
      ((∑ n ∈ Finset.range N, Real.sin (2 * Real.pi * m * ε (x n))) / (N : ℝ))) atTop (𝓝 0) := by
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hsin
    rwa [Complex.ofReal_zero] at hc
  simpa using ha.add (hb.mul_const Complex.I)

/-- The converse direction of **Theorem 4.3.2** (Weyl): vanishing exponential sums imply u.d. mod 1.
Its proof expands a continuous `1`-periodic function in trigonometric polynomials (Fejér /
Stone–Weierstrass), passes the limit through the finite exponential sums, and concludes via the
integral criterion (Theorem 4.3.1). The trigonometric-density step is available in Mathlib
(`AddCircle.span_fourier_closure_eq_top`), but assembling it — through the centered `ε`-averages and
a continuous-to-step squeeze — into the equidistribution statement is a separate development, so the
converse is recorded here as a cited result. -/
@[category research solved, AMS 11, ref "Ber92"]
axiom uniformlyDistributedModOne_of_weylCriterion (x : ℕ → ℝ)
    (h : WeylCriterion x) : UniformlyDistributedModOne x

/-- **Theorem 4.3.2** (Weyl's criterion). A sequence `(xₙ)` of real numbers is uniformly distributed
modulo one **iff** `lim_{N→∞} (1/N) Σ_{n<N} exp(2πi h xₙ) = 0` for every non-zero integer `h`. The
forward direction is proved (via Theorem 4.3.1, applied to `cos` and `sin`); the converse is cited
(trigonometric-polynomial density). -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses weylCriterion_of_uniformlyDistributedModOne uniformlyDistributedModOne_of_weylCriterion]
theorem uniformlyDistributedModOne_iff_weylCriterion (x : ℕ → ℝ) :
    UniformlyDistributedModOne x ↔ WeylCriterion x :=
  ⟨weylCriterion_of_uniformlyDistributedModOne x, uniformlyDistributedModOne_of_weylCriterion x⟩

/-! ### Corollary — `(nα)` is u.d. mod 1 iff `α` is irrational -/

/-- The **Weyl sums** of `(nα)` vanish when `α` is irrational: for every non-zero integer `h`,
`σ_h(N) = (1/N) Σ_{n<N} exp(2πi h n α) → 0`. This is the geometric-series estimate at the heart of
Bertin's Corollary: the sum telescopes to `(zᴺ - 1)/(z - 1)` with `z = exp(2πi h α)`, where `z ≠ 1`
because `h α ∉ ℤ` (`α` irrational, `h ≠ 0`), and `|z| = 1` gives
`|σ_h(N)| ≤ 2/(N |z - 1|) → 0` (Bertin's bound `≤ 1/(N |sin π h α|)`). -/
@[category research solved, AMS 11, ref "Ber92"]
theorem weylCriterion_nα_of_irrational {α : ℝ} (hα : Irrational α) :
    WeylCriterion (fun n => (n : ℝ) * α) := by
  intro h hh
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * h * α) with hz
  -- each term is a power of `z`: `exp(2πi h (n α)) = zⁿ`.
  have hterm : ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * h * (((n : ℝ) * α : ℝ) : ℂ)) = z ^ n := by
    intro n
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  -- `z ≠ 1`: otherwise `h α` would be an integer, contradicting irrationality of `h α`.
  have hirr : Irrational ((h : ℝ) * α) := hα.intCast_mul hh
  have hz1 : z ≠ 1 := by
    rw [hz, Ne, Complex.exp_eq_one_iff]
    rintro ⟨k, hk⟩
    apply hirr.ne_int k
    have h2πI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have key : (h : ℂ) * (α : ℂ) = (k : ℂ) := by
      apply mul_right_cancel₀ h2πI; linear_combination hk
    exact_mod_cast key
  -- `|z| = 1`, since the exponent is purely imaginary.
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (α : ℂ))
      = ((2 * Real.pi * (h : ℝ) * α : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hznorm : ‖z‖ = 1 := by rw [hz, harg, Complex.norm_exp]; simp
  -- the geometric quotient `(zᴺ - 1)/(z - 1)/N → 0` by the modulus bound `|zᴺ - 1| ≤ 2`.
  have hmain : Tendsto (fun N : ℕ => (z ^ N - 1) / (z - 1) / (N : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖z - 1‖))
    have hzz : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [norm_pow, hznorm, one_pow, norm_one]
        _ = 2 := by norm_num
    rw [norm_div, norm_div, Complex.norm_natCast]
    gcongr
  -- transfer to the Weyl average via the geometric-sum identity (`exact` absorbs the coercion form).
  refine hmain.congr (fun N => ?_)
  rw [← geom_sum_eq hz1 N]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => (hterm n).symm)

/-- The converse half of the Corollary: if `(nα)` is uniformly distributed modulo one, then `α` is
irrational. Contrapositive: for rational `α = p/q`, take `h = q`; then `exp(2πi q α) = 1`, so every
Weyl term is `1` and `σ_q(N) = 1 → 1 ≠ 0`, violating Weyl's criterion (Theorem 4.3.2) — which u.d.
mod 1 would entail by `weylCriterion_of_uniformlyDistributedModOne`. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses weylCriterion_of_uniformlyDistributedModOne]
theorem irrational_of_uniformlyDistributedModOne_nα {α : ℝ}
    (hud : UniformlyDistributedModOne (fun n => (n : ℝ) * α)) : Irrational α := by
  by_contra hrat
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = α := by simpa [Irrational, not_not] using hrat
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  -- `q.den · α = q.num ∈ ℤ`, so the character at `h = r.den` is identically `1`.
  have hcast : (r.den : ℝ) * α = (r.num : ℝ) := by rw [← hr, Rat.cast_def]; field_simp
  have hHne : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_nz
  have hHα : ((r.den : ℤ) : ℂ) * (α : ℂ) = (r.num : ℂ) := by exact_mod_cast hcast
  have hexp1 : Complex.exp (2 * Real.pi * Complex.I * ((r.den : ℤ) : ℂ) * (α : ℂ)) = 1 := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((r.den : ℤ) : ℂ) * (α : ℂ))
          = (r.num : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hHα]
    exact Complex.exp_int_mul_two_pi_mul_I r.num
  have hone : ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * ((r.den : ℤ) : ℂ) * (((n : ℝ) * α : ℝ) : ℂ)) = 1 := by
    intro n
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((r.den : ℤ) : ℂ) * (((n : ℝ) * α : ℝ) : ℂ))
          = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((r.den : ℤ) : ℂ) * (α : ℂ)) by
        push_cast; ring, Complex.exp_nat_mul, hexp1, one_pow]
  -- u.d. ⟹ Weyl's criterion (the proved forward direction), evaluated at `h = r.den`.
  have hweyl := weylCriterion_of_uniformlyDistributedModOne _ hud (r.den : ℤ) hHne
  -- but the same sequence of averages is constantly `1`, so it also tends to `1 ≠ 0` — contradiction.
  have hcontra : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 0) := by
    refine hweyl.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    show (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((r.den : ℤ) : ℂ) * (((n : ℝ) * α : ℝ) : ℂ)))
          / (N : ℂ) = 1
    rw [Finset.sum_congr rfl (fun n _ => hone n)]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast hN.ne')
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hcontra)

/-- **Corollary** (Bertin, after Theorem 4.3.2). The sequence `(nα)` is uniformly distributed modulo
one **if and only if** `α` is irrational. The irrational case is the geometric Weyl-sum bound
(`weylCriterion_nα_of_irrational`) fed into Weyl's criterion (Theorem 4.3.2); the rational case fails
because `(nα)` then takes finitely many values modulo one
(`Bertin.finite_range_fract_mul_of_not_irrational`). -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses weylCriterion_nα_of_irrational irrational_of_uniformlyDistributedModOne_nα
    uniformlyDistributedModOne_of_weylCriterion]
theorem uniformlyDistributedModOne_nα_iff_irrational (α : ℝ) :
    UniformlyDistributedModOne (fun n => (n : ℝ) * α) ↔ Irrational α :=
  ⟨irrational_of_uniformlyDistributedModOne_nα,
    fun hα => uniformlyDistributedModOne_of_weylCriterion _ (weylCriterion_nα_of_irrational hα)⟩

/-! ### Theorem 4.3.3 — image of a u.d. sequence under a continuous map -/

/-- A real function continuous on `[-1/2, 1/2]` and bounded by `C` is Riemann-integrable there: its
discontinuities within the interval can only be the two endpoints, a null set. -/
private theorem isRiemannIntegrableOn_of_continuousOn {g : ℝ → ℝ} {C : ℝ}
    (hg : ContinuousOn g (Set.Icc (-(1/2) : ℝ) (1/2))) (hb : ∀ t, |g t| ≤ C) :
    IsRiemannIntegrableOn g (Set.Icc (-(1/2) : ℝ) (1/2)) := by
  refine ⟨⟨C, fun t _ => hb t⟩, measure_mono_null ?_
    (((Set.finite_singleton (1/2 : ℝ)).insert (-(1/2))).measure_zero volume)⟩
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  obtain ⟨htIcc, htdisc⟩ := ht
  by_contra hmem
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  push Not at hmem
  rw [Set.mem_Icc] at htIcc
  exact htdisc (hg.continuousAt (Icc_mem_nhds (lt_of_le_of_ne htIcc.1 (Ne.symm hmem.1))
    (lt_of_le_of_ne htIcc.2 hmem.2)))

/-- The displayed limit in Bertin's proof of Theorem 4.3.3: for `(xₙ)` u.d. mod 1 and `φ` continuous
on `[-1/2, 1/2]`, applying Theorem 4.3.1 to the (continuous, hence Riemann-integrable) real and
imaginary parts `cos`, `sin` of `t ↦ exp(2πi h φ(t))` and recombining via Euler's formula gives
`(1/N) Σ_{n<N} exp(2πi h φ(ε xₙ)) → ∫_{-1/2}^{1/2} exp(2πi h φ(t)) dt` for every integer `h`. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses integralCriterion_of_uniformlyDistributedModOne]
theorem tendsto_average_exp_comp (x : ℕ → ℝ) (hx : UniformlyDistributedModOne x)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Icc (-(1/2) : ℝ) (1/2))) (h : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * h * φ (ε (x n)))) / N) atTop
      (𝓝 (∫ t in (-(1/2) : ℝ)..(1/2), Complex.exp (2 * Real.pi * Complex.I * h * φ t))) := by
  have hcrit := integralCriterion_of_uniformlyDistributedModOne x hx
  have hμcos : ContinuousOn (fun t => Real.cos (2 * Real.pi * h * φ t))
      (Set.Icc (-(1/2) : ℝ) (1/2)) := by fun_prop
  have hμsin : ContinuousOn (fun t => Real.sin (2 * Real.pi * h * φ t))
      (Set.Icc (-(1/2) : ℝ) (1/2)) := by fun_prop
  -- Theorem 4.3.1 on the real parts
  have hcos := hcrit _ (isRiemannIntegrableOn_of_continuousOn hμcos (fun t => Real.abs_cos_le_one _))
  have hsin := hcrit _ (isRiemannIntegrableOn_of_continuousOn hμsin (fun t => Real.abs_sin_le_one _))
  -- Euler's formula on each value `r = φ(…)`
  have hEuler : ∀ r : ℝ, Complex.exp (2 * Real.pi * Complex.I * h * r)
      = ↑(Real.cos (2 * Real.pi * h * r)) + ↑(Real.sin (2 * Real.pi * h * r)) * Complex.I := by
    intro r
    rw [show (2 * (Real.pi : ℂ) * Complex.I * h * (r : ℝ))
          = ((2 * Real.pi * (h : ℝ) * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  -- recombine the sample average
  have hrwsum : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * h * φ (ε (x n)))) / N
        = ↑((∑ n ∈ Finset.range N, Real.cos (2 * Real.pi * h * φ (ε (x n)))) / (N : ℝ))
          + ↑((∑ n ∈ Finset.range N, Real.sin (2 * Real.pi * h * φ (ε (x n)))) / (N : ℝ))
            * Complex.I := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => hEuler (φ (ε (x n)))), Finset.sum_add_distrib,
      ← Finset.sum_mul]
    push_cast; ring
  -- recombine the integral
  have hintIcos : IntervalIntegrable (fun t => (↑(Real.cos (2 * Real.pi * h * φ t)) : ℂ)) volume
      (-(1/2)) (1/2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)]
    exact Complex.continuous_ofReal.comp_continuousOn hμcos
  have hintIsin : IntervalIntegrable
      (fun t => (↑(Real.sin (2 * Real.pi * h * φ t)) : ℂ) * Complex.I) volume (-(1/2)) (1/2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)]
    exact (Complex.continuous_ofReal.comp_continuousOn hμsin).mul continuousOn_const
  have hint : (∫ t in (-(1/2) : ℝ)..(1/2), Complex.exp (2 * Real.pi * Complex.I * h * φ t))
      = ↑(∫ t in (-(1/2) : ℝ)..(1/2), Real.cos (2 * Real.pi * h * φ t))
        + ↑(∫ t in (-(1/2) : ℝ)..(1/2), Real.sin (2 * Real.pi * h * φ t)) * Complex.I := by
    rw [intervalIntegral.integral_congr (g := fun t => ↑(Real.cos (2 * Real.pi * h * φ t))
          + ↑(Real.sin (2 * Real.pi * h * φ t)) * Complex.I) (fun t _ => hEuler (φ t)),
      intervalIntegral.integral_add hintIcos hintIsin, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  rw [tendsto_congr hrwsum, hint]
  exact ((Complex.continuous_ofReal.tendsto _).comp hcos).add
    (((Complex.continuous_ofReal.tendsto _).comp hsin).mul_const Complex.I)

/-- **Theorem 4.3.3** (Bertin). Let `(xₙ)` be uniformly distributed modulo one and `φ` a continuous
function on `[-1/2, 1/2]`. Then the sequence `(φ(ε xₙ))` is uniformly distributed modulo one **iff**
`∫_{-1/2}^{1/2} exp(2πi h φ(t)) dt = 0` for every non-zero integer `h`. Proof (Bertin): by Theorem
4.3.1 the Weyl sums of `(φ(ε xₙ))` converge to those integrals (`tendsto_average_exp_comp`), so they
vanish iff the integrals do; vanishing Weyl sums is uniform distribution by Theorem 4.3.2. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses tendsto_average_exp_comp uniformlyDistributedModOne_iff_weylCriterion]
theorem uniformlyDistributedModOne_comp_continuous_iff (x : ℕ → ℝ)
    (hx : UniformlyDistributedModOne x) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc (-(1/2) : ℝ) (1/2))) :
    UniformlyDistributedModOne (fun n => φ (ε (x n))) ↔
      ∀ h : ℤ, h ≠ 0 →
        (∫ t in (-(1/2) : ℝ)..(1/2), Complex.exp (2 * Real.pi * Complex.I * h * φ t)) = 0 := by
  rw [uniformlyDistributedModOne_iff_weylCriterion]
  constructor
  · intro hweyl h hh
    exact tendsto_nhds_unique (tendsto_average_exp_comp x hx hφ h) (hweyl h hh)
  · intro hint h hh
    rw [← hint h hh]
    exact tendsto_average_exp_comp x hx hφ h

/-! ### §4.4 — Van der Corput's and Fejér's theorems -/

/-- **Theorem 4.4.1** (Van der Corput). If for *every* positive integer `k` the difference sequence
`(xₙ₊ₖ − xₙ)ₙ` is uniformly distributed modulo one, then `(xₙ)` itself is uniformly distributed
modulo one.

Proof (van der Corput): by **van der Corput's fundamental inequality** — a Cauchy–Schwarz bound on
the Weyl sums of `(xₙ)` in terms of those of the differences — for every `H ≥ 1`,
`|σ_h(N)|² ≤ (N+H)/((H+1)N) + (2/(H+1)) Σ_{k=1}^{H} (1 − k/(H+1)) · Re σ^{(k)}_h(N)`, where
`σ^{(k)}_h` is the Weyl sum of the `k`-th difference `(xₙ₊ₖ − xₙ)`. By hypothesis and Theorem 4.3.2
each `σ^{(k)}_h(N) → 0`, so `limsup_N |σ_h(N)|² ≤ 1/(H+1)`; letting `H → ∞` gives `σ_h(N) → 0`,
i.e. `(xₙ)` is u.d. by Theorem 4.3.2. The fundamental inequality is not in Mathlib and is well beyond
a short proof, so the theorem is recorded as a cited result. -/
@[category research solved, AMS 11, ref "Ber92" "vdC31"]
axiom vanDerCorput_theorem_4_4_1 (x : ℕ → ℝ)
    (h : ∀ k : ℕ, 0 < k → UniformlyDistributedModOne (fun n => x (n + k) - x n)) :
    UniformlyDistributedModOne x

/-- **Theorem 4.4.2** (Fejér). Let `g` have a continuous derivative `g'` on `[1, ∞)` such that
(i) `g` is increasing with `g(t) → +∞`, and (ii) `g'` is decreasing with `g'(t) → 0` and
`t · g'(t) → +∞`. Then the sequence `(g(n))ₙ` is uniformly distributed modulo one.

Proof (Fejér): estimate the Weyl sums `Σ_{n≤N} exp(2πi h g(n))` by **van der Corput's lemma** for
exponential sums with a monotone derivative (a Kuzmin–Landau / van der Corput bound of the form
`|Σ exp(2πi g(n))| ≪ 1/‖g'‖ + (oscillation of g')`); the hypotheses `g' ↓ 0` and `t g'(t) → ∞` make
this `o(N)`, so the Weyl sums vanish and `(g(n))` is u.d. by Theorem 4.3.2. The estimate is not in
Mathlib, so the theorem is recorded as a cited result. -/
@[category research solved, AMS 11, ref "Ber92"]
axiom fejer_theorem_4_4_2 (g g' : ℝ → ℝ)
    (hderiv : ∀ t : ℝ, 1 ≤ t → HasDerivAt g (g' t) t)
    (hg'_cont : ContinuousOn g' (Set.Ici 1))
    (hg_mono : MonotoneOn g (Set.Ici 1))
    (hg_top : Tendsto g atTop atTop)
    (hg'_anti : AntitoneOn g' (Set.Ici 1))
    (hg'_zero : Tendsto g' atTop (𝓝 0))
    (hg'_mul_top : Tendsto (fun t => t * g' t) atTop atTop) :
    UniformlyDistributedModOne (fun n : ℕ => g n)

/-- **Theorem 4.4.3** (Bertin). Let `g` have a continuous derivative `g'` on `[1, ∞)` such that
(i) `g` is increasing with `g(t) → +∞`, and (ii) `g'` is decreasing with `t · g'(t) → 0`. Then the
sequence `(g(n))ₙ` is **dense but not** uniformly distributed modulo one.

This is the slow-growth companion of Fejér's theorem (4.4.2): the *same* van der Corput estimate of
the Weyl sums applies, but now `t g'(t) → 0` makes the main term `O(1/(N · g'(N))) → ` a non-zero
constant, so the Weyl sums do not vanish (not u.d.); equidistribution of the differences still gives
density. The estimate is not in Mathlib, so the theorem is recorded as a cited result. -/
@[category research solved, AMS 11, ref "Ber92"]
axiom denseNotUniformlyDistributedModOne_theorem_4_4_3 (g g' : ℝ → ℝ)
    (hderiv : ∀ t : ℝ, 1 ≤ t → HasDerivAt g (g' t) t)
    (hg'_cont : ContinuousOn g' (Set.Ici 1))
    (hg_mono : MonotoneOn g (Set.Ici 1))
    (hg_top : Tendsto g atTop atTop)
    (hg'_anti : AntitoneOn g' (Set.Ici 1))
    (hg'_mul_zero : Tendsto (fun t => t * g' t) atTop (𝓝 0)) :
    (Set.Ico (-(1/2) : ℝ) (1/2) ⊆ closure (Set.range (fun n : ℕ => ε (g n))))
      ∧ ¬ UniformlyDistributedModOne (fun n : ℕ => g n)

/-- **Corollary** (Bertin, after Theorem 4.4.1). If `P` is a polynomial with real coefficients, then
the sequence `(P(n))ₙ` is uniformly distributed modulo one **iff** at least one of the coefficients
of `P − P(0)` is irrational (i.e. some `P.coeff j` with `j ≥ 1` is irrational).

It follows from Theorem 4.4.1: if all higher coefficients are rational then `P(n)` takes finitely
many values modulo one (not u.d.); if some `P.coeff j` (`j ≥ 1`) is irrational, repeatedly passing
to the difference sequence `(P(n+1) − P(n))` lowers the degree while keeping an irrational top
coefficient, reaching the linear case `(βn)` with `β` irrational (u.d. by
`uniformlyDistributedModOne_nα_iff_irrational`), and van der Corput's theorem lifts u.d. back up.
The induction is well beyond a short proof, so this is recorded as cited. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses vanDerCorput_theorem_4_4_1 uniformlyDistributedModOne_nα_iff_irrational]
axiom uniformlyDistributedModOne_eval_iff_exists_irrational_coeff (P : Polynomial ℝ) :
    UniformlyDistributedModOne (fun n : ℕ => P.eval (n : ℝ)) ↔
      ∃ j : ℕ, 1 ≤ j ∧ Irrational (P.coeff j)

/-- **Theorem 4.4.4 (i)** (Bertin). For `a, α > 0` with `α` not an integer, the sequence `(a nᵅ)ₙ` is
uniformly distributed modulo one. (Deduced from Fejér's theorem 4.4.2 for `0 < α < 1` and van der
Corput's theorem 4.4.1 — passing to differences — for `α > 1`.) -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses fejer_theorem_4_4_2 vanDerCorput_theorem_4_4_1]
axiom uniformlyDistributedModOne_mul_rpow_theorem_4_4_4_i (a α : ℝ) (ha : 0 < a) (hα : 0 < α)
    (hαnotint : ∀ m : ℤ, α ≠ (m : ℝ)) :
    UniformlyDistributedModOne (fun n : ℕ => a * (n : ℝ) ^ α)

/-- **Theorem 4.4.4 (ii)** (Bertin). For `a, β > 0`, the sequence `(a (log n)^β)ₙ` is uniformly
distributed modulo one when `β > 1` (Fejér 4.4.2), and **dense but not** u.d. when `0 < β ≤ 1`
(Theorem 4.4.3 for `β < 1`; the example `(log n)` for `β = 1`). -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses fejer_theorem_4_4_2 denseNotUniformlyDistributedModOne_theorem_4_4_3]
axiom mul_log_rpow_theorem_4_4_4_ii (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    (1 < β → UniformlyDistributedModOne (fun n : ℕ => a * (Real.log n) ^ β)) ∧
      (β ≤ 1 →
        (Set.Ico (-(1/2) : ℝ) (1/2) ⊆
            closure (Set.range (fun n : ℕ => ε (a * (Real.log n) ^ β))))
          ∧ ¬ UniformlyDistributedModOne (fun n : ℕ => a * (Real.log n) ^ β))

/-- **Theorem 4.4.4 (iii)** (Bertin). For `a, α, β > 0` with `α` not an integer, the sequence
`(a nᵅ (log n)^β)_{n ≥ 2}` is uniformly distributed modulo one. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses fejer_theorem_4_4_2 vanDerCorput_theorem_4_4_1]
axiom uniformlyDistributedModOne_mul_rpow_log_rpow_theorem_4_4_4_iii (a α β : ℝ) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hαnotint : ∀ m : ℤ, α ≠ (m : ℝ)) :
    UniformlyDistributedModOne (fun n : ℕ => a * (n : ℝ) ^ α * (Real.log n) ^ β)

/-- **Theorem 4.4.4 (iv)** (Bertin). The sequence `(log(log n))_{n ≥ 2}` is **not** uniformly
distributed modulo one (Theorem 4.4.3 with `g = log ∘ log`, where `t g'(t) = 1/log t → 0`). -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses denseNotUniformlyDistributedModOne_theorem_4_4_3]
axiom not_uniformlyDistributedModOne_log_log_theorem_4_4_4_iv :
    ¬ UniformlyDistributedModOne (fun n : ℕ => Real.log (Real.log n))

end Bertin
