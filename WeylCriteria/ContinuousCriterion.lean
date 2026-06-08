/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.UniformDistribution
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# The continuous-function criterion for uniform distribution

The **continuous-function criterion** (Kuipers–Niederreiter, *Uniform Distribution of Sequences*,
Ch. 1, Thm 1.1): a sequence `(xₙ)` is uniformly distributed modulo one **iff** for every continuous
`f`, the averages `(1/N) Σ_{n<N} f(ε xₙ)` converge to `∫_{-1/2}^{1/2} f`.

Both directions are derived from Bertin's **Theorem 4.3.1** (the Riemann-integral criterion,
`BertinPisot.UniformDistribution`):

* **(⟹)** A continuous function on the compact interval `[-1/2, 1/2]` is bounded and continuous
  everywhere, hence Riemann-integrable (`Bertin.IsRiemannIntegrableOn`); so Theorem 4.3.1 applies.
* **(⟸)** Sandwich each interval indicator `𝟙_{[a,b)}` between two continuous trapezoids
  `g⁻ ≤ 𝟙_{[a,b)} ≤ g⁺` with `∫(g⁺ - g⁻)` small (the trapezoids are explicit `max`/`min` of linear
  ramps), apply the criterion to `g⁻, g⁺`, and squeeze: `ν(a,b,N)/N → b - a`.

This is the keystone form: it sits between the interval-indicator definition and the
Riemann-integrable criterion, and the same squeeze underlies Weyl's criterion (it is exactly the
ingredient the converse of Theorem 4.3.2 rests on).

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §4.3.
  - [KN74] Kuipers, L. and Niederreiter, H. *Uniform Distribution of Sequences.* Wiley, 1974, Thm 1.1.
-/

namespace Bertin

open Filter MeasureTheory
open scoped Topology

/-- **The continuous-function criterion.** For every continuous `f`, the averages
`(1/N) Σ_{n<N} f(ε xₙ)` converge to `∫_{-1/2}^{1/2} f`. -/
@[category API, AMS 11, ref "Ber92"]
def ContinuousCriterion (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (ε (x n))) / N) atTop
      (𝓝 (∫ t in (-(1/2) : ℝ)..(1/2), f t))

/-- **(⟹)** Uniform distribution implies the continuous-function criterion: a continuous function on
`[-1/2, 1/2]` is Riemann-integrable, so this is Theorem 4.3.1 specialised to continuous test
functions. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses integralCriterion_of_uniformlyDistributedModOne]
theorem continuousCriterion_of_uniformlyDistributedModOne (x : ℕ → ℝ)
    (h : UniformlyDistributedModOne x) : ContinuousCriterion x := by
  intro f hf
  refine integralCriterion_of_uniformlyDistributedModOne x h f ⟨?_, ?_⟩
  · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
    exact ⟨C, fun t ht => by rw [← Real.norm_eq_abs]; exact hC t ht⟩
  · have hempty : {t ∈ Set.Icc (-(1/2) : ℝ) (1/2) | ¬ ContinuousAt f t} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; exact fun t ht => ht.2 hf.continuousAt
    rw [hempty, measure_empty]

/-! ### Continuous trapezoids sandwiching an interval indicator -/

/-- The lower trapezoid: continuous, `= 1` on `[a+δ, b-δ]`, ramps linearly to `0` on `[a, a+δ]` and
`[b-δ, b]`, and `0` outside `[a, b]`. It lies below `𝟙_{[a,b)}`. -/
private noncomputable def trapLower (a b δ : ℝ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - a) / δ) ((b - t) / δ)))

/-- The upper trapezoid: continuous, `= 1` on `[a, b]`, ramps linearly to `0` on `[a-δ, a]` and
`[b, b+δ]`, and `0` outside `[a-δ, b+δ]`. It lies above `𝟙_{[a,b)}`. -/
private noncomputable def trapUpper (a b δ : ℝ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - (a - δ)) / δ) (((b + δ) - t) / δ)))

private theorem continuous_trapLower (a b δ : ℝ) : Continuous (trapLower a b δ) := by
  unfold trapLower; fun_prop

private theorem continuous_trapUpper (a b δ : ℝ) : Continuous (trapUpper a b δ) := by
  unfold trapUpper; fun_prop

private theorem trapLower_le_ind (a b δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    trapLower a b δ t ≤ (Set.Ico a b).indicator (fun _ => (1:ℝ)) t := by
  unfold trapLower
  by_cases ht : t ∈ Set.Ico a b
  · rw [Set.indicator_of_mem ht]; exact max_le zero_le_one (min_le_left _ _)
  · rw [Set.indicator_of_notMem ht, Set.mem_Ico, not_and_or, not_le, not_lt] at *
    refine max_le le_rfl (le_trans (min_le_right _ _) ?_)
    rcases ht with ht | ht
    · exact le_trans (min_le_left _ _) (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    · exact le_trans (min_le_right _ _) (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)

private theorem ind_le_trapLower (a b δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    (Set.Ico (a + δ) (b - δ)).indicator (fun _ => (1:ℝ)) t ≤ trapLower a b δ t := by
  unfold trapLower
  by_cases ht : t ∈ Set.Ico (a + δ) (b - δ)
  · rw [Set.indicator_of_mem ht, Set.mem_Ico] at *
    refine le_max_of_le_right (le_min le_rfl (le_min ?_ ?_))
    · rw [le_div_iff₀ hδ]; linarith [ht.1]
    · rw [le_div_iff₀ hδ]; linarith [ht.2]
  · rw [Set.indicator_of_notMem ht]; exact le_max_left _ _

private theorem ind_le_trapUpper (a b δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    (Set.Ico a b).indicator (fun _ => (1:ℝ)) t ≤ trapUpper a b δ t := by
  unfold trapUpper
  by_cases ht : t ∈ Set.Ico a b
  · rw [Set.indicator_of_mem ht, Set.mem_Ico] at *
    refine le_max_of_le_right (le_min le_rfl (le_min ?_ ?_))
    · rw [le_div_iff₀ hδ]; linarith [ht.1]
    · rw [le_div_iff₀ hδ]; linarith [ht.2]
  · rw [Set.indicator_of_notMem ht]; exact le_max_left _ _

private theorem trapUpper_le_ind (a b δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    trapUpper a b δ t ≤ (Set.Ico (a - δ) (b + δ)).indicator (fun _ => (1:ℝ)) t := by
  unfold trapUpper
  by_cases ht : t ∈ Set.Ico (a - δ) (b + δ)
  · rw [Set.indicator_of_mem ht]; exact max_le zero_le_one (min_le_left _ _)
  · rw [Set.indicator_of_notMem ht, Set.mem_Ico, not_and_or, not_le, not_lt] at *
    refine max_le le_rfl (le_trans (min_le_right _ _) ?_)
    rcases ht with ht | ht
    · exact le_trans (min_le_left _ _) (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    · exact le_trans (min_le_right _ _) (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)

/-! ### Integrals of interval indicators over `[-1/2, 1/2]` -/

private theorem ind_intervalIntegrable (c d : ℝ) :
    IntervalIntegrable ((Set.Ico c d).indicator (fun _ => (1:ℝ))) volume (-(1/2)) (1/2) := by
  have hfin : volume (Set.uIcc (-(1/2) : ℝ) (1/2)) ≠ ⊤ := by
    rw [Set.uIcc_of_le (by norm_num), Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  exact ((integrableOn_const hfin).indicator measurableSet_Ico).intervalIntegrable

private theorem ind_int_eq (c d : ℝ) (hc : -(1/2) ≤ c) (hd : d ≤ 1/2) (hcd : c ≤ d) :
    ∫ t in (-(1/2) : ℝ)..(1/2), (Set.Ico c d).indicator (fun _ => (1:ℝ)) t = d - c := by
  have hvol : volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico c d) = ENNReal.ofReal (d - c) := by
    apply le_antisymm
    · calc volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico c d)
          ≤ volume (Set.Icc c d) := measure_mono (fun t ht => Set.Ico_subset_Icc_self ht.2)
        _ = ENNReal.ofReal (d - c) := Real.volume_Icc
    · calc ENNReal.ofReal (d - c) = volume (Set.Ioo c d) := (Real.volume_Ioo).symm
        _ ≤ volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico c d) :=
            measure_mono (fun t ht => ⟨Set.mem_Ioc.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩,
              Set.Ioo_subset_Ico_self ht⟩)
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
    setIntegral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def, hvol, ENNReal.toReal_ofReal (by linarith)]

private theorem ind_int_le (c d : ℝ) (hcd : c ≤ d) :
    ∫ t in (-(1/2) : ℝ)..(1/2), (Set.Ico c d).indicator (fun _ => (1:ℝ)) t ≤ d - c := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
    setIntegral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
  calc volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico c d)
      ≤ volume (Set.Ico c d) := measure_mono Set.inter_subset_right
    _ = ENNReal.ofReal (d - c) := Real.volume_Ico

private theorem int_trapLower_ge (a b δ : ℝ) (hδ : 0 < δ) (ha : -(1/2) ≤ a) (hb : b ≤ 1/2)
    (hδb : δ ≤ (b - a) / 2) :
    (b - a) - 2 * δ ≤ ∫ t in (-(1/2) : ℝ)..(1/2), trapLower a b δ t := by
  have h1 := intervalIntegral.integral_mono_on (by norm_num : (-(1/2) : ℝ) ≤ 1/2)
    (ind_intervalIntegrable (a + δ) (b - δ))
    ((continuous_trapLower a b δ).intervalIntegrable _ _)
    (fun t _ => ind_le_trapLower a b δ hδ t)
  rw [ind_int_eq (a + δ) (b - δ) (by linarith) (by linarith) (by linarith)] at h1
  linarith

private theorem int_trapUpper_le (a b δ : ℝ) (hδ : 0 < δ) (hab : a ≤ b) :
    (∫ t in (-(1/2) : ℝ)..(1/2), trapUpper a b δ t) ≤ (b - a) + 2 * δ := by
  have h1 := intervalIntegral.integral_mono_on (by norm_num : (-(1/2) : ℝ) ≤ 1/2)
    ((continuous_trapUpper a b δ).intervalIntegrable _ _)
    (ind_intervalIntegrable (a - δ) (b + δ))
    (fun t _ => trapUpper_le_ind a b δ hδ t)
  have h2 := ind_int_le (a - δ) (b + δ) (by linarith)
  linarith

private theorem sum_indicator_eq_countModOne (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (Set.Ico a b).indicator (fun _ => (1:ℝ)) (ε (x n)))
      = (countModOne x a b N : ℝ) := by
  classical
  simp only [Set.indicator_apply, countModOne]
  rw [Finset.sum_boole]

/-- **(⟸)** The continuous-function criterion implies uniform distribution. For each interval
`[a, b)` and tolerance, sandwich `𝟙_{[a,b)}` between the continuous trapezoids `trapLower ≤ 𝟙 ≤
trapUpper` whose integrals are within `2δ` of `b - a`; applying the criterion to the trapezoids and
squeezing gives `ν(a,b,N)/N → b - a`. -/
@[category research solved, AMS 11, ref "Ber92"]
theorem uniformlyDistributedModOne_of_continuousCriterion (x : ℕ → ℝ)
    (h : ContinuousCriterion x) : UniformlyDistributedModOne x := by
  intro a b ha hab hb
  rw [Metric.tendsto_atTop]
  intro ε₀ hε₀
  obtain ⟨δ, hδ, hδe, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ 4 * δ ≤ ε₀ ∧ δ ≤ (b - a) / 2 := by
    refine ⟨min (ε₀ / 4) ((b - a) / 2), lt_min (by linarith) (by linarith), ?_, min_le_right _ _⟩
    have := min_le_left (ε₀ / 4) ((b - a) / 2); linarith
  have hcl := h (trapLower a b δ) (continuous_trapLower a b δ)
  have hcu := h (trapUpper a b δ) (continuous_trapUpper a b δ)
  have hIl := int_trapLower_ge a b δ hδ ha hb hδb
  have hIu := int_trapUpper_le a b δ hδ hab.le
  have hsl : ∀ N, (∑ n ∈ Finset.range N, trapLower a b δ (ε (x n))) ≤ (countModOne x a b N : ℝ) := by
    intro N; rw [← sum_indicator_eq_countModOne]
    exact Finset.sum_le_sum (fun n _ => trapLower_le_ind a b δ hδ (ε (x n)))
  have hsu : ∀ N, (countModOne x a b N : ℝ) ≤ ∑ n ∈ Finset.range N, trapUpper a b δ (ε (x n)) := by
    intro N; rw [← sum_indicator_eq_countModOne]
    exact Finset.sum_le_sum (fun n _ => ind_le_trapUpper a b δ hδ (ε (x n)))
  rw [Metric.tendsto_atTop] at hcl hcu
  obtain ⟨N₁, hN₁⟩ := hcl (ε₀ / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hcu (ε₀ / 4) (by linarith)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have bl := hN₁ N (le_trans (le_max_left _ _) hN)
  have bu := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at bl bu
  have hAL : (∑ n ∈ Finset.range N, trapLower a b δ (ε (x n))) / N
      ≤ (countModOne x a b N : ℝ) / N := by gcongr; exact hsl N
  have hAU : (countModOne x a b N : ℝ) / N
      ≤ (∑ n ∈ Finset.range N, trapUpper a b δ (ε (x n))) / N := by gcongr; exact hsu N
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **The continuous-function criterion** (Kuipers–Niederreiter, Thm 1.1): a sequence is uniformly
distributed modulo one **iff** the averages `(1/N) Σ_{n<N} f(ε xₙ)` converge to `∫_{-1/2}^{1/2} f`
for every continuous `f`. Both directions follow from Bertin's Theorem 4.3.1. -/
@[category research solved, AMS 11, ref "Ber92", ref "KN74",
  formal_uses continuousCriterion_of_uniformlyDistributedModOne
    uniformlyDistributedModOne_of_continuousCriterion]
theorem uniformlyDistributedModOne_iff_continuousCriterion (x : ℕ → ℝ) :
    UniformlyDistributedModOne x ↔ ContinuousCriterion x :=
  ⟨continuousCriterion_of_uniformlyDistributedModOne x,
    uniformlyDistributedModOne_of_continuousCriterion x⟩

end Bertin
