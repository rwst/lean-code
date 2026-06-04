/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
/-
# The Hardy space `Hᵖ` on the unit disk

For `p > 0`, a function `f` analytic on the open unit disk `D(0,1)` belongs to the **Hardy space**
`Hᵖ` when its integral means
`Mₚ(r, f) = (1 / 2π) ∫_{-π}^{π} ‖f(r e^{iθ})‖ᵖ dθ`
remain bounded as `r → 1⁻`.  This file introduces `Complex.MemHardy` together with the integral
mean `Complex.hardyIntegralMean`, and proves the classical characterisation of `H²` in terms of
the Taylor coefficients — a special case of Parseval's identity:

`Complex.memHardy_two_iff_summable`:
  if `f z = ∑ₙ aₙ zⁿ` on `D(0,1)`, then `f ∈ H²  ↔  ∑ₙ ‖aₙ‖² < ∞`.

The proof reduces the analytic statement to the polynomial Parseval identity
`Polynomial.sum_sq_norm_coeff_eq_circleAverage` via partial sums and the dominated convergence
theorem, and then compares the resulting power series in `r` with `∑ₙ ‖aₙ‖²`.

Reference: Bertin et al. [Ber92], §1.2 "Criteria of rationality in `ℂ`".
-/
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Real NNReal ENNReal

namespace Complex

/-- The `p`-th integral mean of `f` over the circle of radius `r` centred at the origin,
`(1 / 2π) ∫_{-π}^{π} ‖f(r e^{iθ})‖ᵖ dθ`, expressed through `Real.circleAverage`. -/
noncomputable def hardyIntegralMean (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z => ‖f z‖ ^ p) 0 r

/-- `f` belongs to the **Hardy space** `Hᵖ` on the open unit disk `D(0,1)` when it is analytic on
the disk and its integral means `hardyIntegralMean p f r` remain bounded as `r → 1⁻`. -/
def MemHardy (p : ℝ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f (ball 0 1) ∧ BddAbove (hardyIntegralMean p f '' Ico 0 1)

/-- The `N`-th partial sum of the power series `∑ aₙ zⁿ`, written explicitly. -/
private lemma ofScalars_partialSum (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ a).partialSum N z = ∑ k ∈ Finset.range N, a k * z ^ k := by
  show ∑ k ∈ Finset.range N, (FormalMultilinearSeries.ofScalars ℂ a) k (fun _ => z) = _
  exact Finset.sum_congr rfl fun k _ => by
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- `hardyIntegralMean 2 f` is the circle average of `‖f‖²` (natural-power form). -/
private lemma hardyIntegralMean_two (f : ℂ → ℂ) (r : ℝ) :
    hardyIntegralMean 2 f r = Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 r := by
  unfold hardyIntegralMean
  congr 1
  ext z
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **Finite Parseval (radius `r`).** The circle average of `‖·‖²` of the `N`-th partial sum equals
the partial sum `∑_{k<N} ‖aₖ‖² r^{2k}`. This is `Polynomial.sum_sq_norm_coeff_eq_circleAverage`
applied to the scaled polynomial `∑_{k<N} (aₖ rᵏ) Xᵏ`. -/
private lemma circleAverage_normSq_partialSum (a : ℕ → ℂ) (r : ℝ) (N : ℕ) :
    Real.circleAverage
        (fun z => ‖(FormalMultilinearSeries.ofScalars ℂ a).partialSum N z‖ ^ 2) 0 r
      = ∑ k ∈ Finset.range N, ‖a k‖ ^ 2 * r ^ (2 * k) := by
  set Q : ℂ[X] := ∑ k ∈ Finset.range N, Polynomial.monomial k (a k * (r : ℂ) ^ k) with hQ
  have hcm : ∀ θ : ℝ, circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := fun θ => by
    simp [circleMap]
  have hev : ∀ θ : ℝ,
      (FormalMultilinearSeries.ofScalars ℂ a).partialSum N (circleMap 0 r θ)
        = Q.eval (circleMap 0 1 θ) := fun θ => by
    rw [ofScalars_partialSum, hcm θ, hQ, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_monomial, mul_pow]
    ring
  have hca : Real.circleAverage
        (fun z => ‖(FormalMultilinearSeries.ofScalars ℂ a).partialSum N z‖ ^ 2) 0 r
      = Real.circleAverage (fun z => ‖Q.eval z‖ ^ 2) 0 1 := by
    rw [Real.circleAverage_def, Real.circleAverage_def]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    exact congrArg (fun w => ‖w‖ ^ 2) (hev θ)
  rw [hca, ← Polynomial.sum_sq_norm_coeff_eq_circleAverage Q]
  have hcoeff : ∀ i, Q.coeff i = if i ∈ Finset.range N then a i * (r : ℂ) ^ i else 0 := by
    intro i
    rw [hQ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range N) i fun k => a k * (r : ℂ) ^ k]
  have hsub : Q.support ⊆ Finset.range N := by
    intro i hi
    by_contra h
    rw [Polynomial.mem_support_iff, hcoeff i, if_neg h] at hi
    exact hi rfl
  rw [Finset.sum_subset hsub fun i _ hni => by
    rw [Polynomial.mem_support_iff, not_not] at hni; rw [hni]; simp]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hcoeff i, if_pos hi, norm_mul, mul_pow]
  congr 1
  rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← pow_mul, mul_comm]

/-- The coefficients are square-summable against `r^{2n}` for `0 ≤ r < 1`: the square of the
`ℓ¹`-summable sequence `‖aₙ‖ rⁿ`. -/
private lemma summable_normSq_mul_pow {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖a n‖ ^ 2 * r ^ (2 * n)) := by
  have hb : Summable (fun n => ‖a n‖ * r ^ n) := by
    have hlt : ENNReal.ofReal r < (FormalMultilinearSeries.ofScalars ℂ a).radius :=
      lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr hr1) hf.r_le
    have hsum := (FormalMultilinearSeries.ofScalars ℂ a).summable_norm_mul_pow
      (r := r.toNNReal) hlt
    simpa [FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal r hr0] using hsum
  have hbnn : ∀ n, 0 ≤ ‖a n‖ * r ^ n := fun n => by positivity
  have hrw : ∀ n, ‖a n‖ ^ 2 * r ^ (2 * n) = (‖a n‖ * r ^ n) ^ 2 := fun n => by
    rw [mul_pow, ← pow_mul, Nat.mul_comm]
  simp only [hrw]
  set B := ∑' n, ‖a n‖ * r ^ n with hBdef
  have hB : ∀ n, ‖a n‖ * r ^ n ≤ B := fun n => hb.le_tsum n (fun j _ => hbnn j)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hb.mul_left B)
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hB n) (hbnn n)

/-- **Parseval (radius `r`).** For `f z = ∑ aₙ zⁿ` analytic on the disk and `0 ≤ r < 1`,
`(1/2π) ∫ ‖f(r e^{iθ})‖² dθ = ∑ₙ ‖aₙ‖² r^{2n}`. -/
private lemma circleAverage_normSq_eq_tsum {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 r = ∑' n, ‖a n‖ ^ 2 * r ^ (2 * n) := by
  have key : Tendsto
      (fun N => Real.circleAverage
        (fun z => ‖(FormalMultilinearSeries.ofScalars ℂ a).partialSum N z‖ ^ 2) 0 r)
      atTop (𝓝 (Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 r)) := by
    have hb : Summable (fun n => ‖a n‖ * r ^ n) := by
      have hlt : ENNReal.ofReal r < (FormalMultilinearSeries.ofScalars ℂ a).radius :=
        lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr hr1) hf.r_le
      have hsum := (FormalMultilinearSeries.ofScalars ℂ a).summable_norm_mul_pow
        (r := r.toNNReal) hlt
      simpa [FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal r hr0] using hsum
    have hbnn : ∀ n, 0 ≤ ‖a n‖ * r ^ n := fun n => by positivity
    set C := ∑' n, ‖a n‖ * r ^ n with hC
    have hbound : ∀ N θ,
        ‖(FormalMultilinearSeries.ofScalars ℂ a).partialSum N (circleMap 0 r θ)‖ ≤ C := by
      intro N θ
      rw [ofScalars_partialSum]
      calc ‖∑ k ∈ Finset.range N, a k * circleMap 0 r θ ^ k‖
          ≤ ∑ k ∈ Finset.range N, ‖a k * circleMap 0 r θ ^ k‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range N, ‖a k‖ * r ^ k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_mul, norm_pow, norm_circleMap_zero, abs_of_nonneg hr0]
        _ ≤ C := hb.sum_le_tsum _ fun i _ => hbnn i
    have hcont : ∀ N, Continuous
        (fun z : ℂ => (FormalMultilinearSeries.ofScalars ℂ a).partialSum N z) := by
      intro N
      have hpoly : (fun z : ℂ => (FormalMultilinearSeries.ofScalars ℂ a).partialSum N z)
          = fun z => ∑ k ∈ Finset.range N, a k * z ^ k := funext (ofScalars_partialSum a N)
      rw [hpoly]; fun_prop
    have hptw : ∀ θ, Tendsto
        (fun N => ‖(FormalMultilinearSeries.ofScalars ℂ a).partialSum N (circleMap 0 r θ)‖ ^ 2)
        atTop (𝓝 (‖f (circleMap 0 r θ)‖ ^ 2)) := by
      intro θ
      have hz : circleMap 0 r θ ∈ Metric.eball (0 : ℂ) 1 := by
        rw [Metric.mem_eball, edist_dist, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
        exact ENNReal.ofReal_lt_one.mpr hr1
      have htend := hf.tendsto_partialSum hz
      have hcomp := ((continuous_norm.pow 2).tendsto (f (0 + circleMap 0 r θ))).comp htend
      simpa [Function.comp_def] using hcomp
    have hpi : (0 : ℝ) ≤ 2 * π := by positivity
    simp only [Real.circleAverage_def]
    refine Filter.Tendsto.const_smul ?_ _
    simp_rw [intervalIntegral.integral_of_le hpi]
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => C ^ 2) ?_ ?_ ?_ ?_
    · exact fun N =>
        (((hcont N).comp (continuous_circleMap 0 r)).norm.pow 2).aestronglyMeasurable
    · exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    · intro N
      refine ae_of_all _ fun θ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound N θ) 2
    · exact ae_of_all _ fun θ => hptw θ
  simp_rw [circleAverage_normSq_partialSum] at key
  have hsum : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖a k‖ ^ 2 * r ^ (2 * k)) atTop
      (𝓝 (∑' n, ‖a n‖ ^ 2 * r ^ (2 * n))) :=
    (summable_normSq_mul_pow hf hr0 hr1).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique key hsum

/-- **Characterisation of `H²`.** If `f z = ∑ₙ aₙ zⁿ` on the open unit disk, then `f` belongs to
the Hardy space `H²` iff its Taylor coefficients are square-summable, `∑ₙ ‖aₙ‖² < ∞`.
(Bertin et al. [Ber92], §1.2.) -/
theorem memHardy_two_iff_summable {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 1) :
    MemHardy 2 f ↔ Summable (fun n => ‖a n‖ ^ 2) := by
  have hmean : ∀ r : ℝ, 0 ≤ r → r < 1 →
      hardyIntegralMean 2 f r = ∑' n, ‖a n‖ ^ 2 * r ^ (2 * n) := fun r hr0 hr1 => by
    rw [hardyIntegralMean_two, circleAverage_normSq_eq_tsum hf hr0 hr1]
  have hanalytic : AnalyticOnNhd ℂ f (ball 0 1) := by
    refine hf.analyticOnNhd.mono (le_of_eq ?_)
    rw [← Metric.eball_ofReal, ENNReal.ofReal_one]
  constructor
  · rintro ⟨-, M, hM⟩
    have hle : ∀ r : ℝ, 0 ≤ r → r < 1 → ∑' n, ‖a n‖ ^ 2 * r ^ (2 * n) ≤ M := fun r hr0 hr1 => by
      rw [← hmean r hr0 hr1]; exact hM ⟨r, ⟨hr0, hr1⟩, rfl⟩
    refine summable_of_sum_range_le (c := M) (fun n => sq_nonneg _) (fun N => ?_)
    have htend : Tendsto (fun r : ℝ => ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n))
        (𝓝[<] 1) (𝓝 (∑ n ∈ Finset.range N, ‖a n‖ ^ 2)) := by
      have hc : Continuous (fun r : ℝ => ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n)) := by
        fun_prop
      have h1 := hc.tendsto 1
      simp only [one_pow, mul_one] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    have hsub : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [hsub] with r hr
    have hr0 : 0 ≤ r := le_of_lt hr.1
    have hr1 : r < 1 := hr.2
    calc ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n)
        ≤ ∑' n, ‖a n‖ ^ 2 * r ^ (2 * n) :=
          (summable_normSq_mul_pow hf hr0 hr1).sum_le_tsum _ (fun i _ => by positivity)
      _ ≤ M := hle r hr0 hr1
  · intro hsum
    refine ⟨hanalytic, ∑' n, ‖a n‖ ^ 2, ?_⟩
    rintro y ⟨r, ⟨hr0, hr1⟩, rfl⟩
    rw [hmean r hr0 hr1]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_normSq_mul_pow hf hr0 hr1) hsum
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hr0 hr1.le)

end Complex
