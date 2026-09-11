/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Asymptotics.ExpGrowth
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Box-counting (Minkowski) dimension

The **upper box dimension** of a set `A` in a pseudo-emetric space is

`dim_B A = limsup_{ε → 0⁺} log N(ε, A) / log (1/ε)`,

where `N(ε, A)` is the least number of closed `ε`-balls needed to cover `A`.  Unlike the
Hausdorff dimension it is not built from a measure: it is a pure counting rate, and only a
countable set of scales is needed to compute it, since `N(·, A)` is antitone.

This file takes that last observation as the definition.  For a ratio `r ∈ (0,1)`,

`coveringGrowth r A := expGrowthSup (fun n => N (rⁿ, A))`

is the exponential growth rate of the covering numbers along the geometric scales `rⁿ`
(`Mathlib.Analysis.Asymptotics.ExpGrowth`), and

`upperBoxDimWith r A := coveringGrowth r A / log r⁻¹`,   `upperBoxDim A := upperBoxDimWith 2⁻¹ A`.

The main structural theorem is that the ratio does not matter:

* `upperBoxDimWith_eq` — `upperBoxDimWith r A = upperBoxDimWith s A` for all `r, s ∈ (0,1)`,
* `upperBoxDim_eq_upperBoxDimWith` — hence `upperBoxDim` may be computed at any ratio.

This is what makes the definition legitimate, and it is also the practical tool: a
self-similar set with `k` branches of contraction ratio `r` is naturally covered at the
scales `rⁿ`, not at the dyadic ones.

## Main results

* `upperBoxDimWith_eq`, `lowerBoxDimWith_eq`, `upperBoxDim_eq_upperBoxDimWith`,
  `lowerBoxDim_eq_lowerBoxDimWith` — independence of the ratio, and
  `lowerBoxDim_le_upperBoxDim`.
* `upperBoxDim_le_of_covering`, `upperBoxDim_le_of_covering_nat` — the upper bound from an
  explicit cover: `k` branches at ratio `r`, up to a constant, give
  `dim_B A ≤ log k / log r⁻¹`; `upperBoxDim_le_of_covering_mul`,
  `upperBoxDim_le_of_covering_mul_nat` allow a fixed constant in the *radius* as well, the
  form a tail estimate produces.
* `le_upperBoxDim_of_separated`, `le_lowerBoxDim_of_separated` — the matching lower bounds
  from separated subsets, via `Metric.packingNumber_two_mul_le_externalCoveringNumber`.
  Together with the previous item these pin the dimension of a self-similar set with strong
  separation, and show that its box dimension *exists*.
* `upperBoxDim_mono`, `upperBoxDim_nonneg`, `coveringGrowth_empty`.
* `coveringGrowth_const_mul`, `coveringGrowthInf_const_mul` — a fixed factor in the radius is
  invisible to the growth rate.
* `externalCoveringNumber_add_le` — covering numbers are submultiplicative on sumsets — and
  hence `coveringGrowth_add_le` and `upperBoxDim_add_le`:
  `dim_B (A + B) ≤ dim_B A + dim_B B`.  Since `x ↦ -x` is an isometry
  (`externalCoveringNumber_neg`, `upperBoxDim_neg`), the same holds for difference sets:
  `upperBoxDim_sub_le`.
* `Real.volume_eq_zero_of_upperBoxDim_lt_one` — a subset of `ℝ` of upper box dimension `< 1`
  is Lebesgue-null, via `Real.volume_le_externalCoveringNumber_mul`.  No Hausdorff measure is
  involved.
* `dimH_le_upperBoxDim` — comparison with Mathlib's Hausdorff dimension:
  `dimH A ≤ dim_B A` for `A` nonempty.  A cover by `N` balls of radius `ε` is an admissible
  cover in the definition of `μH[d]`, contributing `N · (2ε)ᵈ`.

Three auxiliary results are stated for their own sake, being about Mathlib objects only:
`Metric.exists_isCover_encard_eq_externalCoveringNumber` (an optimal external cover exists
when the covering number is finite — the external analogue of
`Metric.exists_set_encard_eq_coveringNumber`), and `Monotone.expGrowthSup_comp_add`,
`Monotone.expGrowthInf_comp_add` (an index shift does not change an exponential growth rate).

## What is not here

A *lower* bound on the Hausdorff dimension, and hence the value of `dimH` for a self-similar
set: that needs a measure carried by the set, and Mathlib has no iterated function systems
and no Moran/Hutchinson formula.  The general principle such a measure would be fed to does
exist — `MeasureTheory.Measure.le_hausdorffMeasure` is the mass distribution principle — but
the measure itself has to be built by hand in each case.  Until then
`le_upperBoxDim_of_separated` is the box-dimension substitute, and it needs nothing beyond
the separation estimate that a strongly separated IFS supplies directly.

## References

* K. Falconer, *Fractal Geometry*, Ch. 2–3.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Ch. 5.
-/

@[expose] public section

open Filter Set ExpGrowth
open scoped ENNReal NNReal Pointwise Topology

/-! ## Ceilings are asymptotically neutral -/

namespace Real

/-- `⌈n·c⌉ / n → c`. -/
theorem tendsto_natCeil_mul_div_atTop {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => (⌈(n : ℝ) * c⌉₊ : ℝ) / n) atTop (𝓝 c) := by
  have hlow : ∀ᶠ n : ℕ in atTop, c ≤ (⌈(n : ℝ) * c⌉₊ : ℝ) / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn0]
    calc c * n = (n : ℝ) * c := by ring
      _ ≤ (⌈(n : ℝ) * c⌉₊ : ℝ) := Nat.le_ceil _
  have hhigh : ∀ᶠ n : ℕ in atTop, (⌈(n : ℝ) * c⌉₊ : ℝ) / n ≤ c + 1 / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn0]
    have h1 : (⌈(n : ℝ) * c⌉₊ : ℝ) < (n : ℝ) * c + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (c + 1 / n) * n = (n : ℝ) * c + 1 := by field_simp
    rw [h2]; linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ hlow hhigh
  simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The `EReal` form of `Real.tendsto_natCeil_mul_div_atTop`, in the shape
`Monotone.expGrowthSup_comp` consumes. -/
theorem tendsto_natCeil_mul_div_atTop_ereal {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => ((⌈(n : ℝ) * c⌉₊ : ℕ) : EReal) / (n : EReal)) atTop
      (𝓝 (c : EReal)) := by
  have h := tendsto_natCeil_mul_div_atTop hc
  rw [← EReal.tendsto_coe] at h
  refine h.congr fun n => ?_
  rw [EReal.coe_div, EReal.coe_coe_eq_natCast, EReal.coe_coe_eq_natCast]

/-- `(n + m) / n → 1`. -/
theorem tendsto_natCast_add_div_atTop (m : ℕ) :
    Tendsto (fun n : ℕ => ((n + m : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have heq : (fun n : ℕ => ((n + m : ℕ) : ℝ) / n) =ᶠ[atTop] fun n : ℕ => 1 + (m : ℝ) / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    push_cast
    field_simp
  refine Filter.Tendsto.congr' heq.symm ?_
  have h0 : Tendsto (fun n : ℕ => (m : ℝ) / n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (m : ℝ)
  simpa using tendsto_const_nhds.add h0

/-- The `EReal` form of `Real.tendsto_natCast_add_div_atTop`. -/
theorem tendsto_natCast_add_div_atTop_ereal (m : ℕ) :
    Tendsto (fun n : ℕ => ((n + m : ℕ) : EReal) / (n : EReal)) atTop (𝓝 (1 : EReal)) := by
  have h := tendsto_natCast_add_div_atTop m
  rw [← EReal.tendsto_coe, EReal.coe_one] at h
  refine h.congr fun n => ?_
  rw [EReal.coe_div, EReal.coe_coe_eq_natCast, EReal.coe_coe_eq_natCast]

end Real

/-! ## Index shifts do not change an exponential growth rate -/

/-- Shifting the index of a monotone sequence does not change its exponential growth rate. -/
theorem Monotone.expGrowthSup_comp_add {u : ℕ → ℝ≥0∞} (hu : Monotone u) (m : ℕ) :
    expGrowthSup (fun n => u (n + m)) = expGrowthSup u := by
  have h := hu.expGrowthSup_comp (v := fun n : ℕ => n + m)
    (Real.tendsto_natCast_add_div_atTop_ereal m) (by simp)
    (by rw [← EReal.coe_one]; exact EReal.coe_ne_top 1)
  simpa [Function.comp_def] using h

/-- The `liminf` form of `Monotone.expGrowthSup_comp_add`. -/
theorem Monotone.expGrowthInf_comp_add {u : ℕ → ℝ≥0∞} (hu : Monotone u) (m : ℕ) :
    expGrowthInf (fun n => u (n + m)) = expGrowthInf u := by
  have h := hu.expGrowthInf_comp (v := fun n : ℕ => n + m)
    (Real.tendsto_natCast_add_div_atTop_ereal m) (by simp)
    (by rw [← EReal.coe_one]; exact EReal.coe_ne_top 1)
  simpa [Function.comp_def] using h

/-! ## An `EReal` rescaling identity -/

namespace EReal

/-- `(a/b) · Y / a = Y / b` for positive reals `a, b` and any extended real `Y`. -/
theorem coe_div_mul_div_cancel {a b : ℝ} (ha : 0 < a) (_hb : 0 < b) (Y : EReal) :
    ((a / b : ℝ) : EReal) * Y / (a : EReal) = Y / (b : EReal) := by
  rw [EReal.coe_div, EReal.mul_div_right, EReal.div_div, mul_comm (a : EReal) Y]
  exact EReal.mul_div_mul_cancel (EReal.coe_ne_bot a) (EReal.coe_ne_top a)
    (EReal.coe_ne_zero.mpr ha.ne')

end EReal

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X] {A B : Set X}

/-! ## The definitions -/

/-- The exponential growth rate of the covering numbers of `A` along the geometric scales
`rⁿ`.  For `r ∈ (0,1)` this is `log r⁻¹` times the upper box dimension of `A`. -/
noncomputable def coveringGrowth (r : ℝ≥0) (A : Set X) : EReal :=
  expGrowthSup fun n => (externalCoveringNumber (r ^ n) A : ℝ≥0∞)

/-- The lower analogue of `Metric.coveringGrowth`. -/
noncomputable def coveringGrowthInf (r : ℝ≥0) (A : Set X) : EReal :=
  expGrowthInf fun n => (externalCoveringNumber (r ^ n) A : ℝ≥0∞)

/-- The **upper box dimension** of `A`, computed along the scales `rⁿ`.  By
`Metric.upperBoxDimWith_eq` the value does not depend on `r ∈ (0,1)`. -/
noncomputable def upperBoxDimWith (r : ℝ≥0) (A : Set X) : EReal :=
  coveringGrowth r A / ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal)

/-- The **lower box dimension** of `A`, computed along the scales `rⁿ`. -/
noncomputable def lowerBoxDimWith (r : ℝ≥0) (A : Set X) : EReal :=
  coveringGrowthInf r A / ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal)

/-- The **upper box (Minkowski) dimension** of a set. -/
noncomputable def upperBoxDim (A : Set X) : EReal := upperBoxDimWith 2⁻¹ A

/-- The **lower box (Minkowski) dimension** of a set. -/
noncomputable def lowerBoxDim (A : Set X) : EReal := lowerBoxDimWith 2⁻¹ A

/-! ## Positivity of the normalising logarithm -/

private theorem logInv_pos {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) : 0 < Real.log (r : ℝ)⁻¹ := by
  have h0 : (0 : ℝ) < (r : ℝ) := hr0
  have h1 : (r : ℝ) < 1 := hr1
  exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨h0, h1⟩)

private theorem logInv_nonneg_ereal {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) :
    (0 : EReal) ≤ ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
  exact_mod_cast (logInv_pos hr0 hr1).le

private theorem half_pos_nnreal : (0 : ℝ≥0) < 2⁻¹ := by norm_num

private theorem half_lt_one_nnreal : (2⁻¹ : ℝ≥0) < 1 := by norm_num

/-! ## Monotonicity of the covering numbers along a geometric scale -/

theorem monotone_externalCoveringNumber_pow {r : ℝ≥0} (hr : r ≤ 1) (A : Set X) :
    Monotone fun n : ℕ => (externalCoveringNumber (r ^ n) A : ℝ≥0∞) :=
  monotone_nat_of_le_succ fun n =>
    ENat.toENNReal_mono (externalCoveringNumber_anti (pow_le_pow_right_of_le_one' hr n.le_succ))

/-! ## Independence of the ratio -/

/-- Comparison of the covering growth at two ratios: the rates are proportional, with the
factor forced by the two logarithms.  Applying this twice, with `r` and `s` swapped, gives
the equality `Metric.upperBoxDimWith_eq`. -/
theorem externalCoveringNumber_pow_le_comp {r s : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 < s) (hs1 : s < 1) (A : Set X) :
    (fun n : ℕ => (externalCoveringNumber (r ^ n) A : ℝ≥0∞))
      ≤ (fun m : ℕ => (externalCoveringNumber (s ^ m) A : ℝ≥0∞))
        ∘ fun n : ℕ => ⌈(n : ℝ) * (Real.log (r : ℝ)⁻¹ / Real.log (s : ℝ)⁻¹)⌉₊ := by
  have hlr : 0 < Real.log (r : ℝ)⁻¹ := logInv_pos hr0 hr1
  have hls : 0 < Real.log (s : ℝ)⁻¹ := logInv_pos hs0 hs1
  set c : ℝ := Real.log (r : ℝ)⁻¹ / Real.log (s : ℝ)⁻¹ with hcdef
  have hcs : c * Real.log (s : ℝ)⁻¹ = Real.log (r : ℝ)⁻¹ := div_mul_cancel₀ _ hls.ne'
  intro n
  refine ENat.toENNReal_mono (externalCoveringNumber_anti ?_)
  have hceil : (n : ℝ) * c ≤ (⌈(n : ℝ) * c⌉₊ : ℝ) := Nat.le_ceil _
  have hkey : (n : ℝ) * Real.log (r : ℝ)⁻¹
      ≤ (⌈(n : ℝ) * c⌉₊ : ℝ) * Real.log (s : ℝ)⁻¹ := by
    calc (n : ℝ) * Real.log (r : ℝ)⁻¹ = (n : ℝ) * c * Real.log (s : ℝ)⁻¹ := by
          rw [mul_assoc, hcs]
      _ ≤ (⌈(n : ℝ) * c⌉₊ : ℝ) * Real.log (s : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hceil hls.le
  have hreal : (s : ℝ) ^ (⌈(n : ℝ) * c⌉₊) ≤ (r : ℝ) ^ n := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      show Real.log (s : ℝ) = -Real.log (s : ℝ)⁻¹ by rw [Real.log_inv]; ring,
      show Real.log (r : ℝ) = -Real.log (r : ℝ)⁻¹ by rw [Real.log_inv]; ring]
    linarith
  rw [← NNReal.coe_le_coe]
  push_cast
  exact hreal

/-- Comparison of the covering growth at two ratios: the rates are proportional, with the
factor forced by the two logarithms.  Applying this twice, with `r` and `s` swapped, gives
the equality `Metric.upperBoxDimWith_eq`. -/
theorem coveringGrowth_le_of_lt_one {r s : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s)
    (hs1 : s < 1) (A : Set X) :
    coveringGrowth r A
      ≤ ((Real.log (r : ℝ)⁻¹ / Real.log (s : ℝ)⁻¹ : ℝ) : EReal) * coveringGrowth s A := by
  have hc : 0 < Real.log (r : ℝ)⁻¹ / Real.log (s : ℝ)⁻¹ :=
    div_pos (logInv_pos hr0 hr1) (logInv_pos hs0 hs1)
  calc coveringGrowth r A ≤ _ :=
        expGrowthSup_monotone (externalCoveringNumber_pow_le_comp hr0 hr1 hs0 hs1 A)
    _ = _ :=
        (monotone_externalCoveringNumber_pow hs1.le A).expGrowthSup_comp
          (Real.tendsto_natCeil_mul_div_atTop_ereal hc.le)
          (EReal.coe_ne_zero.mpr hc.ne') (EReal.coe_ne_top _)

/-- The `liminf` twin of `Metric.coveringGrowth_le_of_lt_one`. -/
theorem coveringGrowthInf_le_of_lt_one {r s : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s)
    (hs1 : s < 1) (A : Set X) :
    coveringGrowthInf r A
      ≤ ((Real.log (r : ℝ)⁻¹ / Real.log (s : ℝ)⁻¹ : ℝ) : EReal) * coveringGrowthInf s A := by
  have hc : 0 < Real.log (r : ℝ)⁻¹ / Real.log (s : ℝ)⁻¹ :=
    div_pos (logInv_pos hr0 hr1) (logInv_pos hs0 hs1)
  calc coveringGrowthInf r A ≤ _ :=
        expGrowthInf_monotone (externalCoveringNumber_pow_le_comp hr0 hr1 hs0 hs1 A)
    _ = _ :=
        (monotone_externalCoveringNumber_pow hs1.le A).expGrowthInf_comp
          (Real.tendsto_natCeil_mul_div_atTop_ereal hc.le)
          (EReal.coe_ne_zero.mpr hc.ne') (EReal.coe_ne_top _)

/-- **The upper box dimension does not depend on the ratio at which it is computed.** -/
theorem upperBoxDimWith_eq {r s : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (A : Set X) : upperBoxDimWith r A = upperBoxDimWith s A := by
  have main : ∀ {p q : ℝ≥0}, 0 < p → p < 1 → 0 < q → q < 1 →
      upperBoxDimWith p A ≤ upperBoxDimWith q A := by
    intro p q hp0 hp1 hq0 hq1
    calc upperBoxDimWith p A
        = coveringGrowth p A / ((Real.log (p : ℝ)⁻¹ : ℝ) : EReal) := rfl
      _ ≤ ((Real.log (p : ℝ)⁻¹ / Real.log (q : ℝ)⁻¹ : ℝ) : EReal) * coveringGrowth q A
            / ((Real.log (p : ℝ)⁻¹ : ℝ) : EReal) :=
          EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal hp0 hp1)
            (coveringGrowth_le_of_lt_one hp0 hp1 hq0 hq1 A)
      _ = coveringGrowth q A / ((Real.log (q : ℝ)⁻¹ : ℝ) : EReal) :=
          EReal.coe_div_mul_div_cancel (logInv_pos hp0 hp1) (logInv_pos hq0 hq1) _
      _ = upperBoxDimWith q A := rfl
  exact le_antisymm (main hr0 hr1 hs0 hs1) (main hs0 hs1 hr0 hr1)

/-- **The lower box dimension does not depend on the ratio at which it is computed.** -/
theorem lowerBoxDimWith_eq {r s : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (A : Set X) : lowerBoxDimWith r A = lowerBoxDimWith s A := by
  have main : ∀ {p q : ℝ≥0}, 0 < p → p < 1 → 0 < q → q < 1 →
      lowerBoxDimWith p A ≤ lowerBoxDimWith q A := by
    intro p q hp0 hp1 hq0 hq1
    calc lowerBoxDimWith p A
        = coveringGrowthInf p A / ((Real.log (p : ℝ)⁻¹ : ℝ) : EReal) := rfl
      _ ≤ ((Real.log (p : ℝ)⁻¹ / Real.log (q : ℝ)⁻¹ : ℝ) : EReal) * coveringGrowthInf q A
            / ((Real.log (p : ℝ)⁻¹ : ℝ) : EReal) :=
          EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal hp0 hp1)
            (coveringGrowthInf_le_of_lt_one hp0 hp1 hq0 hq1 A)
      _ = coveringGrowthInf q A / ((Real.log (q : ℝ)⁻¹ : ℝ) : EReal) :=
          EReal.coe_div_mul_div_cancel (logInv_pos hp0 hp1) (logInv_pos hq0 hq1) _
      _ = lowerBoxDimWith q A := rfl
  exact le_antisymm (main hr0 hr1 hs0 hs1) (main hs0 hs1 hr0 hr1)

/-- `Metric.lowerBoxDim` may be computed at any ratio in `(0,1)`. -/
theorem lowerBoxDim_eq_lowerBoxDimWith {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (A : Set X) :
    lowerBoxDim A = lowerBoxDimWith r A :=
  lowerBoxDimWith_eq half_pos_nnreal half_lt_one_nnreal hr0 hr1 A

/-- The lower box dimension never exceeds the upper one. -/
theorem lowerBoxDim_le_upperBoxDim (A : Set X) : lowerBoxDim A ≤ upperBoxDim A :=
  EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal half_pos_nnreal half_lt_one_nnreal)
    expGrowthInf_le_expGrowthSup

/-- `Metric.upperBoxDim` may be computed at any ratio in `(0,1)`. -/
theorem upperBoxDim_eq_upperBoxDimWith {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (A : Set X) :
    upperBoxDim A = upperBoxDimWith r A :=
  upperBoxDimWith_eq (by norm_num) (by norm_num) hr0 hr1 A

/-! ## Monotonicity in the set -/

theorem coveringGrowth_mono (r : ℝ≥0) (h : A ⊆ B) : coveringGrowth r A ≤ coveringGrowth r B :=
  expGrowthSup_monotone fun _ => ENat.toENNReal_mono (externalCoveringNumber_mono_set h)

theorem upperBoxDimWith_mono {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (h : A ⊆ B) :
    upperBoxDimWith r A ≤ upperBoxDimWith r B :=
  EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal hr0 hr1) (coveringGrowth_mono r h)

theorem upperBoxDim_mono (h : A ⊆ B) : upperBoxDim A ≤ upperBoxDim B :=
  upperBoxDimWith_mono half_pos_nnreal half_lt_one_nnreal h

/-! ## The empty set, and nonnegativity -/

@[simp] theorem coveringGrowth_empty (r : ℝ≥0) : coveringGrowth r (∅ : Set X) = ⊥ := by
  have h : (fun n : ℕ => (externalCoveringNumber (r ^ n) (∅ : Set X) : ℝ≥0∞)) = 0 := by
    funext n; simp
  rw [coveringGrowth, h, expGrowthSup_zero]

theorem le_coveringGrowth {r : ℝ≥0} (hr1 : r ≤ 1) (hA : A.Nonempty) : 0 ≤ coveringGrowth r A := by
  refine (monotone_externalCoveringNumber_pow hr1 A).expGrowthSup_nonneg ?_
  intro hcon
  have h0 := congrFun hcon 0
  simp only [Pi.zero_apply, ENat.toENNReal_eq_zero, externalCoveringNumber_eq_zero] at h0
  exact hA.ne_empty h0

theorem upperBoxDimWith_nonneg {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hA : A.Nonempty) :
    0 ≤ upperBoxDimWith r A :=
  calc (0 : EReal) = 0 / ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := EReal.zero_div.symm
    _ ≤ upperBoxDimWith r A :=
        EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal hr0 hr1)
          (le_coveringGrowth hr1.le hA)

theorem upperBoxDim_nonneg (hA : A.Nonempty) : 0 ≤ upperBoxDim A :=
  upperBoxDimWith_nonneg half_pos_nnreal half_lt_one_nnreal hA

/-! ## Upper bounds from an explicit cover -/

/-- If `A` can be covered by `C · kⁿ` balls of radius `rⁿ` for every `n`, its covering growth
at ratio `r` is at most `log k`.  The constant `C` is invisible to the growth rate. -/
theorem coveringGrowth_le_log {r : ℝ≥0} {C k : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ n, (externalCoveringNumber (r ^ n) A : ℝ≥0∞) ≤ C * k ^ n) :
    coveringGrowth r A ≤ ENNReal.log k :=
  (expGrowthSup_le_of_eventually_le hC (Eventually.of_forall h)).trans expGrowthSup_pow.le

/-- **The upper bound on the box dimension from an explicit cover.**  `k` branches at
contraction ratio `r`, up to a constant, give `dim_B A ≤ log k / log r⁻¹`. -/
theorem upperBoxDim_le_of_covering {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {C k : ℝ≥0∞}
    (hC : C ≠ ⊤) (h : ∀ n, (externalCoveringNumber (r ^ n) A : ℝ≥0∞) ≤ C * k ^ n) :
    upperBoxDim A ≤ ENNReal.log k / ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
  rw [upperBoxDim_eq_upperBoxDimWith hr0 hr1]
  exact EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal hr0 hr1)
    (coveringGrowth_le_log hC h)

/-- `Metric.upperBoxDim_le_of_covering` in the form met in practice: `C · kⁿ` balls of radius
`rⁿ`, with natural-number counts, and a real-valued bound. -/
theorem upperBoxDim_le_of_covering_nat {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {C k : ℕ}
    (hk : 0 < k) (h : ∀ n, externalCoveringNumber (r ^ n) A ≤ (C : ℕ∞) * (k : ℕ∞) ^ n) :
    upperBoxDim A ≤ ((Real.log k / Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
  have hcast : ∀ n, (externalCoveringNumber (r ^ n) A : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (k : ℝ≥0∞) ^ n := by
    intro n
    have := ENat.toENNReal_mono (h n)
    simpa using this
  have hlog : ENNReal.log ((k : ℝ≥0∞)) = ((Real.log k : ℝ) : EReal) := by
    rw [ENNReal.log_pos_real (by exact_mod_cast hk.ne') (by simp)]
    norm_num
  have := upperBoxDim_le_of_covering (A := A) hr0 hr1 (C := (C : ℝ≥0∞)) (k := (k : ℝ≥0∞))
    (by simp) hcast
  rwa [hlog, ← EReal.coe_div] at this

/-! ## Lower bounds -/

/-- The dual of `Metric.coveringGrowth_le_log`. -/
theorem log_le_coveringGrowth {r : ℝ≥0} {C k : ℝ≥0∞} (hC : C ≠ 0)
    (h : ∀ᶠ n in atTop, C * k ^ n ≤ (externalCoveringNumber (r ^ n) A : ℝ≥0∞)) :
    ENNReal.log k ≤ coveringGrowth r A :=
  expGrowthSup_pow.ge.trans (expGrowthSup_of_eventually_ge hC h)

/-! ## A fixed factor in the radius is invisible -/

private theorem monotone_externalCoveringNumber_const_mul_pow {r c : ℝ≥0} (hr : r ≤ 1)
    (A : Set X) : Monotone fun n : ℕ => (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞) :=
  monotone_nat_of_le_succ fun n =>
    ENat.toENNReal_mono (externalCoveringNumber_anti
      (mul_le_mul_of_nonneg_left (pow_le_pow_right_of_le_one' hr n.le_succ) zero_le))

/-- The two shifts that absorb a constant factor in the radius: `r ^ m ≤ c` compensates the
factor in one direction, `c * r ^ m' ≤ 1` in the other. -/
private theorem exists_pow_le_and_const_mul_pow_le {r c : ℝ≥0} (hr1 : r < 1) (hc0 : 0 < c) :
    ∃ m m' : ℕ, r ^ m ≤ c ∧ c * r ^ m' ≤ 1 := by
  obtain ⟨m, hm⟩ := NNReal.exists_pow_lt_of_lt_one hc0 hr1
  obtain ⟨m', hm'⟩ := NNReal.exists_pow_lt_of_lt_one (inv_pos.mpr hc0) hr1
  refine ⟨m, m', hm.le, ?_⟩
  calc c * r ^ m' ≤ c * c⁻¹ := mul_le_mul_of_nonneg_left hm'.le zero_le
    _ = 1 := mul_inv_cancel₀ hc0.ne'

/-- Multiplying the radius by a fixed positive constant does not change the covering growth:
the constant is absorbed by a bounded shift of the scale index. -/
theorem coveringGrowth_const_mul {r c : ℝ≥0} (hr1 : r < 1) (hc0 : 0 < c) (A : Set X) :
    expGrowthSup (fun n => (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞))
      = coveringGrowth r A := by
  obtain ⟨m, m', hm, hm'⟩ := exists_pow_le_and_const_mul_pow_le hr1 hc0
  refine le_antisymm ?_ ?_
  · have hle : ∀ n, (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞)
        ≤ (externalCoveringNumber (r ^ (n + m)) A : ℝ≥0∞) := fun n =>
      ENat.toENNReal_mono (externalCoveringNumber_anti (by
        calc r ^ (n + m) = r ^ n * r ^ m := pow_add r n m
          _ ≤ r ^ n * c := mul_le_mul_of_nonneg_left hm zero_le
          _ = c * r ^ n := mul_comm _ _))
    calc expGrowthSup (fun n => (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞))
        ≤ expGrowthSup (fun n => (externalCoveringNumber (r ^ (n + m)) A : ℝ≥0∞)) :=
          expGrowthSup_monotone hle
      _ = coveringGrowth r A :=
          (monotone_externalCoveringNumber_pow hr1.le A).expGrowthSup_comp_add m
  · have hle : ∀ n, (externalCoveringNumber (r ^ n) A : ℝ≥0∞)
        ≤ (externalCoveringNumber (c * r ^ (n + m')) A : ℝ≥0∞) := fun n =>
      ENat.toENNReal_mono (externalCoveringNumber_anti (by
        calc c * r ^ (n + m') = c * r ^ m' * r ^ n := by rw [pow_add]; ring
          _ ≤ 1 * r ^ n := mul_le_mul_of_nonneg_right hm' zero_le
          _ = r ^ n := one_mul _))
    calc coveringGrowth r A
        ≤ expGrowthSup (fun n => (externalCoveringNumber (c * r ^ (n + m')) A : ℝ≥0∞)) :=
          expGrowthSup_monotone hle
      _ = expGrowthSup (fun n => (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞)) :=
          (monotone_externalCoveringNumber_const_mul_pow hr1.le A).expGrowthSup_comp_add m'

/-- `Metric.coveringGrowth_const_mul` for the lower covering growth. -/
theorem coveringGrowthInf_const_mul {r c : ℝ≥0} (hr1 : r < 1) (hc0 : 0 < c) (A : Set X) :
    expGrowthInf (fun n => (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞))
      = coveringGrowthInf r A := by
  obtain ⟨m, m', hm, hm'⟩ := exists_pow_le_and_const_mul_pow_le hr1 hc0
  refine le_antisymm ?_ ?_
  · have hle : ∀ n, (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞)
        ≤ (externalCoveringNumber (r ^ (n + m)) A : ℝ≥0∞) := fun n =>
      ENat.toENNReal_mono (externalCoveringNumber_anti (by
        calc r ^ (n + m) = r ^ n * r ^ m := pow_add r n m
          _ ≤ r ^ n * c := mul_le_mul_of_nonneg_left hm zero_le
          _ = c * r ^ n := mul_comm _ _))
    calc expGrowthInf (fun n => (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞))
        ≤ expGrowthInf (fun n => (externalCoveringNumber (r ^ (n + m)) A : ℝ≥0∞)) :=
          expGrowthInf_monotone hle
      _ = coveringGrowthInf r A :=
          (monotone_externalCoveringNumber_pow hr1.le A).expGrowthInf_comp_add m
  · have hle : ∀ n, (externalCoveringNumber (r ^ n) A : ℝ≥0∞)
        ≤ (externalCoveringNumber (c * r ^ (n + m')) A : ℝ≥0∞) := fun n =>
      ENat.toENNReal_mono (externalCoveringNumber_anti (by
        calc c * r ^ (n + m') = c * r ^ m' * r ^ n := by rw [pow_add]; ring
          _ ≤ 1 * r ^ n := mul_le_mul_of_nonneg_right hm' zero_le
          _ = r ^ n := one_mul _))
    calc coveringGrowthInf r A
        ≤ expGrowthInf (fun n => (externalCoveringNumber (c * r ^ (n + m')) A : ℝ≥0∞)) :=
          expGrowthInf_monotone hle
      _ = expGrowthInf (fun n => (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞)) :=
          (monotone_externalCoveringNumber_const_mul_pow hr1.le A).expGrowthInf_comp_add m'

/-- `Metric.upperBoxDim_le_of_covering` with a fixed constant allowed in the radius. -/
theorem upperBoxDim_le_of_covering_mul {r c : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hc0 : 0 < c)
    {C k : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ n, (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞) ≤ C * k ^ n) :
    upperBoxDim A ≤ ENNReal.log k / ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
  rw [upperBoxDim_eq_upperBoxDimWith hr0 hr1]
  refine EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal hr0 hr1) ?_
  rw [← coveringGrowth_const_mul hr1 hc0 A]
  exact (expGrowthSup_le_of_eventually_le hC (Eventually.of_forall h)).trans expGrowthSup_pow.le

/-- `Metric.upperBoxDim_le_of_covering_nat` with a fixed constant allowed in the radius: this is
the form met when the cover at depth `n` has radius `c · rⁿ` for a `c` coming from a tail
estimate. -/
theorem upperBoxDim_le_of_covering_mul_nat {r c : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hc0 : 0 < c)
    {C k : ℕ} (hk : 0 < k)
    (h : ∀ n, externalCoveringNumber (c * r ^ n) A ≤ (C : ℕ∞) * (k : ℕ∞) ^ n) :
    upperBoxDim A ≤ ((Real.log k / Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
  have hcast : ∀ n, (externalCoveringNumber (c * r ^ n) A : ℝ≥0∞)
      ≤ (C : ℝ≥0∞) * (k : ℝ≥0∞) ^ n := by
    intro n
    have := ENat.toENNReal_mono (h n)
    simpa using this
  have hlog : ENNReal.log ((k : ℝ≥0∞)) = ((Real.log k : ℝ) : EReal) := by
    rw [ENNReal.log_pos_real (by exact_mod_cast hk.ne') (by simp)]
    norm_num
  have := upperBoxDim_le_of_covering_mul (A := A) hr0 hr1 hc0 (C := (C : ℝ≥0∞)) (k := (k : ℝ≥0∞))
    (by simp) hcast
  rwa [hlog, ← EReal.coe_div] at this

/-! ## Lower bounds from separated subsets -/

/-- A `c·rⁿ`-separated subset of `A` of cardinality `kⁿ` forces `kⁿ` balls of radius
`(c/2)·rⁿ`: the packing number at a radius is at most the external covering number at half
that radius. -/
private theorem pow_le_externalCoveringNumber_of_separated {r c : ℝ≥0} {k : ℕ} {S : ℕ → Set X}
    (hsub : ∀ n, S n ⊆ A) (hsep : ∀ n, IsSeparated ((c * r ^ n : ℝ≥0) : ℝ≥0∞) (S n))
    (hcard : ∀ n, (k : ℕ∞) ^ n ≤ (S n).encard) (n : ℕ) :
    ((k : ℝ≥0∞)) ^ n ≤ (externalCoveringNumber (c / 2 * r ^ n) A : ℝ≥0∞) := by
  have h2c' : (2 : ℝ≥0) * (c / 2) = c := by field_simp
  have h1 : ((k : ℕ∞)) ^ n ≤ packingNumber (2 * (c / 2 * r ^ n)) A := by
    refine (hcard n).trans ?_
    rw [show (2 : ℝ≥0) * (c / 2 * r ^ n) = c * r ^ n by rw [← mul_assoc, h2c']]
    exact (hsep n).encard_le_packingNumber (hsub n)
  have h2 := packingNumber_two_mul_le_externalCoveringNumber (c / 2 * r ^ n) A
  simpa using ENat.toENNReal_mono (h1.trans h2)

/-- **The lower bound on the box dimension from separated subsets.**  If for every `n` the set
`A` contains a `c·rⁿ`-separated subset of cardinality at least `kⁿ`, then
`log k / log r⁻¹ ≤ dim_B A`.  The constant `c` may be any positive number: a factor in the
radius is absorbed by `Metric.coveringGrowth_const_mul`. -/
theorem le_upperBoxDim_of_separated {r c : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hc0 : 0 < c)
    {k : ℕ} (hk : 0 < k) {S : ℕ → Set X} (hsub : ∀ n, S n ⊆ A)
    (hsep : ∀ n, IsSeparated ((c * r ^ n : ℝ≥0) : ℝ≥0∞) (S n))
    (hcard : ∀ n, (k : ℕ∞) ^ n ≤ (S n).encard) :
    ((Real.log k / Real.log (r : ℝ)⁻¹ : ℝ) : EReal) ≤ upperBoxDim A := by
  have hc'0 : (0 : ℝ≥0) < c / 2 := by positivity
  have hgrowth : ENNReal.log (k : ℝ≥0∞)
      ≤ expGrowthSup (fun n => (externalCoveringNumber (c / 2 * r ^ n) A : ℝ≥0∞)) :=
    expGrowthSup_pow.ge.trans
      (expGrowthSup_monotone (pow_le_externalCoveringNumber_of_separated hsub hsep hcard))
  rw [coveringGrowth_const_mul hr1 hc'0 A] at hgrowth
  have hlogk : ((Real.log k : ℝ) : EReal) = ENNReal.log (k : ℝ≥0∞) := by
    rw [ENNReal.log_pos_real (by exact_mod_cast hk.ne') (by simp)]
    norm_num
  rw [upperBoxDim_eq_upperBoxDimWith hr0 hr1, upperBoxDimWith, EReal.coe_div, hlogk]
  exact EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal hr0 hr1) hgrowth

/-- `Metric.le_upperBoxDim_of_separated` for the lower box dimension: separated subsets at
*every* scale bound the `liminf` as well, so together with an upper bound from a cover they
show that the box dimension exists. -/
theorem le_lowerBoxDim_of_separated {r c : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hc0 : 0 < c)
    {k : ℕ} (hk : 0 < k) {S : ℕ → Set X} (hsub : ∀ n, S n ⊆ A)
    (hsep : ∀ n, IsSeparated ((c * r ^ n : ℝ≥0) : ℝ≥0∞) (S n))
    (hcard : ∀ n, (k : ℕ∞) ^ n ≤ (S n).encard) :
    ((Real.log k / Real.log (r : ℝ)⁻¹ : ℝ) : EReal) ≤ lowerBoxDim A := by
  have hc'0 : (0 : ℝ≥0) < c / 2 := by positivity
  have hgrowth : ENNReal.log (k : ℝ≥0∞)
      ≤ expGrowthInf (fun n => (externalCoveringNumber (c / 2 * r ^ n) A : ℝ≥0∞)) :=
    expGrowthInf_pow.ge.trans
      (expGrowthInf_monotone (pow_le_externalCoveringNumber_of_separated hsub hsep hcard))
  rw [coveringGrowthInf_const_mul hr1 hc'0 A] at hgrowth
  have hlogk : ((Real.log k : ℝ) : EReal) = ENNReal.log (k : ℝ≥0∞) := by
    rw [ENNReal.log_pos_real (by exact_mod_cast hk.ne') (by simp)]
    norm_num
  rw [lowerBoxDim_eq_lowerBoxDimWith hr0 hr1, lowerBoxDimWith, EReal.coe_div, hlogk]
  exact EReal.div_le_div_right_of_nonneg (logInv_nonneg_ereal hr0 hr1) hgrowth

/-! ## An optimal external cover exists when the covering number is finite

The internal analogue is `Metric.exists_set_encard_eq_coveringNumber`; the external one is
what the sumset bound below needs. -/

theorem exists_isCover_encard_eq_externalCoveringNumber {ε : ℝ≥0} {A : Set X}
    (h : externalCoveringNumber ε A ≠ ⊤) :
    ∃ C : Set X, IsCover ε A C ∧ C.encard = externalCoveringNumber ε A := by
  have hne : Nonempty { s : Set X // IsCover ε A s } := by
    by_contra hcon
    refine h ?_
    rw [externalCoveringNumber]
    simp only [iInf_eq_top]
    intro C hC
    exact absurd (⟨⟨C, hC⟩⟩ : Nonempty { s : Set X // IsCover ε A s }) hcon
  obtain ⟨C, hC⟩ :=
    ENat.exists_eq_iInf (fun C : { s : Set X // IsCover ε A s } => (C : Set X).encard)
  refine ⟨C, C.2, ?_⟩
  rw [hC, externalCoveringNumber]
  simp_rw [iInf_subtype]

end Metric

/-! ## Sumsets -/

namespace Metric

variable {E : Type*} [SeminormedAddCommGroup E] {A B : Set E}

/-- The sum of an `ε`-cover of `A` and a `δ`-cover of `B` is an `(ε+δ)`-cover of `A + B`. -/
theorem IsCover.add {ε δ : ℝ≥0} {C D : Set E} (hC : IsCover ε A C) (hD : IsCover δ B D) :
    IsCover (ε + δ) (A + B) (C + D) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨c, hc, hac⟩ := hC ha
  obtain ⟨d, hd, hbd⟩ := hD hb
  refine ⟨c + d, Set.add_mem_add hc hd, ?_⟩
  calc edist (a + b) (c + d) ≤ edist a c + edist b d := edist_add_add_le _ _ _ _
    _ ≤ (ε : ℝ≥0∞) + (δ : ℝ≥0∞) := add_le_add hac hbd
    _ = ((ε + δ : ℝ≥0) : ℝ≥0∞) := by push_cast; ring

/-- **Covering numbers are submultiplicative on sumsets.** -/
theorem externalCoveringNumber_add_le (ε δ : ℝ≥0) (A B : Set E) :
    externalCoveringNumber (ε + δ) (A + B)
      ≤ externalCoveringNumber ε A * externalCoveringNumber δ B := by
  rcases eq_or_ne A ∅ with rfl | hA
  · simp
  rcases eq_or_ne B ∅ with rfl | hB
  · simp
  rcases eq_or_ne (externalCoveringNumber ε A) ⊤ with hA' | hA'
  · rw [hA', ENat.top_mul (by simpa [externalCoveringNumber_eq_zero] using hB)]; exact le_top
  rcases eq_or_ne (externalCoveringNumber δ B) ⊤ with hB' | hB'
  · rw [hB', ENat.mul_top (by simpa [externalCoveringNumber_eq_zero] using hA)]; exact le_top
  obtain ⟨C, hC, hCcard⟩ := exists_isCover_encard_eq_externalCoveringNumber hA'
  obtain ⟨D, hD, hDcard⟩ := exists_isCover_encard_eq_externalCoveringNumber hB'
  have hsub : C + D ⊆ (fun p : E × E => p.1 + p.2) '' (C ×ˢ D) := by
    rintro _ ⟨c, hc, d, hd, rfl⟩
    exact ⟨(c, d), ⟨hc, hd⟩, rfl⟩
  calc externalCoveringNumber (ε + δ) (A + B) ≤ (C + D).encard :=
        (hC.add hD).externalCoveringNumber_le_encard
    _ ≤ ((fun p : E × E => p.1 + p.2) '' (C ×ˢ D)).encard := Set.encard_le_encard hsub
    _ ≤ (C ×ˢ D).encard := Set.encard_image_le _ _
    _ = C.encard * D.encard := Set.encard_prod
    _ = externalCoveringNumber ε A * externalCoveringNumber δ B := by rw [hCcard, hDcard]

/-- **The covering growth is subadditive on sumsets.** -/
theorem coveringGrowth_add_le {r : ℝ≥0} (hr1 : r < 1) (hA : A.Nonempty) (hB : B.Nonempty) :
    coveringGrowth r (A + B) ≤ coveringGrowth r A + coveringGrowth r B := by
  have hh0 : (0 : ℝ≥0) < 2⁻¹ := by norm_num
  have hAeq := coveringGrowth_const_mul hr1 hh0 A
  have hBeq := coveringGrowth_const_mul hr1 hh0 B
  have hstep : (fun n => (externalCoveringNumber (r ^ n) (A + B) : ℝ≥0∞))
      ≤ (fun n => (externalCoveringNumber (2⁻¹ * r ^ n) A : ℝ≥0∞))
        * fun n => (externalCoveringNumber (2⁻¹ * r ^ n) B : ℝ≥0∞) := by
    intro n
    have hsplit : (2⁻¹ : ℝ≥0) * r ^ n + 2⁻¹ * r ^ n = r ^ n := by
      rw [← add_mul]; norm_num
    have h := externalCoveringNumber_add_le (2⁻¹ * r ^ n) (2⁻¹ * r ^ n) A B
    rw [hsplit] at h
    simpa using ENat.toENNReal_mono h
  have hA0 : (0 : EReal)
      ≤ expGrowthSup fun n => (externalCoveringNumber (2⁻¹ * r ^ n) A : ℝ≥0∞) := by
    rw [hAeq]; exact le_coveringGrowth hr1.le hA
  have hB0 : (0 : EReal)
      ≤ expGrowthSup fun n => (externalCoveringNumber (2⁻¹ * r ^ n) B : ℝ≥0∞) := by
    rw [hBeq]; exact le_coveringGrowth hr1.le hB
  calc coveringGrowth r (A + B)
      ≤ expGrowthSup ((fun n => (externalCoveringNumber (2⁻¹ * r ^ n) A : ℝ≥0∞))
          * fun n => (externalCoveringNumber (2⁻¹ * r ^ n) B : ℝ≥0∞)) :=
        expGrowthSup_monotone hstep
    _ ≤ (expGrowthSup fun n => (externalCoveringNumber (2⁻¹ * r ^ n) A : ℝ≥0∞))
          + expGrowthSup fun n => (externalCoveringNumber (2⁻¹ * r ^ n) B : ℝ≥0∞) :=
        expGrowthSup_mul_le (Or.inl (fun hc => by simp [hc] at hA0))
          (Or.inr (fun hc => by simp [hc] at hB0))
    _ = coveringGrowth r A + coveringGrowth r B := by rw [hAeq, hBeq]

/-- **Upper box dimension is subadditive on sumsets**, `dim_B (A + B) ≤ dim_B A + dim_B B`. -/
theorem upperBoxDim_add_le (hA : A.Nonempty) (hB : B.Nonempty) :
    upperBoxDim (A + B) ≤ upperBoxDim A + upperBoxDim B := by
  have hnn : (0 : EReal) ≤ ((Real.log (((2⁻¹ : ℝ≥0)) : ℝ)⁻¹ : ℝ) : EReal) :=
    logInv_nonneg_ereal half_pos_nnreal half_lt_one_nnreal
  calc upperBoxDim (A + B) ≤ (coveringGrowth 2⁻¹ A + coveringGrowth 2⁻¹ B)
        / ((Real.log (((2⁻¹ : ℝ≥0)) : ℝ)⁻¹ : ℝ) : EReal) :=
        EReal.div_le_div_right_of_nonneg hnn (coveringGrowth_add_le half_lt_one_nnreal hA hB)
    _ = upperBoxDim A + upperBoxDim B := EReal.add_div_of_nonneg_right hnn

/-! ## Difference sets

`x ↦ -x` is an isometry, so it changes no covering number; `A - B = A + (-B)` then turns the
sumset bound into a bound for difference sets. -/

/-- The negative of an `ε`-cover of `A` is an `ε`-cover of `-A`. -/
theorem IsCover.neg {ε : ℝ≥0} {C : Set E} (hC : IsCover ε A C) : IsCover ε (-A) (-C) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hC (Set.mem_neg.mp hx)
  refine ⟨-y, Set.neg_mem_neg.mpr hy, ?_⟩
  have hxy' : edist (-x) y ≤ (ε : ℝ≥0∞) := hxy
  show edist x (-y) ≤ (ε : ℝ≥0∞)
  rwa [← edist_neg_neg x (-y), neg_neg]

@[simp] theorem externalCoveringNumber_neg (ε : ℝ≥0) (A : Set E) :
    externalCoveringNumber ε (-A) = externalCoveringNumber ε A := by
  have key : ∀ (B : Set E), externalCoveringNumber ε (-B) ≤ externalCoveringNumber ε B := by
    intro B
    refine le_iInf₂ fun C hC => ?_
    refine hC.neg.externalCoveringNumber_le_encard.trans (le_of_eq ?_)
    rw [← Set.image_neg_eq_neg]
    exact neg_injective.encard_image C
  refine le_antisymm (key A) ?_
  have := key (-A)
  rwa [neg_neg] at this

@[simp] theorem coveringGrowth_neg (r : ℝ≥0) (A : Set E) :
    coveringGrowth r (-A) = coveringGrowth r A := by
  simp only [coveringGrowth, externalCoveringNumber_neg]

@[simp] theorem upperBoxDim_neg (A : Set E) : upperBoxDim (-A) = upperBoxDim A := by
  simp only [upperBoxDim, upperBoxDimWith, coveringGrowth_neg]

/-- **Upper box dimension is subadditive on difference sets**,
`dim_B (A - B) ≤ dim_B A + dim_B B`.  This is the form M1 Corollary 5 of `note-1061-M1.html`
uses, for `X(α) = C(α) - K`. -/
theorem upperBoxDim_sub_le (hA : A.Nonempty) (hB : B.Nonempty) :
    upperBoxDim (A - B) ≤ upperBoxDim A + upperBoxDim B := by
  rw [sub_eq_add_neg, ← upperBoxDim_neg B]
  exact upperBoxDim_add_le hA hB.neg

end Metric

/-! ## Sets of upper box dimension below one in `ℝ` are Lebesgue-null -/

namespace Real

open Metric MeasureTheory

/-- A cover by `N` closed balls of radius `ε > 0` bounds the Lebesgue measure of a subset of
`ℝ` by `N · 2ε`. -/
theorem volume_le_externalCoveringNumber_mul {A : Set ℝ} {ε : ℝ≥0} (hε : 0 < ε) :
    volume A ≤ (externalCoveringNumber ε A : ℝ≥0∞) * ENNReal.ofReal (2 * ε) := by
  have hpos : (0 : ℝ) < 2 * ε := by positivity
  rcases eq_or_ne (externalCoveringNumber ε A) ⊤ with hN | hN
  · rw [hN, ENat.toENNReal_top, ENNReal.top_mul (by simp [hε.ne'])]
    exact le_top
  obtain ⟨C, hC, hCcard⟩ := exists_isCover_encard_eq_externalCoveringNumber hN
  have hfin : C.Finite := Set.encard_ne_top_iff.mp (by rw [hCcard]; exact hN)
  rw [isCover_iff_subset_iUnion_closedEBall] at hC
  have hsub : A ⊆ ⋃ y ∈ hfin.toFinset, Metric.closedBall y (ε : ℝ) := by
    intro x hx
    have hx' := hC hx
    simp only [Set.mem_iUnion, exists_prop] at hx' ⊢
    obtain ⟨y, hyC, hy⟩ := hx'
    refine ⟨y, by simpa using hyC, ?_⟩
    rw [Metric.mem_closedEBall] at hy
    rw [Metric.mem_closedBall, dist_edist]
    calc (edist x y).toReal ≤ (((ε : ℝ≥0) : ℝ≥0∞)).toReal :=
          ENNReal.toReal_mono (by simp) hy
      _ = (ε : ℝ) := by simp
  calc volume A ≤ volume (⋃ y ∈ hfin.toFinset, Metric.closedBall y (ε : ℝ)) := measure_mono hsub
    _ ≤ ∑ y ∈ hfin.toFinset, volume (Metric.closedBall y (ε : ℝ)) :=
        measure_biUnion_finset_le _ _
    _ = (hfin.toFinset.card : ℝ≥0∞) * ENNReal.ofReal (2 * ε) := by
        simp [Real.volume_closedBall, Finset.sum_const, nsmul_eq_mul]
    _ = (externalCoveringNumber ε A : ℝ≥0∞) * ENNReal.ofReal (2 * ε) := by
        rw [← hCcard, hfin.encard_eq_coe_toFinset_card]
        norm_cast

/-- **A subset of `ℝ` of upper box dimension `< 1` is Lebesgue-null.**  This is the step
`dim_B < 1 ⇒ Leb = 0` of the box-counting argument; no Hausdorff measure is involved. -/
theorem volume_eq_zero_of_upperBoxDim_lt_one {A : Set ℝ} (h : upperBoxDim A < 1) :
    volume A = 0 := by
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  have hcbot : c ≠ ⊥ := (bot_le.trans_lt hc1).ne'
  have hctop : c ≠ ⊤ := (hc2.trans_le le_top).ne
  set t : ℝ := c.toReal with htdef
  have hcs : c = (t : EReal) := (EReal.coe_toReal hctop hcbot).symm
  have ht1 : t < 1 := by
    have : ((t : ℝ) : EReal) < ((1 : ℝ) : EReal) := by rw [← hcs, EReal.coe_one]; exact hc2
    exact_mod_cast this
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hden : ((Real.log (((2⁻¹ : ℝ≥0)) : ℝ)⁻¹ : ℝ) : EReal) = ((Real.log 2 : ℝ) : EReal) := by
    norm_num
  have hgrow : coveringGrowth 2⁻¹ A < ((t * Real.log 2 : ℝ) : EReal) := by
    have hlt := hc1
    rw [upperBoxDim, upperBoxDimWith, hden, hcs,
      EReal.div_lt_iff (by exact_mod_cast hL) (EReal.coe_ne_top _)] at hlt
    rwa [EReal.coe_mul]
  set b : ℝ := Real.exp (t * Real.log 2) with hbdef
  have hb0 : 0 < b := Real.exp_pos _
  have hb2 : b < 2 := by
    have h1 : t * Real.log 2 < Real.log 2 := by nlinarith
    calc b = Real.exp (t * Real.log 2) := hbdef
      _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr h1
      _ = 2 := Real.exp_log two_pos
  have hev : ∀ᶠ n : ℕ in atTop,
      (externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ n) := by
    filter_upwards [eventually_le_exp hgrow] with n hn
    refine hn.trans (le_of_eq ?_)
    rw [show ((t * Real.log 2 : ℝ) : EReal) * (n : EReal)
        = ((t * Real.log 2 * n : ℝ) : EReal) by norm_cast, EReal.exp_coe, hbdef,
      ← Real.exp_nat_mul]
    ring_nf
  have hbound : ∀ᶠ n : ℕ in atTop, volume A ≤ ENNReal.ofReal (2 * (b / 2) ^ n) := by
    filter_upwards [hev] with n hn
    have hεpos : (0 : ℝ≥0) < (2⁻¹ : ℝ≥0) ^ n := by positivity
    refine (volume_le_externalCoveringNumber_mul hεpos).trans ?_
    have hcast : ((((2⁻¹ : ℝ≥0) ^ n : ℝ≥0)) : ℝ) = ((2 : ℝ)⁻¹) ^ n := by push_cast; ring
    rw [hcast]
    calc (externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A : ℝ≥0∞)
          * ENNReal.ofReal (2 * ((2 : ℝ)⁻¹) ^ n)
        ≤ ENNReal.ofReal (b ^ n) * ENNReal.ofReal (2 * ((2 : ℝ)⁻¹) ^ n) := by gcongr
      _ = ENNReal.ofReal (2 * (b / 2) ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_eq_mul_inv, mul_pow]
          ring
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (b / 2) ^ n)) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => 2 * (b / 2) ^ n) atTop (𝓝 0) := by
      have hlt1 : b / 2 < 1 := by rw [div_lt_one two_pos]; exact hb2
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt1).const_mul (2 : ℝ)
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp hr
    rwa [ENNReal.ofReal_zero] at h2
  exact le_antisymm (ge_of_tendsto hlim hbound) zero_le

end Real

/-! ## Comparison with the Hausdorff dimension

A cover of `A` by `N` closed balls of radius `ε` is an admissible cover in the definition of
the Hausdorff measure `μH[d]`, contributing `N · (2ε)ᵈ`.  So a covering rate below `d` forces
`μH[d] A = 0`, which is `dimH A ≤ dim_B A`.  The inequality is genuinely one-way — `ℚ ∩ [0,1]`
has Hausdorff dimension `0` and upper box dimension `1` — and it needs `A` nonempty, since
`upperBoxDim ∅ = ⊥` while `dimH ∅ = 0`. -/

namespace Metric

open MeasureTheory

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] {A : Set X}

/-- The engine of `Metric.dimH_le_upperBoxDim`: if `A` is covered by at most `bⁿ` balls of
radius `2⁻ⁿ` for all large `n`, and `b · 2⁻ᵈ < 1`, then `μH[d] A = 0`.  The covering numbers
enter only through the geometric decay of `bⁿ · (2 · 2⁻ⁿ)ᵈ = 2ᵈ · (b · 2⁻ᵈ)ⁿ`. -/
private theorem hausdorffMeasure_eq_zero_of_covering_pow {d b : ℝ} (hd : 0 < d) (hb : 0 < b)
    (hbd : b * ((2 : ℝ)⁻¹) ^ d < 1)
    (hcov : ∀ᶠ n : ℕ in atTop,
      (externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ n)) :
    μH[d] A = 0 := by
  classical
  -- A *finite* cover at every scale, optimal wherever the covering number is finite.  The
  -- second component is vacuous at the scales where it is infinite, and there `∅` will do.
  have hex : ∀ n : ℕ, ∃ C : Set X, C.Finite ∧
      (externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A ≠ ⊤ →
        IsCover ((2⁻¹ : ℝ≥0) ^ n) A C ∧
          C.encard = externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A) := by
    intro n
    rcases eq_or_ne (externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A) ⊤ with h | h
    · exact ⟨∅, Set.finite_empty, fun hcon => absurd h hcon⟩
    · obtain ⟨C, hC, hCcard⟩ := exists_isCover_encard_eq_externalCoveringNumber h
      exact ⟨C, Set.encard_ne_top_iff.mp (by rw [hCcard]; exact h), fun _ => ⟨hC, hCcard⟩⟩
  choose Cov hCovFin hCovProp using hex
  have : ∀ n : ℕ, Fintype (Cov n) := fun n => (hCovFin n).fintype
  have hpos : ∀ n : ℕ, (0 : ℝ) < 2 * ((2 : ℝ)⁻¹) ^ n := fun n => by positivity
  have hcoe : ∀ n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ)⁻¹) ^ n)
      = 2 * (((2⁻¹ : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) := by
    intro n
    have hcast : (((2⁻¹ : ℝ≥0) ^ n : ℝ≥0) : ℝ) = ((2 : ℝ)⁻¹) ^ n := by push_cast; ring
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_coe_nnreal, hcast]
  have hnetop : ∀ n : ℕ, (externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A : ℝ≥0∞)
      ≤ ENNReal.ofReal (b ^ n) → externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A ≠ ⊤ := by
    intro n hn h
    rw [h, ENat.toENNReal_top, top_le_iff] at hn
    exact ENNReal.ofReal_ne_top hn
  -- The cover family, indexed by the finite cover itself.
  set T : ∀ n : ℕ, (Cov n) → Set X :=
    fun n y => closedEBall (y : X) (((2⁻¹ : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) with hT
  have hediam : ∀ᶠ n : ℕ in atTop,
      ∀ i, ediam (T n i) ≤ ENNReal.ofReal (2 * ((2 : ℝ)⁻¹) ^ n) := by
    filter_upwards with n i
    rw [hcoe n, hT]
    exact ediam_closedEBall_le
  have hsub : ∀ᶠ n : ℕ in atTop, A ⊆ ⋃ i, T n i := by
    filter_upwards [hcov] with n hn
    have hcov' := (hCovProp n (hnetop n hn)).1
    rw [isCover_iff_subset_iUnion_closedEBall] at hcov'
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcov' hx)
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * ((2 : ℝ)⁻¹) ^ n)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => 2 * ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul (2 : ℝ)
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    rwa [ENNReal.ofReal_zero] at h2
  have hmain := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum d A
    (fun n : ℕ => ENNReal.ofReal (2 * ((2 : ℝ)⁻¹) ^ n)) hr T hediam hsub
  -- The sums decay geometrically.
  set q : ℝ := b * ((2 : ℝ)⁻¹) ^ d with hq
  have hq0 : 0 < q := by
    rw [hq]
    have : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ d := Real.rpow_pos_of_pos (by norm_num) d
    positivity
  have hsum : ∀ᶠ n : ℕ in atTop,
      (∑ i, ediam (T n i) ^ d) ≤ ENNReal.ofReal ((2 : ℝ) ^ d * q ^ n) := by
    filter_upwards [hcov, hediam] with n hn hdi
    have hcard : ((Fintype.card (Cov n) : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ n) := by
      have h1 : ((Cov n).encard : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ n) := by
        rw [(hCovProp n (hnetop n hn)).2]; exact hn
      have h2 : (Cov n).encard = (Fintype.card (Cov n) : ℕ∞) := by
        rw [← ENat.card_coe_set_eq, ENat.card_eq_coe_fintype_card]
      rw [h2] at h1
      exact_mod_cast h1
    have hreal : b ^ n * (2 * ((2 : ℝ)⁻¹) ^ n) ^ d = (2 : ℝ) ^ d * q ^ n := by
      have h1 : (2 * ((2 : ℝ)⁻¹) ^ n) ^ d = (2 : ℝ) ^ d * (((2 : ℝ)⁻¹) ^ d) ^ n := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        rw [← Real.rpow_natCast ((2 : ℝ)⁻¹) n, ← Real.rpow_mul (by norm_num),
          mul_comm (n : ℝ) d, Real.rpow_mul (by norm_num), Real.rpow_natCast]
      rw [h1, hq, mul_pow]
      ring
    calc (∑ i, ediam (T n i) ^ d)
        ≤ ∑ _i : (Cov n), (ENNReal.ofReal (2 * ((2 : ℝ)⁻¹) ^ n)) ^ d :=
          Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hdi i) hd.le
      _ = ((Fintype.card (Cov n) : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (2 * ((2 : ℝ)⁻¹) ^ n)) ^ d := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (b ^ n) * ENNReal.ofReal ((2 * ((2 : ℝ)⁻¹) ^ n) ^ d) := by
          rw [ENNReal.ofReal_rpow_of_pos (hpos n)]
          gcongr
      _ = ENNReal.ofReal (b ^ n * (2 * ((2 : ℝ)⁻¹) ^ n) ^ d) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal ((2 : ℝ) ^ d * q ^ n) := by rw [hreal]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((2 : ℝ) ^ d * q ^ n)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => (2 : ℝ) ^ d * q ^ n) atTop (𝓝 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hbd).const_mul ((2 : ℝ) ^ d)
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    rwa [ENNReal.ofReal_zero] at h2
  refine le_antisymm (hmain.trans ?_) bot_le
  calc liminf (fun n : ℕ => ∑ i, ediam (T n i) ^ d) atTop
      ≤ liminf (fun n : ℕ => ENNReal.ofReal ((2 : ℝ) ^ d * q ^ n)) atTop :=
        liminf_le_liminf hsum
    _ = 0 := hlim.liminf_eq

/-- **The Hausdorff dimension is at most the upper box dimension.**  Both are `⊥`-free on a
nonempty set, and the hypothesis cannot be dropped: `upperBoxDim ∅ = ⊥ < 0 = dimH ∅`.

The inequality is typically strict for sets that are small but spread out — `dimH (ℚ ∩ [0,1]) = 0`
while its upper box dimension is `1` — and is an equality for self-similar sets with strong
separation. -/
theorem dimH_le_upperBoxDim (hA : A.Nonempty) : (dimH A : EReal) ≤ upperBoxDim A := by
  refine le_of_forall_gt_imp_ge_of_dense fun y hy => ?_
  rcases eq_or_ne y ⊤ with rfl | hytop
  · exact le_top
  have hy0 : (0 : EReal) < y := (upperBoxDim_nonneg hA).trans_lt hy
  have hybot : y ≠ ⊥ := ne_bot_of_gt hy0
  set t : ℝ := y.toReal with htdef
  have hyt : y = ((t : ℝ) : EReal) := (EReal.coe_toReal hytop hybot).symm
  have ht0 : (0 : ℝ) < t := by
    have h : ((0 : ℝ) : EReal) < ((t : ℝ) : EReal) := by rw [← hyt]; exact_mod_cast hy0
    exact_mod_cast h
  -- an intermediate exponent, strictly between the covering rate and `t`
  obtain ⟨c, hc1, hc2⟩ := exists_between hy
  have hcbot : c ≠ ⊥ := ne_bot_of_gt ((upperBoxDim_nonneg hA).trans_lt hc1)
  have hctop : c ≠ ⊤ := by rintro rfl; exact not_top_lt hc2
  set s : ℝ := c.toReal with hsdef
  have hcs : c = ((s : ℝ) : EReal) := (EReal.coe_toReal hctop hcbot).symm
  have hst : s < t := by
    have h : ((s : ℝ) : EReal) < ((t : ℝ) : EReal) := by rw [← hcs, ← hyt]; exact hc2
    exact_mod_cast h
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hden : ((Real.log (((2⁻¹ : ℝ≥0)) : ℝ)⁻¹ : ℝ) : EReal) = ((Real.log 2 : ℝ) : EReal) := by
    norm_num
  have hgrow : coveringGrowth 2⁻¹ A < ((s * Real.log 2 : ℝ) : EReal) := by
    have hlt := hc1
    rw [upperBoxDim, upperBoxDimWith, hden, hcs,
      EReal.div_lt_iff (by exact_mod_cast hL) (EReal.coe_ne_top _)] at hlt
    rwa [EReal.coe_mul]
  set b : ℝ := Real.exp (s * Real.log 2) with hbdef
  have hb0 : 0 < b := Real.exp_pos _
  have hev : ∀ᶠ n : ℕ in atTop,
      (externalCoveringNumber ((2⁻¹ : ℝ≥0) ^ n) A : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ n) := by
    filter_upwards [eventually_le_exp hgrow] with n hn
    refine hn.trans (le_of_eq ?_)
    rw [show ((s * Real.log 2 : ℝ) : EReal) * (n : EReal)
        = ((s * Real.log 2 * n : ℝ) : EReal) by norm_cast, EReal.exp_coe, hbdef,
      ← Real.exp_nat_mul]
    ring_nf
  have hbd : b * ((2 : ℝ)⁻¹) ^ t < 1 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Real.log_inv, hbdef,
      ← Real.exp_add, Real.exp_lt_one_iff]
    nlinarith
  have hdle : dimH A ≤ ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) := by
    refine dimH_le_of_hausdorffMeasure_ne_top (d := Real.toNNReal t) ?_
    rw [Real.coe_toNNReal t ht0.le,
      hausdorffMeasure_eq_zero_of_covering_pow ht0 hb0 hbd hev]
    exact ENNReal.zero_ne_top
  calc (dimH A : EReal) ≤ (((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) : EReal) := by exact_mod_cast hdle
    _ = y := by
        rw [show ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t from rfl,
          EReal.coe_ennreal_ofReal, hyt, max_eq_left (by exact_mod_cast ht0.le)]

end Metric
