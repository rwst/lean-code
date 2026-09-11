/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

/-!
# The mass distribution principle

If a set `A` carries a nonzero measure `μ` satisfying a **Frostman condition**

`μ s ≤ C · (diam s)ᵈ`  for every set `s` of small diameter,

then `dim_H A ≥ d`.  This is the standard — and essentially the only — way to bound a Hausdorff
dimension from below: an arbitrary cover `A ⊆ ⋃ sᵢ` by small sets satisfies
`0 < μ A ≤ ∑ μ sᵢ ≤ C ∑ (diam sᵢ)ᵈ`, so no cover can make the `d`-sum small.

Mathlib already contains the sharp form of that argument,
`MeasureTheory.Measure.le_hausdorffMeasure`, which asks for the Frostman condition with
`C = 1`.  In practice a constant is unavoidable, and the
only thing needed to reinstate it is to apply the sharp form to `C⁻¹ • μ`.  That is all this file
does, plus the translation into `dimH`.

## Main results

* `MeasureTheory.Measure.smul_le_hausdorffMeasure_of_frostman` — `C⁻¹ • μ ≤ μH[d]`.
* `MeasureTheory.Measure.le_dimH_of_frostman` — `ENNReal.ofReal d ≤ dimH A` when `μ A ≠ 0`.

## References

* K. Falconer, *Fractal Geometry*, Ch. 4.1 ("mass distribution principle").
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Ch. 8.
-/

open Metric Set
open scoped ENNReal NNReal MeasureTheory

namespace MeasureTheory.Measure

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The mass distribution principle**, measure form: a Frostman condition with constant `C`
bounds `C⁻¹ • μ` by the `d`-dimensional Hausdorff measure.  This is
`MeasureTheory.Measure.le_hausdorffMeasure` with the constant divided out. -/
theorem smul_le_hausdorffMeasure_of_frostman (μ : Measure X) {d : ℝ} {C ε : ℝ≥0∞}
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤) (hε : 0 < ε)
    (h : ∀ s : Set X, ediam s ≤ ε → μ s ≤ C * ediam s ^ d) :
    C⁻¹ • μ ≤ μH[d] := by
  refine le_hausdorffMeasure d _ ε hε fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  calc C⁻¹ * μ s ≤ C⁻¹ * (C * ediam s ^ d) := by gcongr; exact h s hs
    _ = ediam s ^ d := by rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, one_mul]

/-- **The mass distribution principle.**  A set carrying a nonzero measure that spreads its mass
no faster than `C · rᵈ` on sets of diameter `r` has Hausdorff dimension at least `d`.

The hypothesis is on *all* subsets of small diameter, not only the measurable ones — which is
what an arbitrary cover produces — but for a Borel measure it is enough to verify it on closed
balls, every set of diameter `r` being contained in one of radius `r`. -/
theorem le_dimH_of_frostman (μ : Measure X) {A : Set X} {d : ℝ} {C ε : ℝ≥0∞}
    (hd : 0 ≤ d) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤) (hε : 0 < ε)
    (h : ∀ s : Set X, ediam s ≤ ε → μ s ≤ C * ediam s ^ d) (hA : μ A ≠ 0) :
    ENNReal.ofReal d ≤ dimH A := by
  have hne : μH[d] A ≠ 0 := by
    intro h0
    refine hA ?_
    have hle := Measure.le_iff'.mp (smul_le_hausdorffMeasure_of_frostman μ hC0 hCtop hε h) A
    rw [h0, Measure.smul_apply, smul_eq_mul, le_zero_iff, mul_eq_zero] at hle
    exact hle.resolve_left (ENNReal.inv_ne_zero.mpr hCtop)
  have hd' : ((Real.toNNReal d : ℝ≥0) : ℝ) = d := Real.coe_toNNReal d hd
  have := le_dimH_of_hausdorffMeasure_ne_zero (s := A) (d := Real.toNNReal d) (by rwa [hd'])
  rwa [show ((Real.toNNReal d : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal d from rfl] at this

end MeasureTheory.Measure
