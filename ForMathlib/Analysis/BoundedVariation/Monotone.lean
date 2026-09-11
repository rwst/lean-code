/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# The variation of a monotone function on a closed interval

Mathlib knows that a monotone function has locally bounded variation
(`MonotoneOn.locallyBoundedVariationOn`), but not what its variation *is*.  On a closed
interval it is of course the total rise,

  `eVariationOn f (Icc a b) = ENNReal.ofReal (f b - f a)`,

because every admissible sum telescopes.  This file records that, its antitone mirror, and
the combined absolute-value form, for real-valued `f` on a linear order.

These are the atoms out of which the variation of a piecewise monotone function is assembled:
combined with `eVariationOn.sum'` they compute the variation of, say, a trigonometric
polynomial over a union of monotone pieces.

## Main results

* `eVariationOn.eq_ofReal_sub_of_monotoneOn`
* `eVariationOn.eq_ofReal_sub_of_antitoneOn`
* `eVariationOn.eq_ofReal_abs_sub`, the two combined
-/

open Set

namespace eVariationOn

variable {α : Type*} [LinearOrder α] {f : α → ℝ} {a b : α}

/-- The variation of a monotone real function on `[a, b]` is its total rise `f b - f a`. -/
theorem eq_ofReal_sub_of_monotoneOn (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (f b - f a) := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  refine le_antisymm ?_ ?_
  · simp only [eVariationOn, iSup_le_iff]
    rintro ⟨n, ⟨u, hu, ust⟩⟩
    have hstep : ∀ i : ℕ, 0 ≤ f (u (i + 1)) - f (u i) := fun i =>
      sub_nonneg.mpr (hf (ust i) (ust (i + 1)) (hu (Nat.le_succ i)))
    have hedist : ∀ i : ℕ, edist (f (u (i + 1))) (f (u i))
        = ENNReal.ofReal (f (u (i + 1)) - f (u i)) := by
      intro i
      rw [edist_dist, Real.dist_eq, abs_of_nonneg (hstep i)]
    simp only [hedist]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hstep i]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Finset.sum_range_sub fun i => f (u i)]
    have h1 : f (u n) ≤ f b := hf (ust n) hb (ust n).2
    have h2 : f a ≤ f (u 0) := hf ha (ust 0) (ust 0).1
    linarith
  · have h := edist_le f ha hb
    rwa [edist_dist, Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (hf ha hb hab))] at h

/-- The variation of an antitone real function on `[a, b]` is its total fall `f a - f b`. -/
theorem eq_ofReal_sub_of_antitoneOn (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (f a - f b) := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  refine le_antisymm ?_ ?_
  · simp only [eVariationOn, iSup_le_iff]
    rintro ⟨n, ⟨u, hu, ust⟩⟩
    have hstep : ∀ i : ℕ, 0 ≤ f (u i) - f (u (i + 1)) := fun i =>
      sub_nonneg.mpr (hf (ust i) (ust (i + 1)) (hu (Nat.le_succ i)))
    have hedist : ∀ i : ℕ, edist (f (u (i + 1))) (f (u i))
        = ENNReal.ofReal (-(f (u (i + 1)) - f (u i))) := by
      intro i
      rw [edist_dist, Real.dist_eq, abs_of_nonpos (by linarith [hstep i])]
    simp only [hedist, neg_sub]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hstep i]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ∑ i ∈ Finset.range n, (f (u i) - f (u (i + 1)))
        = -∑ i ∈ Finset.range n, (f (u (i + 1)) - f (u i)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_range_sub fun i => f (u i)]
    have h1 : f b ≤ f (u n) := hf (ust n) hb (ust n).2
    have h2 : f (u 0) ≤ f a := hf ha (ust 0) (ust 0).1
    linarith
  · have h := edist_le f ha hb
    rwa [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hf ha hb hab))] at h

/-- The variation of a monotone-or-antitone real function on `[a, b]` is `|f b - f a|`. -/
theorem eq_ofReal_abs_sub (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal |f b - f a| := by
  rcases hf with hf | hf
  · rw [eq_ofReal_sub_of_monotoneOn hab hf,
      abs_of_nonneg (sub_nonneg.mpr (hf (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab))]
  · rw [eq_ofReal_sub_of_antitoneOn hab hf,
      abs_of_nonpos (sub_nonpos.mpr (hf (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab)),
      neg_sub]

end eVariationOn
