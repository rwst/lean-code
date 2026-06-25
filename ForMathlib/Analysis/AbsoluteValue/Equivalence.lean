/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence

@[expose] public section
/-!
# Equivalence of real absolute values via the closed unit ball

Two real-valued absolute values on a field are equivalent exactly when they have the same closed
unit ball `{x | v x ≤ 1}`. This is the `≤ 1` companion of `AbsoluteValue.isEquiv_iff_lt_one_iff`.
As a consequence, two equivalent absolute values that agree at a single point of absolute value
different from `0` and `1` are equal — the shared value pins the scaling exponent of the equivalence
to `1`.

## Main statements

* `AbsoluteValue.isEquiv_iff_le_one_iff`: `f.IsEquiv g ↔ ∀ x, f x ≤ 1 ↔ g x ≤ 1`.
* `AbsoluteValue.IsEquiv.eq_of_apply_eq`: equivalent absolute values agreeing at a point `a` with
  `a ≠ 0` and `f a ≠ 1` are equal.
-/

namespace AbsoluteValue

variable {F : Type*} [Field F]

/-- **Two real absolute values on a field are equivalent iff they share the same closed unit ball.**
The `≤ 1` companion of `AbsoluteValue.isEquiv_iff_lt_one_iff`. -/
theorem isEquiv_iff_le_one_iff {f g : AbsoluteValue F ℝ} :
    f.IsEquiv g ↔ ∀ x, f x ≤ 1 ↔ g x ≤ 1 := by
  refine ⟨fun h _ => h.le_one_iff, fun H a b => ?_⟩
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [map_zero, AbsoluteValue.nonpos_iff]
  · rw [← div_le_one (f.pos hb), ← map_div₀, H, map_div₀, div_le_one (g.pos hb)]

/-- **Equivalent absolute values that agree at one nontrivial point are equal.** If `f` and `g` are
equivalent and `f a = g a` with `a ≠ 0` and `f a ≠ 1`, then `f = g`: writing `g = f ^ c` for the
equivalence exponent `c > 0`, the shared value at `a` forces `c = 1`. -/
theorem IsEquiv.eq_of_apply_eq {f g : AbsoluteValue F ℝ} (h : f.IsEquiv g) {a : F}
    (ha0 : a ≠ 0) (ha1 : f a ≠ 1) (hfa : f a = g a) : f = g := by
  obtain ⟨c, _, hceq⟩ := isEquiv_iff_exists_rpow_eq.mp h
  have hc1 : c = 1 := by
    have h2 := congrFun hceq a
    rw [← hfa] at h2
    exact (Real.rpow_right_inj (x := f a) (f.pos ha0) ha1).mp (by rw [h2, Real.rpow_one])
  ext x
  have hx := congrFun hceq x
  rwa [hc1, Real.rpow_one] at hx

end AbsoluteValue
