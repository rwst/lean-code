import Mathlib
open Real

example (a m n : ℚ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hab : a = sqrt m + sqrt n) :
    IsSquare m ∧ IsSquare n := by
  have h : √n = ((√m + √n)^2 + n - m) / (2 * (√m + √n)) := by
    by_cases hn : n = 0
    · simp_all
    by_cases hm : m = 0
    · field_simp [hm]
      ring_nf
      simp_all only [le_refl, Rat.cast_zero, sqrt_zero, zero_add,
        Rat.cast_nonneg, sq_sqrt]
    field_simp
    ring_nf
    simp_all only [Rat.cast_nonneg, sq_sqrt, add_add_sub_cancel]
    ring_nf
  rw [← hab] at h
  have hsqrule (x₁ x₂ : ℝ) (h: x₁ = x₂) : x₁ ^ 2 = x₂ ^ 2 :=
    congrFun (congrArg HPow.hPow h) 2
  have h₄ : n = ((a ^ 2 + n - m) / (2 * a)) ^ 2 := by
    apply hsqrule at h
    rw [sq_sqrt] at h
    norm_cast at h
    exact Rat.cast_nonneg.mpr hn
  have h₅ : IsSquare (((a ^ 2 + n - m) / (2 * a)) ^ 2) :=
      IsSquare_sq ((a ^ 2 + n - m) / (2 * a))
  rw [← h₄] at h₅
  constructor
  swap
  . exact h₅ /- This is the first statement: `IsSquare n`. -/
             /- Now solving for `m`. -/
  . have h₆ : a - sqrt n = sqrt m := sub_eq_iff_eq_add.mpr hab
    rw [h, sq] at h₆
    apply hsqrule at h₆
    rw [sq_sqrt (Rat.cast_nonneg.mpr hm)] at h₆
    norm_cast at h₆
    have h₈ : IsSquare ((a - (a * a + n - m) / (2 * a)) ^ 2) :=
      IsSquare_sq (a - (a * a + n - m) / (2 * a))
    rw [h₆] at h₈
    exact h₈


