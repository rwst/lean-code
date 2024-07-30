import Mathlib
open Nat

/-- For `a > 1`, `a ^ b = a` iff `b = 1`. -/
lemma pow_eq_self_iff (a b : ℕ) (ha : 1 < a) : b = 1 ↔ a ^ b = a := by
  constructor
  · intro h
    rw [h]
    exact pow_one a
  · intro h
    nth_rw 2 [Eq.symm (pow_one a)] at h
    rw [pow_right_inj (zero_lt_of_lt ha) (Ne.symm (Nat.ne_of_lt ha))] at h
    exact h

