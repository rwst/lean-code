import Mathlib.Data.Nat.Defs
open Nat

/-- For `a > 1`, `a ^ b = a` iff `b = 1`. -/
lemma pow_eq_self_iff (a b : ℕ) (ha : 2 ≤ a) : a ^ b = a ↔ b = 1 :=
  (Nat.pow_right_injective ha).eq_iff' a.pow_one

