import Mathlib

set_option autoImplicit false

theorem Nat.le_of_le_sub_one (hxb: x ≤ b - 1): x ≤ b := by
  apply LE.le.trans hxb (a := x) (c := b) (b := b - 1)
  exact sub_le b 1

theorem Nat.le_iff_eq_or_le_sub_one: x = b ∨ x ≤ b - 1 ↔ x ≤ b := by
  constructor
  · intro h
    rcases h with h | h
    · rw [le_iff_lt_or_eq]; exact Or.inr h
    · apply le_of_le_sub_one at h; exact h
  · intro h'
    rw [le_iff_lt_or_eq, or_comm] at h'
    rcases h' with h₁ | h₂
    · left; exact h₁
    · right; exact le_sub_one_of_lt h₂

