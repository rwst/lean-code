import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

theorem not_all_pow_pow_add_prime : ¬ ∀ n : ℕ, Nat.Prime (2 ^ (2 ^ n) + 1) := by
  intro h
  specialize h 5
  norm_num at h

