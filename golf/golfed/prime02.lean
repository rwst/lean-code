import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic

open Nat

theorem pow_of_pow_add_prime {a n : ℕ} (ha : 1 < a) (hn : n ≠ 0) (hP : (a ^ n + 1).Prime) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  have h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow, hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne', add_left_inj, pow_eq_self_iff ha] at h
  rw [h, mul_one]

