import Mathlib.Data.Nat.Prime.Basic

open Nat

theorem prime_of_pow_sub_one_prime (a n : ℕ) (ha : 1 < a) (hn : 1 < n) (hP : (a ^ n - 1).Prime) :
    a = 2 ∧ n.Prime := by
  by_contra h₀
  have h₁ : a ≠ 2 ∨ ¬ n.Prime := by
    exact (Decidable.not_and_iff_or_not (a = 2) (Nat.Prime n)).mp h₀
  have h₂ (h : a ≠ 2) : ¬ (a ^ n - 1).Prime := by
    by_contra h₅
    have : (a - 1) ∣ a ^ n - 1 := by
      nth_rw 2 [← Nat.one_pow n]
      apply nat_sub_dvd_pow_sub_pow a 1 n
    have : ¬ (a ^ n - 1).Prime := by
      apply not_prime_of_dvd_of_ne this
      · omega
      · have : a ≠ a ^ n := Nat.ne_of_lt (lt_self_pow ha hn)
        omega
    contradiction
  have h₃ (hnP : ¬ n.Prime) : ¬ (a ^ n - 1).Prime := by
    have h₄ := hnP
    have minFac_lt : n.minFac < n := (not_prime_iff_minFac_lt hn).mp hnP
    have lt_minFac : 1 < n.minFac := by
      have : n.minFac = 0 ∨ n.minFac = 1 ∨ 1 < n.minFac := by omega
      rcases this with h | _ | h
      · by_contra; exact (not_eq_zero_of_lt (minFac_pos n)) h
      · have : ¬n = 1 := Nat.ne_of_lt' hn
        by_contra; simp_all only [minFac_eq_one_iff]
      · exact h
    apply (not_prime_iff_exists_dvd_ne (n := a ^ n - 1) (Prime.two_le hP)).mpr
    apply (not_prime_iff_exists_dvd_ne (n := n) hn).mp at h₄
    use a ^ minFac n - 1
    have h₅ : a < a ^ n.minFac := lt_self_pow ha lt_minFac
    have h₆ (x m n : ℕ) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by
      nth_rw 2 [← one_pow n]
      rw [pow_mul x m n]
      apply nat_sub_dvd_pow_sub_pow (x ^ m) 1
    constructor
    · match exists_eq_mul_left_of_dvd (minFac_dvd n) with
      | ⟨m, hm⟩ =>
          nth_rw 2 [hm]
          rw [mul_comm]
          exact h₆ a n.minFac m
    · constructor
      · rw [ne_eq, pred_eq_succ_iff, zero_add]
        omega
      · rw [ne_eq]
        have : ¬ a ^ n.minFac = a ^ n := Nat.ne_of_lt <| pow_lt_pow_right ha minFac_lt
        have : 0 < a ^ n.minFac := zero_lt_of_lt h₅
        have : 0 < a ^ n := by exact zero_lt_of_lt <| lt_self_pow ha hn
        omega
  rcases h₁ with h₁' | h₁'
  · apply h₂ at h₁'
    contradiction
  · apply h₃ at h₁'
    contradiction

