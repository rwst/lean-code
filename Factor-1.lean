import Mathlib

lemma ordCompl_two_div_two (x : ℕ) (hx : x % 2 = 0) : ordCompl[2] (x / 2) = ordCompl[2] x := by
  have : x = 2^1 * (x / 2) := by omega
  conv_rhs => rw [this, Nat.ordCompl_self_pow_mul _ _ Nat.prime_two]

lemma ordCompl_two_pow_mul (k x : ℕ) :
    ordCompl[2] (2^k * x) = ordCompl[2] x :=
  Nat.ordCompl_self_pow_mul x k Nat.prime_two

lemma ordCompl_two_mul_pow (k m : ℕ) (hm_odd : m % 2 = 1) :
    ordCompl[2] (2^k * m) = m := by
  rw [Nat.ordCompl_self_pow_mul _ _ Nat.prime_two]
  exact (Nat.ordCompl_eq_self_iff_zero_or_not_dvd m Nat.prime_two).mpr (Or.inr (by omega))
