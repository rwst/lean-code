import Mathlib

/-- When `p` is prime and divides `x`, the p-order complement of `x / p` equals the p-order complement of `x`. -/
lemma ordCompl_p_div_p (x p : ℕ) (hp : p.Prime) (hx : p ∣ x) :
    ordCompl[p] (x / p) = ordCompl[p] x := by
  rcases hx with ⟨k, rfl⟩; rw [Nat.mul_comm p k, Nat.mul_div_left k hp.pos,
    ← Nat.ordCompl_self_pow_mul k 1 hp, pow_one, mul_comm]

/-- Special case of `ordCompl_p_div_p` for `p = 2`. -/
lemma ordCompl_two_div_two (x : ℕ) (hx : x % 2 = 0) : ordCompl[2] (x / 2) = ordCompl[2] x :=
  ordCompl_p_div_p x 2 Nat.prime_two (Nat.dvd_of_mod_eq_zero hx)

lemma ordCompl_two_pow_mul (k x : ℕ) : ordCompl[2] (2^k * x) = ordCompl[2] x :=
  Nat.ordCompl_self_pow_mul x k Nat.prime_two

/-- For prime `p` and `m` not divisible by `p`, the p-order complement of `p^k * m` is `m`. -/
lemma ordCompl_p_pow_mul_of_not_dvd (k m p : ℕ) (hp : p.Prime) (hm : ¬p ∣ m) :
    ordCompl[p] (p^k * m) = m := by
  rw [Nat.ordCompl_self_pow_mul m k hp, (Nat.ordCompl_eq_self_iff_zero_or_not_dvd m hp).2 (Or.inr hm)]

/-- For prime `p`, the p-order complement of `p^k * m` equals `m` if and only if `p` does not divide `m`
    or `m = 0`. -/
lemma ordCompl_p_pow_mul_iff (k m p : ℕ) (hp : p.Prime) :
    ordCompl[p] (p^k * m) = m ↔ m = 0 ∨ ¬p ∣ m := by
  rw [Nat.ordCompl_self_pow_mul m k hp, Nat.ordCompl_eq_self_iff_zero_or_not_dvd m hp]

/-- Special case of `ordCompl_p_pow_mul_of_not_dvd` for `p = 2`. -/
lemma ordCompl_two_mul_pow (k m : ℕ) (hm_odd : m % 2 = 1) : ordCompl[2] (2^k * m) = m := by
  refine ordCompl_p_pow_mul_of_not_dvd k m 2 Nat.prime_two ?_; intro h; omega
