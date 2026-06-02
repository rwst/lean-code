lemma pow_pow_add_primeFactors_one_lt {a n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ a ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 1) + 1 := by
  have : Fact (2 < p) := Fact.mk (lt_of_le_of_ne hp.two_le hp2.symm)
  have : Fact p.Prime := Fact.mk hp
  have ha1 : (a : ZMod p) ^ (2 ^ n) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (natCast_zmod_eq_zero_iff_dvd (a ^ (2 ^ n) + 1) p).mpr hpdvd
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero n two_ne_zero), zero_eq_neg] at ha1
    exact one_ne_zero ha1
  have ha : orderOf (a : ZMod p) = 2 ^ (n + 1) := by
    apply orderOf_eq_prime_pow
    · rw [ha1]
      exact ZMod.neg_one_ne_one
    · rw [pow_succ, pow_mul, ha1, neg_one_sq]
  simpa [ha, dvd_def, Nat.sub_eq_iff_eq_add hp.one_le, mul_comm] using orderOf_dvd_card_sub_one ha0

/-- Prime factors of `Fₙ = 2 ^ (2 ^ n) + 1`, `1 < n`, are of form `k * 2 ^ (n + 2) + 1`. -/
lemma fermat_primeFactors_one_lt (n p : ℕ) (hn : 1 < n) (hp : p.Prime)
    (hpdvd : p ∣ 2 ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  have : Fact p.Prime := Fact.mk hp
  have hp2 : p ≠ 2 := by
    exact ((even_pow.mpr ⟨even_two, pow_ne_zero n two_ne_zero⟩).add_one).ne_two_of_dvd_nat hpdvd
  have hp8 : p % 8 = 1 := by
    obtain ⟨k, rfl⟩ := pow_pow_add_primeFactors_one_lt hp hp2 hpdvd
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [add_assoc, pow_add, ← mul_assoc, ← mod_add_mod, mul_mod]
    norm_num
  obtain ⟨a, ha⟩ := (exists_sq_eq_two_iff hp2).mpr (Or.inl hp8)
  suffices h : p ∣ a.val ^ (2 ^ (n + 1)) + 1 by
    exact pow_pow_add_primeFactors_one_lt hp hp2 h
  rw [← natCast_zmod_eq_zero_iff_dvd, Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hpdvd ⊢
  rwa [ZMod.natCast_val, ZMod.cast_id, pow_succ', pow_mul, sq, ← ha]

/-- Prime factors of `Fₙ = 2 ^ (2 ^ n) + 1` are either 3, 5, or of form `k * 2 ^ (n + 2) + 1`. -/
lemma fermat_primeFactors (n p : ℕ) (hP : p.Prime)
    (hpdvd : p ∣ 2 ^ (2 ^ n) + 1) :
    p = 3 ∨ p = 5 ∨ ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  obtain h | ⟨h | h⟩ : n = 0 ∨ n = 1 ∨ 1 < n := by omega
  · left
    rw [h] at hpdvd
    exact (prime_dvd_prime_iff_eq hP prime_three).mp hpdvd
  · right; left
    rw [h] at hpdvd
    norm_num at hpdvd
    exact (prime_dvd_prime_iff_eq hP prime_five).mp hpdvd
  · right; right
    exact fermat_primeFactors_one_lt n p h hP hpdvd

