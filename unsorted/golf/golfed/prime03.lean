lemma pepin_primality (n : ℕ) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (2 ^ (2 ^ n) + 1))) :
    (2 ^ (2 ^ n) + 1).Prime := by
  have := Fact.mk (succ_lt_succ (Nat.one_lt_pow (pow_ne_zero n two_ne_zero) one_lt_two))
  have key : 2 ^ n = 2 ^ n - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · rw [Nat.add_sub_cancel, key, pow_succ, pow_mul, ← pow_succ, ← key, h, neg_one_sq]
  · intro p hp1 hp2
    rw [Nat.add_sub_cancel, (Nat.prime_dvd_prime_iff_eq hp1 prime_two).mp (hp1.dvd_of_dvd_pow hp2),
        key, pow_succ, Nat.mul_div_cancel _ two_pos, ← pow_succ, ← key, h]
    exact ZMod.neg_one_ne_one

