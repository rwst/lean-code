lemma pepin_primality (n : ℕ) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (2 ^ (2 ^ n) + 1))) :
    (2 ^ (2 ^ n) + 1).Prime := by
  have hneg1ne1: (-1 : ZMod (2 ^ (2 ^ n) + 1)) ≠ (1 : ZMod (2 ^ (2 ^ n) + 1)) := by
    by_contra h'
    let h := (ZMod.neg_eq_self_iff (1 : ZMod (2 ^ (2 ^ n) + 1))).mp h'
    rcases h with h | h
    · absurd h
      rw [Fin.one_eq_zero_iff, ← ne_eq, succ_ne_succ]
      exact NeZero.ne (2 ^ 2 ^ n)
    · absurd h
      have : Fact (1 < 2 ^ (2 ^ n) + 1) := by
        simp only [lt_add_iff_pos_left, ofNat_pos, pow_pos]
        exact { out := trivial }
      rw [val_one]
      norm_num
      simp only [reduceEqDiff]
      rw [pow_eq_one_iff (x := 2) (n := 2 ^ n)]
      · exact succ_succ_ne_one 0
      · exact Ne.symm (NeZero.ne' (2 ^ n))
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · norm_num
    apply Mathlib.Tactic.Ring.pow_nat _ h neg_one_sq
    rw [mul_comm, ← Nat.pow_add' 2 (2 ^ n - 1) 1]
    norm_num
    rw [Nat.sub_add_cancel Nat.one_le_two_pow]
  · norm_num
    intro p H' H''
    rw [(Nat.prime_dvd_prime_iff_eq H' prime_two).mp ((Nat.Prime.dvd_of_dvd_pow H') H'')]
    have : 2 ^ (2 ^ n) / 2 = 2 ^ (2 ^ n - 1) := by
      rw [← Nat.mul_right_inj (a := 2), ← Nat.pow_add' 2 (2 ^ n - 1) 1,
        mul_comm, Nat.div_mul_cancel]
      · norm_num
        rw [Nat.sub_add_cancel Nat.one_le_two_pow]
      · exact dvd_pow_self 2 (Ne.symm (NeZero.ne' (2 ^ n)))
      · exact Ne.symm (zero_ne_add_one 1)
    rw [this, h]
    exact hneg1ne1
