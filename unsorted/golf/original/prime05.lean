lemma fermat_primeFactors (n p : ℕ) (hn : 1 < n) (hP : p.Prime) (hp' : p ≠ 2)
    (hpdvd : p ∣ 2 ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  haveI hp := Fact.mk hP
  have h₀ : 2 ^ (2 ^ n) = (-1 : ZMod p) := by
    have : 2 ^ (2 ^ n) + 1 = (0 : ZMod p) := by
      exact_mod_cast (ZMod.natCast_zmod_eq_zero_iff_dvd (2 ^ (2 ^ n) + 1) p).mpr hpdvd
    exact Eq.symm (neg_eq_of_add_eq_zero_left this)
  have h₁ : 2 ^ (2 ^ (n + 1)) = (1 : ZMod p) := by
    exact Mathlib.Tactic.Ring.pow_nat rfl h₀ neg_one_sq
  have h2ne0 : (0 : ZMod p) ≠ (2 : ZMod p) := by
    have h' := intCast_eq_intCast_iff_dvd_sub 0 2 p
    norm_cast at h'
    rw [ne_eq, h']
    have : Int.subNatNat 2 0 = 2 := rfl
    rw [this]
    norm_cast
    by_contra h''
    apply Nat.le_of_dvd at h''
    · have : 2 ≤ p := Prime.two_le hP
      omega
    · norm_num
  have h1neneg : (1 : ZMod p) ≠ (-1 : ZMod p) := by
    by_contra h'
    have h := (ZMod.neg_eq_self_iff (1 : ZMod p)).mp h'.symm
    rcases h with h | h
    · absurd h; exact one_ne_zero
    · absurd h
      rw [val_one p]
      exact Ne.symm hp'
  have h₂ : 2 ^ (n + 1) ∣ p - 1 := by
rwst marked this conversation as resolved.
    have : orderOf (2 : ZMod p) = 2 ^ (n + 1) := by
      apply orderOf_eq_prime_pow
      · rw [h₀, ← ne_eq]
        exact Ne.symm h1neneg
      · exact h₁
    rw [← this]
    apply ZMod.orderOf_dvd_card_sub_one h2ne0.symm
  have hpmod8 : p % 8 = 1 := by
    have : 8 ∣ p - 1 := by
      apply Nat.dvd_trans (a := 8) (b := 2 ^ (n + 1)) (c := p - 1)
      · use 2 ^ (n - 2)
        have : 8 = 2 ^ 3 := by norm_num
        rw [this, Eq.symm (Nat.pow_add 2 3 (n - 2)), pow_right_inj]
        · omega
        · linarith
        · linarith
      · exact h₂
    have : 1 ≤ p := NeZero.one_le
    omega
  have hsq : IsSquare (2 : ZMod p) :=
      (ZMod.exists_sq_eq_two_iff hp').mpr (Or.intro_left (p % 8 = 7) hpmod8)
  have hsqex : ∃ m : ZMod p, m ^ 2 = (2 : ZMod p) := by
    obtain ⟨c, hsq'⟩ := IsSquare.exists_sq (2 : ZMod p) hsq
    use c
    exact id (Eq.symm hsq')
  have hOrd_dvd (a : ZMod p) (ha : a ^ 2 = (2 : ZMod p)) : 2 ^ (n + 2) ∣ p - 1 := by
    have hOrd : orderOf (a : ZMod p) = 2 ^ (n + 2) := by
      have : a ^ (2 ^ (n + 2)) = (1 : ZMod p) := by
        have : 2 = 1 + 1 := rfl
        nth_rw 2 [this]
        rw [← add_assoc, Nat.pow_succ', pow_mul a 2]
        exact ha ▸ h₁
      apply orderOf_eq_prime_pow
      · rw [← ha] at h₀
        rw [Nat.pow_succ', pow_mul a 2, h₀]
        exact Ne.symm h1neneg
      · exact this
    rw [← hOrd]
    apply ZMod.orderOf_dvd_card_sub_one
    contrapose! ha
    rw [ha, ne_eq, zero_pow]
    · exact h2ne0
    · norm_num
  have : ∃ k : ℕ, p - 1 = k * 2 ^ (n + 2) := by
    apply exists_eq_mul_left_of_dvd
    obtain ⟨w, h⟩ := hsqex
    apply hOrd_dvd
    · exact h
  rcases this with ⟨k', h'⟩
  use k'
  rw [← h']
  omega

