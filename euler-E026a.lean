import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open Nat

lemma two_pow_isprimepower {m n : ℕ} (h1 : 0 < m) (h2 : 2 ^ m = n) : IsPrimePow n :=
  ⟨2, m, Nat.prime_two.prime, h1, h2⟩

lemma ne_iff_add_self {a b c : ℕ}: a ≠ b ↔ a + c ≠ b + c := by omega

lemma ne_self_pow (a n : ℕ) (ha : 1 < a) (hn : 1 < n): a ≠ a ^ n := by
  rw [ne_iff_lt_or_gt]
  exact Or.inl <| lt_self_pow ha hn

lemma simplify1 (a m' : ℕ) (ha : a > 0) :
    a ^ (2 * m' + 1) + 1 + (a + 1) * (a ^ (2 * m' + 2) - a ^ (2 * m' + 1)) =
    a ^ (2 * m' + 3) + 1 :=
  have h₁ (a b c d : ℕ): a + b + c + d - a = b + c + d := by omega
  have h₂ (a b : ℕ) (h : b ≤ a): 1 + a - b + b = 1 + a := by omega
  calc
    a ^ (2 * m' + 1) + 1 + (a + 1) * (a ^ (2 * m' + 2) - a ^ (2 * m' + 1)) =
      a ^ (2 * m' + 1) + 1 + a * (a ^ (2 * m' + 2) - a ^ (2 * m' + 1)) +
      (a ^ (2 * m' + 2) - a ^ (2 * m' + 1)) := by
      linarith
    _ = a ^ (2 * m' + 1) + 1 + a * (a ^ (2 * m' + 2) - a ^ (2 * m' + 1)) +
      a ^ (2 * m' + 2) - a ^ (2 * m' + 1) := by
      rw [← Nat.add_sub_assoc]
      exact pow_le_pow_of_le_right ha (le_succ (2 * m' + 1))
    _ = 1 + a * (a ^ (2 * m' + 2) - a ^ (2 * m' + 1)) + a ^ (2 * m' + 2) := by
      rw [h₁]
    _ = 1 + (a * a ^ (2 * m' + 2) - a * a ^ (2 * m' + 1)) + a ^ (2 * m' + 2) := by
      rw [Nat.mul_sub_left_distrib a (a ^ (2 * m' + 2)) (a ^ (2 * m' + 1))]
    _ = 1 + (a ^ (2 * m' + 2 + 1) - a ^ (2 * m' + 1 + 1)) + a ^ (2 * m' + 2) := by
      simp_rw [← Nat.pow_succ']
    _ = 1 + (a ^ (2 * m' + 3) - a ^ (2 * m' + 2)) + a ^ (2 * m' + 2) := by
      linarith
    _ = 1 + a ^ (2 * m' + 3) - a ^ (2 * m' + 2) + a ^ (2 * m' + 2) := by
      rw [← Nat.add_sub_assoc]
      exact pow_le_pow_of_le_right ha (le_succ (2 * m' + 2))
    _ = 1 + a ^ (2 * m' + 3) := by
      apply h₂ (a ^ (2 * m' + 3)) (a ^ (2 * m' + 2))
      exact pow_le_pow_of_le_right ha (le_succ (2 * m' + 2))
    _ = a ^ (2 * m' + 3) + 1 := by
      exact Nat.add_comm 1 (a ^ (2 * m' + 3))

-- "$a^{2m+1}+1$ can be divided by $a+1$" [Euler, E026]
-- Proof by induction
theorem H1 (a m : ℕ) (ha : a > 0) : (a + 1) ∣ a ^ (2 * m + 1) + 1 := by
  have h₃ (a m' : ℕ) : a ^ (2 * m' + 2 + 1) = a ^ (2 * m' + 3) := by ring_nf
  have hdvd (a m' : ℕ) : (a + 1) ∣ (a + 1) * (a ^ (2 * m' + 2) - a ^ (2 * m' + 1)) :=
    dvd_mul_right (a + 1) (a ^ (2 * m' + 2) - a ^ (2 * m' + 1))
  induction m with
  | zero =>
    exact Dvd.intro_left (Nat.pow a 0) rfl
  | succ m' ih =>
    rw [Nat.mul_succ, h₃ a m', ← simplify1 a m' ha]
    exact dvd_add ih (hdvd a m')

-- "$a^p+1$ divides $a^{p(2m+1)}+1$" [Euler, E026]
-- Substitute $a$ for $a^p$ in the above.
lemma H2 (a m p: ℕ) (ha : a > 0) : (a ^ p + 1) ∣ a ^ (p * (2 * m + 1)) + 1 := by
  rw [pow_mul a p (2 * m + 1)]
  exact H1 (a ^ p) m (pos_pow_of_pos p ha)

/- The odd part of `n > 0` is either 1, or is `∈ [1, n)`. -/
lemma ord_compl_eq_or_lt (n p : ℕ) (hn : 0 < n) :
    ord_compl[p] n = 1 ∨ (1 < ord_compl[p] n ∧ n ≥ ord_compl[p] n) := by
  have h (n m : ℕ) (hn1 : n ≤ m) (hn2 : 1 ≤ n) : n = 1 ∨ (1 < n ∧ m ≥ n) := by omega
  apply h (ord_compl[p] n)
  · apply ord_compl_le n
  · apply ord_compl_pos p (not_eq_zero_of_lt hn)

/- With respect to prime `p`, the odd part of `p ^ m` is 1. -/
lemma ord_compl_of_pow (m n p: ℕ) (hp : p.Prime) (hn : n = p ^ m) : ord_compl[p] n = 1 := by
  rw [hn, Prime.factorization_pow, Finsupp.single_eq_same]
  simp only [Prime.pos hp, ofNat_pos, pow_pos, Nat.div_self]
  exact hp

lemma ord_pow_of_compl (n p: ℕ) (hp : p.Prime) (hnop : ord_compl[p] n = 1)
    : ∃ m : ℕ, n = p ^ m := by
  have h : p ^ n.factorization p * (n / p ^ n.factorization p) = n := ord_proj_mul_ord_compl_eq_self n p
  use n.factorization p
  rw [hnop, mul_one] at h
  exact h.symm

lemma simplify2 (n : ℕ) (hn : n ≠ 0): (ord_proj[2] n) * (2 * ((ord_compl[2] n - 1) / 2) + 1) = n :=
  calc
    (ord_proj[2] n) * (2 * ((ord_compl[2] n - 1) / 2) + 1) =
        (ord_proj[2] n) * ((ord_compl[2] n - 1) + 1) := by
      rw [two_mul_div_two_of_even (n := (ord_compl[2] n - 1))]
      apply Nat.Odd.sub_odd _ (odd_iff.mpr (by rfl))
      exact odd_iff.mpr <| two_dvd_ne_zero.mp <| not_dvd_ord_compl prime_two hn
    _ = (ord_proj[2] n) * (ord_compl[2] n) := by
      have (n : ℕ) (hn : 1 ≤ n) (h : Odd n) : Even (n - 1) := by
        exact Nat.Odd.sub_odd h (odd_iff.mpr (by rfl))
      rw [Nat.sub_add_cancel <| zero_lt_of_lt <| ord_compl_pos 2 hn]
    _ = n := by
      rw [ord_proj_mul_ord_compl_eq_self]

-- "if any numbers of the form $a^n+1$ are prime, it is necessary,
--  that they be of the form $a^{2^m}+1$" [Euler, E026]
theorem H3 (a n : ℕ) (ha : 1 < a) (hn : 1 < n)
    (hP : Nat.Prime (a ^ n + 1)) : ∃ m : ℕ, n = 2 ^ m := by
  /- First we show that the goal `n = 2 ^ m` is equivalent to the statement
     "the odd part of `n` is 1", which is written in Lean using the `factorization` function. -/
  apply ord_pow_of_compl n 2 prime_two
  /- The goal is now to show that the odd part of `n` must be 1.
     The odd part of any number is either 1 (which is equivalent to being a power
     of two), or greater than one and less or equal `n`. This is hypothesis `h₁`
     which is proved by applying lemma `ord_compl_eq_or_lt`. -/
  have h₁ : ord_compl[2] n = 1 ∨ (1 < ord_compl[2] n ∧ n ≥ ord_compl[2] n) :=
    ord_compl_eq_or_lt n 2 (Nat.zero_lt_of_lt hn)
  /- If we can disprove the second proposition, then the first remains true in `h₁`,
     and `h₁` can simply be applied. For this logical argument we need the
     `true_or_false` lemma, which we apply to `h₁`. -/
  have true_or_false (A B : Prop) (hB : ¬ B) (hab : A ∨ B) : A := by simp_all only [or_false]
  apply true_or_false at h₁
  /- This opens the hypothesis `hB` as goal, which is the negation of the
     second proposition in `h₁`. -/
  case hB
  /- In this part we prove that setting `n` as of form `m₁ * (2 * m₂ + 1)`, `m₁, m₂ > 0`
     (the current goal) leads to a contradiction. However, first the goal is to be
     rewritten to match the lemma `H2` we proved earlier. -/
  · by_contra hB'
    rcases hB' with ⟨ h₂, _ ⟩
    apply Iff.mpr (Nat.not_prime_iff_exists_dvd_ne (by exact Prime.two_le hP))
    . use a ^ ord_proj[2] n + 1
      constructor
      . nth_rewrite 2 [← simplify2 n (not_eq_zero_of_lt hn)]
        apply H2 a (m := (ord_compl[2] n - 1) / 2) (p := ord_proj[2] n)
        exact zero_lt_of_lt ha
      . constructor
        . rw [add_left_ne_self]
          apply pow_ne_zero
          exact not_eq_zero_of_lt ha
        . rw [ne_eq, add_right_cancel_iff]
          rw [pow_right_inj (a := a) (m := ord_proj[2] n) (n := n)
            (zero_lt_of_lt ha) (Ne.symm (Nat.ne_of_lt ha))]
          rw [← ne_eq]
          rw [← mul_lt_mul_left (b := 1) (c := ord_compl[2] n)
            (a := ord_proj[2] n)] at h₂
          rw [← Nat.mul_comm (n / ord_proj[2] n) (ord_proj[2] n)] at h₂
          rw [Nat.div_mul_cancel, mul_one] at h₂
          apply Nat.ne_of_lt at h₂
          . exact h₂
          . exact ord_proj_dvd n 2
          . exact ord_proj_pos n 2
    . exact hP
  /- Having excluded the other case, only the possibility remains that `n` is a
    power of two. -/
  exact h₁
