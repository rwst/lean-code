import Mathlib.Tactic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Nat.Factorization.Basic

namespace CollatzMapBasics

-- 2^k mod 3 is 1 if k is even (and k > 0), 2 if k is odd
lemma pow_two_mod_three (k : ℕ) : 2^k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with | zero => rfl | succ k ih =>
  rw [Nat.pow_succ, Nat.mul_mod, ih]
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1 <;> simp [*] at * <;> omega

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

lemma exists_predecessor_of_odd (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) :
  ∃ x k : ℕ, x % 2 = 1 ∧ (3 * x + 1) = 2^k * y := by
  obtain h | h : y % 3 = 1 ∨ y % 3 = 2 := by omega
  · exact ⟨(4 * y - 1) / 3, 2, by omega, by omega⟩
  · exact ⟨(2 * y - 1) / 3, 1, by omega, by omega⟩

/--
If `y` is a multiple of 3, it implies there is no number `n`
(and shift `k`) such that performing a `3n+1` step and `k` divisions reaches `y`.
-/
lemma no_odd_predecessor_for_div3 (y : ℕ) (h_div3 : y % 3 = 0) :
  ∀ n k : ℕ, 3 * n + 1 ≠ y * 2^k := by
  intro n k h
  have := congrArg (· % 3) h
  simp [Nat.add_mod, Nat.mul_mod, h_div3] at this

/-- For y ≡ 1 (mod 6), there exists x > 1 odd such that 3x+1 = 4y -/
lemma exists_predecessor_gt_one_mod1 (y : ℕ) (hy_mod6 : y % 6 = 1) (hy_gt : y > 1) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^2 * y := by
  use (4 * y - 1) / 3
  have : 3 * ((4 * y - 1) / 3) = 4 * y - 1 := Nat.mul_div_cancel' (by omega)
  refine ⟨by omega, by omega, by omega⟩

/-- For y ≡ 5 (mod 6), there exists x > 1 odd such that 3x+1 = 2y -/
lemma exists_predecessor_gt_one_mod5 (y : ℕ) (hy_mod6 : y % 6 = 5) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^1 * y := by
  use (2 * y - 1) / 3
  have : 3 * ((2 * y - 1) / 3) = 2 * y - 1 := Nat.mul_div_cancel' (by omega)
  refine ⟨by omega, by omega, by omega⟩

lemma parity_of_mod_pow_succ {k m n : ℕ} (h : m % 2 ^ (k + 1) = n % 2 ^ (k + 1)) :
    m % 2 = n % 2 := by
  have h1 : m % 2 ^ (k + 1) % 2 = m % 2 :=
    Nat.mod_mod_of_dvd m (dvd_pow_self 2 (Nat.succ_ne_zero k))
  have h2 : n % 2 ^ (k + 1) % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (dvd_pow_self 2 (Nat.succ_ne_zero k))
  omega

lemma int_dvd_sub_of_mod_eq {a b c : ℕ} (h : a % c = b % c) :
    (c : ℤ) ∣ ((a : ℤ) - (b : ℤ)) :=
  Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (by exact_mod_cast h))

lemma nat_mod_eq_of_int_dvd_sub {a b c : ℕ} (h : (c : ℤ) ∣ ((a : ℤ) - (b : ℤ))) :
    a % c = b % c := by
  exact_mod_cast Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp h)

lemma coprime_pow_three_pow_two (s k : ℕ) : Nat.Coprime (3 ^ s) (2 ^ k) := by
  apply Nat.Coprime.pow; decide

/-- `X n` is `(1 - (-1)^n) / 2`, i.e., 0 when `n` is even and 1 when `n` is odd. -/
def X (n : ℕ) : ℕ := ((1 - (-1 : ℤ)^n) / 2).toNat

lemma X_even {n : ℕ} (h : n % 2 = 0) : X n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  simp [X, pow_mul]

lemma X_odd {n : ℕ} (h : n % 2 = 1) : X n = 1 := by
  obtain ⟨k, hk⟩ := Nat.odd_iff.mpr h
  subst hk
  simp [X, pow_succ, pow_mul]

lemma X_eq_mod (n : ℕ) : X n = n % 2 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [X_even (by omega)]; omega
  · rw [X_odd (by omega)]; omega

lemma X_congr {m n : ℕ} (h : m % 2 = n % 2) : X m = X n := by
  rw [X_eq_mod, X_eq_mod, h]
