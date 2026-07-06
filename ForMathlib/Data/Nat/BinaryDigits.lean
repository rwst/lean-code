/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Binary digit sums and bit runs

Bridge lemmas between `Nat.digits 2` (the binary digit list) and `Nat.testBit`
(bit access), absent from Mathlib:

* `Nat.testBit_eq_decide_div_mod` — `n.testBit i = decide (n / 2 ^ i % 2 = 1)`;
* `Nat.mod_two_pow_succ` — peeling the top bit off a remainder:
  `n % 2 ^ (i + 1) = 2 ^ i * (n.testBit i).toNat + n % 2 ^ i`;
* `Nat.mod_two_pow_eq_of_testBit_eq_false` — a run of zero bits collapses
  remainders: if bits `x ≤ i < y` of `n` are all `false`, then
  `n % 2 ^ y = n % 2 ^ x`;
* `Nat.sum_digits_two_eq_sum_testBit` — the binary digit sum as a Boolean
  count: `(Nat.digits 2 n).sum = ∑ i ∈ range k, (n.testBit i).toNat` whenever
  `n < 2 ^ k`.
-/

namespace Nat

/-- `testBit` as the parity of a shifted quotient. -/
lemma testBit_eq_decide_div_mod (n i : ℕ) :
    n.testBit i = decide (n / 2 ^ i % 2 = 1) := by
  have h : (n / 2 ^ i).testBit 0 = n.testBit (0 + i) := Nat.testBit_div_two_pow n 0
  rw [zero_add] at h
  rw [← h, Nat.testBit_zero]

/-- Peeling the top bit off a remainder:
`n % 2 ^ (i + 1) = 2 ^ i · bit_i(n) + n % 2 ^ i`. -/
lemma mod_two_pow_succ (n i : ℕ) :
    n % 2 ^ (i + 1) = 2 ^ i * (n.testBit i).toNat + n % 2 ^ i := by
  have h : n % (2 ^ i * 2) = n % 2 ^ i + 2 ^ i * (n / 2 ^ i % 2) := Nat.mod_mul
  have hbit : (n.testBit i).toNat = n / 2 ^ i % 2 := by
    rw [testBit_eq_decide_div_mod]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h2 | h2 <;> rw [h2] <;> simp
  rw [pow_succ, h, hbit]
  omega

/-- A run of zero bits in positions `[x, y)` collapses the remainders:
`n % 2 ^ y = n % 2 ^ x`. -/
lemma mod_two_pow_eq_of_testBit_eq_false {n x y : ℕ} (hxy : x ≤ y)
    (h : ∀ i, x ≤ i → i < y → n.testBit i = false) :
    n % 2 ^ y = n % 2 ^ x := by
  revert h
  induction y, hxy using Nat.le_induction with
  | base => intro _; rfl
  | succ y hxy ih =>
    intro h
    have hy : n.testBit y = false := h y hxy (Nat.lt_succ_self y)
    rw [mod_two_pow_succ, hy]
    simpa using ih (fun i hxi hiy => h i hxi (Nat.lt_succ_of_lt hiy))

/-- The binary digit sum as a count of set bits: for any `k` with `n < 2 ^ k`,
`(Nat.digits 2 n).sum = ∑ i < k, bit_i(n)`. -/
lemma sum_digits_two_eq_sum_testBit {n k : ℕ} (h : n < 2 ^ k) :
    (Nat.digits 2 n).sum = ∑ i ∈ Finset.range k, (n.testBit i).toNat := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst hn
    simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) hn]
      have hdiv : n / 2 < 2 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        rw [pow_succ] at h
        exact h
      have h0 : (n.testBit 0).toNat = n % 2 := by
        rw [Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> rw [h2] <;> simp
      have hsucc : ∀ i, n.testBit (i + 1) = (n / 2).testBit i := fun i =>
        Nat.testBit_add_one n i
      rw [List.sum_cons, ih hdiv, Finset.sum_range_succ']
      simp only [hsucc, h0]
      omega

end Nat
