/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database
import CITED.DimitrovHowe
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.IntervalCases

/-!
# The sparse side of the digit-block program: powers of 3 with `s₂ ≤ 3` (B5a, B5b)

Milestones **M-2 = Theorem B5a** and **M-4 = Theorem B5b** of the digit-block
plan ([A4+] §3.4), the *upper-bound-side* complement of Stewart's theorem
(`TH/StewartDigits.lean`, rung M3½): the full classification of the powers of `3`
whose binary expansion is *sparse*.

  `s₂(3^m) ≤ 2  ⟺  m ∈ {0, 1, 2}`   (`digitSum_three_pow_le_two`, **B5a**),
  `s₂(3^m) = 3  ⟺  m = 4`            (`digitSum_three_pow_eq_three`, **B5b**),

with the exact value split of B5a

  `s₂(3^m) = 1 ⟺ m = 0`   and   `s₂(3^m) = 2 ⟺ m ∈ {1, 2}`.

Here `s₂(n) := (Nat.digits 2 n).sum` is the binary digit sum, exactly the
convention of `TH/StewartDigits.lean`.  Sanity: `3^0 = 1₂`, `3^1 = 11₂`,
`3^2 = 1001₂` (all `s₂ ≤ 2`), while `3^3 = 11011₂` (`s₂ = 4`) and
`3^4 = 1010001₂` (`s₂ = 3`) already break the bound — the two witnesses that
calibrate the lower bounds of B1–B3.

## Proof (elementary, no Baker — the plan's warm-up file)

The digit sum of an odd number `n` satisfies `s₂(n) = 1 + s₂(n / 2)` (peeling
the least significant bit).  So `s₂(3^m) ≤ 2` forces `s₂(3^m / 2) ≤ 1`, and a
number with binary digit sum `≤ 1` is `0` or a power of `2` (`dsle1`, via the
`s₂ = 0 ⟺ n = 0` base case `dse0`).  Hence

  `3^m = 1`   (⟹ `m = 0`)   or   `3^m = 2^a + 1`   for some `a ≥ 1`.

The Diophantine core `three_pow_ne_two_pow_succ` rules out the second equation
for `m ≥ 3`, elementarily:

* **`m` odd.**  `3^m ≡ 3 (mod 8)` while `m ≥ 3` gives `2^a = 3^m − 1 ≥ 26`,
  so `a ≥ 3` and `8 ∣ 2^a`, forcing `3^m ≡ 1 (mod 8)` — contradiction.
* **`m` even**, `m = 2k`, `k ≥ 2`.  Then
  `2^a = 3^{2k} − 1 = (3^k − 1)(3^k + 1)`, and each factor divides the prime
  power `2^a`, so `3^k − 1 = 2^s`, `3^k + 1 = 2^t`.  Subtracting,
  `2^t − 2^s = 2`, whence `2^s ∣ 2` and `3^k − 1 = 2^s ≤ 2 < 8 ≤ 3^k − 1`
  (as `k ≥ 2`) — contradiction.

This is the lifting-the-exponent content of [A4+] §3.4 in self-contained
`mod 8` + prime-power-divisor form.  Axiom footprint: **std3** (no [BW93]).

## B5b: `s₂ = 3` (on the cited Dimitrov–Howe result)

The next sparse case is genuinely harder.  `s₂(3^m) = 3` is, by oddness and the
same bit-peeling, equivalent to `3^m = 2^a + 2^b + 1` with `1 ≤ b < a`
(`digitSum_two_eq_two`, extending the `s₂ ≤ 1` helper to `s₂ = 2`).  The
resulting exponential Diophantine equation has the unique solution
`3^4 = 2^6 + 2^4 + 1 = 81` — this is the `n = 3` case of **Dimitrov–Howe 2023**
([DH23], §1), proved there by an elementary but *computational* congruence
argument (moduli `5440` and `2^7·5·17·257`, Magma enumeration).  That
Diophantine core is recorded as the cited axiom
`DH.three_pow_three_binary_digits` (`CITED/DimitrovHowe.lean`); B5b
(`digitSum_three_pow_eq_three`) is the digit-sum characterization proved from it.
So B5b's footprint is **std3 + [DH23]** (a single cited axiom), whereas B5a is
axiom-free std3.

## Contents

* `digitSum_three_pow_le_two` — **Theorem B5a**: `s₂(3^m) ≤ 2 ⟺ m ≤ 2`.
* `digitSum_three_pow_eq_one` — the `s₂ = 1` slice: `⟺ m = 0`.
* `digitSum_three_pow_eq_two` — the `s₂ = 2` slice: `⟺ m = 1 ∨ m = 2`.
* `digitSum_three_pow_eq_three` — **Theorem B5b**: `s₂(3^m) = 3 ⟺ m = 4`
  (on the cited [DH23] axiom).
* `digitSum_three_pow_three`, `digitSum_three_pow_four` — the calibrating
  witnesses `s₂(27) = 4`, `s₂(81) = 3`.

## References

* [Ste80] Stewart, C. L. *On the representation of an integer in two different
  bases.* J. reine angew. Math. **319** (1980), 63–72.  (The lower-bound
  anchor of the digit program; B5a is its sparse-side complement.)
* [DH23] Dimitrov, Howe. *Powers of 3 with few nonzero bits and a conjecture of
  Erdős.* arXiv:2105.06440 (2023).  (The `s₂ = 3` classification B5b; B5a is the
  elementary `s₂ ≤ 2` precursor of their equation (1).)
* [A4+] `plan-A4+.html` (this repository, 2026-07): §3.4 (B5a), §5.2 (this
  file), §6 (milestone M-2).
-/

namespace TH

/-! ## Digit-sum bookkeeping: sparse numbers are powers of two -/

/-- A number with binary digit sum `0` is `0`. -/
private lemma digitSum_two_eq_zero {n : ℕ} (h : (Nat.digits 2 n).sum = 0) : n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · exfalso
      rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) hn, List.sum_cons] at h
      have hdm := Nat.div_add_mod n 2
      have hlt : n / 2 < n := Nat.div_lt_self hn (by norm_num)
      have h2 : (Nat.digits 2 (n / 2)).sum = 0 := by omega
      have := ih (n / 2) hlt h2
      omega

/-- A number with binary digit sum `≤ 1` is `0` or a power of `2`. -/
private lemma digitSum_two_le_one {n : ℕ} (h : (Nat.digits 2 n).sum ≤ 1) :
    n = 0 ∨ ∃ b, n = 2 ^ b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl rfl
    · right
      rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) hn, List.sum_cons] at h
      have hdm := Nat.div_add_mod n 2
      have hlt : n / 2 < n := Nat.div_lt_self hn (by norm_num)
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · -- `n` even: `n = 2·(n/2)`, and `n/2` is a power of `2`
        rw [h2, zero_add] at h
        rcases ih (n / 2) hlt h with hz | ⟨b, hb⟩
        · exfalso; omega
        · exact ⟨b + 1, by rw [pow_succ]; omega⟩
      · -- `n` odd: `s₂(n/2) = 0`, so `n/2 = 0` and `n = 1 = 2^0`
        rw [h2] at h
        have h0 : (Nat.digits 2 (n / 2)).sum = 0 := by omega
        have := digitSum_two_eq_zero h0
        exact ⟨0, by omega⟩

/-- A number with binary digit sum `2` is a sum of two distinct powers of `2`. -/
private lemma digitSum_two_eq_two {n : ℕ} (h : (Nat.digits 2 n).sum = 2) :
    ∃ c d, c < d ∧ n = 2 ^ c + 2 ^ d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · simp at h
      · exact hp
    rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) hn, List.sum_cons] at h
    have hdm := Nat.div_add_mod n 2
    have hlt : n / 2 < n := Nat.div_lt_self hn (by norm_num)
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · -- `n` even: `n/2` still has digit sum `2`
      rw [h2, zero_add] at h
      obtain ⟨c, d, hcd, hq⟩ := ih (n / 2) hlt h
      exact ⟨c + 1, d + 1, by omega, by rw [pow_succ, pow_succ]; omega⟩
    · -- `n` odd: `s₂(n/2) = 1`, a power of `2`, so `n = 2^0 + 2^{b+1}`
      rw [h2] at h
      have h1 : (Nat.digits 2 (n / 2)).sum ≤ 1 := by omega
      rcases digitSum_two_le_one h1 with hz | ⟨b, hb⟩
      · rw [hz] at h; simp at h
      · exact ⟨0, b + 1, by omega, by rw [pow_succ]; simp; omega⟩

/-! ## The Diophantine core: `3^m = 2^a + 1` needs `m ≤ 2` -/

/-- **The sparse-side Diophantine obstruction** ([A4+] §3.4, the
lifting-the-exponent content in `mod 8` + prime-power form): the equation
`3^m = 2^a + 1` has no solution with `m ≥ 3`.

For `m` odd this is `mod 8` (`3^m ≡ 3` but `2^a ≡ 0` once `a ≥ 3`); for `m = 2k`
even it is the factorization `2^a = (3^k − 1)(3^k + 1)` of a prime power, whose
two factors `2^s, 2^t` differ by `2`, forcing `2^s ∣ 2` against `3^k − 1 ≥ 8`. -/
private lemma three_pow_ne_two_pow_succ {m a : ℕ} (h : 3 ^ m = 2 ^ a + 1)
    (hm : 3 ≤ m) : False := by
  have h27 : (27 : ℕ) ≤ 3 ^ m := by
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  -- `2^a = 3^m − 1 ≥ 26`, so `a ≥ 3` and `8 ∣ 2^a`
  have ha3 : 3 ≤ a := by
    by_contra ha; push Not at ha; interval_cases a <;> omega
  have hdvd8 : (8 : ℕ) ∣ 2 ^ a := by
    have h2 : (2 : ℕ) ^ 3 ∣ 2 ^ a := pow_dvd_pow 2 ha3
    simpa using h2
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨j, hj⟩
  · -- `m = 2k`, `k ≥ 2`: factor `2^a = (3^k − 1)(3^k + 1)`
    have hk2 : m = 2 * k := by omega
    have hk_ge : 2 ≤ k := by omega
    set x : ℕ := 3 ^ k with hxdef
    have hx9 : 9 ≤ x := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk_ge
    have hxx : x * x = 2 ^ a + 1 := by
      rw [hxdef, ← pow_add, ← two_mul, ← hk2]; exact h
    have hfact : 2 ^ a = (x + 1) * (x - 1) := by
      have hsq : x ^ 2 - 1 ^ 2 = (x + 1) * (x - 1) := Nat.sq_sub_sq x 1
      have hx2 : x ^ 2 = x * x := by ring
      omega
    -- each factor divides the prime power `2^a`, hence is a power of `2`
    have hd1 : (x - 1) ∣ 2 ^ a := ⟨x + 1, by rw [hfact]; ring⟩
    have hd2 : (x + 1) ∣ 2 ^ a := ⟨x - 1, hfact⟩
    obtain ⟨s, _, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
    obtain ⟨t, _, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    have hst : s ≤ t := by
      have hle : (2 : ℕ) ^ s ≤ 2 ^ t := by rw [← hs, ← ht]; omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    -- `2^t − 2^s = 2`, so `2^s ∣ 2`, but `3^k − 1 = 2^s ≥ 8`
    have hsub : (2 : ℕ) ^ t - 2 ^ s = 2 := by omega
    have hdvd2 : (2 : ℕ) ^ s ∣ 2 := by
      have hd := Nat.dvd_sub (pow_dvd_pow 2 hst) (dvd_refl ((2 : ℕ) ^ s))
      rwa [hsub] at hd
    have hle2 : (2 : ℕ) ^ s ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  · -- `m` odd: `3^m ≡ 3 (mod 8)`, contradicting `8 ∣ 2^a = 3^m − 1`
    have hmod : 3 ^ m % 8 = 3 := by
      rw [hj, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    rw [h] at hmod
    obtain ⟨c, hc⟩ := hdvd8
    rw [hc] at hmod
    omega

/-! ## Theorem B5a and its value split -/

/-- **Theorem B5a** ([A4+] §3.4; the sparse-side complement of Stewart's
theorem): the powers of `3` with binary digit sum at most `2` are exactly
`3^0, 3^1, 3^2`:

  `s₂(3^m) ≤ 2  ⟺  m ≤ 2`   (i.e. `m ∈ {0, 1, 2}`).

Elementary — `s₂(3^m) ≤ 2` forces `3^m = 1` or `3^m = 2^a + 1`, and the latter
needs `m ≤ 2` by `three_pow_ne_two_pow_succ`.  Footprint **std3** (no [BW93]). -/
@[category research solved, AMS 11, ref "Ste80", group "three_pow_digit_blocks"]
theorem digitSum_three_pow_le_two (m : ℕ) :
    (Nat.digits 2 (3 ^ m)).sum ≤ 2 ↔ m ≤ 2 := by
  constructor
  · intro h
    have hn : 0 < 3 ^ m := by positivity
    have hodd : 3 ^ m % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) hn, List.sum_cons, hodd] at h
    have hdm := Nat.div_add_mod (3 ^ m) 2
    have h1 : (Nat.digits 2 (3 ^ m / 2)).sum ≤ 1 := by omega
    rcases digitSum_two_le_one h1 with hz | ⟨b, hb⟩
    · -- `3^m / 2 = 0`, so `3^m = 1`, so `m = 0`
      have hn1 : 3 ^ m = 1 := by omega
      rcases Nat.pow_eq_one.mp hn1 with h3 | hm0
      · omega
      · omega
    · -- `3^m / 2 = 2^b`, so `3^m = 2^{b+1} + 1`, so `m ≤ 2`
      have hn2 : 3 ^ m = 2 ^ (b + 1) + 1 := by rw [pow_succ]; omega
      by_contra hmc
      push Not at hmc
      exact three_pow_ne_two_pow_succ hn2 (by omega)
  · intro h; interval_cases m <;> decide

/-- The `s₂ = 1` slice of B5a: `3^m` has binary digit sum `1` (i.e. is a power
of `2`) exactly for `m = 0`. -/
@[category research solved, AMS 11, ref "Ste80", group "three_pow_digit_blocks"]
theorem digitSum_three_pow_eq_one (m : ℕ) :
    (Nat.digits 2 (3 ^ m)).sum = 1 ↔ m = 0 := by
  constructor
  · intro h
    have hm2 : m ≤ 2 := (digitSum_three_pow_le_two m).mp (by omega)
    interval_cases m <;> revert h <;> decide
  · rintro rfl; decide

/-- The `s₂ = 2` slice of B5a: `3^m` has binary digit sum `2` (i.e. is a sum of
two distinct powers of `2`) exactly for `m ∈ {1, 2}`. -/
@[category research solved, AMS 11, ref "Ste80", group "three_pow_digit_blocks"]
theorem digitSum_three_pow_eq_two (m : ℕ) :
    (Nat.digits 2 (3 ^ m)).sum = 2 ↔ m = 1 ∨ m = 2 := by
  constructor
  · intro h
    have hm2 : m ≤ 2 := (digitSum_three_pow_le_two m).mp (by omega)
    interval_cases m <;> revert h <;> decide
  · rintro (rfl | rfl) <;> decide

/-! ## Theorem B5b (on the cited Dimitrov–Howe result) -/

/-- **Theorem B5b** ([A4+] §3.4; [DH23], the `n = 3` case): the powers of `3`
with binary digit sum exactly `3` are precisely `3^4 = 81`:

  `s₂(3^m) = 3  ⟺  m = 4`.

By oddness and bit-peeling, `s₂(3^m) = 3` is equivalent to
`3^m = 2^a + 2^b + 1` with `1 ≤ b < a` (via `digitSum_two_eq_two`), and this
exponential Diophantine equation has the unique solution `(m, b, a) = (4, 4, 6)`
by Dimitrov–Howe (the cited axiom `DH.three_pow_three_binary_digits`).
Footprint std3 + [DH23]. -/
@[category research solved, AMS 11, ref "DH23", group "three_pow_digit_blocks"]
theorem digitSum_three_pow_eq_three (m : ℕ) :
    (Nat.digits 2 (3 ^ m)).sum = 3 ↔ m = 4 := by
  constructor
  · intro h
    -- extract the representation `3^m = 2^a + 2^b + 1`, `1 ≤ b < a`
    have hn : 0 < 3 ^ m := by positivity
    have hodd : 3 ^ m % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) hn, List.sum_cons, hodd] at h
    have hdm := Nat.div_add_mod (3 ^ m) 2
    have h2 : (Nat.digits 2 (3 ^ m / 2)).sum = 2 := by omega
    obtain ⟨c, d, hcd, hq⟩ := digitSum_two_eq_two h2
    have hrep : 3 ^ m = 2 ^ (d + 1) + 2 ^ (c + 1) + 1 := by rw [pow_succ, pow_succ]; omega
    -- Dimitrov–Howe: the unique solution is `m = 4`
    exact (DH.three_pow_three_binary_digits hrep (by omega) (by omega)).1
  · rintro rfl; decide

/-- Calibrating witness: `3^3 = 27 = 11011₂` has binary digit sum `4 > 2`. -/
@[category test, AMS 11, ref "Ste80", group "three_pow_digit_blocks"]
lemma digitSum_three_pow_three : (Nat.digits 2 (3 ^ 3)).sum = 4 := by decide

/-- Calibrating witness: `3^4 = 81 = 1010001₂` has binary digit sum `3 > 2`. -/
@[category test, AMS 11, ref "Ste80", group "three_pow_digit_blocks"]
lemma digitSum_three_pow_four : (Nat.digits 2 (3 ^ 4)).sum = 3 := by decide

end TH
