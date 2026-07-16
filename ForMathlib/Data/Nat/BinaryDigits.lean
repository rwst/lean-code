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
* `Nat.mod_two_pow_eq_of_testBit_eq_true` — the all-ones companion: if bits
  `x ≤ i < y` of `n` are all `true`, then `n % 2 ^ y = n % 2 ^ x + (2 ^ y - 2 ^ x)`;
* `Nat.mod_two_pow_add` — peeling a `p`-bit block off a remainder:
  `n % 2 ^ (a + p) = n % 2 ^ a + (n / 2 ^ a % 2 ^ p) · 2 ^ a`;
* `Nat.periodic_mod_identity` — the **`p`-periodic window** remainder identity:
  if bits `x ≤ i` with `i + p < y` satisfy `bitᵢ = bitᵢ₊ₚ`, then for every
  `t` with `x + t·p ≤ y`,
  `(2^p − 1)·(n % 2^{x+tp}) = (2^p − 1)·(n % 2^x) + c·(2^{x+tp} − 2^x)`
  with `c = n / 2^x % 2^p` the repeated `p`-bit pattern (via `chunk_shift`,
  `periodic_chunk_eq`);
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

/-- A run of one bits in positions `[x, y)` collapses the remainders with an
offset: `n % 2 ^ y = n % 2 ^ x + (2 ^ y - 2 ^ x)` (the run contributes the full
block `2^x + ⋯ + 2^{y-1} = 2^y - 2^x`). -/
lemma mod_two_pow_eq_of_testBit_eq_true {n x y : ℕ} (hxy : x ≤ y)
    (h : ∀ i, x ≤ i → i < y → n.testBit i = true) :
    n % 2 ^ y = n % 2 ^ x + (2 ^ y - 2 ^ x) := by
  revert h
  induction y, hxy using Nat.le_induction with
  | base => intro _; omega
  | succ y hxy ih =>
    intro h
    have hy : n.testBit y = true := h y hxy (Nat.lt_succ_self y)
    rw [mod_two_pow_succ, hy, ih (fun i hxi hiy => h i hxi (Nat.lt_succ_of_lt hiy))]
    have h2x : (2 : ℕ) ^ x ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) hxy
    have hpow : (2 : ℕ) ^ (y + 1) = 2 ^ y + 2 ^ y := by rw [pow_succ]; ring
    simp only [Bool.toNat_true, mul_one]
    omega

/-- Peeling a `p`-bit block off a remainder:
`n % 2 ^ (a + p) = n % 2 ^ a + (bits `[a, a+p)` of `n`) · 2 ^ a`
(the `p`-bit generalization of `mod_two_pow_succ`). -/
lemma mod_two_pow_add (n a p : ℕ) :
    n % 2 ^ (a + p) = n % 2 ^ a + (n / 2 ^ a % 2 ^ p) * 2 ^ a := by
  have h : n % (2 ^ a * 2 ^ p) = n % 2 ^ a + 2 ^ a * (n / 2 ^ a % 2 ^ p) := Nat.mod_mul
  rw [← pow_add] at h; rw [h]; ring

/-- Two consecutive `p`-bit blocks of `n` coincide when the bits in the first
block equal the corresponding bits `p` positions higher:
`(n / 2 ^ a) % 2 ^ p = (n / 2 ^ (a + p)) % 2 ^ p`. -/
lemma chunk_shift (n a p : ℕ)
    (h : ∀ r, r < p → n.testBit (a + r) = n.testBit (a + p + r)) :
    (n / 2 ^ a) % 2 ^ p = (n / 2 ^ (a + p)) % 2 ^ p := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < p
  · simp only [hi, decide_true, Bool.true_and]
    have := h i hi
    rw [show i + a = a + i by ring, show i + (a + p) = a + p + i by ring, this]
  · simp only [hi, decide_false, Bool.false_and]

/-- In a `p`-periodic window, every `p`-bit block equals the first one:
if `bitᵢ(n) = bitᵢ₊ₚ(n)` for all `x ≤ i` with `i + p < y`, then for each `j`
with `x + j·p + p ≤ y`, `(n / 2 ^ (x + j·p)) % 2 ^ p = n / 2 ^ x % 2 ^ p`. -/
lemma periodic_chunk_eq {n x y p : ℕ}
    (hper : ∀ i, x ≤ i → i + p < y → n.testBit i = n.testBit (i + p)) :
    ∀ j, x + j * p + p ≤ y → (n / 2 ^ (x + j * p)) % 2 ^ p = (n / 2 ^ x) % 2 ^ p := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [show (j + 1) * p = j * p + p by ring] at hj
    have hstep : (n / 2 ^ (x + j * p)) % 2 ^ p = (n / 2 ^ (x + j * p + p)) % 2 ^ p := by
      apply chunk_shift
      intro r hr
      have := hper (x + j * p + r) (by omega) (by omega)
      rw [show x + j * p + r + p = x + j * p + p + r by ring] at this
      exact this
    rw [show x + (j + 1) * p = x + j * p + p by ring, ← hstep]
    exact ih (by omega)

/-- The **`p`-periodic window remainder identity**.  If bits `x ≤ i` with
`i + p < y` satisfy `bitᵢ(n) = bitᵢ₊ₚ(n)` (the window `[x, y)` is `p`-periodic),
then for every `t` with `x + t·p ≤ y`, with `c = n / 2 ^ x % 2 ^ p` the repeated
`p`-bit pattern,

  `(2 ^ p − 1)·(n % 2 ^ (x + t·p))
      = (2 ^ p − 1)·(n % 2 ^ x) + c·(2 ^ (x + t·p) − 2 ^ x)`.

Multiplying by `2 ^ p − 1` clears the geometric-series denominator
`(2^{tp} − 1)/(2^p − 1)`, keeping everything in `ℕ`. -/
lemma periodic_mod_identity {n x y p : ℕ}
    (hper : ∀ i, x ≤ i → i + p < y → n.testBit i = n.testBit (i + p)) :
    ∀ t, x + t * p ≤ y →
      (2 ^ p - 1) * (n % 2 ^ (x + t * p))
        = (2 ^ p - 1) * (n % 2 ^ x) + (n / 2 ^ x % 2 ^ p) * (2 ^ (x + t * p) - 2 ^ x) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ht' : x + (t * p + p) ≤ y := by
      rw [show (t + 1) * p = t * p + p by ring] at ht; exact ht
    set c : ℕ := n / 2 ^ x % 2 ^ p with hc
    have hchunk : (n / 2 ^ (x + t * p)) % 2 ^ p = c := periodic_chunk_eq hper t (by omega)
    have hpeel : n % 2 ^ (x + (t + 1) * p) = n % 2 ^ (x + t * p) + c * 2 ^ (x + t * p) := by
      rw [show x + (t + 1) * p = (x + t * p) + p by ring, mod_two_pow_add, hchunk]
    rw [hpeel, Nat.mul_add, ih (by omega)]
    have hle1 : 2 ^ x ≤ 2 ^ (x + t * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle2 : (2 : ℕ) ^ (x + t * p) ≤ 2 ^ (x + (t + 1) * p) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [show (t + 1) * p = t * p + p by ring]; omega)
    have hpow : (2 : ℕ) ^ (x + (t + 1) * p) = 2 ^ (x + t * p) * 2 ^ p := by
      rw [← pow_add]; congr 1; ring
    have hp1 : 1 ≤ (2 : ℕ) ^ p := Nat.one_le_two_pow
    have hexpand : (2 ^ p - 1) * (c * 2 ^ (x + t * p))
        = c * (2 ^ (x + (t + 1) * p) - 2 ^ (x + t * p)) := by
      have hd : 2 ^ (x + t * p) * 2 ^ p
          = 2 ^ (x + t * p) * (2 ^ p - 1) + 2 ^ (x + t * p) := by
        obtain ⟨q, hq⟩ : ∃ q, (2 : ℕ) ^ p = q + 1 := ⟨2 ^ p - 1, by omega⟩
        rw [hq, Nat.add_sub_cancel]; ring
      have hkey : (2 : ℕ) ^ (x + (t + 1) * p) - 2 ^ (x + t * p)
          = 2 ^ (x + t * p) * (2 ^ p - 1) := by rw [hpow, hd]; omega
      rw [hkey]; ring
    rw [hexpand]
    have hsub : 2 ^ (x + (t + 1) * p) - 2 ^ x
        = (2 ^ (x + t * p) - 2 ^ x) + (2 ^ (x + (t + 1) * p) - 2 ^ (x + t * p)) := by omega
    rw [hsub, Nat.mul_add]
    ring

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
