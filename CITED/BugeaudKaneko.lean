/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud–Kaneko: nonzero digits of smooth numbers (Cor. 1.5), ℤ-specialization

The effective lower bound on the number of **nonzero digits** of an integer that is
simultaneously *smooth* (few prime factors) and *digit-sparse*, from Bugeaud–Kaneko
([BK17], "On the digital representation of smooth numbers", arXiv:1704.00432; read in
full 2026-07-08).  Their engine is linear forms in complex logarithms (Matveev) together
with `p`-adic logarithmic forms (Yu, `CITED/YuPadicForms.lean`) — Baker–Wüstholz-grade
and, crucially, **effective**.

The clean citable form is **Corollary 1.5** ([BK17]):

> Let `b ≥ 2`, let `S = {q₁, …, q_s}` be a finite set of primes, and let `ε > 0`.  Then
> every sufficiently large integer `N` composed only of primes from `S` (an `S`-unit) and
> **not divisible by `b`** has more than
>
>   `(1 − ε) · (log log N) / (log log log N)`
>
> nonzero digits in its base-`b` expansion.

For `N = 3^m` in base `2` this reads `s₂(3^m) > (1 − ε)·(log log N)/(log log log N)`, and
since `log N = m·log 3` the right-hand side is asymptotically `(1 − ε)·log m / log log m`
— the **same order as Stewart's theorem** (`TH/StewartDigits.lean`), with the constant
sharpened from Stewart's `1/2` to `1 − ε`.  This is the [A4+] gate-G1 result behind the
sparse-side rung **B5** (and, via [BK17] Remark 4.4, the digit-*block* rung **B1**; see
below).

## Statement conventions (the ℤ-specialization — all uses in this corpus)

* **Integers, not the exponent.**  `N` is the integer whose digits are counted (for us
  `N = 3^m`), and the bound is in `log log N / log log log N`.  Contrast Stewart's usual
  phrasing in the *exponent* `m` (`s₂(3^m) ≥ log m / (2 log log m + C)`): the two agree to
  leading order because `log log N = log(m log 3) ∼ log m`.
* **`S`-unit** of `ℤ` = every prime factor lies in the finite set `S : Finset ℕ`:
  `∀ p, p.Prime → p ∣ N → p ∈ S`.  For `N = 3^m` this holds with `S = {3}`.
* **`b ∤ N`** is required (else trailing zeros make the count basis-dependent); for
  `N = 3^m`, `b = 2` it is automatic (`3^m` is odd).
* **Nonzero-digit count** is `Bugeaud.nonzeroDigits b N = (Nat.digits b N).countP (· ≠ 0)`.
  In base `2` the digits are `0`/`1`, so `nonzeroDigits 2 N = (Nat.digits 2 N).sum`
  (`nonzeroDigits_two_eq_digitSum`) — exactly the `s₂` functional of
  `TH/StewartDigits.lean`.
* **"Sufficiently large" = `∃ n₀, ∀ N ≥ n₀`.**  The threshold `n₀ = n₀(b, S, ε)` is
  **effective** ([BK17]); we record only its existence.

## The digit-block companion (Remark 4.4), *not* axiomatized here

[BK17] Remark 4.4 states that the same proofs give the analogue of Cor. 1.5 with "number
of nonzero digits" replaced by **"number of blocks composed of the same digit"**.  For
`3^m` in base `2` that is `≫ log m / log log m` binary *blocks* `=` digit changes `+ 1`,
i.e. the effective form of rung **B1** ([A4+]).  It needs the block-count vocabulary that
[A4+] §5.2 places in `TH/DigitBlocks/Defs.lean`; it is transcribed there when B1 is built,
not here.  The integer-power precedent is Blecksmith–Filaseta–Nicol 1993.

## Contents

* `BK.nonzeroDigits` — the number of nonzero base-`b` digits.
* `BK.nonzeroDigits_two_eq_digitSum` — in base `2` it is the digit sum.
* `BK.nonzeroDigits_sUnit_lower` — **Corollary 1.5** of [BK17], recorded as a cited
  effective `axiom`.
* `BK.digitSum_three_pow_base_two_lower` — the `N = 3^m`, `b = 2` instance, proved from
  the axiom; the effective Stewart sharpening `s₂(3^m) > (1 − ε)(log log 3^m)/(log log log
  3^m)` for `m` large.

## References

* [BK17] Bugeaud, Yann, and Hajime Kaneko. "On the digital representation of smooth
  numbers." arXiv:1704.00432 (2017).  (Corollary 1.5, p. 2; Theorems 1.1–1.3; Remark 4.4
  the block analogue.  Engine: Matveev + Yu `p`-adic logs.)
* [Ste80] C. L. Stewart, "On the representation of an integer in two different bases," J.
  reine angew. Math. 319 (1980), 63–72.  (The `1/2`-constant baseline; here
  `TH/StewartDigits.lean`.)  [BFN93] Blecksmith–Filaseta–Nicol, Acta Arith. 64 (1993),
  331–339 (integer-power precedent).
* [A4+] `plan-A4+.html` (this repository, 2026-07): gate G1 (this transcription), rungs
  B1/B5.
-/

namespace BK

/-- The number of **nonzero digits** of `N` in base `b`. -/
@[category API, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
def nonzeroDigits (b N : ℕ) : ℕ := (Nat.digits b N).countP (· != 0)

/-- The sum of a list of base-`2` digits (each `< 2`) equals the count of its nonzero
entries. -/
private lemma sum_eq_countP_lt_two : ∀ (l : List ℕ), (∀ d ∈ l, d < 2) →
    l.sum = l.countP (· != 0)
  | [], _ => by simp
  | a :: t, h => by
    have ht : ∀ d ∈ t, d < 2 := fun d hd => h d (List.mem_cons_of_mem a hd)
    have ha : a < 2 := h a (List.mem_cons_self ..)
    rw [List.sum_cons, List.countP_cons, sum_eq_countP_lt_two t ht, Nat.add_comm]
    congr 1
    interval_cases a <;> simp

/-- In base `2` the nonzero-digit count is the digit sum (digits are `0`/`1`): this is the
`s₂` functional of `TH/StewartDigits.lean`. -/
@[category API, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
lemma nonzeroDigits_two_eq_digitSum (N : ℕ) :
    nonzeroDigits 2 N = (Nat.digits 2 N).sum := by
  unfold nonzeroDigits
  rw [sum_eq_countP_lt_two _ (fun d hd => Nat.digits_lt_base (by norm_num) hd)]

/-- **Bugeaud–Kaneko, Corollary 1.5** ([BK17]): for a base `b ≥ 2`, a finite set of primes
`S`, and every `ε > 0`, every sufficiently large integer `N` that is an `S`-unit
(all prime factors in `S`) and is not divisible by `b` has

  `(1 − ε) · (log log N) / (log log log N) < (number of nonzero base-b digits of N)`.

Recorded as a cited **effective** `axiom` on the authority of [BK17] — a linear-forms
estimate (Matveev in `ℂ` + Yu `p`-adic, `CITED/YuPadicForms.lean`) we do not re-derive.
The threshold `n₀ = n₀(b, S, ε)` is effective; only its existence is recorded.  For
`b = 2` this is the effective sharpening of Stewart's theorem (constant `1/2 → 1 − ε`). -/
@[category research solved, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
axiom nonzeroDigits_sUnit_lower (b : ℕ) (hb : 2 ≤ b) (S : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S) → ¬ (b ∣ N) →
      (1 - ε) * (Real.log (Real.log (N : ℝ)) / Real.log (Real.log (Real.log (N : ℝ))))
        < (nonzeroDigits b N : ℝ)

/-- **The `N = 3^m`, base-`2` instance** ([BK17] Cor. 1.5 at `S = {3}`, `b = 2`): the
binary digit sum of `3^m` satisfies, for all `m` beyond an effective threshold,

  `(1 − ε) · (log log 3^m) / (log log log 3^m) < s₂(3^m)`.

Since `log 3^m = m·log 3`, the left side is asymptotically `(1 − ε)·log m / log log m`,
sharpening the `1/2` constant of `TH.stewart_digitSum_three_pow`.  Proved from
`nonzeroDigits_sUnit_lower` (the `S`-unit hypothesis and `2 ∤ 3^m` are discharged by
parity). -/
@[category research solved, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
lemma digitSum_three_pow_base_two_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m →
      (1 - ε) * (Real.log (Real.log ((3 ^ m : ℕ) : ℝ))
          / Real.log (Real.log (Real.log ((3 ^ m : ℕ) : ℝ))))
        < ((Nat.digits 2 (3 ^ m)).sum : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := nonzeroDigits_sUnit_lower 2 (by norm_num) {3} ε hε
  refine ⟨n₀, fun m hm => ?_⟩
  have hN : n₀ ≤ 3 ^ m := le_trans hm (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  have hSunit : ∀ p : ℕ, p.Prime → p ∣ 3 ^ m → p ∈ ({3} : Finset ℕ) := by
    intro p hp hpd
    have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (Nat.Prime.dvd_of_dvd_pow hp hpd)
    simp [h3]
  have hb : ¬ (2 ∣ 3 ^ m) := by rw [Nat.two_dvd_ne_zero, Nat.pow_mod]; norm_num
  have h := hn₀ (3 ^ m) hN hSunit hb
  rwa [nonzeroDigits_two_eq_digitSum] at h

end BK
