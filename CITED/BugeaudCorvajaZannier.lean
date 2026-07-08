/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.GCD.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Bugeaud–Corvaja–Zannier GCD bound (Math. Z. 2003), ℚ / S = {∞, 2, 3} case

**Theorem 1** of Bugeaud–Corvaja–Zannier ([BCZ03], p. 80; read in full 2026-07-08), a
Schmidt-Subspace-theorem consequence: powers `aⁿ − 1` and `bⁿ − 1` of multiplicatively
independent bases share almost nothing.

> Let `a, b` be multiplicatively independent integers `≥ 2`, and let `ε > 0`.  Then,
> provided `n` is sufficiently large,
>
>   `gcd(aⁿ − 1, bⁿ − 1) < exp(ε·n)`.

The archetype is `a = 2`, `b = 3`: `gcd(2ⁿ − 1, 3ⁿ − 1) < exp(ε·n)` for all sufficiently
large `n` — the "pure `ℚ`, `S = {∞, 2, 3}`" instance advertised in [M4A3] §8 (the
Subspace argument runs over the places `S = {∞} ∪ {p : p ∣ ab}`, which for `a·b = 6` is
exactly `{∞, 2, 3}`).

## Statement conventions (faithful transcription)

* **Bases general, headline `ℚ`-specialized.**  The `axiom` `gcd_pow_sub_one_lt` keeps
  the bases `a, b` general (the theorem's actual generality); the proved lemma
  `gcd_two_three_pow_lt` is the `a = 2`, `b = 3` (`S = {∞, 2, 3}`) case, its
  hypotheses discharged by `multIndep_two_three`.  (Mirrors the sibling engines
  `CZ.pseudoPisot_approx`/`NKR.sUnit_pair_integrality`, general statement plus the
  concrete `Γ = ⟨2, 3⟩` instance.)
* **Multiplicative independence** of `a, b ≥ 2` is `MultIndep a b`:
  `∀ m n : ℕ, aᵐ = bⁿ → m = 0 ∧ n = 0`.  For positive bases this is the usual condition
  (`aˣ = bʸ` over `ℤ` forces `x = y = 0`; opposite signs are impossible for bases `≥ 2`).
* **`exp(ε·n)`, the paper's form.**  Since `ε > 0` is arbitrary, this is equivalent to the
  `2^{εn}` form of [M4A3] §8 (replace `ε` by `ε·log 2`); we keep [BCZ03]'s `Real.exp`.
* **`gcd` over `ℕ`.**  `Nat.gcd (aⁿ − 1) (bⁿ − 1)` with truncated subtraction; for `a ≥ 2`
  and `n ≥ 1` the arguments are `≥ 1`, so this is the genuine GCD, cast to `ℝ` for the
  bound.
* **"Sufficiently large" = `∃ N, ∀ n ≥ N`.**  The bound `N = N(a, b, ε)` is
  **ineffective** ([BCZ03], Remark 5: the Diophantine input gives no computable `N`); we
  record only its existence, never a value.

The best-possible comparison ([BCZ03], Remark 1): for `b` not a power of `a`,
`gcd(aⁿ − 1, bⁿ − 1) ≪ a^{n/2}`, and the exponent `1/2` cannot be improved (Remark 2), so
the `exp(εn)` bound is far stronger than any elementary estimate but stays ineffective.

## Contents

* `BCZ.MultIndep` — multiplicative independence of two naturals.
* `BCZ.multIndep_two_three` — `MultIndep 2 3` (parity: `2 ∤ 3ⁿ`), proved.
* `BCZ.gcd_pow_sub_one_lt` — **Theorem 1** of [BCZ03], recorded as a cited `axiom`.
* `BCZ.gcd_two_three_pow_lt` — the `a = 2, b = 3` (`S = {∞, 2, 3}`) headline, proved from
  the axiom.

## References

* [BCZ03] Bugeaud, Yann, Pietro Corvaja, and Umberto Zannier. "An upper bound for the
  G.C.D. of `aⁿ − 1` and `bⁿ − 1`." *Mathematische Zeitschrift* **243** (2003), 79–84.
  (Theorem 1, p. 80; Subspace-theorem proof via the "small linear form" `1/(aⁿ−1)`.)
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §7 (engine audit), §8 row 4
  (transcription brief).
-/

namespace BCZ

/-- Two naturals `a, b` are **multiplicatively independent** when the only solution of
`aᵐ = bⁿ` in nonnegative exponents is the trivial one.  For bases `≥ 2` this is the usual
multiplicative independence (an `aˣ = bʸ` over `ℤ` reduces to this). -/
@[category API, AMS 11, ref "BCZ03", group "three_halves_m4"]
def MultIndep (a b : ℕ) : Prop := ∀ m n : ℕ, a ^ m = b ^ n → m = 0 ∧ n = 0

/-- `2` and `3` are multiplicatively independent: `2ᵐ = 3ⁿ` forces `m = n = 0`, since a
positive power of `2` is even while every power of `3` is odd. -/
@[category API, AMS 11, ref "BCZ03", group "three_halves_m4"]
lemma multIndep_two_three : MultIndep 2 3 := by
  intro m n h
  have hm : m = 0 := by
    by_contra hm
    have h2 : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 hm
    rw [h] at h2
    have hcop : Nat.gcd 2 (3 ^ n) = 1 := Nat.Coprime.pow_right n (by decide)
    have : (2 : ℕ) ∣ 1 := hcop ▸ Nat.dvd_gcd (dvd_refl 2) h2
    exact absurd (Nat.dvd_one.mp this) (by norm_num)
  subst hm
  simp only [pow_zero] at h
  rcases Nat.pow_eq_one.mp h.symm with h3 | hn0
  · norm_num at h3
  · exact ⟨rfl, hn0⟩

/-- **Bugeaud–Corvaja–Zannier, Theorem 1** ([BCZ03]): for multiplicatively independent
integers `a, b ≥ 2` and every `ε > 0`, the greatest common divisor of `aⁿ − 1` and
`bⁿ − 1` satisfies

  `gcd(aⁿ − 1, bⁿ − 1) < exp(ε·n)`   for all sufficiently large `n`.

Recorded as a cited `axiom` on the authority of [BCZ03] — a Schmidt-Subspace-theorem
argument (viewing `1/(aⁿ − 1)` as a small linear form in `S`-unit variables, `S` the
primes dividing `ab` together with `∞`) that we do not re-derive.  The threshold index
`N = N(a, b, ε)` is **ineffective** ([BCZ03], Remark 5). -/
@[category research solved, AMS 11, ref "BCZ03", group "three_halves_m4"]
axiom gcd_pow_sub_one_lt (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hind : MultIndep a b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Nat.gcd (a ^ n - 1) (b ^ n - 1) : ℝ) < Real.exp (ε * n)

/-- **The `S = {∞, 2, 3}` headline** ([BCZ03], Theorem 1 at `a = 2`, `b = 3`): for every
`ε > 0`, `gcd(2ⁿ − 1, 3ⁿ − 1) < exp(ε·n)` for all sufficiently large `n`.  Proved from
`gcd_pow_sub_one_lt` and `multIndep_two_three`. -/
@[category research solved, AMS 11, ref "BCZ03", group "three_halves_m4"]
lemma gcd_two_three_pow_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Nat.gcd (2 ^ n - 1) (3 ^ n - 1) : ℝ) < Real.exp (ε * n) :=
  gcd_pow_sub_one_lt 2 3 (by norm_num) (by norm_num) multIndep_two_three ε hε

end BCZ
