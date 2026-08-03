/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.EvertseSUnit
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FinCases
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bennett–Billerey: sums of two `S`-units that are perfect powers

M. A. Bennett and N. Billerey, *Sums of two `S`-units via Frey–Hellegouarch curves*
([BB16], arXiv:1603.07922v2, 24 May 2016).  For a finite set of primes `S`, an *`S`-unit* is a
nonzero integer `±p₁^α₁ ⋯ p_k^α_k` (equivalently: a nonzero integer all of whose prime factors
lie in `S`).  The paper studies

  `x + y = zⁿ`,  `x, y` `S`-units, `z` a nonzero integer, `n ≥ 2`,   (equation (2))

calling a quadruple `(x, y, z, n)` **primitive** when `gcd(x, y)` is `n`-th power free, and
**solves it completely** for two sets of primes:

* `S = {2, 3}` (**Theorem 7.1**) — eleven infinite families plus nine sporadic quadruples;
* `S = {3, 5, 7}` (**Theorem 7.2**, the paper's main theorem) — exactly 56 pairs `(x, y)`.

Behind the tables sits the qualitative dichotomy (**Theorem 3.2**, **Corollary 3.4**): for a fixed
exponent there are always finitely many primitive solutions, and there are finitely many in total
**if and only if `2 ∉ S`**.  Both tables illustrate it — `S = {2,3}` has the infinite families
`2^{n-1} + 2^{n-1} = 2ⁿ`, `2·3^{n-1} + 3^{n-1} = 3ⁿ`, … while `S = {3,5,7}` is a finite list.

## Method (not reproduced here)

Frey–Hellegouarch curves of signatures `(n,n,n)`, `(n,n,2)` and `(n,n,3)`, modularity of elliptic
curves over `ℚ`, Ribet's level-lowering, Cremona's tables, Magma/PARI newform computations at
levels up to `19845 = 3⁴·5·7²`, local sieving, and degree-5 Thue–Mahler solvers.  The paper's
stated point is that this route **avoids lower bounds for linear forms in logarithms entirely**
— which the authors call "impractical for explicitly solving equation (2) for any set `S` with at
least two elements".  None of this machinery exists in Mathlib, so the results are recorded as
statement-faithful cited `axiom`s in the usual `CITED/` style, with the tables themselves
machine-checked for internal consistency (see the `_sound` lemmas below).

## Where this sits in the corpus

`CITED/` already holds the *lower-bound* engines for the `S = {2,3}` world: `Rhin.logForm_lower_bound`
(`H^{-13.3}`), `Ellison.pillai_lower_bound` (`|2ʲ − 3^q|`), `BakerWustholz`, `Matveev`,
`LaurentTwoLogs`, `BugeaudLaurent`, `YuPadicForms`, plus the Subspace-flavoured finiteness engines
`Evertse.sUnit_sum_lower`, `BCZ.gcd_pow_sub_one_lt` and `CZ.pseudoPisot_approx*`.  [BB16] is a
**fourth, axiom-disjoint lane**: its §3 finiteness statements come from Shafarevich's theorem plus
modularity, using neither Baker nor Schmidt.  It is also the published, complete answer to the
sub-case of `plans/report-bugeaud-recent.html` strategy **I.3** ("solve `2^a3^b − z^d = m`
completely for `T = {2,3}`") in which `m` is itself a `{2,3}`-unit: put `y = −m` in Theorem 7.1.

**What it does not give.**  Nothing about `|2ʲ − 3^q|` in general (only when that difference is a
perfect power), hence `Ellison.pillai_lower_bound` and `Rhin.logForm_lower_bound` are untouched;
and nothing about `‖(3/2)ⁿ‖`, equidistribution or orbit complexity.

## Contents

Set-up: `IsSUnit`, `NthPowerFree`, `IsPrimitiveSolution`, with the bridge
`isSUnit_two_three_of_evertse` to the existing `{2,3}`-specific `Evertse.IsSUnit`.

Cited axioms:
* `exponent_le` — **[BB16] Theorem 3.2**: for `|z| > 1` the exponent `n` is bounded in terms of
  `S` and a bound on `gcd(x, y)` (the linear-forms-free exponent bound).
* `finite_primitiveSolution` — **[BB16] Corollary 3.4**, first part: finiteness for fixed `n`.
* `finite_primitiveSolution_iff` — **[BB16] Corollary 3.4**, second part: finiteness over all `n`
  holds **iff** `2 ∉ S`.
* `primitive_two_three` — **[BB16] Theorem 7.1**: the complete list for `S = {2,3}`.
* `primitive_three_five_seven` — **[BB16] Theorem 7.2**: the complete list for `S = {3,5,7}`.

Proved glue (no cited input):
* `family23_sound`, `sporadic23_sound`, `powers357_sound`, `powers357_pairs` — every tabulated
  tuple really does satisfy `x + y = zⁿ`, and the `(z, n)`-augmented `{3,5,7}` table projects
  exactly onto the paper's pair list.
* `sUnit_sub_one_eq_pow` / `three_smooth_sub_one_eq_pow` — **the only `3`-smooth number exceeding
  a perfect power `zⁿ` (`z ≥ 2`, `n ≥ 2`) by one is `9 = 2³ + 1`** (Catalan-adjacent).
* `sUnit_add_one_eq_pow` / `three_smooth_add_one_eq_pow` — the `3`-smooth numbers one *less* than
  such a perfect power are exactly `3, 8, 24, 48, 288` (`4, 9, 25, 49, 289`).

## References

* [BB16] M. A. Bennett, N. Billerey, *Sums of two `S`-units via Frey–Hellegouarch curves*,
  arXiv:1603.07922v2 (2016).  Theorems 3.2, 3.3, 7.1, 7.2, Corollary 3.4, Propositions 6.2–6.4.
* [ST86] T. N. Shorey, R. Tijdeman, *Exponential Diophantine equations*, Cambridge Tracts 87,
  CUP 1986.  Chapter 9; Theorem 9.1/9.2 are the results [BB16] §3 reproves modularly.
* [dW89] B. M. M. de Weger, *Algorithms for Diophantine equations*, CWI Tract 65, 1989.  Chapter 7
  — the classical linear-forms-in-logarithms + LLL route, including `S = {2,3,5,7}`.
-/

namespace BB16

/-! ## The Diophantine set-up -/

/-- **`S`-unit** ([BB16] §1): a nonzero integer of the shape `±p₁^α₁ ⋯ p_k^α_k` with the `pᵢ`
ranging over the finite set of primes `S`.  Stated here in the equivalent divisor form — `x ≠ 0`
and every prime factor of `x` lies in `S` — which is the form that generalises painlessly over
`S` and is what the proofs below actually use.

For `S = {2, 3}` this agrees with the pre-existing `Evertse.IsSUnit` (one direction is
`isSUnit_two_three_of_evertse`; the converse is unique factorisation and is not needed here). -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
def IsSUnit (S : Finset ℕ) (x : ℤ) : Prop :=
  x ≠ 0 ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → p ∈ S

/-- **`n`-th power free**: no `n`-th power of a prime divides `m`.  For `n = 2` this is
`Squarefree`; [BB16] uses it on `gcd(x, y)` to define *primitive* solutions. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
def NthPowerFree (n : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ n ∣ m)

/-- **A primitive solution of [BB16] equation (2)**: `x + y = zⁿ` with `x, y` `S`-units, `z` a
nonzero integer, `n ≥ 2`, and `gcd(x, y)` `n`-th power free (the paper's *primitivity*). -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
structure IsPrimitiveSolution (S : Finset ℕ) (x y z : ℤ) (n : ℕ) : Prop where
  /-- The exponent is at least `2`. -/
  two_le_exp : 2 ≤ n
  /-- The left summand is an `S`-unit. -/
  sUnit_left : IsSUnit S x
  /-- The right summand is an `S`-unit. -/
  sUnit_right : IsSUnit S y
  /-- The base of the power is nonzero. -/
  base_ne_zero : z ≠ 0
  /-- Primitivity: `gcd(x, y)` is `n`-th power free. -/
  gcd_powerFree : NthPowerFree n (Int.gcd x y : ℤ)
  /-- Equation (2). -/
  sum_eq_pow : x + y = z ^ n

/-! ### Elementary API -/

/-- An `S`-unit is nonzero. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma IsSUnit.ne_zero {S : Finset ℕ} {x : ℤ} (h : IsSUnit S x) : x ≠ 0 := h.1

/-- `S`-units are closed under negation. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma IsSUnit.neg {S : Finset ℕ} {x : ℤ} (h : IsSUnit S x) : IsSUnit S (-x) :=
  ⟨neg_ne_zero.mpr h.1, fun p hp hdvd => h.2 p hp (dvd_neg.mp hdvd)⟩

/-- `1` is an `S`-unit (the empty product). -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma isSUnit_one (S : Finset ℕ) : IsSUnit S 1 := by
  refine ⟨one_ne_zero, fun p hp hdvd => ?_⟩
  have h1 : p ∣ 1 := by exact_mod_cast hdvd
  exact absurd (Nat.dvd_one.mp h1) hp.ne_one

/-- `-1` is an `S`-unit. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma isSUnit_neg_one (S : Finset ℕ) : IsSUnit S (-1) := (isSUnit_one S).neg

/-- `1` is `n`-th power free for every `n ≥ 1`. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma nthPowerFree_one {n : ℕ} (hn : n ≠ 0) : NthPowerFree n (1 : ℤ) := by
  intro p hp hdvd
  have h1 : p ^ n ∣ 1 := by exact_mod_cast hdvd
  rcases Nat.pow_eq_one.mp (Nat.dvd_one.mp h1) with h | h
  · exact hp.ne_one h
  · exact hn h

/-- `2^a · 3^b` is a `{2, 3}`-unit. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma isSUnit_two_three_pow (a b : ℕ) : IsSUnit {2, 3} ((2 : ℤ) ^ a * 3 ^ b) := by
  refine ⟨by positivity, fun p hp hdvd => ?_⟩
  have hcast : ((2 ^ a * 3 ^ b : ℕ) : ℤ) = (2 : ℤ) ^ a * 3 ^ b := by push_cast; ring
  have h1 : p ∣ 2 ^ a * 3 ^ b := by
    rw [← hcast] at hdvd
    exact_mod_cast hdvd
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
  · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    simp [hp2]
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    simp [hp3]

/-- The bridge to the pre-existing `{2, 3}`-specific predicate of `CITED/EvertseSUnit.lean`:
an `Evertse.IsSUnit` is a `BB16.IsSUnit {2, 3}`.  (The converse holds by unique factorisation
but is not needed below.) -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma isSUnit_two_three_of_evertse {x : ℤ} (h : Evertse.IsSUnit x) : IsSUnit {2, 3} x := by
  obtain ⟨a, b, h | h⟩ := h
  · exact h ▸ isSUnit_two_three_pow a b
  · exact h ▸ (isSUnit_two_three_pow a b).neg

/-- If a power of `2` equals `1` the exponent vanishes. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma exp_eq_zero_of_two_pow_eq_one {k : ℕ} (h : (2 : ℤ) ^ k = 1) : k = 0 := by
  have h2 : (2 : ℕ) ^ k = 1 := by exact_mod_cast h
  rcases Nat.pow_eq_one.mp h2 with hcon | hcon
  · norm_num at hcon
  · exact hcon

/-- If a power of `3` equals `1` the exponent vanishes. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma exp_eq_zero_of_three_pow_eq_one {k : ℕ} (h : (3 : ℤ) ^ k = 1) : k = 0 := by
  have h2 : (3 : ℕ) ^ k = 1 := by exact_mod_cast h
  rcases Nat.pow_eq_one.mp h2 with hcon | hcon
  · norm_num at hcon
  · exact hcon

/-- A perfect power `zⁿ` with `z ≥ 2` and `n ≥ 2` is at least `4`. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
lemma four_le_pow {z : ℤ} {n : ℕ} (hz : 2 ≤ z) (hn : 2 ≤ n) : (4 : ℤ) ≤ z ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm0 : (0 : ℤ) < z ^ m := pow_pos (by omega) m
  have hm1 : (1 : ℤ) ≤ z ^ m := by have := Int.add_one_le_iff.mpr hm0; linarith
  have hrw : z ^ (m + 2) = z ^ m * (z * z) := by ring
  rw [hrw]; nlinarith

/-! ## §3: finiteness without linear forms in logarithms

[BB16] §3 recovers the classical finiteness statements of [ST86] Chapter 9 from Frey–Hellegouarch
curves, modularity and Shafarevich's theorem — deliberately *not* from Baker's method.  This is
the lane-defining content of the paper: everything in `CITED/` other than these axioms rests on
either linear forms in logarithms or the Subspace theorem. -/

/-- **[BB16] Theorem 3.2** (the exponent bound).  Let `x, y, w` be `S`-units with
`gcd(x, y) ≤ a`.  If `x + y = w zⁿ` with `n ≥ 2` and `|z| > 1`, then `n` is bounded by a constant
depending only on `S` and `a`.

Proved in [BB16] via `(n,n,n)`- and `(n,n,3)`-Frey–Hellegouarch curves: `E` arises modulo `n`
from a weight-2 newform of level bounded in terms of `S`, and Deligne's bound then forces
`n ≤ (1 + √q)^{2[K:ℚ]}`.  **No linear forms in logarithms are used.**  Recorded as a cited
`axiom`. -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
axiom exponent_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (a : ℕ) :
    ∃ N : ℕ, ∀ (x y w z : ℤ) (n : ℕ), IsSUnit S x → IsSUnit S y → IsSUnit S w →
      Int.gcd x y ≤ a → 2 ≤ n → 1 < |z| → x + y = w * z ^ n → n ≤ N

/-- **[BB16] Corollary 3.4**, first part: for a *fixed* exponent `n ≥ 2` there are only finitely
many primitive solutions `(x, y, z)` of equation (2).  Recorded as a cited `axiom`. -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
axiom finite_primitiveSolution (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) (hn : 2 ≤ n) :
    {t : ℤ × ℤ × ℤ | IsPrimitiveSolution S t.1 t.2.1 t.2.2 n}.Finite

/-- **[BB16] Corollary 3.4**, second part — the dichotomy that organises the whole paper:
equation (2) has only finitely many primitive solutions `(x, y, z, n)` **iff `2 ∉ S`**.

The failure at `2 ∈ S` is explicit: `(2^{n-1}, 2^{n-1}, 2, n)` is primitive for every `n ≥ 2`.
The converse uses that `x, y` and `w` are then all odd, so the reduced base `z'` is even, whence
`|z'| > 1` and `exponent_le` applies.  Recorded as a cited `axiom`. -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
axiom finite_primitiveSolution_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    {t : ℤ × ℤ × ℤ × ℕ | IsPrimitiveSolution S t.1 t.2.1 t.2.2.1 t.2.2.2}.Finite ↔ 2 ∉ S

/-! ## §7.1: the case `S = {2, 3}` -/

/-- The eleven infinite families of [BB16] **Theorem 7.1**, verbatim (the exponents `n-1`, `n-2`,
`n-3` are the paper's; the truncated subtraction is harmless because `n ≥ 2`, and the last family
carries its own `3 ≤ n` guard as in the paper). -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
def Family23 (x y z : ℤ) (n : ℕ) : Prop :=
  (x = 2 ∧ y = -1 ∧ z = 1) ∨
  (x = 3 ∧ y = -2 ∧ z = 1) ∨
  (x = 4 ∧ y = -3 ∧ z = 1) ∨
  (x = 9 ∧ y = -8 ∧ z = 1) ∨
  (x = 2 ^ (n - 1) ∧ y = 2 ^ (n - 1) ∧ z = 2) ∨
  (x = 3 * 2 ^ (n - 2) ∧ y = 2 ^ (n - 2) ∧ z = 2) ∨
  (x = 3 * 2 ^ (n - 1) ∧ y = -2 ^ (n - 1) ∧ z = 2) ∨
  (x = 2 * 3 ^ (n - 1) ∧ y = 3 ^ (n - 1) ∧ z = 3) ∨
  (x = 2 ^ 2 * 3 ^ (n - 1) ∧ y = -3 ^ (n - 1) ∧ z = 3) ∨
  (x = 2 ^ 3 * 3 ^ (n - 2) ∧ y = 3 ^ (n - 2) ∧ z = 3) ∨
  (3 ≤ n ∧ x = 3 ^ 2 * 2 ^ (n - 3) ∧ y = -2 ^ (n - 3) ∧ z = 2)

/-- The nine sporadic primitive solutions `(x, y, z, n)` of [BB16] **Theorem 7.1**. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
def sporadic23 : List (ℤ × ℤ × ℤ × ℕ) :=
  [(16, 9, 5, 2), (18, -2, 4, 2), (24, 1, 5, 2), (27, -2, 5, 2), (81, -32, 7, 2),
   (48, 1, 7, 2), (128, -3, 5, 3), (288, 1, 17, 2), (486, -2, 22, 2)]

/-- **[BB16] Theorem 7.1.**  The only primitive solutions to `x + y = zⁿ` with `x, y` `{2,3}`-units
and `x ≥ |y| > 0`, `z > 0`, are the eleven infinite families `Family23` together with the nine
sporadic quadruples `sporadic23`.

Recorded as a cited `axiom`: the proof reduces to `n ≥ 5` prime, applies `(n,n,n)`- and
`(n,n,3)`-Frey–Hellegouarch curves to force `max{ord₂(xyw), ord₃(xyw)} ≤ 3` (via newforms of
level dividing `6`, resp. `12`, together with the elementary resolution of `3^k − 2^l = ±1`),
and finishes by a finite calculation.  The `n ≤ 4` cases come from Cremona's tables of elliptic
curves of conductor `< 350000`; their Proposition 6.2 is exactly this list at `n = 3`, which the
transcription here reproduces. -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
axiom primitive_two_three {x y z : ℤ} {n : ℕ}
    (h : IsPrimitiveSolution {2, 3} x y z n) (hxy : |y| ≤ x) (hz : 0 < z) :
    Family23 x y z n ∨ (x, y, z, n) ∈ sporadic23

/-- Consistency check on the transcription of the families: every listed family really does
satisfy `x + y = zⁿ`.  Proved outright — no cited input. -/
@[category test, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem family23_sound {x y z : ℤ} {n : ℕ} (hn : 2 ≤ n) (h : Family23 x y z n) :
    x + y = z ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  simp only [Family23, e1, e2] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨hm, rfl, rfl, rfl⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · ring
  · ring
  · ring
  · ring
  · ring
  · ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e3 : k + 1 + 2 - 3 = k := by omega
    rw [e3]; ring

/-- Consistency check on the transcription of the sporadic table: every listed quadruple really
does satisfy `x + y = zⁿ`.  Proved outright — no cited input. -/
@[category test, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem sporadic23_sound : ∀ t ∈ sporadic23, t.1 + t.2.1 = t.2.2.1 ^ t.2.2.2 := by
  intro t ht
  fin_cases ht <;> norm_num

/-- No sporadic solution of Theorem 7.1 has second summand `-1`. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem sporadic23_snd_ne_neg_one : ∀ t ∈ sporadic23, t.2.1 ≠ -1 := by decide

/-- The sporadic solutions of Theorem 7.1 with second summand `1` are exactly
`24 + 1 = 5²`, `48 + 1 = 7²` and `288 + 1 = 17²`. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem sporadic23_snd_eq_one : ∀ t ∈ sporadic23, t.2.1 = 1 →
    (t.1 = 24 ∧ t.2.2.1 = 5 ∧ t.2.2.2 = 2) ∨ (t.1 = 48 ∧ t.2.2.1 = 7 ∧ t.2.2.2 = 2) ∨
      (t.1 = 288 ∧ t.2.2.1 = 17 ∧ t.2.2.2 = 2) := by decide

/-! ## §7.2: the case `S = {3, 5, 7}` — the main theorem of [BB16] -/

/-- The 56 pairs `(x, y)` of [BB16] **Theorem 7.2**, verbatim. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
def pairs357 : List (ℤ × ℤ) :=
  [(3, 1), (5, -1), (5, 3), (7, -3), (7, 1), (9, -5), (9, -1), (9, 7), (15, -7), (15, 1),
   (21, -5), (21, 15), (25, -21), (25, -9), (25, 7), (27, 5), (35, -27), (35, -3), (35, 1),
   (49, -45), (49, 15), (63, 1), (81, -49), (105, -5), (125, 3), (135, -35), (135, -7),
   (147, -3), (175, 21), (175, 81), (189, -125), (189, 7), (225, -9), (343, -243),
   (375, -343), (405, -5), (441, -225), (625, -49), (675, 1), (729, -245), (1029, -5),
   (1225, -225), (1323, -27), (1875, -147), (3375, 2401), (3969, -1225), (3969, -125),
   (9375, 1029), (10125, -125), (15625, -1701), (50625, -3969), (59535, 1),
   (540225, -2401), (688905, -5), (4782969, 4375), (24310125, -10125)]

/-- **[BB16] Theorem 7.2** (the main theorem of the paper).  The only primitive solutions to
`x + y = zⁿ` with `x, y` `{3,5,7}`-units and `x > |y| > 0` have `(x, y)` in the list `pairs357`.
Since `2 ∉ {3,5,7}`, `finite_primitiveSolution_iff` predicts a finite list — and it is.

Recorded as a cited `axiom`: the proof combines Lemmas 7.3/7.4 (primitive divisors of `xⁿ + yⁿ`),
Propositions 7.5/7.6, Table 1 of admissible `(δ₃, δ₅, δ₇)`-levels, `(n,n,2)`/`(n,n,3)`/`(n,n,n)`
Frey–Hellegouarch curves with newform computations at levels up to `19845`, local sieving at
auxiliary primes, and degree-5 Thue–Mahler solving; the authors describe it as "approaching the
limits of current off-the-shelf technology". -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
axiom primitive_three_five_seven {x y z : ℤ} {n : ℕ}
    (h : IsPrimitiveSolution {3, 5, 7} x y z n) (hxy : |y| < x) :
    (x, y) ∈ pairs357

/-- The `{3,5,7}` table augmented with the base and exponent, `(x, y, z, n)`.  [BB16] Theorem 7.2
lists only the pairs `(x, y)`; the `(z, n)` here are **computed in this repository**, not quoted
from the paper (each `x + y` is a perfect power, in exactly one way once `gcd(x, y)` is required
`n`-th power free).  Its purpose is to certify the pair table: see `powers357_sound` and
`powers357_pairs`. -/
@[category API, AMS 11, ref "BB16", group "bb16_sunit_powers"]
def powers357 : List (ℤ × ℤ × ℤ × ℕ) :=
  [(3, 1, 2, 2), (5, -1, 2, 2), (5, 3, 2, 3), (7, -3, 2, 2), (7, 1, 2, 3), (9, -5, 2, 2),
   (9, -1, 2, 3), (9, 7, 4, 2), (15, -7, 2, 3), (15, 1, 4, 2),
   (21, -5, 4, 2), (21, 15, 6, 2), (25, -21, 2, 2), (25, -9, 4, 2), (25, 7, 2, 5),
   (27, 5, 2, 5), (35, -27, 2, 3), (35, -3, 2, 5), (35, 1, 6, 2),
   (49, -45, 2, 2), (49, 15, 4, 3), (63, 1, 4, 3), (81, -49, 2, 5), (105, -5, 10, 2),
   (125, 3, 2, 7), (135, -35, 10, 2), (135, -7, 2, 7),
   (147, -3, 12, 2), (175, 21, 14, 2), (175, 81, 16, 2), (189, -125, 4, 3), (189, 7, 14, 2),
   (225, -9, 6, 3), (343, -243, 10, 2),
   (375, -343, 2, 5), (405, -5, 20, 2), (441, -225, 6, 3), (625, -49, 24, 2), (675, 1, 26, 2),
   (729, -245, 22, 2), (1029, -5, 32, 2),
   (1225, -225, 10, 3), (1323, -27, 6, 4), (1875, -147, 12, 3), (3375, 2401, 76, 2),
   (3969, -1225, 14, 3), (3969, -125, 62, 2),
   (9375, 1029, 102, 2), (10125, -125, 10, 4), (15625, -1701, 118, 2), (50625, -3969, 6, 6),
   (59535, 1, 244, 2),
   (540225, -2401, 14, 5), (688905, -5, 830, 2), (4782969, 4375, 2188, 2),
   (24310125, -10125, 30, 5)]

/-- Consistency check: every row of the augmented `{3,5,7}` table satisfies `x + y = zⁿ`.
Proved outright — no cited input. -/
@[category test, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem powers357_sound : ∀ t ∈ powers357, t.1 + t.2.1 = t.2.2.1 ^ t.2.2.2 := by
  intro t ht
  fin_cases ht <;> norm_num

/-- Consistency check: the augmented table projects exactly onto [BB16] Theorem 7.2's pair list,
in the paper's order.  Together with `powers357_sound` this certifies that all 56 transcribed
pairs are genuine sums of two `{3,5,7}`-units equal to a perfect power. -/
@[category test, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem powers357_pairs : powers357.map (fun t => (t.1, t.2.1)) = pairs357 := rfl

/-! ## Consequences for `3`-smooth numbers next to perfect powers

Two Catalan-adjacent corollaries of Theorem 7.1, obtained by taking the second summand to be
`∓1`.  These are exactly the `m = ±1` instances of `plans/report-bugeaud-recent.html` strategy
I.3, and they are complete: no exponent, and no `3`-smooth number, is left unaccounted for. -/

/-- **The only `3`-smooth number one more than a perfect power is `9 = 2³ + 1`.**

If `x` is a `{2,3}`-unit and `x - 1 = zⁿ` with `z ≥ 2` and `n ≥ 2`, then `x = 9`, `z = 2`,
`n = 3`.  Derived from `primitive_two_three` with `y = -1`. -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem sUnit_sub_one_eq_pow {x z : ℤ} {n : ℕ}
    (hx : IsSUnit {2, 3} x) (hn : 2 ≤ n) (hz : 2 ≤ z) (h : x - 1 = z ^ n) :
    x = 9 ∧ z = 2 ∧ n = 3 := by
  have hzpos : (0 : ℤ) < z := by omega
  have h4 : (4 : ℤ) ≤ z ^ n := four_le_pow hz hn
  have hgcd : (Int.gcd x (-1) : ℤ) = 1 := by simp [Int.gcd]
  have hsol : IsPrimitiveSolution ({2, 3} : Finset ℕ) x (-1) z n :=
    { two_le_exp := hn
      sUnit_left := hx
      sUnit_right := isSUnit_neg_one _
      base_ne_zero := by omega
      gcd_powerFree := by rw [hgcd]; exact nthPowerFree_one (by omega)
      sum_eq_pow := by linarith }
  have hxy : |(-1 : ℤ)| ≤ x := by rw [abs_neg, abs_one]; linarith
  rcases primitive_two_three hsol hxy hzpos with hfam | hspor
  · rcases hfam with ⟨_, _, hz1⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ |
      ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ |
      ⟨_, hy1, _⟩ | ⟨_, hx1, hy1, hz1⟩
    · omega
    · norm_num at hy1
    · norm_num at hy1
    · norm_num at hy1
    · have := pow_pos (show (0 : ℤ) < 2 by norm_num) (n - 1); linarith
    · have := pow_pos (show (0 : ℤ) < 2 by norm_num) (n - 2); linarith
    · exfalso
      have := exp_eq_zero_of_two_pow_eq_one (k := n - 1) (by linarith)
      omega
    · have := pow_pos (show (0 : ℤ) < 3 by norm_num) (n - 1); linarith
    · exfalso
      have := exp_eq_zero_of_three_pow_eq_one (k := n - 1) (by linarith)
      omega
    · have := pow_pos (show (0 : ℤ) < 3 by norm_num) (n - 2); linarith
    · have hn3 : n = 3 := by
        have := exp_eq_zero_of_two_pow_eq_one (k := n - 3) (by linarith)
        omega
      subst hn3
      norm_num at hx1
      exact ⟨hx1, hz1, rfl⟩
  · exact absurd rfl (sporadic23_snd_ne_neg_one _ hspor)

/-- **The `3`-smooth numbers one less than a perfect power `zⁿ` (`z ≥ 2`, `n ≥ 2`) are exactly
`3, 8, 24, 48, 288`** — that is, `4 = 2²`, `9 = 3²`, `25 = 5²`, `49 = 7²`, `289 = 17²`.

Derived from `primitive_two_three` with `y = 1`.  Note every witness has `n = 2`: no `3`-smooth
number is one less than a perfect cube or higher power. -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem sUnit_add_one_eq_pow {x z : ℤ} {n : ℕ}
    (hx : IsSUnit {2, 3} x) (hn : 2 ≤ n) (hz : 2 ≤ z) (h : x + 1 = z ^ n) :
    (x = 3 ∧ z = 2 ∧ n = 2) ∨ (x = 8 ∧ z = 3 ∧ n = 2) ∨ (x = 24 ∧ z = 5 ∧ n = 2) ∨
      (x = 48 ∧ z = 7 ∧ n = 2) ∨ (x = 288 ∧ z = 17 ∧ n = 2) := by
  have hzpos : (0 : ℤ) < z := by omega
  have h4 : (4 : ℤ) ≤ z ^ n := four_le_pow hz hn
  have hgcd : (Int.gcd x 1 : ℤ) = 1 := by simp [Int.gcd]
  have hsol : IsPrimitiveSolution ({2, 3} : Finset ℕ) x 1 z n :=
    { two_le_exp := hn
      sUnit_left := hx
      sUnit_right := isSUnit_one _
      base_ne_zero := by omega
      gcd_powerFree := by rw [hgcd]; exact nthPowerFree_one (by omega)
      sum_eq_pow := by linarith }
  have hxy : |(1 : ℤ)| ≤ x := by rw [abs_one]; linarith
  rcases primitive_two_three hsol hxy hzpos with hfam | hspor
  · rcases hfam with ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ |
      ⟨_, hy1, _⟩ | ⟨hx1, hy1, hz1⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ | ⟨_, hy1, _⟩ |
      ⟨hx1, hy1, hz1⟩ | ⟨_, _, hy1, _⟩
    · norm_num at hy1
    · norm_num at hy1
    · norm_num at hy1
    · norm_num at hy1
    · exfalso
      have := exp_eq_zero_of_two_pow_eq_one (k := n - 1) hy1.symm
      omega
    · have hn2 : n = 2 := by
        have := exp_eq_zero_of_two_pow_eq_one (k := n - 2) hy1.symm
        omega
      subst hn2
      norm_num at hx1
      exact Or.inl ⟨hx1, hz1, rfl⟩
    · exfalso
      have := pow_pos (show (0 : ℤ) < 2 by norm_num) (n - 1); linarith
    · exfalso
      have := exp_eq_zero_of_three_pow_eq_one (k := n - 1) hy1.symm
      omega
    · exfalso
      have := pow_pos (show (0 : ℤ) < 3 by norm_num) (n - 1); linarith
    · have hn2 : n = 2 := by
        have := exp_eq_zero_of_three_pow_eq_one (k := n - 2) hy1.symm
        omega
      subst hn2
      norm_num at hx1
      exact Or.inr (Or.inl ⟨hx1, hz1, rfl⟩)
    · exfalso
      have := pow_pos (show (0 : ℤ) < 2 by norm_num) (n - 3); linarith
  · rcases sporadic23_snd_eq_one _ hspor rfl with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩)))

/-- Fully explicit form of `sUnit_sub_one_eq_pow`: `2^a·3^b − 1 = zⁿ` with `z ≥ 2`, `n ≥ 2`
forces `2^a·3^b = 9`, `z = 2`, `n = 3`. -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem three_smooth_sub_one_eq_pow {a b : ℕ} {z : ℤ} {n : ℕ}
    (hn : 2 ≤ n) (hz : 2 ≤ z) (h : (2 : ℤ) ^ a * 3 ^ b - 1 = z ^ n) :
    (2 : ℤ) ^ a * 3 ^ b = 9 ∧ z = 2 ∧ n = 3 :=
  sUnit_sub_one_eq_pow (isSUnit_two_three_pow a b) hn hz h

/-- Fully explicit form of `sUnit_add_one_eq_pow`. -/
@[category research solved, AMS 11, ref "BB16", group "bb16_sunit_powers"]
theorem three_smooth_add_one_eq_pow {a b : ℕ} {z : ℤ} {n : ℕ}
    (hn : 2 ≤ n) (hz : 2 ≤ z) (h : (2 : ℤ) ^ a * 3 ^ b + 1 = z ^ n) :
    ((2 : ℤ) ^ a * 3 ^ b = 3 ∧ z = 2 ∧ n = 2) ∨ ((2 : ℤ) ^ a * 3 ^ b = 8 ∧ z = 3 ∧ n = 2) ∨
      ((2 : ℤ) ^ a * 3 ^ b = 24 ∧ z = 5 ∧ n = 2) ∨ ((2 : ℤ) ^ a * 3 ^ b = 48 ∧ z = 7 ∧ n = 2) ∨
      ((2 : ℤ) ^ a * 3 ^ b = 288 ∧ z = 17 ∧ n = 2) :=
  sUnit_add_one_eq_pow (isSUnit_two_three_pow a b) hn hz h

end BB16
