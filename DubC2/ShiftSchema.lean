/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.DubickasWord
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Divisor sets on intervals of real shifts: `3/2` and `4/3` with `{2,3}`, `5/2` with `{2,5}`, `6/5` with `{2,3,5}`

Milestone M1 of `plans/plan-dubC2-transform.html` (lane α, the seed schema `𝒮₋₁`), in the form
the exact `ν`-sweep `DubC2/xresfree.py` found: not a statement at one shift, but at **every real
shift `ν ∈ [4/3, 17/3]`**, and then by `6`-periodicity on that arc of the shift circle `ℝ/6ℤ`.

> **Theorem.**  For every real `ξ ≠ 0` and every real `ν` with `4/3 ≤ ν − 6k ≤ 17/3` for some
> integer `k`, infinitely many of the integers `⌊ξ(3/2)ⁿ + ν⌋` are divisible by `2` or by `3`.

At `ν = −1` (i.e. `k = −1`) this is the atlas cell `DubC2.Atlas.b3_2_num1_P2_3` without kernel
data: `⌊ξ(3/2)ⁿ⌋` is odd or `≡ 1 (mod 3)` infinitely often.

## Why no certificate data is needed

Both primes divide `pq = 6`, so avoiding them constrains only the **carry**
`sₙ = 2x_{n+1} − 3xₙ`: `xₙ` odd forces `sₙ` odd, and `3 ∤ x_{n+1}` forces `3 ∤ sₙ`
(`carry_dvd_iff_of_dvd_left`, `carry_dvd_iff_of_dvd_right`, any base: `eventually_avoids_iff`).
The residues carry no further information, and what is left is the
one-dimensional system `2y_{n+1} = 3yₙ − sₙ − ν` on `[0,1)` with letters `±1 (mod 6)` in
the open window `(−2 − ν, 3 − ν)` (`carry_bounds`).  Across `[4/3, 17/3]` it has five regimes:

| `ν` | letters | mechanism |
|---|---|---|
| `[4/3, 2)` | `−1, 1` | after a `1` the orbit sits below the fixed point `ν − 1` of the `−1` branch, which forces `−1` forever |
| `[2, 3]` | `−1` | one letter |
| `(3, 4)` | `−5, −1` | neither letter can repeat: the word alternates |
| `[4, 5]` | `−5` | one letter |
| `(5, 17/3]` | `−7, −5` | after a `−7` the orbit sits above the fixed point `ν − 5` of the `−5` branch, which forces `−5` forever |

In every regime the carry word is eventually periodic, which [DN05] Lemma 2
(`Z32.not_isEventuallyPeriodic_carry`, proved for every shift) forbids.  The endpoints are sharp
for this mechanism: `4/3` is where the image `[0, 1 − ν/2)` of the letter `1` stops lying below
`ν − 1`, and `17/3` is its mirror under `ν ↦ 1 − ν (mod 6)`.

## What is *not* claimed

On the complementary arc `(−1/3, 4/3)` the sweep measures positive entropy of the carry-word
model, so no residue×cell certificate exists there at any cell count; that is a statement about
the method, not about `ξ`.  At `ν = 0` the set `{2,3}` contains `{2}`, which is Mahler's question
([Dub06eo]) and is fenced off (`ObsAtlas.b3_2_nu0_killed`).

## Main results

* `DubC2.Schema.eventually_avoids_iff`, `DubC2.Schema.frequently_dvd_of_letters` — **any base**
  `p/q` (coprime, `p > q ≥ 2`) and any finite set `𝒫` of primes dividing `pq`: eventual avoidance
  of `𝒫` by the orbit is eventual avoidance by the carry letters (equivalently, letters coprime
  to `∏𝒫`, `isCoprime_prod_iff`), so unavoidability follows once every such letter word is
  eventually periodic.  `carry_window` is the general alphabet window.
* `DubC2.Schema.carry_eventually_periodic` — carry letters avoiding `{2,3}` from some point on
  make the word eventually periodic, for every `ν ∈ [4/3, 17/3]`.
* `DubC2.Schema.three_halves_two_three` — the theorem, for `ν ∈ [4/3, 17/3]`.
* `DubC2.Schema.three_halves_two_three_circle` — the same on the arc `[4/3, 17/3] + 6ℤ`.
* `DubC2.Schema.three_halves_minus_one` — the atlas cell `ν = −1`, data-free.
* `DubC2.Schema.four_thirds_two_three` — the same mechanism at `4/3`, on the two clean arcs
  `ν ∈ [3/2, 2] ∪ [5, 11/2]`; `DubC2.Schema.four_thirds_minus_one` — its atlas cell `ν = −1`.
  (Between the arcs the sweep finds a fractal pattern of certified and positive-entropy shifts,
  not formalized.)
* `DubC2.Schema.five_halves_two_five` — `{2,5}` is unavoidable for `⌊ξ(5/2)ⁿ + ν⌋` at every real
  `ν ∈ [8/5, 5/3] ∪ [8/3, 41/15] + (10/3)ℤ` (two mirror fixed-point traps; the period is
  `∏𝒫/(p−q) = 10/3` because translating `3ν` by `10` only relabels the letters).  At `ν = −1`
  the minimal set is `{2,3,5}` ([DN05] Theorem 3).
* `DubC2.Schema.six_fifths_two_three_five` — `{2,3,5}` for `⌊ξ(6/5)ⁿ + ν⌋` at every real
  `ν ∈ [−1, −2/3] + 30ℤ`; `six_fifths_minus_one` is the atlas cell, i.e. [Nov12] Theorem 1.4
  re-proved without certificate data.  Mechanism: at most one letter `−1`, else a `6/5`
  divergence from the fixed point `1 + ν`.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Lemma 2.
* [Nov12] A. Novikas, *Composite numbers in the sequences of integers*, doctoral dissertation,
  Vilnius University, 2012.
* [Dub06eo] A. Dubickas, *Even and odd integral parts of powers of a real number*, Glasgow Math. J.
  **48** (2006), 331–336.
-/

namespace DubC2.Schema

open Filter Z32 ForMathlib.SubwordComplexity

variable {ξ ν : ℝ}

/-! ## Residue-free cells in any base

For coprime `p > q` and a set `𝒫` of primes each dividing `pq`, avoidance of `𝒫` by the orbit
is exactly coprimality of the carry letters to `∏𝒫` (`eventually_avoids_iff`,
`isCoprime_prod_iff`), so the certificate reduces to the one-dimensional system
`q y_{n+1} = p yₙ − sₙ − (p−q)ν` with letters in the window `carry_window`. -/

section ResidueFree

variable {p q : ℕ}

/-- A prime `ℓ ∣ p` (so `ℓ ∤ q`) divides the letter `sₙ = q x_{n+1} − p xₙ` iff it divides
`x_{n+1}`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem carry_dvd_iff_of_dvd_left {ℓ : ℕ} (hℓ : ℓ.Prime) (hcop : Nat.Coprime p q) (hl : ℓ ∣ p)
    (n : ℕ) : (ℓ : ℤ) ∣ carry p q ξ ν n ↔ (ℓ : ℤ) ∣ xInt p q ξ ν (n + 1) := by
  have hpr : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hq : ¬ (ℓ : ℤ) ∣ q := by
    rw [Int.natCast_dvd_natCast]
    exact fun h => hℓ.one_lt.ne' (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hl h))
  have hp : (ℓ : ℤ) ∣ (p : ℤ) * xInt p q ξ ν n :=
    dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hl) _
  rw [carry, dvd_sub_left hp, hpr.dvd_mul]
  exact or_iff_right hq

/-- A prime `ℓ ∣ q` (so `ℓ ∤ p`) divides the letter `sₙ` iff it divides `xₙ`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem carry_dvd_iff_of_dvd_right {ℓ : ℕ} (hℓ : ℓ.Prime) (hcop : Nat.Coprime p q) (hl : ℓ ∣ q)
    (n : ℕ) : (ℓ : ℤ) ∣ carry p q ξ ν n ↔ (ℓ : ℤ) ∣ xInt p q ξ ν n := by
  have hpr : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ p := by
    rw [Int.natCast_dvd_natCast]
    exact fun h => hℓ.one_lt.ne' (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hl))
  have hq : (ℓ : ℤ) ∣ (q : ℤ) * xInt p q ξ ν (n + 1) :=
    dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hl) _
  rw [carry, dvd_sub_right hq, hpr.dvd_mul]
  exact or_iff_right hp

/-- For a set of primes, being coprime to `∏𝒫` is avoiding every `ℓ ∈ 𝒫`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem isCoprime_prod_iff {P : Finset ℕ} (hP : ∀ ℓ ∈ P, ℓ.Prime) (z : ℤ) :
    IsCoprime z (∏ ℓ ∈ P, (ℓ : ℤ)) ↔ ∀ ℓ ∈ P, ¬ (ℓ : ℤ) ∣ z := by
  rw [IsCoprime.prod_right_iff]
  refine forall₂_congr fun ℓ hℓ => ?_
  rw [isCoprime_comm, Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp (hP ℓ hℓ))]

/-- Avoiding a prime `ℓ ∣ pq` at times `n` and `n+1` keeps it out of the letter `sₙ`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem letters_of_avoid {ℓ : ℕ} (hℓ : ℓ.Prime) (hcop : Nat.Coprime p q) (hl : ℓ ∣ p * q)
    {n : ℕ} (h0 : ¬ (ℓ : ℤ) ∣ xInt p q ξ ν n) (h1 : ¬ (ℓ : ℤ) ∣ xInt p q ξ ν (n + 1)) :
    ¬ (ℓ : ℤ) ∣ carry p q ξ ν n := by
  rcases (Nat.Prime.dvd_mul hℓ).mp hl with h | h
  · rwa [carry_dvd_iff_of_dvd_left hℓ hcop h]
  · rwa [carry_dvd_iff_of_dvd_right hℓ hcop h]

/-- Conversely, a prime `ℓ ∣ pq` missing from the letters `sₙ, s_{n+1}` misses `x_{n+1}`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem avoid_of_letters {ℓ : ℕ} (hℓ : ℓ.Prime) (hcop : Nat.Coprime p q) (hl : ℓ ∣ p * q)
    {n : ℕ} (h0 : ¬ (ℓ : ℤ) ∣ carry p q ξ ν n) (h1 : ¬ (ℓ : ℤ) ∣ carry p q ξ ν (n + 1)) :
    ¬ (ℓ : ℤ) ∣ xInt p q ξ ν (n + 1) := by
  rcases (Nat.Prime.dvd_mul hℓ).mp hl with h | h
  · rwa [← carry_dvd_iff_of_dvd_left hℓ hcop h]
  · rwa [← carry_dvd_iff_of_dvd_right hℓ hcop h]

/-- **Residue-free cells, any base.**  If every prime of `𝒫` divides `pq` (`gcd(p,q) = 1`), the
orbit `⌊ξ(p/q)ⁿ + ν⌋` eventually avoids `𝒫` iff the carry word eventually avoids `𝒫`: the
residues carry no information beyond the letters. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem eventually_avoids_iff (hcop : Nat.Coprime p q) {P : Finset ℕ}
    (hP : ∀ ℓ ∈ P, ℓ.Prime ∧ ℓ ∣ p * q) :
    (∀ᶠ n in atTop, ∀ ℓ ∈ P, ¬ (ℓ : ℤ) ∣ xInt p q ξ ν n) ↔
      ∀ᶠ n in atTop, ∀ ℓ ∈ P, ¬ (ℓ : ℤ) ∣ carry p q ξ ν n := by
  simp only [eventually_atTop]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn ℓ hℓ => letters_of_avoid (hP ℓ hℓ).1 hcop (hP ℓ hℓ).2
      (hN n hn ℓ hℓ) (hN (n + 1) (by omega) ℓ hℓ)⟩
  · rintro ⟨N, hN⟩
    refine ⟨N + 1, fun n hn ℓ hℓ => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ n by omega)
    exact avoid_of_letters (hP ℓ hℓ).1 hcop (hP ℓ hℓ).2
      (hN m (by omega) ℓ hℓ) (hN (m + 1) (by omega) ℓ hℓ)

/-- The alphabet window `−q − (p−q)ν < sₙ < p − (p−q)ν` ([Dub09AA] (3)). -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem carry_window (hp : 0 < p) (hq : 0 < q) (n : ℕ) :
    -(q : ℝ) - ((p : ℝ) - q) * ν < carry p q ξ ν n ∧
      (carry p q ξ ν n : ℝ) < p - ((p : ℝ) - q) * ν := by
  have h := carry_eq (p := p) (q := q) (ξ := ξ) (ν := ν) hq n
  have h0 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := ν) n
  have h1 := yFract_lt_one (p := p) (q := q) (ξ := ξ) (ν := ν) n
  have h2 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := ν) (n + 1)
  have h3 := yFract_lt_one (p := p) (q := q) (ξ := ξ) (ν := ν) (n + 1)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  constructor <;> nlinarith

/-- **The residue-free schema.**  To show that `𝒫` (primes dividing `pq`) is unavoidable for
`⌊ξ(p/q)ⁿ + ν⌋`, `q ≥ 2`, it suffices that every carry word whose letters from some point on
avoid `𝒫` is eventually periodic: [DN05] Lemma 2 does the rest. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem frequently_dvd_of_letters (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hξ : ξ ≠ 0) {P : Finset ℕ} (hP : ∀ ℓ ∈ P, ℓ.Prime ∧ ℓ ∣ p * q)
    (h : ∀ N, (∀ n, N ≤ n → ∀ ℓ ∈ P, ¬ (ℓ : ℤ) ∣ carry p q ξ ν n) →
      IsEventuallyPeriodic (carry p q ξ ν)) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ P, (ℓ : ℤ) ∣ xInt p q ξ ν n := by
  by_contra hc
  rw [not_frequently] at hc
  have hc' : ∀ᶠ n in atTop, ∀ ℓ ∈ P, ¬ (ℓ : ℤ) ∣ xInt p q ξ ν n :=
    hc.mono fun n hn ℓ hℓ hd => hn ⟨ℓ, hℓ, hd⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((eventually_avoids_iff hcop hP).mp hc')
  exact not_isEventuallyPeriodic_carry hq hpq hcop hξ (h N hN)

end ResidueFree

/-! ## Base `3/2`: the arithmetic side -/

theorem carry_def (n : ℕ) :
    carry 3 2 ξ ν n = 2 * xInt 3 2 ξ ν (n + 1) - 3 * xInt 3 2 ξ ν n := by
  simp [carry]

/-! ## The archimedean side -/

/-- [Dub09AA] (3) at `p/q = 3/2`: `sₙ = 3yₙ − 2y_{n+1} − ν`. -/
theorem carry_eq' (n : ℕ) :
    (carry 3 2 ξ ν n : ℝ) = 3 * yFract 3 2 ξ ν n - 2 * yFract 3 2 ξ ν (n + 1) - ν := by
  have h := carry_eq (p := 3) (q := 2) (ξ := ξ) (ν := ν) (by norm_num) n
  norm_num at h
  linarith

/-- The alphabet window `−2 − ν < sₙ < 3 − ν`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem carry_bounds (n : ℕ) :
    -2 - ν < (carry 3 2 ξ ν n : ℝ) ∧ (carry 3 2 ξ ν n : ℝ) < 3 - ν := by
  have h := carry_window (p := 3) (q := 2) (ξ := ξ) (ν := ν) (by norm_num) (by norm_num) n
  norm_num at h
  exact h

/-! ## The five regimes -/

section Regimes

variable {N : ℕ}

local notation "c" => carry 3 2 ξ ν
local notation "y" => yFract 3 2 ξ ν

/-- An eventually-period-`2` word is eventually periodic. -/
theorem isEventuallyPeriodic_of_two {u : ℕ → ℤ} (h : ∀ n, N ≤ n → u (n + 2) = u n) :
    IsEventuallyPeriodic u :=
  ⟨N, 2, by norm_num, h⟩

/-- An eventually constant word is eventually periodic. -/
theorem isEventuallyPeriodic_of_const {u : ℕ → ℤ} {a : ℤ} (h : ∀ n, N ≤ n → u n = a) :
    IsEventuallyPeriodic u :=
  ⟨N, 1, by norm_num, fun n hn => by rw [h n hn, h (n + 1) (by omega)]⟩

/-- Regime `[4/3, 2)`, letters `−1, 1`: after a `1` the word is `(−1)^∞`. -/
theorem regime_one (hν : 4 / 3 ≤ ν) (hν' : ν < 2)
    (hL : ∀ n, N ≤ n → c n = -1 ∨ c n = 1) : IsEventuallyPeriodic c := by
  by_cases hex : ∃ n, N ≤ n ∧ c n = 1
  · obtain ⟨n₀, hn₀, h1⟩ := hex
    -- after the `1`, the orbit is below `ν − 1`
    have hstart : y (n₀ + 1) < ν - 1 := by
      have h := carry_eq' (ξ := ξ) (ν := ν) n₀
      have hy := yFract_lt_one (p := 3) (q := 2) (ξ := ξ) (ν := ν) n₀
      rw [h1] at h; push_cast at h
      linarith
    -- below `ν − 1` the letter is `−1` and the orbit stays below `ν − 1`
    have hstep : ∀ k, n₀ + 1 ≤ k → y k < ν - 1 → c k = -1 ∧ y (k + 1) < ν - 1 := by
      intro k hk hyk
      have h := carry_eq' (ξ := ξ) (ν := ν) k
      have hy0 := yFract_nonneg (p := 3) (q := 2) (ξ := ξ) (ν := ν) (k + 1)
      rcases hL k (by omega) with hc | hc
      · rw [hc] at h; push_cast at h
        exact ⟨hc, by linarith⟩
      · rw [hc] at h; push_cast at h
        exfalso; linarith
    have hall : ∀ j, y (n₀ + 1 + j) < ν - 1 := by
      intro j
      induction j with
      | zero => simpa using hstart
      | succ j ih =>
        have := (hstep (n₀ + 1 + j) (by omega) ih).2
        simpa [Nat.add_assoc] using this
    refine isEventuallyPeriodic_of_const (N := n₀ + 1) (a := -1) fun k hk => ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact (hstep _ hk (hall j)).1
  · push Not at hex
    refine isEventuallyPeriodic_of_const (N := N) (a := -1) fun n hn => ?_
    rcases hL n hn with h | h
    · exact h
    · exact absurd h (hex n hn)

/-- Regime `(3, 4)`, letters `−5, −1`: no letter repeats, so the word alternates. -/
theorem regime_three (hν : 3 < ν) (hν' : ν < 4)
    (hL : ∀ n, N ≤ n → c n = -5 ∨ c n = -1) : IsEventuallyPeriodic c := by
  have hne : ∀ n, N ≤ n → c (n + 1) ≠ c n := by
    intro n hn heq
    have h := carry_eq' (ξ := ξ) (ν := ν) n
    have h' := carry_eq' (ξ := ξ) (ν := ν) (n + 1)
    have a0 := yFract_nonneg (p := 3) (q := 2) (ξ := ξ) (ν := ν) n
    have a1 := yFract_lt_one (p := 3) (q := 2) (ξ := ξ) (ν := ν) n
    have b0 := yFract_nonneg (p := 3) (q := 2) (ξ := ξ) (ν := ν) (n + 1)
    have b1 := yFract_lt_one (p := 3) (q := 2) (ξ := ξ) (ν := ν) (n + 1)
    have c0 := yFract_nonneg (p := 3) (q := 2) (ξ := ξ) (ν := ν) (n + 2)
    have c1 := yFract_lt_one (p := 3) (q := 2) (ξ := ξ) (ν := ν) (n + 2)
    rw [heq] at h'
    rcases hL n hn with hc | hc
    · rw [hc] at h h'; push_cast at h h'; linarith
    · rw [hc] at h h'; push_cast at h h'; linarith
  refine isEventuallyPeriodic_of_two (N := N) fun n hn => ?_
  have h1 := hne n hn
  have h2 := hne (n + 1) (by omega)
  rw [show n + 1 + 1 = n + 2 by omega] at h2
  rcases hL n hn with a | a <;> rcases hL (n + 1) (by omega) with b | b <;>
    rcases hL (n + 2) (by omega) with d | d <;> omega

/-- Regime `(5, 17/3]`, letters `−7, −5`: after a `−7` the word is `(−5)^∞`. -/
theorem regime_five (hν : 5 < ν) (hν' : ν ≤ 17 / 3)
    (hL : ∀ n, N ≤ n → c n = -7 ∨ c n = -5) : IsEventuallyPeriodic c := by
  by_cases hex : ∃ n, N ≤ n ∧ c n = -7
  · obtain ⟨n₀, hn₀, h7⟩ := hex
    have hstart : ν - 5 ≤ y (n₀ + 1) := by
      have h := carry_eq' (ξ := ξ) (ν := ν) n₀
      have hy := yFract_nonneg (p := 3) (q := 2) (ξ := ξ) (ν := ν) n₀
      rw [h7] at h; push_cast at h
      linarith
    have hstep : ∀ k, n₀ + 1 ≤ k → ν - 5 ≤ y k → c k = -5 ∧ ν - 5 ≤ y (k + 1) := by
      intro k hk hyk
      have h := carry_eq' (ξ := ξ) (ν := ν) k
      have hy1 := yFract_lt_one (p := 3) (q := 2) (ξ := ξ) (ν := ν) (k + 1)
      rcases hL k (by omega) with hc | hc
      · rw [hc] at h; push_cast at h
        exfalso; linarith
      · rw [hc] at h; push_cast at h
        exact ⟨hc, by linarith⟩
    have hall : ∀ j, ν - 5 ≤ y (n₀ + 1 + j) := by
      intro j
      induction j with
      | zero => simpa using hstart
      | succ j ih =>
        have := (hstep (n₀ + 1 + j) (by omega) ih).2
        simpa [Nat.add_assoc] using this
    refine isEventuallyPeriodic_of_const (N := n₀ + 1) (a := -5) fun k hk => ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact (hstep _ hk (hall j)).1
  · push Not at hex
    refine isEventuallyPeriodic_of_const (N := N) (a := -5) fun n hn => ?_
    rcases hL n hn with h | h
    · exact absurd h (hex n hn)
    · exact h

end Regimes

/-! ## Assembly -/

/-- **The carry word is eventually periodic** as soon as its letters avoid `{2,3}` from some point
on, for every real `ν ∈ [4/3, 17/3]`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem carry_eventually_periodic (hν : 4 / 3 ≤ ν) (hν' : ν ≤ 17 / 3) {N : ℕ}
    (hA : ∀ n, N ≤ n → ∀ ℓ ∈ ({2, 3} : Finset ℕ), ¬ (ℓ : ℤ) ∣ carry 3 2 ξ ν n) :
    IsEventuallyPeriodic (carry 3 2 ξ ν) := by
  -- the admissible letters: odd, prime to `3`, inside the window
  have hlet : ∀ n, N ≤ n → ¬ (2 : ℤ) ∣ carry 3 2 ξ ν n ∧ ¬ (3 : ℤ) ∣ carry 3 2 ξ ν n :=
    fun n hn => ⟨by exact_mod_cast hA n hn 2 (by simp), by exact_mod_cast hA n hn 3 (by simp)⟩
  have hb := carry_bounds (ξ := ξ) (ν := ν)
  -- integer forms of the window at a rational bound
  have lo : ∀ n (r : ℤ), (r : ℝ) ≤ -2 - ν → r < carry 3 2 ξ ν n := fun n r hr => by
    have := (hb n).1; exact_mod_cast (show (r : ℝ) < carry 3 2 ξ ν n by linarith)
  have hi : ∀ n (r : ℤ), 3 - ν ≤ (r : ℝ) → carry 3 2 ξ ν n < r := fun n r hr => by
    have := (hb n).2; exact_mod_cast (show (carry 3 2 ξ ν n : ℝ) < r by linarith)
  rcases lt_or_ge ν 2 with h2 | h2
  · -- `[4/3, 2)`: letters `−1, 1`
    refine regime_one (N := N) hν h2 fun n hn => ?_
    have a := lo n (-4) (by push_cast; linarith)
    have b := hi n 2 (by push_cast; linarith)
    have := hlet n hn; omega
  rcases le_or_gt ν 3 with h3 | h3
  · -- `[2, 3]`: the single letter `−1`
    refine isEventuallyPeriodic_of_const (N := N) (a := -1) fun n hn => ?_
    have a := lo n (-5) (by push_cast; linarith)
    have b := hi n 1 (by push_cast; linarith)
    have := hlet n hn; omega
  rcases lt_or_ge ν 4 with h4 | h4
  · -- `(3, 4)`: letters `−5, −1`
    refine regime_three (N := N) h3 h4 fun n hn => ?_
    have a := lo n (-6) (by push_cast; linarith)
    have b := hi n 0 (by push_cast; linarith)
    have := hlet n hn; omega
  rcases le_or_gt ν 5 with h5 | h5
  · -- `[4, 5]`: the single letter `−5`
    refine isEventuallyPeriodic_of_const (N := N) (a := -5) fun n hn => ?_
    have a := lo n (-7) (by push_cast; linarith)
    have b := hi n (-1) (by push_cast; linarith)
    have := hlet n hn; omega
  · -- `(5, 17/3]`: letters `−7, −5`
    refine regime_five (N := N) h5 hν' fun n hn => ?_
    have a := lo n (-8) (by push_cast; linarith)
    have b := hi n (-2) (by push_cast; linarith)
    have := hlet n hn; omega

/-- **`{2,3}` is unavoidable for `⌊ξ(3/2)ⁿ + ν⌋` at every real shift `ν ∈ [4/3, 17/3]`.** -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem three_halves_two_three (hξ : ξ ≠ 0) (hν : 4 / 3 ≤ ν) (hν' : ν ≤ 17 / 3) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 3 2 ξ ν n ∨ (3 : ℤ) ∣ xInt 3 2 ξ ν n := by
  refine (frequently_dvd_of_letters (p := 3) (q := 2) (by norm_num) (by norm_num) (by norm_num) hξ
    (P := {2, 3}) (by decide) fun _ hA => carry_eventually_periodic hν hν' hA).mono
    fun n h => by simpa using h

/-- An integer shift by `6` translates every term by `6`. -/
theorem xInt_add_six_mul (k : ℤ) (n : ℕ) :
    xInt 3 2 ξ (ν + 6 * k) n = xInt 3 2 ξ ν n + 6 * k := by
  simp only [xInt, orb]
  rw [← add_assoc, show (6 : ℝ) * k = ((6 * k : ℤ) : ℝ) by push_cast; ring, Int.floor_add_intCast]

/-- **The arc of the shift circle `ℝ/6ℤ`.**  If `ν − 6k ∈ [4/3, 17/3]` for some integer `k`, then
for every real `ξ ≠ 0` infinitely many `⌊ξ(3/2)ⁿ + ν⌋` are divisible by `2` or by `3`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem three_halves_two_three_circle (hξ : ξ ≠ 0) (k : ℤ) (hν : 4 / 3 ≤ ν - 6 * k)
    (hν' : ν - 6 * k ≤ 17 / 3) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 3 2 ξ ν n ∨ (3 : ℤ) ∣ xInt 3 2 ξ ν n := by
  refine (three_halves_two_three (ν := ν - 6 * k) hξ hν hν').mono fun n hn => ?_
  have h := xInt_add_six_mul (ξ := ξ) (ν := ν - 6 * k) k n
  rw [sub_add_cancel] at h
  rw [h]
  rcases hn with h2 | h3
  · left; exact dvd_add h2 (Dvd.intro (3 * k) (by ring))
  · right; exact dvd_add h3 (Dvd.intro (2 * k) (by ring))

/-- **The atlas cell `(3/2, ν = −1, {2,3})`, data-free**: for every real `ξ ≠ 0`,
`⌊ξ(3/2)ⁿ⌋` is odd or `≡ 1 (mod 3)` infinitely often (stated as `2 ∣ x` or `3 ∣ x` for
`x = ⌊ξ(3/2)ⁿ − 1⌋`). -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem three_halves_minus_one (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 3 2 ξ (-1) n ∨ (3 : ℤ) ∣ xInt 3 2 ξ (-1) n :=
  three_halves_two_three_circle hξ (-1) (by norm_num) (by norm_num)

/-! ## Base `4/3`: the two clean arcs `[3/2, 2]` and `[5, 11/2]`

At `4/3` both primes again divide `pq = 12`: `2 ∣ p`, `3 ∣ q`.  The windows of the letters now
**overlap** (each has length `3/4`, letters are `2` apart), so a letter is not a function of `y`;
what replaces the fixed-point trap of `3/2` is a divergence: past the fixed point of the main
branch *both* branches push the orbit away by a factor `≥ 4/3`, and `y` cannot leave `[0,1)`. -/

/-- Expansion by `4/3` against a bound is impossible. -/
theorem no_expansion {d : ℕ → ℝ} {k₀ : ℕ} {B : ℝ} (h0 : 0 < d k₀)
    (hstep : ∀ k, k₀ ≤ k → (4 / 3 : ℝ) * d k ≤ d (k + 1)) (hB : ∀ k, k₀ ≤ k → d k ≤ B) :
    False := by
  have hpow : ∀ j, (4 / 3 : ℝ) ^ j * d k₀ ≤ d (k₀ + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hstep (k₀ + j) (by omega)
      rw [pow_succ, ← Nat.add_assoc]
      nlinarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / d k₀) (by norm_num : (1 : ℝ) < 4 / 3)
  have := hpow j
  have := hB (k₀ + j) (by omega)
  rw [div_lt_iff₀ h0] at hj
  linarith

theorem carry_def4 (n : ℕ) :
    carry 4 3 ξ ν n = 3 * xInt 4 3 ξ ν (n + 1) - 4 * xInt 4 3 ξ ν n := by
  simp [carry]

/-- `sₙ = 4yₙ − 3y_{n+1} − ν` at `4/3`. -/
theorem carry_eq4 (n : ℕ) :
    (carry 4 3 ξ ν n : ℝ) = 4 * yFract 4 3 ξ ν n - 3 * yFract 4 3 ξ ν (n + 1) - ν := by
  have h := carry_eq (p := 4) (q := 3) (ξ := ξ) (ν := ν) (by norm_num) n
  norm_num at h
  linarith

section FourThirds

local notation "c" => carry 4 3 ξ ν
local notation "y" => yFract 4 3 ξ ν

/-- **The carry word at `4/3` is eventually periodic** when its letters avoid `{2,3}` from
some point on, for every real `ν ∈ [3/2, 2] ∪ [5, 11/2]`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem carry_eventually_periodic4 (hν : (3 / 2 ≤ ν ∧ ν ≤ 2) ∨ (5 ≤ ν ∧ ν ≤ 11 / 2)) {N : ℕ}
    (hA : ∀ n, N ≤ n → ∀ ℓ ∈ ({2, 3} : Finset ℕ), ¬ (ℓ : ℤ) ∣ c n) : IsEventuallyPeriodic c := by
  have hlet : ∀ n, N ≤ n → ¬ (2 : ℤ) ∣ c n ∧ ¬ (3 : ℤ) ∣ c n :=
    fun n hn => ⟨by exact_mod_cast hA n hn 2 (by simp), by exact_mod_cast hA n hn 3 (by simp)⟩
  have hy0 : ∀ k, 0 ≤ y k := fun k => yFract_nonneg (p := 4) (q := 3) (ξ := ξ) (ν := ν) k
  have hy1 : ∀ k, y k < 1 := fun k => yFract_lt_one (p := 4) (q := 3) (ξ := ξ) (ν := ν) k
  have hb : ∀ n, -3 - ν < (c n : ℝ) ∧ (c n : ℝ) < 4 - ν := fun n => by
    have := carry_eq4 (ξ := ξ) (ν := ν) n
    have := hy0 n; have := hy1 n; have := hy0 (n + 1); have := hy1 (n + 1)
    constructor <;> linarith
  rcases hν with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `[3/2, 2]`: letters `−1, 1`; a `1` puts the orbit below `ν − 1`, where it diverges
    have hL : ∀ n, N ≤ n → c n = -1 ∨ c n = 1 := fun n hn => by
      have a : (-5 : ℤ) < c n := by
        have := (hb n).1; exact_mod_cast (show ((-5 : ℤ) : ℝ) < c n by push_cast; linarith)
      have b : c n < 3 := by
        have := (hb n).2; exact_mod_cast (show (c n : ℝ) < ((3 : ℤ) : ℝ) by push_cast; linarith)
      have := hlet n hn; omega
    by_cases hex : ∃ n, N ≤ n ∧ c n = 1
    · exfalso
      obtain ⟨n₀, hn₀, hc1⟩ := hex
      refine no_expansion (d := fun k => ν - 1 - y k) (k₀ := n₀ + 1) (B := 1) ?_ ?_ ?_
      · have h := carry_eq4 (ξ := ξ) (ν := ν) n₀
        rw [hc1] at h; push_cast at h
        have := hy1 n₀
        show 0 < ν - 1 - y (n₀ + 1)
        linarith
      · intro k hk
        have h := carry_eq4 (ξ := ξ) (ν := ν) k
        show (4 / 3 : ℝ) * (ν - 1 - y k) ≤ ν - 1 - y (k + 1)
        rcases hL k (by omega) with hc | hc <;> rw [hc] at h <;> push_cast at h <;> linarith
      · intro k _
        have := hy0 k
        show ν - 1 - y k ≤ 1
        linarith
    · push Not at hex
      refine isEventuallyPeriodic_of_const (N := N) (a := -1) fun n hn => ?_
      rcases hL n hn with h | h
      · exact h
      · exact absurd h (hex n hn)
  · -- `[5, 11/2]`: letters `−7, −5`; a second `−7` puts the orbit strictly above `ν − 5`
    have hL : ∀ n, N ≤ n → c n = -7 ∨ c n = -5 := fun n hn => by
      have a : (-9 : ℤ) < c n := by
        have := (hb n).1; exact_mod_cast (show ((-9 : ℤ) : ℝ) < c n by push_cast; linarith)
      have b : c n < -1 := by
        have := (hb n).2; exact_mod_cast (show (c n : ℝ) < ((-1 : ℤ) : ℝ) by push_cast; linarith)
      have := hlet n hn; omega
    -- above `ν − 5` the orbit stays above, expanding
    have hup : ∀ k, N ≤ k → ν - 5 ≤ y k →
        (4 / 3 : ℝ) * (y k - (ν - 5)) ≤ y (k + 1) - (ν - 5) := by
      intro k hk hyk
      have h := carry_eq4 (ξ := ξ) (ν := ν) k
      rcases hL k hk with hc | hc <;> rw [hc] at h <;> push_cast at h <;> linarith
    by_cases hex : ∃ n, N ≤ n ∧ c n = -7
    · obtain ⟨n₀, hn₀, hc7⟩ := hex
      have hstart : ν - 5 ≤ y (n₀ + 1) := by
        have h := carry_eq4 (ξ := ξ) (ν := ν) n₀
        rw [hc7] at h; push_cast at h
        have := hy0 n₀
        linarith
      have habove : ∀ j, ν - 5 ≤ y (n₀ + 1 + j) := by
        intro j
        induction j with
        | zero => simpa using hstart
        | succ j ih =>
          have := hup (n₀ + 1 + j) (by omega) ih
          rw [← Nat.add_assoc]
          nlinarith
      refine isEventuallyPeriodic_of_const (N := n₀ + 2) (a := -5) fun n hn => ?_
      rcases hL n (by omega) with hc | hc
      · exfalso
        -- a second `−7` at `n`: strictly above afterwards, then divergence
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show n₀ + 1 ≤ n by omega)
        have hyn := habove j
        rw [← hj] at hyn
        refine no_expansion (d := fun k => y k - (ν - 5)) (k₀ := n + 1) (B := 1) ?_ ?_ ?_
        · have h := carry_eq4 (ξ := ξ) (ν := ν) n
          rw [hc] at h; push_cast at h
          show 0 < y (n + 1) - (ν - 5)
          linarith
        · intro k hk
          obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show n₀ + 1 ≤ k by omega)
          exact hup _ (by omega) (habove i)
        · intro k _
          have := hy1 k
          show y k - (ν - 5) ≤ 1
          linarith
      · exact hc
    · push Not at hex
      refine isEventuallyPeriodic_of_const (N := N) (a := -5) fun n hn => ?_
      rcases hL n hn with h | h
      · exact absurd h (hex n hn)
      · exact h

end FourThirds

/-- **`{2,3}` is unavoidable for `⌊ξ(4/3)ⁿ + ν⌋` at every real `ν ∈ [3/2, 2] ∪ [5, 11/2]`.** -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem four_thirds_two_three (hξ : ξ ≠ 0)
    (hν : (3 / 2 ≤ ν ∧ ν ≤ 2) ∨ (5 ≤ ν ∧ ν ≤ 11 / 2)) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 4 3 ξ ν n ∨ (3 : ℤ) ∣ xInt 4 3 ξ ν n := by
  refine (frequently_dvd_of_letters (p := 4) (q := 3) (by norm_num) (by norm_num) (by norm_num) hξ
    (P := {2, 3}) (by decide) fun _ hA => carry_eventually_periodic4 hν hA).mono
    fun n h => by simpa using h

/-- An integer shift by `6` translates every term by `6` (base `4/3`). -/
theorem xInt4_add_six_mul (k : ℤ) (n : ℕ) :
    xInt 4 3 ξ (ν + 6 * k) n = xInt 4 3 ξ ν n + 6 * k := by
  simp only [xInt, orb]
  rw [← add_assoc, show (6 : ℝ) * k = ((6 * k : ℤ) : ℝ) by push_cast; ring, Int.floor_add_intCast]

/-- **The atlas cell `(4/3, ν = −1, {2,3})`, data-free** (`−1 = 5 − 6`). -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem four_thirds_minus_one (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 4 3 ξ (-1) n ∨ (3 : ℤ) ∣ xInt 4 3 ξ (-1) n := by
  refine (four_thirds_two_three (ν := 5) hξ (Or.inr ⟨by norm_num, by norm_num⟩)).mono
    fun n hn => ?_
  have h := xInt4_add_six_mul (ξ := ξ) (ν := 5) (-1) n
  norm_num at h
  rw [h]
  rcases hn with h2 | h3
  · left; exact dvd_sub h2 (by norm_num)
  · right; exact dvd_sub h3 (by norm_num)

/-! ## Base `5/2`, `𝒫 = {2,5}`: two mirror arcs per period `10/3`

`2 ∣ q` and `5 ∣ p`, so the letters are prime to `10`.  Write `u = 3ν − 10k`: translating `u` by
`10` only relabels the letters (`s ↦ s − 10`), so everything is stated for `c + 10k`.  On both
arcs the mechanism is the fixed-point trap of `3/2`. -/

/-- Expansion by a factor `r > 1` against a bound is impossible. -/
theorem no_expansion_of {r : ℝ} (hr : 1 < r) {d : ℕ → ℝ} {k₀ : ℕ} {B : ℝ} (h0 : 0 < d k₀)
    (hstep : ∀ k, k₀ ≤ k → r * d k ≤ d (k + 1)) (hB : ∀ k, k₀ ≤ k → d k ≤ B) : False := by
  have hpow : ∀ j, r ^ j * d k₀ ≤ d (k₀ + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hstep (k₀ + j) (by omega)
      rw [pow_succ, ← Nat.add_assoc]
      nlinarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / d k₀) hr
  have := hpow j
  have := hB (k₀ + j) (by omega)
  rw [div_lt_iff₀ h0] at hj
  linarith

theorem carry_def52 (n : ℕ) :
    carry 5 2 ξ ν n = 2 * xInt 5 2 ξ ν (n + 1) - 5 * xInt 5 2 ξ ν n := by
  simp [carry]

/-- `sₙ = 5yₙ − 2y_{n+1} − 3ν` at `5/2`. -/
theorem carry_eq52 (n : ℕ) :
    (carry 5 2 ξ ν n : ℝ) = 5 * yFract 5 2 ξ ν n - 2 * yFract 5 2 ξ ν (n + 1) - 3 * ν := by
  have h := carry_eq (p := 5) (q := 2) (ξ := ξ) (ν := ν) (by norm_num) n
  norm_num at h
  linarith

section FiveHalves

local notation "c" => carry 5 2 ξ ν
local notation "y" => yFract 5 2 ξ ν

/-- **The carry word at `5/2` is eventually periodic** when its letters avoid `{2,5}` from
some point on, for `u = 3ν − 10k ∈ [24/5, 5] ∪ [8, 41/5]`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem carry_eventually_periodic52 (k : ℤ)
    (hν : (24 / 5 ≤ 3 * ν - 10 * k ∧ 3 * ν - 10 * k ≤ 5) ∨
      (8 ≤ 3 * ν - 10 * k ∧ 3 * ν - 10 * k ≤ 41 / 5)) {N : ℕ}
    (hA : ∀ n, N ≤ n → ∀ ℓ ∈ ({2, 5} : Finset ℕ), ¬ (ℓ : ℤ) ∣ c n) :
    IsEventuallyPeriodic c := by
  set u := 3 * ν - 10 * k with hu
  have hlet : ∀ n, N ≤ n → ¬ (2 : ℤ) ∣ c n ∧ ¬ (5 : ℤ) ∣ c n :=
    fun n hn => ⟨by exact_mod_cast hA n hn 2 (by simp), by exact_mod_cast hA n hn 5 (by simp)⟩
  have hy0 : ∀ k, 0 ≤ y k := fun k => yFract_nonneg (p := 5) (q := 2) (ξ := ξ) (ν := ν) k
  have hy1 : ∀ k, y k < 1 := fun k => yFract_lt_one (p := 5) (q := 2) (ξ := ξ) (ν := ν) k
  -- the identity in the relabelled letter `c + 10k`
  have he : ∀ n, ((c n + 10 * k : ℤ) : ℝ) = 5 * y n - 2 * y (n + 1) - u := fun n => by
    have := carry_eq52 (ξ := ξ) (ν := ν) n
    push_cast; rw [hu]; linarith
  have hb : ∀ n, -2 - u < ((c n + 10 * k : ℤ) : ℝ) ∧ ((c n + 10 * k : ℤ) : ℝ) < 5 - u :=
    fun n => by
      have := he n; have := hy0 n; have := hy1 n; have := hy0 (n + 1); have := hy1 (n + 1)
      constructor <;> linarith
  rcases hν with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- letters `−3, −1` (relabelled); after a `−1` the orbit is below `f = (u−3)/3`
    have hL : ∀ n, N ≤ n → c n + 10 * k = -3 ∨ c n + 10 * k = -1 := fun n hn => by
      have a : (-7 : ℤ) < c n + 10 * k := by
        have := (hb n).1
        exact_mod_cast (show ((-7 : ℤ) : ℝ) < ((c n + 10 * k : ℤ) : ℝ) by push_cast at *; linarith)
      have b : c n + 10 * k < 1 := by
        have := (hb n).2
        exact_mod_cast (show ((c n + 10 * k : ℤ) : ℝ) < ((1 : ℤ) : ℝ) by push_cast at *; linarith)
      have := hlet n hn; omega
    have hstep : ∀ m, N ≤ m → y m < (u - 3) / 3 →
        c m + 10 * k = -3 ∧ y (m + 1) < (u - 3) / 3 := by
      intro m hm hym
      have h := he m
      have := hy0 (m + 1)
      rcases hL m hm with hc | hc
      · rw [hc] at h; push_cast at h; exact ⟨hc, by linarith⟩
      · rw [hc] at h; push_cast at h; exfalso; linarith
    by_cases hex : ∃ n, N ≤ n ∧ c n + 10 * k = -1
    · obtain ⟨n₀, hn₀, hc1⟩ := hex
      have hstart : y (n₀ + 1) < (u - 3) / 3 := by
        have h := he n₀
        rw [hc1] at h; push_cast at h
        have := hy1 n₀
        linarith
      have hall : ∀ j, y (n₀ + 1 + j) < (u - 3) / 3 := by
        intro j
        induction j with
        | zero => simpa using hstart
        | succ j ih =>
          have := (hstep (n₀ + 1 + j) (by omega) ih).2
          simpa [Nat.add_assoc] using this
      refine isEventuallyPeriodic_of_const (N := n₀ + 1) (a := -3 - 10 * k) fun m hm => ?_
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      have := (hstep _ (by omega) (hall j)).1
      omega
    · push Not at hex
      refine isEventuallyPeriodic_of_const (N := N) (a := -3 - 10 * k) fun n hn => ?_
      rcases hL n hn with h | h
      · omega
      · exact absurd h (hex n hn)
  · -- letters `−9, −7` (relabelled); after a `−9` the orbit is above `f = (u−7)/3`
    have hL : ∀ n, N ≤ n → c n + 10 * k = -9 ∨ c n + 10 * k = -7 := fun n hn => by
      have a : (-11 : ℤ) < c n + 10 * k := by
        have := (hb n).1
        exact_mod_cast (show ((-11 : ℤ) : ℝ) < ((c n + 10 * k : ℤ) : ℝ) by push_cast at *; linarith)
      have b : c n + 10 * k < -3 := by
        have := (hb n).2
        exact_mod_cast (show ((c n + 10 * k : ℤ) : ℝ) < ((-3 : ℤ) : ℝ) by push_cast at *; linarith)
      have := hlet n hn; omega
    have hstep : ∀ m, N ≤ m → (u - 7) / 3 ≤ y m →
        c m + 10 * k = -7 ∧ (u - 7) / 3 ≤ y (m + 1) := by
      intro m hm hym
      have h := he m
      have := hy1 (m + 1)
      rcases hL m hm with hc | hc
      · rw [hc] at h; push_cast at h; exfalso; linarith
      · rw [hc] at h; push_cast at h; exact ⟨hc, by linarith⟩
    by_cases hex : ∃ n, N ≤ n ∧ c n + 10 * k = -9
    · obtain ⟨n₀, hn₀, hc9⟩ := hex
      have hstart : (u - 7) / 3 ≤ y (n₀ + 1) := by
        have h := he n₀
        rw [hc9] at h; push_cast at h
        have := hy0 n₀
        linarith
      have hall : ∀ j, (u - 7) / 3 ≤ y (n₀ + 1 + j) := by
        intro j
        induction j with
        | zero => simpa using hstart
        | succ j ih =>
          have := (hstep (n₀ + 1 + j) (by omega) ih).2
          simpa [Nat.add_assoc] using this
      refine isEventuallyPeriodic_of_const (N := n₀ + 1) (a := -7 - 10 * k) fun m hm => ?_
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      have := (hstep _ (by omega) (hall j)).1
      omega
    · push Not at hex
      refine isEventuallyPeriodic_of_const (N := N) (a := -7 - 10 * k) fun n hn => ?_
      rcases hL n hn with h | h
      · exact absurd h (hex n hn)
      · omega

end FiveHalves

/-- **`{2,5}` is unavoidable for `⌊ξ(5/2)ⁿ + ν⌋`** at every real `ν` with
`ν − 10k/3 ∈ [8/5, 5/3] ∪ [8/3, 41/15]` for some integer `k`.  (At `ν = −1` the minimal set is
`{2,3,5}`, [DN05] Theorem 3; the two-prime set works on these arcs of the shift circle.) -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_schema"]
theorem five_halves_two_five (hξ : ξ ≠ 0) (k : ℤ)
    (hν : (8 / 5 ≤ ν - 10 * k / 3 ∧ ν - 10 * k / 3 ≤ 5 / 3) ∨
      (8 / 3 ≤ ν - 10 * k / 3 ∧ ν - 10 * k / 3 ≤ 41 / 15)) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 5 2 ξ ν n ∨ (5 : ℤ) ∣ xInt 5 2 ξ ν n := by
  have hν' : (24 / 5 ≤ 3 * ν - 10 * k ∧ 3 * ν - 10 * k ≤ 5) ∨
      (8 ≤ 3 * ν - 10 * k ∧ 3 * ν - 10 * k ≤ 41 / 5) := by
    rcases hν with ⟨a, b⟩ | ⟨a, b⟩
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  refine (frequently_dvd_of_letters (p := 5) (q := 2) (by norm_num) (by norm_num) (by norm_num) hξ
    (P := {2, 5}) (by decide) fun _ hA => carry_eventually_periodic52 k hν' hA).mono
    fun n h => by simpa using h

/-! ## Base `6/5`, `𝒫 = {2,3,5}`: the arc through `ν = −1`

`2, 3 ∣ p` and `5 ∣ q`, so the letters are prime to `30`, and the period of the shift circle is
`30/(p−q) = 30`.  With `u = ν − 30k ∈ [−1, −2/3]` the letters are `±1` (relabelled by `+30k`).
Put `d = y − (1+u)`, measured from the fixed point of the `1` branch: the `1` branch gives
`d' = 6d/5` and the `−1` branch `d' = (6d+2)/5`.  A `−1` lands at `d ≥ 0` (this is `u ≤ −2/3`),
both branches keep `d ≥ 0`, and a second `−1` makes `d > 0`, after which `d` grows by `6/5`
per step while `d < 1`: impossible.  So at most one `−1` occurs, and the word is eventually `1^∞`. -/

theorem carry_def65 (n : ℕ) :
    carry 6 5 ξ ν n = 5 * xInt 6 5 ξ ν (n + 1) - 6 * xInt 6 5 ξ ν n := by
  simp [carry]

/-- `sₙ = 6yₙ − 5y_{n+1} − ν` at `6/5`. -/
theorem carry_eq65 (n : ℕ) :
    (carry 6 5 ξ ν n : ℝ) = 6 * yFract 6 5 ξ ν n - 5 * yFract 6 5 ξ ν (n + 1) - ν := by
  have h := carry_eq (p := 6) (q := 5) (ξ := ξ) (ν := ν) (by norm_num) n
  norm_num at h
  linarith

section SixFifths

local notation "c" => carry 6 5 ξ ν
local notation "y" => yFract 6 5 ξ ν

/-- **The carry word at `6/5` is eventually periodic** when its letters avoid `{2,3,5}` from
some point on, for `ν − 30k ∈ [−1, −2/3]`. -/
@[category research solved, AMS 11 37, ref "DN05" "Nov12", group "dubc2_schema"]
theorem carry_eventually_periodic65 (k : ℤ) (h1 : -1 ≤ ν - 30 * k) (h2 : ν - 30 * k ≤ -2 / 3)
    {N : ℕ} (hA : ∀ n, N ≤ n → ∀ ℓ ∈ ({2, 3, 5} : Finset ℕ), ¬ (ℓ : ℤ) ∣ c n) :
    IsEventuallyPeriodic c := by
  set u := ν - 30 * k with hu
  have hy0 : ∀ k, 0 ≤ y k := fun k => yFract_nonneg (p := 6) (q := 5) (ξ := ξ) (ν := ν) k
  have hy1 : ∀ k, y k < 1 := fun k => yFract_lt_one (p := 6) (q := 5) (ξ := ξ) (ν := ν) k
  have he : ∀ n, ((c n + 30 * k : ℤ) : ℝ) = 6 * y n - 5 * y (n + 1) - u := fun n => by
    have := carry_eq65 (ξ := ξ) (ν := ν) n
    push_cast; rw [hu]; linarith
  have hL : ∀ n, N ≤ n → c n + 30 * k = -1 ∨ c n + 30 * k = 1 := by
    intro n hn
    have a : (-5 : ℤ) < c n + 30 * k := by
      have := he n; have := hy0 n; have := hy1 (n + 1)
      exact_mod_cast (show ((-5 : ℤ) : ℝ) < ((c n + 30 * k : ℤ) : ℝ) by
        rw [he n]; push_cast; linarith)
    have b : c n + 30 * k < 7 := by
      have := hy1 n; have := hy0 (n + 1)
      exact_mod_cast (show ((c n + 30 * k : ℤ) : ℝ) < ((7 : ℤ) : ℝ) by
        rw [he n]; push_cast; linarith)
    have p2 : ¬ (2 : ℤ) ∣ c n := by exact_mod_cast hA n hn 2 (by simp)
    have p3 : ¬ (3 : ℤ) ∣ c n := by exact_mod_cast hA n hn 3 (by simp)
    have p5 : ¬ (5 : ℤ) ∣ c n := by exact_mod_cast hA n hn 5 (by simp)
    have r2 : ¬ (2 : ℤ) ∣ c n + 30 * k := by omega
    have r3 : ¬ (3 : ℤ) ∣ c n + 30 * k := by omega
    have r5 : ¬ (5 : ℤ) ∣ c n + 30 * k := by omega
    generalize c n + 30 * k = C at a b r2 r3 r5 ⊢
    interval_cases C <;> omega
  -- `d = y − (1 + u)`: both branches, from `d ≥ 0`, stay at `d ≥ 0`
  have hd : ∀ m, N ≤ m →
      (c m + 30 * k = 1 → y (m + 1) - (1 + u) = 6 / 5 * (y m - (1 + u))) ∧
      (c m + 30 * k = -1 → y (m + 1) - (1 + u) = (6 * (y m - (1 + u)) + 2) / 5) := by
    intro m _
    have h := he m
    constructor <;> intro hc <;> rw [hc] at h <;> push_cast at h <;> linarith
  by_cases hex : ∃ n, N ≤ n ∧ c n + 30 * k = -1
  · obtain ⟨n₀, hn₀, hc1⟩ := hex
    have hstart : 0 ≤ y (n₀ + 1) - (1 + u) := by
      rw [(hd n₀ hn₀).2 hc1]; have := hy0 n₀; linarith
    have hnn : ∀ j, 0 ≤ y (n₀ + 1 + j) - (1 + u) := by
      intro j
      induction j with
      | zero => simpa using hstart
      | succ j ih =>
        rw [← Nat.add_assoc]
        rcases hL (n₀ + 1 + j) (by omega) with hc | hc
        · rw [(hd _ (by omega)).2 hc]; linarith
        · rw [(hd _ (by omega)).1 hc]; positivity
    refine isEventuallyPeriodic_of_const (N := n₀ + 1) (a := 1 - 30 * k) fun m hm => ?_
    rcases hL m (by omega) with hc | hc
    · exfalso
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hm
      have hdm := hnn j
      rw [← hj] at hdm
      refine no_expansion_of (r := 6 / 5) (by norm_num) (d := fun i => y i - (1 + u))
        (k₀ := m + 1) (B := 1) ?_ ?_ ?_
      · show 0 < y (m + 1) - (1 + u)
        rw [(hd m (by omega)).2 hc]; linarith
      · intro i hi
        obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (show n₀ + 1 ≤ i by omega)
        have hl := hnn l
        show 6 / 5 * (y (n₀ + 1 + l) - (1 + u)) ≤ y (n₀ + 1 + l + 1) - (1 + u)
        rcases hL (n₀ + 1 + l) (by omega) with hc' | hc'
        · rw [(hd _ (by omega)).2 hc']; linarith
        · rw [(hd _ (by omega)).1 hc']
      · intro i _
        have := hy1 i
        show y i - (1 + u) ≤ 1
        linarith
    · omega
  · push Not at hex
    refine isEventuallyPeriodic_of_const (N := N) (a := 1 - 30 * k) fun n hn => ?_
    rcases hL n hn with h | h
    · exact absurd h (hex n hn)
    · omega

end SixFifths

/-- **`{2,3,5}` is unavoidable for `⌊ξ(6/5)ⁿ + ν⌋` at every real `ν ∈ [−1, −2/3] + 30ℤ`.**
At `ν = −1` this is [Nov12] Theorem 1.4 ([DN05] Theorem 3 form). -/
@[category research solved, AMS 11 37, ref "DN05" "Nov12", group "dubc2_schema"]
theorem six_fifths_two_three_five (hξ : ξ ≠ 0) (k : ℤ) (h1 : -1 ≤ ν - 30 * k)
    (h2 : ν - 30 * k ≤ -2 / 3) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 6 5 ξ ν n ∨ (3 : ℤ) ∣ xInt 6 5 ξ ν n ∨
      (5 : ℤ) ∣ xInt 6 5 ξ ν n := by
  refine (frequently_dvd_of_letters (p := 6) (q := 5) (by norm_num) (by norm_num) (by norm_num) hξ
    (P := {2, 3, 5}) (by decide) fun _ hA => carry_eventually_periodic65 k h1 h2 hA).mono
    fun n h => by simpa using h

/-- **The atlas cell `(6/5, ν = −1, {2,3,5})`, data-free.** -/
@[category research solved, AMS 11 37, ref "DN05" "Nov12", group "dubc2_schema"]
theorem six_fifths_minus_one (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 6 5 ξ (-1) n ∨ (3 : ℤ) ∣ xInt 6 5 ξ (-1) n ∨
      (5 : ℤ) ∣ xInt 6 5 ξ (-1) n :=
  six_fifths_two_three_five hξ 0 (by norm_num) (by norm_num)

end DubC2.Schema
