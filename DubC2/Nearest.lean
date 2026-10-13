/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NearestCert
import Mathlib.Analysis.SpecificLimits.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# `{2,5}` is an unavoidable divisor set for the nearest integer to `ξ(3/2)ⁿ`

Milestone M3 of `plans/plan-dubC2.html`, capstone.

> **Theorem.**  For every real `ξ ≠ 0`, infinitely many of the nearest integers
> `[ξ(3/2)ⁿ + ½] = round (ξ(3/2)ⁿ)` are divisible by `2` or by `5`.

This is the case that [DN05] Theorem 4 conspicuously omits — its neighbours `7`, `5/3` and
`7/5` are settled there, and `3/2` at the shift `ν = ½` is absent from the whole shifted-integer
-part literature, including [Nov12]'s complete inventory.  The corresponding *floor* statement
is [FS67]'s theorem, and it needs the four primes `{2,5,7,11}`; the nearest-integer case is
therefore **strictly easier**, at `{2,5} ⊊ {2,5,7,11}`.  The reason is visible in
`DubC2/NearestStep.lean`: at `ν = ½` the two letters split `[0,1)` evenly, so `AA` and `BB` are
both expensive, whereas at `ν = 0` the letter `A` cannot repeat at all and `B`-runs are
unbounded — a much richer language.

## Main results

* `DubC2.round_divisor_set` — the theorem above, as a `∃ᶠ … in atTop` statement.
* `DubC2.infinite_dvd_two_or_five` — the same, as `Set.Infinite`.
* `DubC2.round_composite` — the arithmetic corollary for `ξ > 0`: infinitely many
  `round (ξ(3/2)ⁿ)` are composite.

## What is *not* claimed

The statement is `i.o.`, with no bound on the gaps, and that is not laziness: M1's experiment
X0 shows the gaps are genuinely unbounded.  A successful `𝒫` leaves one periodic carry word
behind, and a periodic carry word can be realised on arbitrarily long prefixes by a `ξ`
constructed by CRT (`DubC2/xscan.py --construct` exhibits avoiding prefixes of length
`9, 33, 129, 513`).  A syndetic — "within a bounded window" — form of the theorem is therefore
false for `𝒫 = {2,5}`, and by the same argument for every set that this method kills.

## Minimality (checked numerically at M1, not formalised)

No single prime works, and among the pairs `{2, ℓ}` with `ℓ ≤ 19` only `{2,5}` does; the
determinized entropies are `{2} → 1.50003` (the full archimedean value `3/2`), `{2,7} →
1.35032`, `{2,11} → 1.39041`, `{2,13} → 1.43405`, `{2,17} → 1.35692`, `{2,19} → 1.40675`,
`{2,5} → 1.00000`.  See `plans/note-dubC2-M1.html` §4.2 and `DubC2/README.md`.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648.
* [FS67] R. Forman, H. N. Shapiro, *An arithmetic property of certain rational powers*, Comm.
  Pure Appl. Math. **20** (1967), 561–573.
* [Nov12] A. Novikas, *Composite numbers in the sequences of integers*, doctoral dissertation,
  Vilnius University, 2012 — §1.6.
-/

namespace DubC2

open Filter

variable {ξ : ℝ}

/-! ## The theorem -/

/-- **`{2,5}` is unavoidable for `round (ξ(3/2)ⁿ)`.**  For every real `ξ ≠ 0`, infinitely many
nearest integers `[ξ(3/2)ⁿ + ½]` are divisible by `2` or by `5`. -/
@[category research solved, AMS 11 37, ref "DN05" "FS67", group "dn05_nearest_32"]
theorem round_divisor_set (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ round (ξ * ((3 : ℝ) / 2) ^ n) ∨
      (5 : ℤ) ∣ round (ξ * ((3 : ℝ) / 2) ^ n) := by
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨n, hn, hna⟩ := exists_not_avoids hξ N
  refine ⟨n, hn, ?_⟩
  rw [← xN_eq_round]
  simpa only [Avoids, not_and_or, not_not] using hna

/-- The same statement in the `∃ p ∈ 𝒫` shape of the plan. -/
@[category research solved, AMS 11 37, ref "DN05" "FS67", group "dn05_nearest_32"]
theorem round_divisor_set_mem (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ p ∈ ({2, 5} : Set ℕ), (p : ℤ) ∣ round (ξ * ((3 : ℝ) / 2) ^ n) := by
  refine (round_divisor_set hξ).mono ?_
  rintro n (h | h)
  · exact ⟨2, by simp, by exact_mod_cast h⟩
  · exact ⟨5, by simp, by exact_mod_cast h⟩

/-- The same statement as a `Set.Infinite`. -/
@[category research solved, AMS 11 37, ref "DN05" "FS67", group "dn05_nearest_32"]
theorem infinite_dvd_two_or_five (hξ : ξ ≠ 0) :
    {n : ℕ | (2 : ℤ) ∣ round (ξ * ((3 : ℝ) / 2) ^ n) ∨
      (5 : ℤ) ∣ round (ξ * ((3 : ℝ) / 2) ^ n)}.Infinite :=
  Nat.frequently_atTop_iff_infinite.mp (round_divisor_set hξ)

/-! ## The composite corollary -/

/-- For `ξ > 0` the nearest integers grow past any bound. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem eventually_five_lt_round (hξ : 0 < ξ) :
    ∀ᶠ n in atTop, (5 : ℤ) < round (ξ * ((3 : ℝ) / 2) ^ n) := by
  have h1 : Tendsto (fun n : ℕ => ξ * ((3 : ℝ) / 2) ^ n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hξ (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  refine (h1.eventually_gt_atTop 6).mono fun n hn => ?_
  have hr : |ξ * ((3 : ℝ) / 2) ^ n - round (ξ * ((3 : ℝ) / 2) ^ n)| ≤ 1 / 2 :=
    abs_sub_round _
  have : (5 : ℝ) < (round (ξ * ((3 : ℝ) / 2) ^ n) : ℝ) := by
    cases abs_le.mp hr with
    | intro hlo hhi => linarith
  exact_mod_cast this

/-- **Infinitely many composite nearest integers.**  For every real `ξ > 0` infinitely many
`round (ξ(3/2)ⁿ)` are composite: they exceed `5` and are divisible by `2` or by `5`. -/
@[category research solved, AMS 11 37, ref "DN05" "FS67", group "dn05_nearest_32"]
theorem round_composite (hξ : 0 < ξ) :
    ∃ᶠ n in atTop, ¬ Prime (round (ξ * ((3 : ℝ) / 2) ^ n)) ∧
      1 < round (ξ * ((3 : ℝ) / 2) ^ n) := by
  refine ((round_divisor_set hξ.ne').and_eventually (eventually_five_lt_round hξ)).mono ?_
  rintro n ⟨hdvd, hgt⟩
  set x : ℤ := round (ξ * ((3 : ℝ) / 2) ^ n) with hx
  have hpos : 0 < x := by omega
  have hnat : (5 : ℕ) < x.natAbs := by omega
  refine ⟨fun hp => ?_, by omega⟩
  have hpn : Nat.Prime x.natAbs := Int.prime_iff_natAbs_prime.mp hp
  rcases hdvd with h | h
  · have : (2 : ℕ) ∣ x.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    rcases (Nat.Prime.eq_one_or_self_of_dvd hpn 2 this) with h1 | h1 <;> omega
  · have : (5 : ℕ) ∣ x.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    rcases (Nat.Prime.eq_one_or_self_of_dvd hpn 5 this) with h1 | h1 <;> omega

end DubC2
