/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.BlockApproximants
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Wiring the approximants into a too-well-approximated rational family (Route (i), Phase 3→4)

Phase 3 (`B3.Approximants`) proved the isometric distance bound `approximant_distance_bound` against an
**abstract** approximant `α` agreeing with `v` modulo `2^N`, and Phase 3/the block generalisation
(`B3.BlockApproximants`) proved that periodic completions `blockVal` have **rational** `Φ`-image
(`Φ_blockValue_mem_ratInt`). Neither was consumed by anything — they were scaffolding pointing at the
Missing Lemma. This file connects them.

* **The digit bridge (`toZModPow_eq_of_binaryDigit_agree`).** `approximant_distance_bound` needs the
  *value-level* hypothesis `toZModPow N v = toZModPow N α`, but a stammering structure (`AB.ConditionStar`)
  delivers *digit-level* agreement: the binary digits of `v` and `α` coincide on a prefix. The bridge
  converts one to the other. *Proof:* `x = parity x + 2·S x` (`BL.parity_add_two_mul_S`), so equal
  leading digits (`parity x = parity y`) give `x − y = 2·(S x − S y)`; an induction on the prefix length
  `N` (the digit at depth `k` is `parity (Sᵏ·) = binaryDigit · k`) yields `2^N ∣ x − y`, i.e.
  `x ≡ y (mod 2^N)`.
* **The packaging theorem (`tooWellApproximated_of_agreement`).** Given the integer `n = Φ(v)`, a family
  of approximants `αₘ` with `Φ(αₘ) ∈ ℚ` (rational) and binary digits agreeing with `v` up to depth
  `Nₘ → ∞`, the rationals `Φ(αₘ)` approximate the integer `n` arbitrarily well:
  `‖n − Φ(αₘ)‖ ≤ 2^{−Nₘ} → 0`. This **consumes** `approximant_distance_bound` (through the bridge) and is
  precisely the *too-well-approximated rational family* that the `p`-adic Subspace Theorem turns into the
  Missing Lemma (`Φ(v) ∉ ℤ`).
* **The block instance (`blockVal_tooWellApproximated`).** Specialising the family to periodic
  completions `αₘ = blockVal cₘ pₘ eₘ` **consumes** `Φ_blockValue_mem_ratInt` for the rationality
  hypothesis, leaving only the (combinatorial) digit agreement to be supplied.

## The remaining concrete step

What stays open is the **construction of the `αₘ` family from `AB.ConditionStar`** and the proof of its
digit agreement `hagree`. Concretely: extract from the stammering data `(rₘ, sₘ, w)` the per-window
block `Vₘ` (period `pₘ = sₘ`, offsets `eₘ` = the `1`-bit positions of `v` in one period after the
pre-period `Uₘ`), set `Nₘ = rₘ + ⌊w·sₘ⌋`, and prove `binaryDigit v k = binaryDigit (blockVal …) k` for
`k < Nₘ` from `ConditionStar`'s periodicity clause `a i = a (i − sₘ)`. This needs (i) a pre-period–aware
variant of `blockVal` (`Φ` of `Uₘ` followed by the repeated block) and (ii) the value↔digit identity
`binaryDigit (blockVal …) = ` the periodic `0/1` pattern. Both are standard but nontrivial `PadicInt`
digit bookkeeping; they are *not* axiomatised (nothing here is an open conjecture), only deferred. With
`hagree` in hand, `blockVal_tooWellApproximated` immediately yields the Subspace-Theorem input.

## Contents
* `binaryDigit_zero`, `binaryDigit_succ` — the recursion `binaryDigit x 0 = parity x`,
  `binaryDigit x (k+1) = binaryDigit (S x) k`.
* `dvd_two_pow_sub_of_binaryDigit_agree` — digit agreement on a prefix gives `2^N ∣ x − y`.
* `toZModPow_eq_of_binaryDigit_agree` — the digit→value bridge.
* `tendsto_two_pow_neg` — `2^{−Nₘ} → 0` when `Nₘ → ∞`.
* `tooWellApproximated_of_agreement` — (proved) the packaging theorem: a digit-agreeing rational family
  approximates `n = Φ(v)` arbitrarily well.
* `blockVal_tooWellApproximated` — (proved) the periodic-completion instance.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the shift `S`, `(1.2)`; the isometry, Cor A.3).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§4, the periodic-completion approximants and the Subspace Theorem).
-/

namespace B3

open BL AB Function Filter

/-! ### The digit recursion -/

/-- The `0`-th binary digit is the parity: `binaryDigit x 0 = parity x` (`S⁰ = id`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem binaryDigit_zero (x : ℤ_[2]) : binaryDigit x 0 = parity x := by
  simp only [binaryDigit, Function.iterate_zero_apply]

/-- Deleting the lowest bit shifts the digit index: `binaryDigit x (k+1) = binaryDigit (S x) k`
(`Sᵏ⁺¹ x = Sᵏ (S x)`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem binaryDigit_succ (x : ℤ_[2]) (k : ℕ) : binaryDigit x (k + 1) = binaryDigit (S x) k := by
  simp only [binaryDigit, Function.iterate_succ_apply]

/-! ### The digit → value bridge -/

/-- **Digit agreement on a prefix gives congruence `mod 2^N`.** If `x` and `y` have the same first `N`
binary digits (`binaryDigit x k = binaryDigit y k` for `k < N`) then `2^N ∣ x − y`. *Proof* by induction
on `N`: the leading digits agree (`parity x = parity y`), so `x − y = 2·(S x − S y)`
(`parity_add_two_mul_S`), and the remaining digits of `x, y` are the digits of `S x, S y`
(`binaryDigit_succ`), giving `2^N ∣ S x − S y` by induction; multiply by `2`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem dvd_two_pow_sub_of_binaryDigit_agree : ∀ (N : ℕ) (x y : ℤ_[2]),
    (∀ k, k < N → binaryDigit x k = binaryDigit y k) → (2 : ℤ_[2]) ^ N ∣ x - y
  | 0, x, y, _ => by simp
  | N + 1, x, y, h => by
    have hpar : (parity x : ℤ_[2]) = (parity y : ℤ_[2]) := by
      have h0 := h 0 (Nat.succ_pos N)
      rw [binaryDigit_zero, binaryDigit_zero] at h0
      rw [h0]
    have hxy : x - y = 2 * (S x - S y) := by
      have hx := parity_add_two_mul_S x
      have hy := parity_add_two_mul_S y
      linear_combination hy - hx + hpar
    have hSdvd : (2 : ℤ_[2]) ^ N ∣ S x - S y :=
      dvd_two_pow_sub_of_binaryDigit_agree N (S x) (S y) (fun k hk => by
        have hk1 := h (k + 1) (Nat.succ_lt_succ hk)
        rwa [binaryDigit_succ, binaryDigit_succ] at hk1)
    rw [hxy, pow_succ']
    exact mul_dvd_mul_left 2 hSdvd

/-- **The digit→value bridge.** Binary-digit agreement on a prefix is `2`-adic congruence:
`(∀ k < N, binaryDigit x k = binaryDigit y k) → toZModPow N x = toZModPow N y`. This feeds the
digit-level output of a stammering structure into the value-level `approximant_distance_bound`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem toZModPow_eq_of_binaryDigit_agree (x y : ℤ_[2]) (N : ℕ)
    (h : ∀ k, k < N → binaryDigit x k = binaryDigit y k) :
    PadicInt.toZModPow N x = PadicInt.toZModPow N y :=
  (toZModPow_eq_iff_dvd_sub x y N).mpr (dvd_two_pow_sub_of_binaryDigit_agree N x y h)

/-! ### The packaging theorem -/

/-- `2^{−Nₘ} → 0` when `Nₘ → ∞`: the over-approximation bounds tend to `0`. -/
@[category API, AMS 11 37, ref "AB07"]
theorem tendsto_two_pow_neg (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun m => (2 : ℝ) ^ (-(N m : ℤ))) atTop (nhds 0) := by
  have hbase : Tendsto (fun k : ℕ => (2 : ℝ) ^ (-(k : ℤ))) atTop (nhds 0) := by
    have heq : (fun k : ℕ => (2 : ℝ) ^ (-(k : ℤ))) = (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) := by
      funext k; rw [zpow_neg, zpow_natCast, inv_pow]
    rw [heq]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact hbase.comp hN

/-- **The packaging theorem (proved): a digit-agreeing rational family is too well approximating.** Let
`n = Φ(v)` be an integer. Given approximants `αₘ` with `Φ(αₘ)` **rational** (`∈ RatInt`) and binary
digits agreeing with `v` up to depth `Nₘ → ∞`, the rationals `Φ(αₘ)` approximate the integer `n`
faster than any geometric rate: `‖n − Φ(αₘ)‖ ≤ 2^{−Nₘ}`, and `‖n − Φ(αₘ)‖ → 0`.

This is the assembled output of Phase 3 — it **consumes** `approximant_distance_bound` (via the digit
bridge `toZModPow_eq_of_binaryDigit_agree`) — and is exactly the *too-well-approximated rational family*
that the `p`-adic Subspace Theorem (Phase 4, the `Φ`-side application) converts into the Missing Lemma
`Φ(v) ∉ ℤ`. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem tooWellApproximated_of_agreement {v : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2]))
    {α : ℕ → ℤ_[2]} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hrat : ∀ m, Φ (α m) ∈ RatInt)
    (hagree : ∀ m, ∀ k, k < N m → binaryDigit v k = binaryDigit (α m) k) :
    (∀ m, Φ (α m) ∈ RatInt) ∧
    (∀ m, ‖(n : ℤ_[2]) - Φ (α m)‖ ≤ (2 : ℝ) ^ (-(N m : ℤ))) ∧
    Tendsto (fun m => ‖(n : ℤ_[2]) - Φ (α m)‖) atTop (nhds 0) := by
  have hbound : ∀ m, ‖(n : ℤ_[2]) - Φ (α m)‖ ≤ (2 : ℝ) ^ (-(N m : ℤ)) := fun m =>
    approximant_distance_bound hv (toZModPow_eq_of_binaryDigit_agree v (α m) (N m) (hagree m))
  exact ⟨hrat, hbound, squeeze_zero (fun m => norm_nonneg _) hbound (tendsto_two_pow_neg N hN)⟩

/-- **The periodic-completion instance (proved).** When the approximants are periodic completions
`αₘ = blockVal cₘ pₘ eₘ` (multi-bit blocks, `B3.BlockApproximants`), the rationality hypothesis of
`tooWellApproximated_of_agreement` is discharged by `Φ_blockValue_mem_ratInt` — **consuming** the block
generalisation. Only the digit agreement `hagree` (that the periodic completion matches `v` on the
stammering window) remains to be supplied from `AB.ConditionStar`. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem blockVal_tooWellApproximated {v : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2]))
    {cc pp : ℕ → ℕ} {ee : ℕ → ℕ → ℕ} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hp : ∀ m, 0 < pp m)
    (he_lt : ∀ m r, r < cc m → ee m r < pp m)
    (he_mono : ∀ m r r', r < r' → r' < cc m → ee m r < ee m r')
    (hagree : ∀ m, ∀ k, k < N m →
      binaryDigit v k = binaryDigit (blockVal (cc m) (pp m) (ee m)) k) :
    (∀ m, Φ (blockVal (cc m) (pp m) (ee m)) ∈ RatInt) ∧
    (∀ m, ‖(n : ℤ_[2]) - Φ (blockVal (cc m) (pp m) (ee m))‖ ≤ (2 : ℝ) ^ (-(N m : ℤ))) ∧
    Tendsto (fun m => ‖(n : ℤ_[2]) - Φ (blockVal (cc m) (pp m) (ee m))‖) atTop (nhds 0) :=
  tooWellApproximated_of_agreement hv hN
    (fun m => Φ_blockValue_mem_ratInt (hp m) (he_lt m) (he_mono m)) hagree

end B3
