/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.PeriodicMatching
import AB.StammeringSequences
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.List.GetD
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The truncate-and-complete construction: `ConditionStar` ⟹ a too-well-approximated rational family
(Route (i), Phase 3→4 — the construction half)

This file discharges the **pure construction** that was the last gap in turning Adamczewski–Bugeaud's
`ConditionStar` (`AB.ConditionStar`, [[ab-complexity-corpus-root]]) into the "too-well-approximated
rational family" the (Φ-side) Subspace Theorem consumes. Everything below the level of `ConditionStar`
is already proved ([[b3-automatic-cc-corpus-root]]): `binaryDigit_window_agreement`
(`B3.PeriodicMatching`) reduces the digit agreement to two `2`-adic congruences plus the periodicity
clause, and `Φ_prefixBlockVal_mem_ratInt` (`B3.PrefixApproximants`) gives rationality. What remained was
to actually *build* the approximant `αₙ = Uₙ Vₙ^∞` meeting those congruences. That is done here.

## The construction

For the `n`-th repetition datum `(rₙ, sₙ)` of `ConditionStar`, the **truncate-and-complete** approximant
of `v ∈ ℤ₂` is the pre-period `Uₙ = v mod 2^{rₙ}` followed by the block `Vₙ = (Sʳⁿv) mod 2^{sₙ}` repeated
forever:

> `truncApprox v t p := prefixBlockVal (appr v t) t (blockCard B) p (blockOffset B)`,
> `B := appr (Sᵗv) p`   (`t = rₙ`, `p = sₙ`).

* The pre-period and block integers are `PadicInt.appr` (the canonical natural-number truncation): `appr x m
  < 2^m` (`appr_lt`) and `2^m ∣ x − appr x m` (`appr_spec` + `Ideal.mem_span_singleton`,
  `dvd_sub_appr`) — exactly the two congruences `2^t ∣ v − A`, `2^p ∣ Sᵗv − B`.
* The block `B` (a natural `< 2^p`) is split into its `1`-bit positions via `Nat.bitIndices`:
  `blockCard B = |bitIndices B|` ones at offsets `blockOffset B r = (bitIndices B)[r]`. Then
  `blockFirst (blockCard B) (blockOffset B) = B` (`blockFirst_blockOffset`,
  `Nat.sum_map_two_pow_bitIndices`), the offsets are strictly increasing (`blockOffset_strictMono`,
  `Nat.bitIndices_sorted`) and `< p` (`blockOffset_lt`, `Nat.two_pow_le_of_mem_bitIndices`) — the
  `he_mono`/`he_lt` data the block lemmas need. The **all-zero block** `B = 0` gives `blockCard 0 = 0`,
  the `c = 0` case now handled (`blockVal_zero`, [[b3-automatic-cc-corpus-root]]).

## The capstone

`conditionStar_tooWellApproximated`: if `Φ v = n ∈ ℕ` and the parity vector `binaryDigit v` satisfies
`ConditionStar w` (`w > 1`), then there is a family `αₘ` of approximants with `Φ(αₘ) ∈ ℚ ∩ ℤ₂` and
`‖n − Φ(αₘ)‖ ≤ 2^{−Nₘ} → 0` (with `Nₘ = rₘ + ⌊w·sₘ⌋` the stammering-window length, which `→ ∞` because
`sₘ` is strictly increasing and `w > 1`). The agreement on `[0, Nₘ)` is `binaryDigit_window_agreement`
fed the two `appr`-congruences and the `ConditionStar` periodicity clause; rationality is
`Φ_truncApprox_mem_ratInt`; the norm bound and convergence are `tooWellApproximated_of_agreement`
(`B3.StammeringWiring`). This is precisely the *input* to a Subspace-Theorem transcendence argument — the
construction half of the Missing Lemma is now complete. What remains is **not** a routine instance of the
`v`-side criterion (`AB.transcendental_of_conditionStar`): the approximants `Φ(αₘ)` have *base-`3`*
denominators `3^{cₘ} − 2^{pₘ}` (height `≈ 3^{cₘ}`, `cₘ ≈` odd steps) against the *base-`2`* rate
`2^{−Nₘ}` (`Nₘ ≈` total steps), and since the target `n` is trivially algebraic the contradiction needs
the **multidimensional** `Φ`-side `p`-adic Subspace Theorem governed by that non-linear index — the
genuine open content (see `B3.phi_value_transcendental`), kept `research open`, never an `axiom`.

No new `axiom`s: the whole file rests on the BL/AB literature axioms already cited upstream.

## Contents
* `sum_range_length_getD` — `∑_{r<|L|} f L[r] = (L.map f).sum` (the list↔range-sum bridge).
* `blockCard`, `blockOffset` — the `bitIndices` decomposition of a natural number into a block.
* `blockFirst_blockOffset`, `blockOffset_strictMono`, `blockOffset_lt` — its defining properties.
* `dvd_sub_appr` — the `appr` congruence `2^t ∣ x − appr x t`.
* `truncApprox` — the truncate-and-complete approximant `Uₙ Vₙ^∞`.
* `Φ_truncApprox_mem_ratInt`, `binaryDigit_truncApprox_agreement` — its rationality and digit agreement.
* `conditionStar_tooWellApproximated` — (capstone) `ConditionStar` ⟹ the too-well-approximated rational
  family.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169.
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§4 Condition (∗)_w; §2 Lemma 1, the truncate-and-complete
  approximants of a stammering expansion).
-/

namespace B3

open BL AB Function Filter PadicInt

/-! ### A list↔range-sum bridge -/

/-- `∑_{r < |L|} f (L[r]) = (L.map f).sum`: summing `f` over the entries of a list, indexed by position,
is the list-sum of `L.map f`. (`L.getD r 0 = L[r]` for `r < |L|`; proved by induction splitting off the
head with `Finset.sum_range_succ'`.) -/
@[category API, AMS 11 68, ref "AB07"]
theorem sum_range_length_getD (L : List ℕ) (f : ℕ → ℕ) :
    ∑ r ∈ Finset.range L.length, f (L.getD r 0) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, add_comm]

/-! ### The block of a natural number, via its binary `1`-bit positions -/

/-- The **number of `1`-bits** of `B`: `blockCard B = |bitIndices B|`, the count `c` of the block `Vₙ`
read as an integer. The all-zero block `B = 0` gives `blockCard 0 = 0` (the empty block). -/
@[category API, AMS 11 68, ref "AB07"]
def blockCard (B : ℕ) : ℕ := B.bitIndices.length

/-- The **`r`-th `1`-bit position** of `B`: `blockOffset B r = (bitIndices B)[r]` (the sorted list of bit
positions), i.e. the offset `eᵣ` of the `r`-th one in the block `Vₙ`. -/
@[category API, AMS 11 68, ref "AB07"]
def blockOffset (B : ℕ) (r : ℕ) : ℕ := B.bitIndices.getD r 0

/-- **The block reconstructs `B`.** `blockFirst (blockCard B) (blockOffset B) = B`: summing `2^{eᵣ}` over
the `1`-bit positions of `B` recovers `B` (`Nat.sum_map_two_pow_bitIndices`, via the list↔range-sum
bridge). So the truncate `B` of `Sᵗv` *is* the integer value of the block placed by `(blockCard, blockOffset)`. -/
@[category API, AMS 11 68, ref "AB07"]
theorem blockFirst_blockOffset (B : ℕ) : blockFirst (blockCard B) (blockOffset B) = B := by
  unfold blockFirst blockCard blockOffset
  rw [sum_range_length_getD B.bitIndices (fun i => 2 ^ i)]
  exact B.sum_map_two_pow_bitIndices

/-- **The offsets strictly increase.** `bitIndices B` is strictly sorted (`Nat.bitIndices_sorted`), so the
block offsets satisfy `blockOffset B r < blockOffset B r'` for `r < r' < blockCard B` — the `he_mono`
hypothesis of the block lemmas. -/
@[category API, AMS 11 68, ref "AB07"]
theorem blockOffset_strictMono (B : ℕ) :
    ∀ r r', r < r' → r' < blockCard B → blockOffset B r < blockOffset B r' := by
  intro r r' hrr hr'
  unfold blockOffset blockCard at *
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hr']
  exact Nat.bitIndices_sorted.getElem_lt_getElem_of_lt hrr

/-- **The offsets fit in a period.** If `B < 2^p` then every block offset is `< p`
(`Nat.two_pow_le_of_mem_bitIndices`: a bit position `a` of `B` has `2^a ≤ B < 2^p`) — the `he_lt`
hypothesis of the block lemmas. -/
@[category API, AMS 11 68, ref "AB07"]
theorem blockOffset_lt {B p : ℕ} (hB : B < 2 ^ p) :
    ∀ r, r < blockCard B → blockOffset B r < p := by
  intro r hr
  unfold blockOffset blockCard at *
  rw [List.getD_eq_getElem _ _ hr]
  have h2 : 2 ^ B.bitIndices[r] ≤ B := Nat.two_pow_le_of_mem_bitIndices (List.getElem_mem hr)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h2 hB)

/-! ### The `appr` congruence -/

/-- **The truncation congruence.** `2^t ∣ x − appr x t`: the canonical natural-number truncation
`PadicInt.appr x t < 2^t` (`appr_lt`) is congruent to `x` modulo `2^t`
(`appr_spec` + `Ideal.mem_span_singleton`). This supplies both congruences of
`binaryDigit_window_agreement`: `2^t ∣ v − A` (`A = appr v t`) and `2^p ∣ Sᵗv − B` (`B = appr (Sᵗv) p`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem dvd_sub_appr (x : ℤ_[2]) (t : ℕ) : (2 : ℤ_[2]) ^ t ∣ x - ((appr x t : ℕ) : ℤ_[2]) := by
  simpa using Ideal.mem_span_singleton.mp (appr_spec t x)

/-! ### The truncate-and-complete approximant -/

/-- The **truncate-and-complete approximant** `αₙ = Uₙ Vₙ^∞` of `v ∈ ℤ₂`: the pre-period `Uₙ = v mod 2^t`
(`A = appr v t`) followed by the block `Vₙ = Sᵗv mod 2^p` (`B = appr (Sᵗv) p`) repeated forever. As a
`2`-adic integer, `prefixBlockVal A t (blockCard B) p (blockOffset B)`. For `t = rₙ`, `p = sₙ` this is the
Adamczewski–Bugeaud approximant of the stammering expansion. -/
@[category API, AMS 11 37, ref "BL96" "AB07"]
noncomputable def truncApprox (v : ℤ_[2]) (t p : ℕ) : ℤ_[2] :=
  prefixBlockVal (appr v t) t (blockCard (appr (S^[t] v) p)) p (blockOffset (appr (S^[t] v) p))

/-- **Rationality of the approximant.** `Φ(truncApprox v t p) ∈ RatInt = ℚ ∩ ℤ₂` for `0 < p`: the block
data `(blockCard B, blockOffset B)` satisfies `he_lt`/`he_mono` (`blockOffset_lt`/`blockOffset_strictMono`,
`B = appr (Sᵗv) p < 2^p`) and the pre-period satisfies `appr v t < 2^t`, so
`Φ_prefixBlockVal_mem_ratInt` applies. (Valid even when the block is empty, `blockCard B = 0`.) -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_truncApprox_mem_ratInt (v : ℤ_[2]) (t p : ℕ) (hp : 0 < p) :
    Φ (truncApprox v t p) ∈ RatInt := by
  unfold truncApprox
  exact Φ_prefixBlockVal_mem_ratInt hp (blockOffset_lt (appr_lt (S^[t] v) p))
    (blockOffset_strictMono (appr (S^[t] v) p)) t (appr v t) (appr_lt v t)

/-- **The truncate-and-complete approximant is itself rational (proved).** `truncApprox v t p ∈ RatInt`
(`= ℚ ∩ ℤ₂`) for `0 < p`: as a `2`-adic integer
`truncApprox = prefixBlockVal A t c p e = (A : ℤ₂) + 2ᵗ · blockVal c p e`, a finite integer part plus `2ᵗ`
times the rational periodic completion `blockVal` (`B3.blockVal_mem_ratInt`); `RatInt` closure
(`ratInt_add`/`ratInt_mul`) finishes. This is the *preimage* statement — note it is **not** obtainable from
`Φ_truncApprox_mem_ratInt` by reflecting through `Φ`, since `Φ(ℚ∩ℤ₂)=ℚ∩ℤ₂` is the open Periodicity
Conjecture (`BL.periodicity_conjecture`). It certifies that the approximants `αₘ` differ from an irrational
limit `v` (`v ∉ RatInt`) — the distinctness input of the `Φ`-side Subspace argument
(`B3.phi_ne_natCast`). -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem truncApprox_mem_ratInt (v : ℤ_[2]) (t p : ℕ) (hp : 0 < p) : truncApprox v t p ∈ RatInt := by
  unfold truncApprox prefixBlockVal
  exact ratInt_add ⟨(appr v t : ℚ), by norm_cast⟩
    (ratInt_mul ⟨(2 : ℚ) ^ t, by norm_cast⟩
      (blockVal_mem_ratInt hp (blockOffset_lt (appr_lt (S^[t] v) p))
        (blockOffset_strictMono (appr (S^[t] v) p))))

/-- **Digit agreement of the approximant.** If `v` is `p`-periodic on the window `[t + p, N)`
(`hper`, the `ConditionStar` clause with `t = rₙ`, `p = sₙ`), then `truncApprox v t p` reproduces `v`'s
digits on all of `[0, N)`. *Proof:* `binaryDigit_window_agreement` with the two `appr`-congruences
(`dvd_sub_appr`, plus `blockFirst_blockOffset` to identify the block value `B = appr (Sᵗv) p`),
`appr_lt`, the block `he_lt`/`he_mono`, and `hper`. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem binaryDigit_truncApprox_agreement (v : ℤ_[2]) (t p : ℕ) (hp : 0 < p) {N : ℕ}
    (hper : ∀ i, t + p ≤ i → i < N → binaryDigit v i = binaryDigit v (i - p)) :
    ∀ k, k < N → binaryDigit v k = binaryDigit (truncApprox v t p) k := by
  unfold truncApprox
  refine binaryDigit_window_agreement hp (blockOffset_lt (appr_lt (S^[t] v) p))
    (blockOffset_strictMono (appr (S^[t] v) p)) (appr_lt v t) (dvd_sub_appr v t) ?_ hper
  rw [blockFirst_blockOffset]
  exact dvd_sub_appr (S^[t] v) p

/-! ### The capstone: `ConditionStar` ⟹ a too-well-approximated rational family -/

/-- **The truncate-and-complete capstone (proved).** Let `Φ v = n ∈ ℕ` and suppose the parity vector
`binaryDigit v` satisfies `ConditionStar w` for some `w > 1` (the Adamczewski–Bugeaud stammering
structure). Then there is a family of approximants `αₘ` and window lengths `Nₘ = rₘ + ⌊w·sₘ⌋` with

* `Φ(αₘ) ∈ RatInt` (each approximant maps to a rational `2`-adic number),
* `‖n − Φ(αₘ)‖ ≤ 2^{−Nₘ}`, and
* `‖n − Φ(αₘ)‖ → 0`

— a **too-well-approximated rational family** converging to `n = Φ v`. *Proof:* take
`αₘ = truncApprox v rₘ sₘ`; rationality is `Φ_truncApprox_mem_ratInt`, agreement on `[0, Nₘ)` is
`binaryDigit_truncApprox_agreement` fed the `ConditionStar` periodicity clause, and the norm bound and
convergence are `tooWellApproximated_of_agreement`. `Nₘ → ∞` because `sₘ` is strictly increasing
(`sₘ ≥ m`) and `w > 1` (so `⌊w·sₘ⌋ ≥ sₘ`).

This is exactly the family a (Φ-side) Subspace-Theorem argument needs: the construction half of the
Missing Lemma is complete, and what remains is purely that transcendence application. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem conditionStar_tooWellApproximated {v : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2]))
    {w : ℝ} (hw : 1 < w) (hCS : ConditionStar w (binaryDigit v)) :
    ∃ (α : ℕ → ℤ_[2]) (N : ℕ → ℕ), Tendsto N atTop atTop ∧
      (∀ m, Φ (α m) ∈ RatInt) ∧
      (∀ m, ‖(n : ℤ_[2]) - Φ (α m)‖ ≤ (2 : ℝ) ^ (-(N m : ℤ))) ∧
      Tendsto (fun m => ‖(n : ℤ_[2]) - Φ (α m)‖) atTop (nhds 0) ∧
      (∀ m, α m ∈ RatInt) := by
  obtain ⟨_hnep, r, s, hs_pos, hper, _hbound, hs_mono⟩ := hCS
  -- the window lengths `Nₘ = rₘ + ⌊w·sₘ⌋` go to infinity
  have hmN : ∀ m, m ≤ r m + ⌊w * (s m : ℝ)⌋₊ := by
    intro m
    have h1 : m ≤ s m := hs_mono.le_apply
    have hsm : (0 : ℝ) ≤ (s m : ℝ) := Nat.cast_nonneg (s m)
    have hle : (s m : ℝ) ≤ w * (s m : ℝ) := by nlinarith [hsm, hw.le]
    have h2 : s m ≤ ⌊w * (s m : ℝ)⌋₊ := Nat.le_floor hle
    omega
  have hN : Tendsto (fun m => r m + ⌊w * (s m : ℝ)⌋₊) atTop atTop :=
    tendsto_atTop_mono hmN tendsto_id
  -- the digit agreement on each window, from the `ConditionStar` periodicity clause
  have hagree : ∀ m, ∀ k, k < r m + ⌊w * (s m : ℝ)⌋₊ →
      binaryDigit v k = binaryDigit (truncApprox v (r m) (s m)) k := by
    intro m
    refine binaryDigit_truncApprox_agreement v (r m) (s m) (hs_pos m) ?_
    intro i hi1 hi2
    exact hper m i hi1 hi2
  refine ⟨fun m => truncApprox v (r m) (s m), fun m => r m + ⌊w * (s m : ℝ)⌋₊, hN, ?_⟩
  obtain ⟨hB, hC, hD⟩ := tooWellApproximated_of_agreement hv hN
    (fun m => Φ_truncApprox_mem_ratInt v (r m) (s m) (hs_pos m)) hagree
  exact ⟨hB, hC, hD, fun m => truncApprox_mem_ratInt v (r m) (s m) (hs_pos m)⟩

end B3
