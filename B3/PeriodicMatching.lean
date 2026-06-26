/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.PrefixApproximants
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The periodicity-clause induction: matching `v` on a stammering window (Route (i), Phase 3→4)

This file carries out the **periodicity-clause induction** that turns Adamczewski–Bugeaud's
`ConditionStar` (`AB.ConditionStar`, [[ab-complexity-corpus-root]]) into the digit agreement `hagree`
that `blockVal_tooWellApproximated` (`B3.StammeringWiring`) needs.

`ConditionStar` provides, for each `n`, a pre-period `rₙ`, a period `sₙ`, and the *local* periodicity
clause `a i = a (i − sₙ)` on the window `[rₙ + sₙ, rₙ + ⌊w·sₙ⌋)`. The pre-period–aware approximant
`prefixBlockVal A t c p e` (`B3.PrefixApproximants`, `t = rₙ`, `p = sₙ`) has, by construction, digits that
are eventually `p`-periodic past `t` (`binaryDigit_prefixBlockVal_ge` + `binaryDigit_blockVal_add_period`).
The key lemma propagates agreement from the first prefix-plus-period `[0, t + p)` to the *whole* window
`[0, N)`:

* **`binaryDigit_prefixBlockVal_eq_of_periodic`** (proved). If the approximant agrees with `v` on
  `[0, t + p)` (`hprefix`) and `v` is `p`-periodic on `[t + p, N)` (`hper`, the `ConditionStar` clause
  with `t = rₙ`, `p = sₙ`), then they agree on all of `[0, N)`. *Proof:* strong induction on `k` — below
  `t + p` it is `hprefix`; at `t + p ≤ k < N`, both `v` and the approximant satisfy
  `digit k = digit (k − p)` (for `v` by `hper`, for the approximant by its eventual periodicity), so the
  induction hypothesis at `k − p` closes it.

The hypothesis `hprefix` is the **construction half** — that the approximant's pre-period and first block
reproduce `v`'s first `t + p` digits. Its pre-period part is discharged here
(`binaryDigit_prefixBlockVal_lt_eq_of_dvd`: choose `A ≡ v (mod 2^t)`); its *block* part — that
`blockVal`'s first period equals `v`'s digits on `[rₙ, rₙ + sₙ)` — is the remaining plumbing (choose the
block value `B = (toZModPow sₙ (Sʳⁿ v)).val` and decompose `B = ∑ 2^{eₖ}` via `Nat.bitIndices`,
`Nat.sum_map_two_pow_bitIndices`). The one degenerate case that decomposition hits — an **all-zero
block** `B = 0` forcing `c = 0` — is now handled at the source: `blockVal 0 p e = 0`
(`B3.BlockApproximants`, `blockVal_zero`), and every lemma in this development (including this file's
`binaryDigit_window_agreement`) is stated **without** a `0 < c` hypothesis, so it applies uniformly to the
empty block, where `prefixBlockVal A t 0 p e = A` is the bare pre-period natural number and
`blockFirst 0 e = 0`. The induction here is the mathematical core.

## Contents
* `binaryDigit_prefixBlockVal_lt_eq_of_dvd` — pre-period agreement from `A ≡ v (mod 2^t)`.
* `binaryDigit_prefixBlockVal_eq_of_periodic` — (proved) the periodicity-clause induction:
  prefix agreement + `ConditionStar` periodicity ⟹ agreement on the whole window.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169.
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§4, Condition (∗)_w and its truncate-and-complete approximants).
-/

namespace B3

open BL AB Function Filter

/-- **Pre-period agreement.** If `A ≡ v (mod 2^t)` (i.e. `2^t ∣ v − A`), then within the pre-period the
approximant reproduces `v`'s digits: `binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k` for
`k < t`. From `binaryDigit_prefixBlockVal_lt` and the digit bridge `binaryDigit_agree_of_dvd_two_pow`. -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_lt_eq_of_dvd {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hAv : (2 : ℤ_[2]) ^ t ∣ v - (A : ℤ_[2])) {k : ℕ} (hk : k < t) :
    binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k := by
  rw [binaryDigit_prefixBlockVal_lt hk]
  exact binaryDigit_agree_of_dvd_two_pow t v ((A : ℕ) : ℤ_[2]) hAv k hk

/-- **The periodicity-clause induction (proved).** Suppose the approximant `prefixBlockVal A t c p e`
(`A < 2^t`) agrees with `v` on the first prefix-plus-period `[0, t + p)` (`hprefix`), and `v` is
`p`-periodic on the window `[t + p, N)`:  `binaryDigit v i = binaryDigit v (i − p)` (`hper`). Then they
agree on the *whole* window: `binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k` for all
`k < N`.

With `t = rₙ`, `p = sₙ`, `hper` is exactly Adamczewski–Bugeaud's `ConditionStar` clause (i) (shifted by
the pre-period), so this is the step that converts `ConditionStar` into the digit agreement `hagree` of
`blockVal_tooWellApproximated`. *Proof:* strong induction on `k`; below `t + p` use `hprefix`, and at
`t + p ≤ k < N` reduce to `k − p` (`v` periodic by `hper`, the approximant periodic past `t` by
`binaryDigit_prefixBlockVal_ge` + `binaryDigit_blockVal_add_period`). -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_eq_of_periodic {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hp : 0 < p) (he_lt : ∀ r, r < c → e r < p)
    (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (hA : A < 2 ^ t) {N : ℕ}
    (hprefix : ∀ k, k < t + p → binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k)
    (hper : ∀ i, t + p ≤ i → i < N → binaryDigit v i = binaryDigit v (i - p)) :
    ∀ k, k < N → binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkN
    rcases lt_or_ge k (t + p) with hk | hk
    · exact hprefix k hk
    · have hper_k : binaryDigit v k = binaryDigit v (k - p) := hper k hk hkN
      have hα : binaryDigit (prefixBlockVal A t c p e) k
          = binaryDigit (prefixBlockVal A t c p e) (k - p) := by
        rw [binaryDigit_prefixBlockVal_ge hA (by omega : t ≤ k),
            binaryDigit_prefixBlockVal_ge hA (by omega : t ≤ k - p),
            show k - t = ((k - p) - t) + p from by omega]
        exact binaryDigit_blockVal_add_period hp he_lt he_mono _
      have hih : binaryDigit v (k - p) = binaryDigit (prefixBlockVal A t c p e) (k - p) :=
        ih (k - p) (by omega) (by omega)
      rw [hper_k, hih, hα]

/-! ### Reducing the prefix agreement to two divisibility conditions -/

/-- Shifting `v` shifts its digits: `binaryDigit (Sᵗ v) j = binaryDigit v (t + j)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem binaryDigit_S_iterate (v : ℤ_[2]) (t j : ℕ) :
    binaryDigit (S^[t] v) j = binaryDigit v (t + j) := by
  unfold binaryDigit
  rw [← Function.iterate_add_apply S j t v, Nat.add_comm j t]

/-- **Block agreement.** If the block value `blockFirst c e` matches `Sᵗ v` modulo `2^p`
(`2^p ∣ Sᵗ v − blockFirst c e`), then inside the first block `[t, t + p)` the approximant reproduces
`v`'s digits. *Proof:* `binaryDigit (prefixBlockVal …) k = binaryDigit (blockVal …) (k − t) =
binaryDigit (blockFirst : ℤ₂) (k − t)` (first period, `binaryDigit_blockVal_eq_first`), which equals
`binaryDigit (Sᵗ v) (k − t) = binaryDigit v k` via the digit bridge. -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_block_eq_of_dvd {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hp : 0 < p) (he_lt : ∀ r, r < c → e r < p)
    (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (hA : A < 2 ^ t)
    (hBv : (2 : ℤ_[2]) ^ p ∣ S^[t] v - ((blockFirst c e : ℕ) : ℤ_[2])) {k : ℕ}
    (hk1 : t ≤ k) (hk2 : k < t + p) :
    binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k := by
  rw [binaryDigit_prefixBlockVal_ge hA hk1, binaryDigit_blockVal_eq_first hp he_lt he_mono,
      Nat.mod_eq_of_lt (by omega : k - t < p)]
  conv_lhs => rw [show k = t + (k - t) from by omega, ← binaryDigit_S_iterate v t (k - t)]
  exact binaryDigit_agree_of_dvd_two_pow p (S^[t] v) ((blockFirst c e : ℕ) : ℤ_[2]) hBv (k - t)
    (by omega)

/-- **The prefix agreement from two divisibility conditions (proved).** If `A ≡ v (mod 2^t)` and the
block `blockFirst c e ≡ Sᵗ v (mod 2^p)`, then the approximant reproduces `v`'s digits on the whole first
prefix-plus-period `[0, t + p)` — i.e. it supplies the `hprefix` hypothesis of
`binaryDigit_prefixBlockVal_eq_of_periodic`. Combined with that lemma and `ConditionStar`'s periodicity
clause, this reduces the full window agreement `hagree` to: choosing the pre-period `A` (free) and the
block value `B = blockFirst c e` (its bit-positions give `e`; `Nat.bitIndices`) meeting the two
congruences. -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem prefixAgreement_of_dvd {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hp : 0 < p) (he_lt : ∀ r, r < c → e r < p)
    (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (hA : A < 2 ^ t)
    (hAv : (2 : ℤ_[2]) ^ t ∣ v - ((A : ℕ) : ℤ_[2]))
    (hBv : (2 : ℤ_[2]) ^ p ∣ S^[t] v - ((blockFirst c e : ℕ) : ℤ_[2])) :
    ∀ k, k < t + p → binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k := by
  intro k hk
  rcases lt_or_ge k t with hkt | hkt
  · exact binaryDigit_prefixBlockVal_lt_eq_of_dvd hAv hkt
  · exact binaryDigit_prefixBlockVal_block_eq_of_dvd hp he_lt he_mono hA hBv hkt hk

/-- **The full window agreement (proved), assembled.** Given the block hypotheses, `A < 2^t`, the two
congruences `A ≡ v (mod 2^t)` and `blockFirst c e ≡ Sᵗ v (mod 2^p)`, and `v`'s `p`-periodicity on
`[t + p, N)` (Adamczewski–Bugeaud's `ConditionStar` clause with `t = rₙ`, `p = sₙ`), the approximant
`prefixBlockVal A t c p e` agrees with `v` on all of `[0, N)`. This is exactly the digit-agreement
`hagree` that `blockVal_tooWellApproximated` consumes — modulo the construction of `A` and the block
value `B` meeting the congruences. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem binaryDigit_window_agreement {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hp : 0 < p) (he_lt : ∀ r, r < c → e r < p)
    (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (hA : A < 2 ^ t)
    (hAv : (2 : ℤ_[2]) ^ t ∣ v - ((A : ℕ) : ℤ_[2]))
    (hBv : (2 : ℤ_[2]) ^ p ∣ S^[t] v - ((blockFirst c e : ℕ) : ℤ_[2])) {N : ℕ}
    (hper : ∀ i, t + p ≤ i → i < N → binaryDigit v i = binaryDigit v (i - p)) :
    ∀ k, k < N → binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k :=
  binaryDigit_prefixBlockVal_eq_of_periodic hp he_lt he_mono hA
    (prefixAgreement_of_dvd hp he_lt he_mono hA hAv hBv) hper

end B3
