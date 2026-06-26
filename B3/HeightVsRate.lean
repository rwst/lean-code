/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.SubspaceInstantiation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The height-vs-rate over-approximation estimate (Route (i), the Missing Lemma — gap #2)

This file discharges the **quantitative crux** of the `Φ`-side Subspace application
([[b3-automatic-cc-corpus-root]], `B3.phi_value_transcendental`): the *height-vs-rate* estimate that
turns the constructed too-well-approximated family (`B3.conditionStar_tooWellApproximated`) into the
inequality the multidimensional Subspace Theorem (`AB.subspace_theorem_E`) consumes.

## The estimate

The approximants `Φ(αₘ) = −Pₘ / (3^{cₘ} − 2^{pₘ})` (`B3.Φ_blockValue_mem_ratInt`) carry a **base-`3`**
denominator `subspaceDen cₘ pₘ = 3^{cₘ} − 2^{pₘ}` — the height carrier of the Subspace point
`xₘ = (3^{cₘ} − 2^{pₘ}, −1, −Pₘ)`, of size `≈ 3^{cₘ}` (`cₘ ≈` odd-step count `ℓ`). Meanwhile the
over-approximation rate is **base-`2`**: `‖n − Φ(αₘ)‖₂ ≤ 2^{−Nₘ}` (`Nₘ ≈` total-step count `dₗ`). For the
Subspace product to undercut `H(xₘ)^{−3−ε}` one needs the base-`2` rate to beat the base-`3` height:

> `2^{−Nₘ} ≤ (3^{cₘ})^{−3−ε}`   (the **height-vs-rate estimate**),

which, on taking logarithms, is *exactly* the **index condition**

> `(3 + ε) · cₘ · log 3 ≤ Nₘ · log 2`   (`IndexCondition`).

## What is proved here, and what is open

The **conversion** — index condition ⟹ height-vs-rate inequality — is provable real analysis and is the
content of this file:

* `rate_le_den_rpow` / `rate_le_height_rpow` / `rate_le_subspaceDen_rpow` (proved): the index condition
  gives `2^{−N} ≤ D^{−3−ε}` for any height carrier `0 < D ≤ 3^c` — in particular `D = 3^c` and
  `D = subspaceDen c p` (`subspaceDen_le_pow`: `3^c − 2^p ≤ 3^c`). Bounding against the *larger* `3^c`
  is the safe (sufficient) direction, since `t ↦ t^{−3−ε}` is antitone, so `(3^c)^{−3−ε}` *lower*-bounds
  the true height power.
* `family_rate_le_height` (proved, from the `IndexCondition` hypothesis): the estimate for the whole
  approximant family.
* `index_of_large_w` / `rate_le_height_of_large_w` (proved): the **large-repetition regime** of the index
  condition — if the stammering exponent `w` satisfies `(3 + ε)·log 3 ≤ (w − 1)·log 2` (i.e.
  `w ≥ (3+ε)·log 3/log 2 + 1`), then, using only `cₘ ≤ sₘ` (a block of length `sₘ` has `≤ sₘ` ones) and
  `Nₘ ≥ w·sₘ − 1`, the index condition holds for **every** `m`. This is the precise, quantitative form of
  "`w > 1` ⟹ converges too fast", and the threshold `(3+ε)·log 3/log 2` is exactly the base-`3`-vs-base-`2`
  cost.

What stays **open** is the index condition itself in the **small-repetition regime** (the automatic
sequence only guarantees `w > 1`, generally below the `(3+ε)·log 3/log 2 + 1` threshold). There the
estimate must instead come from the finer `ℓ`-versus-`dₗ` structure of the `3x+1` parity vector (the
base-`2`/base-`3` independence — Cobham/Mahler territory). That is the genuine research content; it is
**not** proved and **not** axiomatised — it is recorded as the hypothesis `IndexCondition`, threaded into
the estimate, never asserted as a theorem (corpus policy on open conjectures).

So this file converts the open content of `B3.phi_value_transcendental` from "the whole Subspace step" into the single,
sharply-stated index inequality `IndexCondition`, and proves it outright whenever the repetition is large.

## Contents
* `rate_le_den_rpow_gen` — (proved) the core at an arbitrary exponent `τ`: index condition ⟹
  `2^{−N} ≤ D^{−τ−ε}` for `0 < D ≤ 3^c` (the `τ = 2` arch-saving and `τ = 3` plain cases share one proof).
* `rate_le_den_rpow` — (proved) the `τ = 3` instance: `2^{−N} ≤ D^{−3−ε}` for `0 < D ≤ 3^c`.
* `rate_le_height_rpow` — (proved) the `D = 3^c` specialisation.
* `subspaceDen_le_pow`, `rate_le_subspaceDen_rpow` — (proved) the estimate against the base-`3`
  denominator `subspaceDen c p = 3^c − 2^p`.
* `IndexConditionExp` / `IndexCondition` / `IndexConditionExpFreq` — the index inequality
  `(τ+ε) cₘ log 3 ≤ Nₘ log 2` at an arbitrary threshold `τ` (its `τ = 3` case `IndexCondition`, and its
  **frequently** `∃ᶠ m` form `IndexConditionExpFreq` for the Tier 2.2 subsequence relaxation) — the open
  `ℓ`-vs-`dₗ` content, supplied as a hypothesis.
* `family_rate_le_height` — (proved) the family estimate from `IndexCondition`.
* `index_of_large_w_gen`, `index_of_large_w`, `rate_le_height_of_large_w` — (proved) the index condition /
  estimate in the large-repetition regime, at an arbitrary threshold `τ` (and its `τ = 3` case); the
  arch-saving `τ = 2` widens the provable regime to `w ≥ ~3.77`.

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6: the over-approximation `|α' − αₙ|_p ≤ p^{−rₙ−w sₙ}` driving the
  Subspace contradiction — the template, here adapted to the base-`3` `Φ`-image).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the formula `(1.6)` giving the base-`3` denominators `3^{cₘ} − 2^{pₘ}`).
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311 (the height `H(x)^{−m−ε}` form of the Subspace bound this estimate must beat).
-/

namespace B3

open BL AB Function

/-! ### The core estimate: index condition ⟹ height-vs-rate inequality -/

/-- **The height-vs-rate estimate at an arbitrary exponent `τ` (proved, general height carrier).** If the
**index condition** `(τ + ε)·c·log 3 ≤ N·log 2` holds (with `0 ≤ τ`), then for any `0 < D ≤ 3^c` the
base-`2` rate `2^{−N}` is at most the height power `D^{−τ−ε}`:

> `(2:ℝ)^{−N} ≤ D^{−τ−ε}`.

*Proof:* write both sides as `Real.exp` (`rpow_def_of_pos`); since `exp` is monotone the claim is
`log 2 · (−N) ≤ log D · (−τ−ε)`, i.e. `(τ+ε)·log D ≤ N·log 2`. Now `log D ≤ log (3^c) = c·log 3`
(`Real.log_le_log`, `Real.log_pow`), so `(τ+ε)·log D ≤ (τ+ε)·c·log 3 ≤ N·log 2` (the index condition). The
exponent `τ` is left free so the **archimedean-saving** instantiation `τ = 2` (`B3.phiPoints_rate`, the
`Φ`-side rate after the `H⁻¹` factor of `B3.subspace_contradiction_of_rate_sharp`) and the original `τ = 3`
(`rate_le_den_rpow`) share one proof. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_den_rpow_gen (τ : ℝ) (hτ : 0 ≤ τ) (c N : ℕ) {D : ℝ} (hD : 0 < D)
    (hDle : D ≤ (3 : ℝ) ^ c) (ε : ℝ) (hε : 0 < ε)
    (hidx : (τ + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ D ^ (-τ - ε) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : Real.log D ≤ (c : ℝ) * Real.log 3 := by
    have h := Real.log_le_log hD hDle
    rwa [Real.log_pow] at h
  have hτε : (0 : ℝ) ≤ τ + ε := by linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hD, Real.exp_le_exp]
  nlinarith [hidx, hlogD, hlog2, mul_le_mul_of_nonneg_left hlogD hτε]

/-- **The height-vs-rate estimate (proved, general height carrier).** If the **index condition**
`(3 + ε)·c·log 3 ≤ N·log 2` holds, then for any `0 < D ≤ 3^c` the base-`2` rate `2^{−N}` is at most the
height power `D^{−3−ε}`:

> `(2:ℝ)^{−N} ≤ D^{−3−ε}`.

The `τ = 3` instance of `rate_le_den_rpow_gen`; the hypothesis `D ≤ 3^c` bounds against the *largest*
admissible height `3^c` (as `t ↦ t^{−3−ε}` is antitone, `(3^c)^{−3−ε} ≤ D^{−3−ε}`), the sufficient
direction for the true (smaller) Subspace height. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_den_rpow (c N : ℕ) {D : ℝ} (hD : 0 < D) (hDle : D ≤ (3 : ℝ) ^ c)
    (ε : ℝ) (hε : 0 < ε)
    (hidx : (3 + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ D ^ (-(3 : ℝ) - ε) :=
  rate_le_den_rpow_gen 3 (by norm_num) c N hD hDle ε hε hidx

/-- **The height-vs-rate estimate against `3^c` (proved).** The `D = 3^c` specialisation of
`rate_le_den_rpow`: the index condition `(3 + ε)·c·log 3 ≤ N·log 2` gives
`2^{−N} ≤ (3^c)^{−3−ε}`. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_height_rpow (c N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hidx : (3 + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ ((3 : ℝ) ^ c) ^ (-(3 : ℝ) - ε) :=
  rate_le_den_rpow c N (by positivity) le_rfl ε hε hidx

/-! ### The estimate against the base-`3` denominator `subspaceDen` -/

/-- **The denominator is at most `3^c`.** `subspaceDen c p = 3^c − 2^p ≤ 3^c` (as a real number), since
`2^p ≥ 0`. So `3^c` is the height carrier's upper bound, and `rate_le_den_rpow` applies at
`D = subspaceDen c p`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem subspaceDen_le_pow (c p : ℕ) : ((subspaceDen c p : ℤ) : ℝ) ≤ (3 : ℝ) ^ c := by
  unfold subspaceDen
  push_cast
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  linarith

/-- **The height-vs-rate estimate against the base-`3` denominator (proved).** When the height carrier
`subspaceDen c p = 3^c − 2^p` is positive (`2^p < 3^c`), the index condition gives
`2^{−N} ≤ (3^c − 2^p)^{−3−ε}` — the over-approximation inequality stated against the *actual* Subspace
denominator. (`rate_le_den_rpow` with `D = subspaceDen c p`, via `subspaceDen_le_pow`.) -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_subspaceDen_rpow (c p N : ℕ) (hDpos : 0 < subspaceDen c p)
    (ε : ℝ) (hε : 0 < ε)
    (hidx : (3 + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ ((subspaceDen c p : ℤ) : ℝ) ^ (-(3 : ℝ) - ε) := by
  refine rate_le_den_rpow c N ?_ (subspaceDen_le_pow c p) ε hε hidx
  exact_mod_cast hDpos

/-! ### The index condition (open content) and the family estimate -/

/-- **The index condition at an arbitrary exponent `τ`** `(τ + ε)·cₘ·log 3 ≤ Nₘ·log 2` for an approximant
family `(cₘ, Nₘ)`: the base-`2` over-approximation modulus `Nₘ` dominates `(τ+ε)·log 3/log 2` times the
base-`3` height exponent `cₘ`. The exponent `τ` is the Subspace height threshold the rate must beat: `τ = 3`
for the plain instantiation (`IndexCondition`), `τ = 2` after the **archimedean `H⁻¹` saving** of
`B3.subspace_contradiction_of_rate_sharp` (`B3.phiPoints_index`). This is the `ℓ`-versus-`dₗ` relationship
(`cₘ ≈` odd steps, `Nₘ ≈` total steps) — the genuine open content of the `Φ`-side Subspace step
(base-`2`/base-`3` independence, Cobham/Mahler), **supplied as a hypothesis**, never asserted; proved
outright only in the large-repetition regime (`index_of_large_w`). -/
@[category API, AMS 11 37, ref "AB07" "BL96"]
def IndexConditionExp (τ : ℝ) (c N : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ m, (τ + ε) * (c m : ℝ) * Real.log 3 ≤ (N m : ℝ) * Real.log 2

/-- **The index condition** `(3 + ε)·cₘ·log 3 ≤ Nₘ·log 2` — the `τ = 3` case of `IndexConditionExp`, the
threshold for the plain (non-arch-saving) Subspace instantiation. -/
@[category API, AMS 11 37, ref "AB07" "BL96"]
def IndexCondition (c N : ℕ → ℕ) (ε : ℝ) : Prop :=
  IndexConditionExp 3 c N ε

/-- **The frequently-satisfied index condition** (Tier 2.2): `(τ + ε)·cₘ·log 3 ≤ Nₘ·log 2` for
**infinitely many** `m` (`∃ᶠ m in atTop`), rather than *all* `m`. The Subspace contradiction
(`B3.subspace_contradiction_of_rate_sharp_frequently`) only ever needs a good *subsequence* of approximants
— matching Adamczewski–Bugeaud — so this is the genuinely necessary (weaker, hence more honest) form of the
open kernel `B3.phiPoints_index`. *Caveat:* it is **not** a route to unconditionality — for a balanced
sequence the index ratio `cₘ/Nₘ` is asymptotically constant, so the frequent good set is infinite exactly
when the universal one is non-empty; the `∃ᶠ` relaxation is correctness/hygiene, not a closing of the gap
(that is Tier 3). -/
@[category API, AMS 11 37, ref "AB07" "BL96"]
def IndexConditionExpFreq (τ : ℝ) (c N : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∃ᶠ m in Filter.atTop, (τ + ε) * (c m : ℝ) * Real.log 3 ≤ (N m : ℝ) * Real.log 2

/-- **The family height-vs-rate estimate (proved, from `IndexCondition`).** Given the index condition for
a family `(cₘ, Nₘ)`, every member satisfies `2^{−Nₘ} ≤ (3^{cₘ})^{−3−ε}`. (Pointwise `rate_le_height_rpow`.)
This is the exact input a Subspace-Theorem transcendence argument consumes on the `Φ`-side. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem family_rate_le_height (c N : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hidx : IndexCondition c N ε) (m : ℕ) :
    (2 : ℝ) ^ (-(N m : ℝ)) ≤ ((3 : ℝ) ^ (c m)) ^ (-(3 : ℝ) - ε) :=
  rate_le_height_rpow (c m) (N m) ε hε (hidx m)

/-! ### The large-repetition regime: the index condition, proved -/

/-- **The index condition holds for large repetition, at an arbitrary threshold `τ` (proved).** Suppose the
block count `c` and period `s` satisfy `c ≤ s` (a length-`s` block has at most `s` ones), the modulus
satisfies `N ≥ w·s − 1` (the stammering-window length `Nₘ = rₘ + ⌊w·sₘ⌋ ≥ ⌊w·sₘ⌋ > w·sₘ − 1`), and the
repetition exponent is large, `(τ + ε)·log 3 ≤ (w − 1)·log 2` (i.e. `w ≥ (τ+ε)·log 3/log 2 + 1`, with
`0 ≤ τ`). Then the index condition `(τ + ε)·c·log 3 ≤ N·log 2` holds.

*Proof:* for `c = 0` it is trivial. For `c ≥ 1`: the threshold gives `(τ+ε)·log 3 ≤ (w−1)·log 2`, so
`(τ+ε)·c·log 3 ≤ c·(w−1)·log 2`; and `c·(w−1) = c·w − c ≤ s·w − 1 ≤ N` (using `c ≤ s`, `c ≥ 1`,
`N ≥ w·s − 1`), whence `c·(w−1)·log 2 ≤ N·log 2`. The **arch-saving** threshold `τ = 2` (Tier 2.1) widens
the provable regime to `w ≥ (2+ε)·log 3/log 2 + 1 ≈ 4.17` (from `≈ 5.75` for `τ = 3`). This worst-case form
uses only `c ≤ s`; it is still short of the small-`w` / overlap-free (Thue–Morse, `w ≤ 2`) case. (The
*actual* index condition at the overlap-free density `c/s ≈ ½` **is** met at `τ = 2` — `2·½·log 3 ≤ log 2·…`
— but capturing that needs a density-aware bound, not this `c ≤ s` worst case; unconditional small-`w` is
Tier 3.) -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem index_of_large_w_gen (τ : ℝ) (hτ : 0 ≤ τ) (c s N : ℕ) (w ε : ℝ) (hε : 0 < ε)
    (hcs : c ≤ s) (hsN : w * (s : ℝ) - 1 ≤ (N : ℝ))
    (hw : (τ + ε) * Real.log 3 ≤ (w - 1) * Real.log 2) :
    (τ + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0; simp only [Nat.cast_zero, mul_zero, zero_mul]; positivity
  · have hcpos' : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcpos
    have hcs' : (c : ℝ) ≤ (s : ℝ) := by exact_mod_cast hcs
    have hwpos : (1 : ℝ) < w := by
      nlinarith [hw, hlog2, mul_pos (show (0 : ℝ) < τ + ε by linarith) hlog3]
    have hcw : (c : ℝ) * (w - 1) ≤ (N : ℝ) := by
      nlinarith [hsN, hcpos', mul_le_mul_of_nonneg_right hcs' (by linarith : (0 : ℝ) ≤ w)]
    calc (τ + ε) * (c : ℝ) * Real.log 3
        ≤ (c : ℝ) * (w - 1) * Real.log 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hw (show (0 : ℝ) ≤ (c : ℝ) by linarith)]
      _ ≤ (N : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hcw hlog2.le

/-- **The index condition holds for large repetition (proved).** The `τ = 3` case of
`index_of_large_w_gen`: if `c ≤ s`, `N ≥ w·s − 1`, and `(3 + ε)·log 3 ≤ (w − 1)·log 2`
(i.e. `w ≥ (3+ε)·log 3/log 2 + 1`), then `(3 + ε)·c·log 3 ≤ N·log 2`. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem index_of_large_w (c s N : ℕ) (w ε : ℝ) (hε : 0 < ε)
    (hcs : c ≤ s) (hsN : w * (s : ℝ) - 1 ≤ (N : ℝ))
    (hw : (3 + ε) * Real.log 3 ≤ (w - 1) * Real.log 2) :
    (3 + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2 :=
  index_of_large_w_gen 3 (by norm_num) c s N w ε hε hcs hsN hw

/-- **The height-vs-rate estimate in the large-repetition regime (proved).** Combining
`index_of_large_w` with `rate_le_height_rpow`: if `c ≤ s`, `N ≥ w·s − 1`, and the repetition is large
(`(3 + ε)·log 3 ≤ (w − 1)·log 2`), then `2^{−N} ≤ (3^c)^{−3−ε}` — the over-approximation inequality holds
unconditionally (no `IndexCondition` hypothesis needed). -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_height_of_large_w (c s N : ℕ) (w ε : ℝ) (hε : 0 < ε)
    (hcs : c ≤ s) (hsN : w * (s : ℝ) - 1 ≤ (N : ℝ))
    (hw : (3 + ε) * Real.log 3 ≤ (w - 1) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ ((3 : ℝ) ^ c) ^ (-(3 : ℝ) - ε) :=
  rate_le_height_rpow c N ε hε (index_of_large_w c s N w ε hε hcs hsN hw)

end B3
