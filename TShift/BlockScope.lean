/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.DyadicBlocks
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The scope of Theorem A: what the rate costs, and what the base is free to be

`TShift/DyadicBlocks.lean` proves Theorem A — the failures of `‖D(p/q)ⁿ‖ < cⁿ` meet at most
`B = K(ε(p,c))·(t+1) + ⌊log₂ N⌋ + 1` dyadic blocks — and instantiates it at `(p, q, D, c)
= (3, 2, 5, 3/4)`.  This file moves Theorem A along its two free parameters and prices each move.
It is WP7 of `plans/plan-Tshift-S2.html`.

## (a) The rate: the price of `θ → 1`

The plan's original question ("how fast does the shadow degrade as `θ ↓ 2/3`?") is backwards
(finding F9): `B` is *smallest* at `θ ↓ 2/3` and blows up as `θ ↑ 1`.  This file states the price
in that, the correct, direction.

* The line count is **monotone in the rate**: `c₁ ≤ c₂ ⟹ K(ε(p,c₁)) ≤ K(ε(p,c₂))`
  (`lineBound_epsilon_mono`), and so is the whole bound (`blockBound_mono`).  The showcase rate
  `3/4` is therefore cheaper than every rate above it, and `θ ↓ 2/3` is the cheapest end.
* The blow-up is **at least cubic**: `K(ε(3,θ)) ≥ 1.27·10⁹/(1−θ)³` for `2/3 ≤ θ < 1`
  (`lineBound_price_cubic`), whence no bound uniform in the rate exists on this route
  (`exists_rate_lineBound_ge`).
* The *other* term does **not** blow up: at base `3/2` a single span `t = 2` serves **every**
  rate `c ≤ 1` (`one_le_four_mul_fArch_three_two`), and `t = 1` still serves every `c ≤ 3/4`.
  So the whole `θ → 1` price sits in `K`, and Theorem A holds at every rate with `t = 2` fixed
  (`TShift.badBlocks_three_two_card_le_rate`).

## (b) The base: the parity scope is free

`BB13.residMul_odd` was stated at `q = 2`.  Nothing in it uses `q = 2` beyond `2 ∣ q`: for `D` and
`p` odd and **`q` even**, `kₙ = D·pⁿ − mₙ·qⁿ` is odd for every `n ≥ 1`, hence never `0`
(`residMul_odd_of_even`, `admissibleMul_of_odd_of_even`).  Since the rest of the per-line layer is
`D`-free and the block bookkeeping is `(p,q)`-free, Theorem A follows at **every** coprime pair
`p > q ≥ 2` with `p` odd and `q` even, at every odd multiplier and every rate — with the two
remaining parameters supplied by existence lemmas that the numerals discharge per instance
(`exists_badBlocks_card_le_of_odd`).  Two new instances are given in full: `(5,2)` with span
`t = 1`, and `(5,4)` — where `q` is even but *not* `2`, the case the old parity clause could not
reach — with span `t = 2`.

Both moves are free of new axioms and of new numerics: they reuse `mahler_line_cover` exactly as
`TShift/DyadicBlocks.lean` does.

## Contents

* `BB13.log_six_ge`, `lineBound_le_of_le`, `epsilon_antitone`, `lineBound_epsilon_mono`,
  `blockBound_mono` — the line count as a function of the rate.
* `BB13.inv_cube_le_lineBound`, `lineBound_price_cubic`, `exists_rate_lineBound_ge` — the `θ → 1`
  price: `K ≥ 2³²/ε³`, i.e. `≥ 1.27·10⁹/(1−θ)³`, and hence unbounded.
* `BB13.one_le_two_pow_mul_fArch` — the span certificate in rational form: `2^t·f_∞ ≥ 1` reduces
  to `(p/(cq))^{2^t} ≥ p`.  Instances: `one_le_four_mul_fArch_three_two` (every `c ≤ 1`),
  `one_le_two_mul_fArch_three_two` (every `c ≤ 3/4`).
* `BB13.residMul_odd_of_even`, `admissibleMul_of_odd_of_even` — the parity scope at even `q`.
* `BB13.badBlocks_finite`, `exists_two_pow_mul_fArch`, `exists_badBlocks_card_le`,
  `exists_badBlocks_card_le_of_odd`, `exists_badBlocks_card_le_of_lt` — Theorem A at a general
  base, with the two parameters existentially supplied.
* `BB13.threshold_of_two_mul_lt_pow` — the height threshold in the form the instances use.
* `TShift.badBlocks_three_two_card_le_rate`, `exists_badBlocks_three_two_card_le` — Theorem A at
  base `3/2` at *every* rate, span `t = 2`.
* `TShift.badBlocks_five_two_card_le`, `badBlocks_five_four_card_le` — the two new bases.
* `TShift.mahler_failures_mul_finite_of_odd_of_even` — Theorem C in the parity scope.

## What is not here

* **No decimal at the new bases.**  `K(ε(5,3/4))` is left symbolic: its certification would need
  enclosures for `log 5`, which this corpus does not carry (the `3/2` showcase is free only
  because `ε(3,3/4) = ε*`).  The true values are tabulated by `tshift_numerics.py`'s `s2` block:
  `K(ε(5,3/4)) = 5 449 831 243 823`, `B(5,2) = 1.09·10¹³`, `B(5,4) = 1.63·10¹³`.
* **No lower bound on the truth.**  `lineBound_price_cubic` and `exists_rate_lineBound_ge` are
  statements about the *bound* `B`, i.e. about the price of this method.  Nothing here says the
  number of bad blocks itself grows as `θ → 1`; at `θ = 3/4` no bad block above the threshold has
  ever been exhibited.
* **No new mechanism.**  Both moves reuse the [BE08] cover; neither improves `κ`, locates a block,
  or produces a date count.  The limits listed in `TShift/DyadicBlocks.lean` ("What is not here")
  apply verbatim.

## Trust ledger

The rate half (§1–§3) and the parity clause (§4) are `std3`; every statement that *counts*
blocks inherits `std3 + BugeaudEvertse.ridout_line_cover` through `BB13.mahler_line_cover`,
exactly as in `TShift/DyadicBlocks.lean`.  No `sorry`, no `native_decide`, no new cited axiom.

## References

* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), Cor. 5.2 (5.13) — the counted quantity `K(ε)`.
* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957), 122–124.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge, 2012
  (Problem 10.13).
* `plans/plan-Tshift-S2.html` WP7 (this file), findings F9 (the direction of the price) and F2
  (the parity scope); `plans/note-Tshift-S2-blocks.html` §2.2 (the counting convention).
-/

namespace BB13

open scoped Real

/-! ## 1. The line count as a function of the rate

`K(ε) = ⌈2³²(1+ε⁻¹)³·log 6·log((1+ε⁻¹)log 6)⌉` is antitone in `ε`, and `ε(p,c) = log(1/c)/log p`
is antitone in `c`; so the count is *monotone in the rate*, and every statement about the price of
raising `θ` is a statement about `ε → 0`. -/

/-- `log 6 ≥ 1.7917594688` — the lower companion of `BB13.log_six_le`, from
`log 6 = log 2 + log 3`. -/
@[category API, AMS 11, ref "BE08", group "tshift_s2"]
theorem log_six_ge : (1.7917594688 : ℝ) ≤ Real.log 6 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, log_three_ge]

/-- **The line count is antitone in the exponent**: a larger `ε` — a weaker approximation demand —
costs fewer lines. -/
@[category API, AMS 11, ref "BE08", group "tshift_s2"]
theorem lineBound_le_of_le {ε₁ ε₂ : ℝ} (h0 : 0 < ε₁) (h : ε₁ ≤ ε₂) :
    BugeaudEvertse.lineBound ε₂ ≤ BugeaudEvertse.lineBound ε₁ := by
  have h0' : (0 : ℝ) < ε₂ := lt_of_lt_of_le h0 h
  have hinv : ε₂⁻¹ ≤ ε₁⁻¹ := inv_anti₀ h0 h
  have hu2 : (1 : ℝ) ≤ 1 + ε₂⁻¹ := by
    have : (0 : ℝ) < ε₂⁻¹ := by positivity
    linarith
  have hu : (1 : ℝ) + ε₂⁻¹ ≤ 1 + ε₁⁻¹ := by linarith
  have hL : (1 : ℝ) ≤ Real.log 6 := one_le_log_six
  have hcube : (1 + ε₂⁻¹) ^ 3 ≤ (1 + ε₁⁻¹) ^ 3 := pow_le_pow_left₀ (by linarith) hu 3
  have hargpos : (0 : ℝ) < (1 + ε₂⁻¹) * Real.log 6 := by nlinarith
  have harg : (1 + ε₂⁻¹) * Real.log 6 ≤ (1 + ε₁⁻¹) * Real.log 6 := by nlinarith
  have hlogarg : Real.log ((1 + ε₂⁻¹) * Real.log 6) ≤ Real.log ((1 + ε₁⁻¹) * Real.log 6) :=
    Real.log_le_log hargpos harg
  have hlognn : (0 : ℝ) ≤ Real.log ((1 + ε₂⁻¹) * Real.log 6) := Real.log_nonneg (by nlinarith)
  rw [BugeaudEvertse.lineBound, BugeaudEvertse.lineBound]
  refine Nat.ceil_mono ?_
  have hstep : (2 : ℝ) ^ 32 * (1 + ε₂⁻¹) ^ 3 * Real.log 6 ≤ 2 ^ 32 * (1 + ε₁⁻¹) ^ 3 * Real.log 6 :=
    by nlinarith
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ 32 * (1 + ε₂⁻¹) ^ 3 * Real.log 6 := by positivity
  exact mul_le_mul hstep hlogarg hlognn (by positivity)

/-- `ε(p, c)` is antitone in the rate: a larger `c` is a weaker demand. -/
@[category API, AMS 11, ref "Bug12", group "tshift_s2"]
theorem epsilon_antitone {p : ℕ} {c₁ c₂ : ℝ} (hp : 1 < p) (hc0 : 0 < c₁) (h : c₁ ≤ c₂) :
    epsilon p c₂ ≤ epsilon p c₁ := by
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hc0' : (0 : ℝ) < c₂ := lt_of_lt_of_le hc0 h
  have hlog : Real.log (1 / c₂) ≤ Real.log (1 / c₁) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hc0' hc0]
    linarith
  rw [epsilon, epsilon]
  exact div_le_div_of_nonneg_right hlog hlp.le

/-- **The line count is monotone in the rate**: raising `θ` never costs fewer lines.  The showcase
`3/4` is therefore cheaper than every rate above it, and the cheapest end of the admissible range
is `θ ↓ 2/3`, not `θ ↑ 1` (finding F9). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem lineBound_epsilon_mono {p : ℕ} {c₁ c₂ : ℝ} (hp : 1 < p) (hc0 : 0 < c₁) (h : c₁ ≤ c₂)
    (hc1 : c₂ < 1) :
    BugeaudEvertse.lineBound (epsilon p c₁) ≤ BugeaudEvertse.lineBound (epsilon p c₂) :=
  lineBound_le_of_le (epsilon_pos hp (lt_of_lt_of_le hc0 h) hc1) (epsilon_antitone hp hc0 h)

/-- The whole block bound is monotone in the rate, at a fixed span and threshold. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem blockBound_mono {p : ℕ} {c₁ c₂ : ℝ} {t N : ℕ} (hp : 1 < p) (hc0 : 0 < c₁) (h : c₁ ≤ c₂)
    (hc1 : c₂ < 1) : blockBound p c₁ t N ≤ blockBound p c₂ t N := by
  simp only [blockBound]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (lineBound_epsilon_mono hp hc0 h hc1)) _

/-! ## 2. The `θ → 1` price

The blow-up as the rate approaches `1` is at least cubic, and it is the *whole* of the price:
§3 shows the other term of `B` stays put. -/

/-- **`K(ε) ≥ 2³²/ε³`** for `0 < ε ≤ 1`: the line count of [BE08] (5.13) is at least the cube term
of its own definition, the two logarithmic factors contributing more than `1` between them
(`log 6 · log(2 log 6) > 1.96`). -/
@[category research solved, AMS 11, ref "BE08", group "tshift_s2"]
theorem inv_cube_le_lineBound {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (2 : ℝ) ^ 32 / ε ^ 3 ≤ BugeaudEvertse.lineBound ε := by
  have hinv : (1 : ℝ) ≤ ε⁻¹ := by simpa using inv_anti₀ h0 h1
  have hL := log_six_ge
  have hl3 := log_three_ge
  have harg : (3 : ℝ) ≤ (1 + ε⁻¹) * Real.log 6 := by nlinarith
  have hlogarg : Real.log 3 ≤ Real.log ((1 + ε⁻¹) * Real.log 6) :=
    Real.log_le_log (by norm_num) harg
  have hone : (1 : ℝ) ≤ Real.log 6 * Real.log ((1 + ε⁻¹) * Real.log 6) := by nlinarith
  have hcube : (ε⁻¹) ^ 3 ≤ (1 + ε⁻¹) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hprod : (2 : ℝ) ^ 32 * (ε⁻¹) ^ 3 * 1
      ≤ ((2 : ℝ) ^ 32 * (1 + ε⁻¹) ^ 3) * (Real.log 6 * Real.log ((1 + ε⁻¹) * Real.log 6)) := by
    refine mul_le_mul ?_ hone (by norm_num) (by positivity)
    nlinarith
  calc (2 : ℝ) ^ 32 / ε ^ 3 = (2 : ℝ) ^ 32 * (ε⁻¹) ^ 3 * 1 := by
        rw [div_eq_mul_inv, ← inv_pow]; ring
    _ ≤ ((2 : ℝ) ^ 32 * (1 + ε⁻¹) ^ 3) * (Real.log 6 * Real.log ((1 + ε⁻¹) * Real.log 6)) := hprod
    _ = (2 : ℝ) ^ 32 * (1 + ε⁻¹) ^ 3 * Real.log 6 * Real.log ((1 + ε⁻¹) * Real.log 6) := by ring
    _ ≤ (BugeaudEvertse.lineBound ε : ℝ) := by
        rw [BugeaudEvertse.lineBound]; exact Nat.le_ceil _

/-- **The `θ → 1` price, cubic.**  For `2/3 ≤ θ < 1` the line count of Theorem A is at least
`1.27·10⁹/(1−θ)³`: the shadow does not degrade as `θ ↓ 2/3` — it degrades as `θ ↑ 1`, and at least
like the cube of `1/(1−θ)` (finding F9, the corrected direction).

Read as a price: each factor-of-`10` step of `1−θ` costs a factor `10³` in `B`.  This is a
statement about the **bound**, not about the number of bad blocks. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem lineBound_price_cubic {θ : ℝ} (h0 : 2 / 3 ≤ θ) (h1 : θ < 1) :
    (1270000000 : ℝ) / (1 - θ) ^ 3 ≤ BugeaudEvertse.lineBound (epsilon 3 θ) := by
  have hθ0 : (0 : ℝ) < θ := by linarith
  have hθ1 : (0 : ℝ) < 1 - θ := by linarith
  have hl3 := log_three_ge
  have hl3pos : (0 : ℝ) < Real.log 3 := by linarith
  have hlogθ : Real.log (1 / θ) ≤ (1 - θ) / θ := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / θ by positivity)
    have heq : 1 / θ - 1 = (1 - θ) / θ := by field_simp
    linarith [heq ▸ h]
  have hlogθ' : Real.log (1 / θ) ≤ 3 / 2 * (1 - θ) := by
    have hdiv : (1 - θ) / θ ≤ 3 / 2 * (1 - θ) := by
      rw [div_le_iff₀ hθ0]
      nlinarith
    linarith
  have hε : epsilon 3 θ ≤ 3 / 2 * (1 - θ) := by
    rw [epsilon, div_le_iff₀ (by exact_mod_cast hl3pos)]
    nlinarith
  have hε0 : 0 < epsilon 3 θ := epsilon_pos (by norm_num) hθ0 h1
  have hε1 : epsilon 3 θ ≤ 1 := by nlinarith
  refine le_trans ?_ (inv_cube_le_lineBound hε0 hε1)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hc3 : (epsilon 3 θ) ^ 3 ≤ (3 / 2 * (1 - θ)) ^ 3 := pow_le_pow_left₀ hε0.le hε 3
  nlinarith [pow_pos hθ1 3]

/-- **No bound uniform in the rate.**  For every `M` there is a rate `θ ∈ (2/3, 1)` whose line
count exceeds `M`, so Theorem A's constant cannot be made independent of `θ` on this route.  (What
is unbounded is the *bound*; see the module docstring.) -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem exists_rate_lineBound_ge (M : ℕ) :
    ∃ θ : ℝ, 2 / 3 < θ ∧ θ < 1 ∧ M ≤ BugeaudEvertse.lineBound (epsilon 3 θ) := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hpos : (0 : ℝ) < (M : ℝ) + 4 := by linarith
  have hne : ((M : ℝ) + 4) ≠ 0 := ne_of_gt hpos
  have hsmall : 1 / ((M : ℝ) + 4) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hspos : (0 : ℝ) < 1 / ((M : ℝ) + 4) := by positivity
  refine ⟨1 - 1 / ((M : ℝ) + 4), by linarith, by linarith, ?_⟩
  have hprice := lineBound_price_cubic (θ := 1 - 1 / ((M : ℝ) + 4)) (by linarith) (by linarith)
  have hsimp : (1 : ℝ) - (1 - 1 / ((M : ℝ) + 4)) = 1 / ((M : ℝ) + 4) := by ring
  rw [hsimp] at hprice
  have hkey : (1270000000 : ℝ) / (1 / ((M : ℝ) + 4)) ^ 3 = 1270000000 * ((M : ℝ) + 4) ^ 3 := by
    field_simp
  rw [hkey] at hprice
  have hcube : (M : ℝ) ≤ ((M : ℝ) + 4) ^ 3 := by
    calc (M : ℝ) ≤ ((M : ℝ) + 4) * 1 := by linarith
      _ ≤ ((M : ℝ) + 4) * ((M : ℝ) + 4) ^ 2 := by nlinarith
      _ = ((M : ℝ) + 4) ^ 3 := by ring
  have hMle : (M : ℝ) ≤ 1270000000 * ((M : ℝ) + 4) ^ 3 := by
    linarith [pow_pos hpos 3]
  exact_mod_cast le_trans hMle hprice

/-! ## 3. The span certificate, and why it does not blow up

`t` enters `B` as `t + 1`, the number of dyadic blocks a line's confinement interval `[a, a/f_∞)`
can meet, and the requirement is `2^t·f_∞ ≥ 1`.  In that form it is a *rational* condition:
`(p/(cq))^{2^t} ≥ p`. -/

/-- **The span certificate in rational form.**  `2^t·f_∞ ≥ 1` — the hypothesis of Theorem A — is
implied by the single rational inequality `p ≤ (p/(cq))^{2^t}`, which every instance discharges by
`norm_num`.  (`BB13.one_le_two_pow_one_mul_fArch` is the `(3, 2, 3/4)` case, proved directly.) -/
@[category API, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem one_le_two_pow_mul_fArch {p q t : ℕ} {c : ℝ} (hp : 1 < p) (hq : 0 < q) (hc0 : 0 < c)
    (h : (p : ℝ) ≤ ((p : ℝ) / (c * q)) ^ (2 ^ t)) : (1 : ℝ) ≤ 2 ^ t * fArch p q c := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hp
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hbase : (0 : ℝ) < (p : ℝ) / (c * q) := by positivity
  have hlog : Real.log p ≤ (2 : ℝ) ^ t * Real.log ((p : ℝ) / (c * q)) := by
    calc Real.log p ≤ Real.log (((p : ℝ) / (c * q)) ^ (2 ^ t)) := Real.log_le_log hp0 h
      _ = (2 : ℝ) ^ t * Real.log ((p : ℝ) / (c * q)) := by rw [Real.log_pow]; push_cast; ring
  rw [fArch_eq_log_div hp hq hc0, ← mul_div_assoc, le_div_iff₀ hlp, one_mul]
  exact hlog

/-- **One span serves every rate at base `3/2`**: `t = 2` works for all `0 < c ≤ 1`, because
`(3/(2c))⁴ ≥ (3/2)⁴ = 81/16 ≥ 3`.  So the `θ → 1` price of §2 is the *whole* price: the block-span
factor of `B` is bounded by `3` at every rate. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem one_le_four_mul_fArch_three_two {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (1 : ℝ) ≤ 2 ^ 2 * fArch 3 2 c := by
  refine one_le_two_pow_mul_fArch (by norm_num) (by norm_num) hc0 ?_
  have hstep : (3 : ℝ) / 2 ≤ 3 / (c * 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hstep 4
  have h81 : (3 : ℝ) ≤ ((3 : ℝ) / 2) ^ (4 : ℕ) := by norm_num
  have key : (3 : ℝ) ≤ ((3 : ℝ) / (c * 2)) ^ (4 : ℕ) := le_trans h81 hpow
  simpa using key

/-- The span `t = 1` still serves every rate `c ≤ 3/4`: `(3/(2c))² ≥ 4 ≥ 3`.  Between `3/4` and
`1` the span rises to `2` (at `c = √3/2 = 0.866…`) and stops there. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem one_le_two_mul_fArch_three_two {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 3 / 4) :
    (1 : ℝ) ≤ 2 ^ 1 * fArch 3 2 c := by
  refine one_le_two_pow_mul_fArch (by norm_num) (by norm_num) hc0 ?_
  have hstep : (2 : ℝ) ≤ 3 / (c * 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hstep 2
  have key : (3 : ℝ) ≤ ((3 : ℝ) / (c * 2)) ^ (2 : ℕ) := by
    have h4 : (3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℕ) := by norm_num
    exact le_trans h4 hpow
  simpa using key

/-! ## 4. The parity scope: `q` even, not `q = 2`

`BB13.residMul_odd` is stated at `q = 2`, but its proof uses only that `qⁿ` is even.  This is the
whole of WP7(b): with the non-vanishing hypothesis discharged at every even `q`, the per-line
layer and the block bookkeeping — both of which are `(p,q)`-generic already — deliver Theorem A at
a general base. -/

/-- **The parity clause at every even `q`.**  For `D` and `p` odd and `q` even,
`kₙ = D·pⁿ − mₙ·qⁿ` is odd for every `n ≥ 1`: `D·pⁿ` is odd and `mₙ·qⁿ` is even.  The `q = 2` case
is `BB13.residMul_odd`. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "tshift_s2"]
theorem residMul_odd_of_even {D p q : ℕ} (hD : Odd D) (hp : Odd p) (hq : Even q) {n : ℕ}
    (hn : 1 ≤ n) : Odd (residMul D p q n) := by
  have hD' : Odd (D : ℤ) := (Int.odd_coe_nat D).mpr hD
  have hp' : Odd (p : ℤ) := (Int.odd_coe_nat p).mpr hp
  have h1 : Odd ((D : ℤ) * (p : ℤ) ^ n) := hD'.mul (hp'.pow)
  have h2 : Even (MnumMul (D : ℚ) p q n * ((q : ℕ) : ℤ) ^ n) := by
    refine Even.mul_left ?_ _
    rw [Int.even_pow]
    exact ⟨(Int.even_coe_nat q).mpr hq, by omega⟩
  exact h1.sub_even h2

/-- **Odd multipliers are admissible at every even `q`** — no size restriction on `D`, and no
appeal to `q = 2`.  This is the hypothesis that carries the whole per-line layer, so the block
count runs at every base `p/q` with `p` odd and `q` even. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "tshift_s2"]
theorem admissibleMul_of_odd_of_even {D p q : ℕ} (hD : Odd D) (hp : Odd p) (hq : Even q) :
    AdmissibleMul D p q := by
  intro a ha h
  have hodd := residMul_odd_of_even hD hp hq ha
  rw [h, Int.odd_iff] at hodd
  norm_num at hodd

/-! ## 5. Theorem A at a general base

The two parameters Theorem A leaves open — the span `t` and the height threshold `N` — always
exist; only their *numerals* are instance work. -/

/-- **A span always exists**: `f_∞ > 0` is Archimedean, so some `2^t` clears `1/f_∞`. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem exists_two_pow_mul_fArch {p q : ℕ} {c : ℝ} (hp : 1 < p) (hq : 0 < q) (hc0 : 0 < c)
    (hcq : c * q < p) : ∃ t : ℕ, (1 : ℝ) ≤ 2 ^ t * fArch p q c := by
  have hF : 0 < fArch p q c := fArch_pos hp hq hc0 hcq
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (fArch p q c)⁻¹ (by norm_num : (1 : ℝ) < 2)
  have hinv : (fArch p q c)⁻¹ * fArch p q c = 1 := inv_mul_cancel₀ (ne_of_gt hF)
  have hstep := mul_lt_mul_of_pos_right ht hF
  rw [hinv] at hstep
  exact ⟨t, hstep.le⟩

/-- **The height threshold in instance form**: below it only `⌊log₂ N⌋ + 1` blocks can hide, and
above it the cover applies.  `2D < p^N` is the whole of the multiplier's contribution. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem threshold_of_two_mul_lt_pow {D N p : ℕ} {c : ℝ} (hD : 0 < D) (hp : 1 < p)
    (h16 : ∀ n, N ≤ n → c ^ n < 1 / 16) (hDN : 2 * D < p ^ N) :
    ∀ n, N ≤ n →
      c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight ((D : ℕ) : ℚ) : ℝ) < (p : ℝ) ^ n := by
  intro n hn
  refine ⟨h16 n hn, ?_⟩
  rw [ratHeight_natCast, max_eq_left hD]
  have hnat : 2 * D < p ^ n := lt_of_lt_of_le hDN (Nat.pow_le_pow_right (by omega) hn)
  have hcast : ((2 * D : ℕ) : ℝ) < ((p ^ n : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at hcast ⊢
  linarith

/-- **The bad blocks form a finite set** — the fact that makes an `ncard` bound a statement rather
than the vacuous `0 ≤ B` (the lesson of WP5(b)). -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem badBlocks_finite {D p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1) : (badBlocks D p q c).Finite :=
  (mahler_failures_mul_finite hq hqp hcop hadm hc0 hc1).image _

/-- **Theorem A at a general base**, with both parameters supplied: for every coprime `p > q ≥ 2`,
every admissible multiplier and every rate `0 < c < 1`, there are a span `t` and a threshold `N`
for which the failures of `‖D(p/q)ⁿ‖ < cⁿ` meet at most `blockBound p c t N` dyadic blocks.

The numerals are instance work (§6); what this says is that the *shape* of Theorem A needs no
hypothesis beyond admissibility. -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem exists_badBlocks_card_le {D p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ t N : ℕ, 1 ≤ N ∧ (badBlocks D p q c).ncard ≤ blockBound p c t N := by
  have hp : 1 < p := lt_trans hq hqp
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqp' : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqp.le
  have hcq : c * (q : ℝ) < (p : ℝ) := by nlinarith
  obtain ⟨t, ht⟩ := exists_two_pow_mul_fArch hp (by omega) hc0 hcq
  obtain ⟨N, hN, hthr⟩ := exists_thresholdMul (D : ℚ) hp hc0 hc1
  exact ⟨t, N, hN, badBlocks_card_le hq hqp hcop hadm hc0 hc1 hN hthr ht⟩

/-- **Theorem A in the parity scope** (WP7(b)): `p` odd, `q` even, `D` odd — no admissibility
hypothesis, no size restriction on the multiplier, no `q = 2`. -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem exists_badBlocks_card_le_of_odd {D p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hD : Odd D) (hp : Odd p) (hqe : Even q) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ t N : ℕ, 1 ≤ N ∧ (badBlocks D p q c).ncard ≤ blockBound p c t N :=
  exists_badBlocks_card_le hq hqp hcop (admissibleMul_of_odd_of_even hD hp hqe) hc0 hc1

/-- **Theorem A at a small multiplier**, the other discharge of admissibility: `0 < D < q` needs no
parity at all (`BB13.admissibleMul_of_lt`). -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem exists_badBlocks_card_le_of_lt {D p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hD0 : 0 < D) (hDq : D < q) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ t N : ℕ, 1 ≤ N ∧ (badBlocks D p q c).ncard ≤ blockBound p c t N :=
  exists_badBlocks_card_le hq hqp hcop (admissibleMul_of_lt hcop hD0 hDq) hc0 hc1

end BB13

/-! # The instances

Base `3/2` at every rate (WP7(a)'s conclusion in Theorem-A form), and two bases that the `q = 2`
parity clause could not reach. -/

namespace TShift

open scoped Real

/-! ## 6. Base `3/2`, every rate -/

/-- **Theorem A at base `3/2`, at every rate**, with the span fixed at `t = 2` — the form in which
the `θ → 1` price is visible: only `K(ε(3,c))` moves.  At `c ≤ 3/4` the sharper span `t = 1` of
`BB13.one_le_two_mul_fArch_three_two` applies and `badBlocks_three_two_card_le` is the sharper
statement. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem badBlocks_three_two_card_le_rate {D N : ℕ} {c : ℝ} (hD : Odd D) (hc0 : 0 < c) (hc1 : c < 1)
    (hN : 1 ≤ N) (h16 : ∀ n, N ≤ n → c ^ n < 1 / 16) (hDN : 2 * D < 3 ^ N) :
    (BB13.badBlocks D 3 2 c).ncard
      ≤ BugeaudEvertse.lineBound (BB13.epsilon 3 c) * 3 + (Nat.log 2 N + 1) := by
  have h := BB13.badBlocks_card_le (D := D) (p := 3) (q := 2) (c := c) (N := N) (t := 2)
    (by norm_num) (by norm_num) (by decide) (admissibleMul_three_two hD) hc0 hc1 hN
    (BB13.threshold_of_two_mul_lt_pow hD.pos (by norm_num) h16 hDN)
    (BB13.one_le_four_mul_fArch_three_two hc0 hc1.le)
  simpa [BB13.blockBound] using h

/-- The rate-general Theorem A with the threshold supplied: at **every** rate `c < 1` and every odd
multiplier, the failures of `‖D(3/2)ⁿ‖ < cⁿ` meet at most `3K(ε(3,c)) + ⌊log₂ N⌋ + 1` dyadic
blocks for some explicit `N`.  Compare `TShift.badBlocks_card_le_five_decimal`, where the numerals
are exhibited at `c = 3/4`. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem exists_badBlocks_three_two_card_le {D : ℕ} {c : ℝ} (hD : Odd D) (hc0 : 0 < c)
    (hc1 : c < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ (BB13.badBlocks D 3 2 c).ncard
      ≤ BugeaudEvertse.lineBound (BB13.epsilon 3 c) * 3 + (Nat.log 2 N + 1) := by
  obtain ⟨N, hN, hthr⟩ := BB13.exists_thresholdMul (p := 3) (D : ℚ) (by norm_num) hc0 hc1
  refine ⟨N, hN, ?_⟩
  have h := BB13.badBlocks_card_le (D := D) (p := 3) (q := 2) (c := c) (N := N) (t := 2)
    (by norm_num) (by norm_num) (by decide) (admissibleMul_three_two hD) hc0 hc1 hN hthr
    (BB13.one_le_four_mul_fArch_three_two hc0 hc1.le)
  simpa [BB13.blockBound] using h

/-! ## 7. Two new bases

`(5,2)` and `(5,4)`: the same `ε` — it depends only on `p` and `c` — but different spans, `t = 1`
against `t = 2`, because the confinement interval `[a, a/f_∞)` is wider when `q` is closer to `p`.
At `(5,4)` the multiplier `q` is even but *not* `2`, which is exactly the case
`BB13.residMul_odd` could not reach. -/

/-- **Theorem A at base `5/2`**, every odd multiplier, rate `3/4`: span `t = 1`, from
`(5/(2·(3/4)))² = 100/9 ≥ 5`.  The line count `K(ε(5,3/4))` is left symbolic (its true value is
`5 449 831 243 823`; certifying a decimal would need enclosures for `log 5`). -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem badBlocks_five_two_card_le {D N : ℕ} (hD : Odd D) (hN : 10 ≤ N) (hDN : 2 * D < 5 ^ N) :
    (BB13.badBlocks D 5 2 (3 / 4)).ncard
      ≤ BugeaudEvertse.lineBound (BB13.epsilon 5 (3 / 4)) * 2 + (Nat.log 2 N + 1) := by
  have hspan : (1 : ℝ) ≤ 2 ^ 1 * BB13.fArch 5 2 (3 / 4) := by
    refine BB13.one_le_two_pow_mul_fArch (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num
  have h := BB13.badBlocks_card_le (D := D) (p := 5) (q := 2) (c := 3 / 4) (N := N) (t := 1)
    (by norm_num) (by norm_num) (by decide)
    (BB13.admissibleMul_of_odd_of_even hD (by decide) (by decide)) (by norm_num) (by norm_num)
    (by omega)
    (BB13.threshold_of_two_mul_lt_pow hD.pos (by norm_num)
      (fun n hn => BB13.three_quarters_pow_lt (by omega)) hDN)
    hspan
  simpa [BB13.blockBound] using h

/-- **Theorem A at base `5/4`** — the case `q` even but not `2`.  Span `t = 2`, from
`(5/(4·(3/4)))⁴ = 625/81 ≥ 5`; the line count is the same `K(ε(5,3/4))` as at base `5/2`, since
`ε` depends only on `p` and the rate. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem badBlocks_five_four_card_le {D N : ℕ} (hD : Odd D) (hN : 10 ≤ N) (hDN : 2 * D < 5 ^ N) :
    (BB13.badBlocks D 5 4 (3 / 4)).ncard
      ≤ BugeaudEvertse.lineBound (BB13.epsilon 5 (3 / 4)) * 3 + (Nat.log 2 N + 1) := by
  have hspan : (1 : ℝ) ≤ 2 ^ 2 * BB13.fArch 5 4 (3 / 4) := by
    refine BB13.one_le_two_pow_mul_fArch (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num
  have h := BB13.badBlocks_card_le (D := D) (p := 5) (q := 4) (c := 3 / 4) (N := N) (t := 2)
    (by norm_num) (by norm_num) (by decide)
    (BB13.admissibleMul_of_odd_of_even hD (by decide) (by decide)) (by norm_num) (by norm_num)
    (by omega)
    (BB13.threshold_of_two_mul_lt_pow hD.pos (by norm_num)
      (fun n hn => BB13.three_quarters_pow_lt (by omega)) hDN)
    hspan
  simpa [BB13.blockBound] using h

/-- **Theorem C in the parity scope**: for every `p` odd, `q` even and coprime to `p`, every odd
multiplier and every rate below `1`, the failure set is finite.  `TShift.failuresMul_three_two_finite`
is the `(3,2)` case. -/
@[category research solved, AMS 11 37, ref "Mah57" "Sch75" "PR19" "BE08" "Bug12", group "tshift_s2"]
theorem mahler_failures_mul_finite_of_odd_of_even {D p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hD : Odd D) (hp : Odd p) (hqe : Even q) (hc0 : 0 < c) (hc1 : c < 1) :
    (BB13.failuresMul D p q c).Finite :=
  BB13.mahler_failures_mul_finite hq hqp hcop (BB13.admissibleMul_of_odd_of_even hD hp hqe) hc0 hc1

end TShift
