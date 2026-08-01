/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.Waring
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Certified decimal bounds for the line counts (W9 of plan2-BB13)

`BugeaudEvertse.lineBound ε` is a ceiling of a transcendental expression; the counts of
`BB13/FailureCount.lean` and `BB13/Waring.lean` are only as quotable as the decimal bounds one
can prove for it.  This file supplies them:

* `lineBound_epsStar_le` — `K(ε*) ≤ 1.86 · 10¹²` (the true value is `1 856 360 182 227`);
* `lineBound_epsW_le` — `K(ε_W) ≤ 1.88 · 10¹²` (true value `1 876 339 827 243`).

## How the certification runs

Everything is derived from three Mathlib facts — `Real.log_two_gt_d9`, `Real.log_two_lt_d9` and
`Real.log_three_near_10` — through the identity `log(4/3) = 2 log 2 − log 3`:

* `1 + 1/ε* ≤ 4.8189`, which is `4.8189·log 3 ≤ 7.6378·log 2` (true with `1.6·10⁻⁵` to spare —
  the chain is sensitive here, since `1/ε*` divides by the small `log(4/3) = 0.2876…`);
* `log 6 ≤ 1.79175947`;
* `log((1 + 1/ε*)·log 6) ≤ 2.15874`, from `log 8.63431 = 3 log 2 + log 1.0792…` and
  `log(1 + t) ≤ t`.

Multiplying, `2³² · 4.8189³ · 1.79175947 · 2.15874 < 1.86 · 10¹²`.  The same chain with
`1/ε_W = (257/256)/ε*` gives the Waring constant.  No `native_decide`, no numerical evaluation of
a transcendental: only rational arithmetic on the certified enclosures.

## References

* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 (5.13) — the counted quantity.
* `plans/plan2-BB13.html` (W9).
-/

namespace BB13

open scoped Real

/-! ### Certified logarithm enclosures -/

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem log_three_le : Real.log 3 ≤ 1.0986122888 := by
  have h := abs_le.mp Real.log_three_near_10
  norm_num at h ⊢
  linarith [h.2]

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem log_three_ge : (1.0986122885 : ℝ) ≤ Real.log 3 := by
  have h := abs_le.mp Real.log_three_near_10
  norm_num at h ⊢
  linarith [h.1]

/-- `log(4/3) = 2 log 2 − log 3`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem log_four_thirds_eq : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem log_four_thirds_ge : (0.2876820718 : ℝ) ≤ Real.log (4 / 3) := by
  rw [log_four_thirds_eq]
  linarith [Real.log_two_gt_d9, log_three_le]

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem log_six_le : Real.log 6 ≤ 1.79175947 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_lt_d9, log_three_le]

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem one_le_log_six : (1 : ℝ) ≤ Real.log 6 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, log_three_ge]

/-! ### The constant at the sharp exponent `ε*` -/

/-- `1 + 1/ε* ≤ 4.8189` — the sensitive step: it amounts to `4.8189·log 3 ≤ 7.6378·log 2`, which
the certified enclosures clear by `1.6 · 10⁻⁵`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem one_add_inv_epsStar_le : 1 + epsStar⁻¹ ≤ 4.8189 := by
  have hl43 : (0 : ℝ) < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hinv : epsStar⁻¹ = Real.log 3 / Real.log (4 / 3) := by rw [epsStar, inv_div]
  have hkey : Real.log 3 ≤ 3.8189 * Real.log (4 / 3) := by
    rw [log_four_thirds_eq]
    linarith [Real.log_two_gt_d9, log_three_le]
  have hdiv : Real.log 3 / Real.log (4 / 3) ≤ 3.8189 := (div_le_iff₀ hl43).mpr hkey
  rw [hinv]
  linarith

@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem one_add_inv_epsStar_nonneg : (0 : ℝ) ≤ 1 + epsStar⁻¹ := by
  have := epsStar_pos
  positivity

/-- **`K(ε*) ≤ 1.86 · 10¹²`.**  The Bugeaud–Evertse line count at the sharp exponent of Problem
10.13, certified; the true value is `1 856 360 182 227`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem lineBound_epsStar_le : BugeaudEvertse.lineBound epsStar ≤ 1860000000000 := by
  rw [BugeaudEvertse.lineBound]
  refine Nat.ceil_le.mpr ?_
  have hA := one_add_inv_epsStar_le
  have hA0 := one_add_inv_epsStar_nonneg
  have hB := log_six_le
  have hB0 : (0 : ℝ) ≤ Real.log 6 := by linarith [one_le_log_six]
  have h1 : (1 : ℝ) ≤ 1 + epsStar⁻¹ := by
    have h := epsStar_pos
    have : 0 < epsStar⁻¹ := by positivity
    linarith
  have hargpos : (0 : ℝ) < (1 + epsStar⁻¹) * Real.log 6 := by nlinarith [one_le_log_six]
  have hargle : (1 + epsStar⁻¹) * Real.log 6 ≤ 8.63431 := by
    nlinarith [mul_le_mul hA hB hB0 (by norm_num : (0 : ℝ) ≤ 4.8189)]
  have hC : Real.log ((1 + epsStar⁻¹) * Real.log 6) ≤ 2.15874 := by
    refine le_trans (Real.log_le_log hargpos hargle) ?_
    rw [show (8.63431 : ℝ) = 8 * (8.63431 / 8) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8.63431 / 8 by norm_num)
    push_cast
    linarith [Real.log_two_lt_d9]
  have hC0 : (0 : ℝ) ≤ Real.log ((1 + epsStar⁻¹) * Real.log 6) := by
    refine Real.log_nonneg ?_
    nlinarith [one_le_log_six]
  push_cast
  calc (2 : ℝ) ^ 32 * (1 + epsStar⁻¹) ^ 3 * Real.log 6 * Real.log ((1 + epsStar⁻¹) * Real.log 6)
      ≤ (2 : ℝ) ^ 32 * 4.8189 ^ 3 * 1.79175947 * 2.15874 := by gcongr
    _ ≤ 1860000000000 := by norm_num

/-! ### The constant at the Waring exponent `ε_W` -/

/-- `1 + 1/ε_W ≤ 4.83382`, from `1/ε_W = (257/256)/ε*`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem one_add_inv_epsW_le : 1 + epsW⁻¹ ≤ 4.83382 := by
  have hpos := epsStar_pos
  have hepsW : epsW = epsStar * (256 / 257) := by rw [epsW]; ring
  have hinv : epsW⁻¹ = (257 / 256) * epsStar⁻¹ := by
    rw [hepsW, mul_inv]
    norm_num
    ring
  have hA := one_add_inv_epsStar_le
  rw [hinv]
  linarith [hA]

@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem one_add_inv_epsW_nonneg : (0 : ℝ) ≤ 1 + epsW⁻¹ := by
  have := epsW_pos
  positivity

/-- **`K(ε_W) ≤ 1.88 · 10¹²`.**  The line count at the Waring exponent; true value
`1 876 339 827 243`.  The `0.4%` exponent shave that buys the factor `4/3` at the archimedean
place costs `1.1%` in the constant. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem lineBound_epsW_le : BugeaudEvertse.lineBound epsW ≤ 1880000000000 := by
  rw [BugeaudEvertse.lineBound]
  refine Nat.ceil_le.mpr ?_
  have hA := one_add_inv_epsW_le
  have hA0 := one_add_inv_epsW_nonneg
  have hB := log_six_le
  have hB0 : (0 : ℝ) ≤ Real.log 6 := by linarith [one_le_log_six]
  have h1 : (1 : ℝ) ≤ 1 + epsW⁻¹ := by
    have h := epsW_pos
    have : 0 < epsW⁻¹ := by positivity
    linarith
  have hargpos : (0 : ℝ) < (1 + epsW⁻¹) * Real.log 6 := by nlinarith [one_le_log_six]
  have hargle : (1 + epsW⁻¹) * Real.log 6 ≤ 8.661043 := by
    nlinarith [mul_le_mul hA hB hB0 (by norm_num : (0 : ℝ) ≤ 4.83382)]
  have hC : Real.log ((1 + epsW⁻¹) * Real.log 6) ≤ 2.16208 := by
    refine le_trans (Real.log_le_log hargpos hargle) ?_
    rw [show (8.661043 : ℝ) = 8 * (8.661043 / 8) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8.661043 / 8 by norm_num)
    push_cast
    linarith [Real.log_two_lt_d9]
  have hC0 : (0 : ℝ) ≤ Real.log ((1 + epsW⁻¹) * Real.log 6) := by
    refine Real.log_nonneg ?_
    nlinarith [one_le_log_six]
  push_cast
  calc (2 : ℝ) ^ 32 * (1 + epsW⁻¹) ^ 3 * Real.log 6 * Real.log ((1 + epsW⁻¹) * Real.log 6)
      ≤ (2 : ℝ) ^ 32 * 4.83382 ^ 3 * 1.79175947 * 2.16208 := by gcongr
    _ ≤ 1880000000000 := by norm_num

/-! ### The counts in decimal form

The two conditional counts of `BB13/FailureCount.lean` and `BB13/Waring.lean` with the certified
constants substituted — the shape the results are quoted in. -/

/-- **`#E ≤ 5 + H · 1.86·10¹²`**: the failure count of Problem 10.13, conditional on a per-line
bound `H` above the certified range, with the constant in decimal form. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_card_le_decimal (H : ℕ) (hfib : ∀ r : ℚ, (highFibre r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.ncard ≤ 5 + H * 1860000000000 :=
  le_trans (failures_card_le_of_heightBound H hfib)
    (Nat.add_le_add_left (Nat.mul_le_mul (le_refl H) lineBound_epsStar_le) 5)

/-- **`#{n ≥ 2 : g(n) ≠ 2ⁿ + ⌊(3/2)ⁿ⌋ − 2} ≤ H · 1.88·10¹²`**: the Waring exception count with the
certified constant, and no additive term. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "Dic36", group "bugeaud_10_13"]
theorem waring_exceptions_card_le_decimal (H : ℕ) (hfib : ∀ r : ℚ, (dicksonFibre r).ncard ≤ H) :
    {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
      ≤ H * 1880000000000 :=
  le_trans (waring_exceptions_card_le_of_heightBound H hfib)
    (Nat.mul_le_mul (le_refl H) lineBound_epsW_le)

end BB13
