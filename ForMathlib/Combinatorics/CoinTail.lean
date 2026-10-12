/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Fintype.Pi

/-!
# The Hoeffding tail bound for coin-toss words, by counting

For words `w : Fin k → Bool`, let `#₁ w` be the number of letters `true`.  The **coin-tail bound**
`card_filter_abs_sub_gt_le` says that at most `2 · 2^k · exp(-2ε²k)` of the `2^k` words have
`|#₁ w - k/2| > εk`.  This is Hoeffding's inequality for `k` fair coins, stated as a pure
counting fact on `Fin k → Bool`, with no probability library.

The proof is the Chernoff argument done on sums:
`∑_w exp(λ(#₁ w - k/2)) = (2 cosh(λ/2))^k ≤ 2^k exp(kλ²/8)` (`sum_exp_mul_centered_le`,
via `Real.cosh_le_exp_half_sq`), then Markov with `λ = ±4ε`.

## Main statements

* `sum_exp_mul_centered_le` — the moment-generating bound for every real `λ`;
* `card_filter_sub_gt_le` — the one-sided tail;
* `card_filter_abs_sub_gt_le` — the two-sided tail.
-/

open Finset Real

namespace CoinTail

/-- The centered count of a word: `#₁ w - k/2`, as a sum of `±1/2`. -/
noncomputable def centered {k : ℕ} (w : Fin k → Bool) : ℝ :=
  ∑ i, if w i then (1 / 2 : ℝ) else -1 / 2

theorem centered_eq {k : ℕ} (w : Fin k → Bool) :
    centered w = ((univ.filter fun i => w i = true).card : ℝ) - k / 2 := by
  have h : ∀ i, (if w i then (1 / 2 : ℝ) else -1 / 2) = (if w i then 1 else 0) - 1 / 2 := by
    intro i; split <;> norm_num
  simp only [centered, h, sum_sub_distrib, sum_boole, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- **Moment-generating bound.** `∑_w exp(λ(#₁ w - k/2)) ≤ 2^k exp(kλ²/8)`. -/
theorem sum_exp_mul_centered_le (k : ℕ) (l : ℝ) :
    ∑ w : Fin k → Bool, exp (l * centered w) ≤ 2 ^ k * exp (k * l ^ 2 / 8) := by
  have hprod : ∀ w : Fin k → Bool, exp (l * centered w)
      = ∏ i, exp (l * if w i then (1 / 2 : ℝ) else -1 / 2) := by
    intro w; rw [centered, mul_sum, exp_sum]
  simp_rw [hprod]
  rw [← Fintype.prod_sum
    (fun (_ : Fin k) (b : Bool) => exp (l * if b then (1 / 2 : ℝ) else -1 / 2))]
  have hone : ∑ b : Bool, exp (l * if b then (1 / 2 : ℝ) else -1 / 2) = 2 * cosh (l / 2) := by
    rw [cosh_eq]; simp; ring_nf
  simp only [hone, prod_const, card_univ, Fintype.card_fin]
  rw [show k * l ^ 2 / 8 = k * ((l / 2) ^ 2 / 2) by ring, exp_nat_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left (cosh_le_exp_half_sq _) (by norm_num)) k

/-- Markov from the moment bound: for `λ > 0`, at most `2^k exp(kλ²/8 - λa)` words have
`λ · (#₁ w - k/2)` above `λa`. -/
theorem card_filter_mul_gt_le (k : ℕ) {l : ℝ} (a : ℝ) :
    ((univ.filter fun w : Fin k → Bool => l * a < l * centered w).card : ℝ)
      ≤ 2 ^ k * exp (k * l ^ 2 / 8 - l * a) := by
  set S := univ.filter fun w : Fin k → Bool => l * a < l * centered w
  have h1 : (S.card : ℝ) * exp (l * a) ≤ ∑ w ∈ S, exp (l * centered w) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun w hw => (exp_lt_exp.mpr (mem_filter.mp hw).2).le
  have h2 : ∑ w ∈ S, exp (l * centered w) ≤ ∑ w, exp (l * centered w) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => (exp_pos _).le
  have h3 := sum_exp_mul_centered_le k l
  rw [exp_sub, mul_div_assoc', le_div_iff₀ (exp_pos _)]
  linarith

/-- **One-sided tail.** At most `2^k exp(-2ε²k)` words have `#₁ w - k/2 > εk`. -/
theorem card_filter_sub_gt_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((univ.filter fun w : Fin k → Bool => ε * k < centered w).card : ℝ)
      ≤ 2 ^ k * exp (-2 * ε ^ 2 * k) := by
  have h := card_filter_mul_gt_le k (l := 4 * ε) (ε * k)
  have hs : (univ.filter fun w : Fin k → Bool => ε * k < centered w)
      = univ.filter fun w : Fin k → Bool => 4 * ε * (ε * k) < 4 * ε * centered w := by
    ext w; simp only [mem_filter, mem_univ, true_and]
    exact (mul_lt_mul_iff_right₀ (by positivity)).symm
  rw [hs]
  convert h using 3; ring

/-- **Lower tail.** At most `2^k exp(-2ε²k)` words have `k/2 - #₁ w > εk`. -/
theorem card_filter_neg_gt_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((univ.filter fun w : Fin k → Bool => ε * k < -centered w).card : ℝ)
      ≤ 2 ^ k * exp (-2 * ε ^ 2 * k) := by
  have h := card_filter_mul_gt_le k (l := -(4 * ε)) (-(ε * k))
  have hs : (univ.filter fun w : Fin k → Bool => ε * k < -centered w)
      = univ.filter fun w : Fin k → Bool =>
          -(4 * ε) * -(ε * k) < -(4 * ε) * centered w := by
    ext w; simp only [mem_filter, mem_univ, true_and]
    rw [neg_mul_neg, neg_mul, ← mul_neg]
    exact (mul_lt_mul_iff_right₀ (by positivity)).symm
  rw [hs]
  convert h using 3; ring

/-- **The coin-tail bound** (Hoeffding for `k` fair coins, by counting). At most
`2 · 2^k · exp(-2ε²k)` words `w : Fin k → Bool` have `|#₁ w - k/2| > εk`. -/
theorem card_filter_abs_sub_gt_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((univ : Finset (Fin k → Bool)).filter fun w =>
        ε * k < |((univ.filter fun i => w i = true).card : ℝ) - k / 2|).card : ℝ)
      ≤ 2 * 2 ^ k * exp (-2 * ε ^ 2 * k) := by
  simp_rw [← centered_eq]
  have hsplit : (univ.filter fun w : Fin k → Bool => ε * k < |centered w|)
      = (univ.filter fun w : Fin k → Bool => ε * k < centered w)
        ∪ (univ.filter fun w : Fin k → Bool => ε * k < -centered w) := by
    rw [← filter_or]; simp_rw [lt_abs]
  have h1 := card_filter_sub_gt_le k hε
  have h2 := card_filter_neg_gt_le k hε
  rw [hsplit]
  calc (((univ.filter fun w : Fin k → Bool => ε * k < centered w)
          ∪ (univ.filter fun w : Fin k → Bool => ε * k < -centered w)).card : ℝ)
      ≤ ((univ.filter fun w : Fin k → Bool => ε * k < centered w).card
          + (univ.filter fun w : Fin k → Bool => ε * k < -centered w).card : ℕ) := by
        exact_mod_cast card_union_le _ _
    _ ≤ 2 * 2 ^ k * exp (-2 * ε ^ 2 * k) := by push_cast; linarith

end CoinTail
