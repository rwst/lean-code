/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The `ℚ₂` value of the minimal word (plan-B1E2, WP3)

The **2-adic** reading of `RB.x_mul_pow`'s identity: in `ℚ₂`,

  `∑ⱼ wⱼ(2/3)ʲ = −3x₀`   (`tsum_wmin_padic`),

and, on the shifted word, `∑ⱼ w_{n+j}(2/3)ʲ = −3xₙ` (`tsum_wmin_shift_padic`).

## One identity, two readings

`RB.Basic` proves `(2/3)ⁿxₙ = x₀ + (1/3)Σ_{j<n} wⱼ(2/3)ʲ` over `ℝ`; the same induction runs
verbatim over `ℚ₂` (`x_mul_pow_padic` — any characteristic-zero field will do). Only the *limit*
differs, and it differs completely:

| | `‖(2/3)ⁿxₙ‖` | limit of the partial sums |
|---|---|---|
| **archimedean** (`RB.Basic`) | `→ K − …` | `3(K − x₀)`, an unknown real |
| **2-adic** (here) | `= 2⁻ⁿ‖xₙ‖ ≤ 2⁻ⁿ → 0` | `−3x₀`, **an integer** |

The 2-adic side collapses because `|2/3|₂ = 1/2` (`norm_two_thirds`) while `xₙ` stays a 2-adic
integer, so the orbit term vanishes and the sum is pinned to `−3x₀` exactly. Elementary, and as
far as we know new.

## Why this does *not* prove non-automaticity

It is tempting — and rev. 1 of [B1E2] did exactly this — to read the pinned rational value
against a Mahler-method theorem and conclude a contradiction. **It is not a contradiction.**
[AF17] Cor 1.8's alternative is *`f(α)` transcendental **or** `f(α) ∈ k`*, and here `k = ℚ` and
`f(2/3) = −3x₀ ∈ ℚ`: this identity lands squarely in the **permitted** branch. AF prove the
alternative cannot be removed even for transcendental `f` (§8.1). See
`CITED.AdamczewskiFaverjon`'s module doc and [B1E2] §0.1.

The transcendence-forcing shape needs a *regular* point, i.e. [AF17] Thm 1.4 rather than
Cor 1.8 — and no `p`-adic analogue of Thm 1.4 (or of Nishioka's theorem) exists **for linear
systems**, in any form. That is the single named input on which [B1E2]'s Track I is parked; it
is not a gap in this file. So this file is a **bonus**: true, cheap, apparently new, and
deliberately *not* load-bearing. The archimedean twin (`RB.tsum_wmin_eq`) is what carries the
plan's capstone.

## Contents

* `RB.norm_two_thirds` (`‖2/3‖₂ = 1/2`), `norm_natCast_le_one`, `norm_term_le`.
* `RB.x_mul_pow_padic` — the partial-sum identity over `ℚ₂`.
* `RB.tendsto_x_mul_pow_padic` — the orbit term vanishes 2-adically.
* **`RB.tsum_wmin_padic`** — `∑ⱼ wⱼ(2/3)ʲ = −3x₀` in `ℚ₂`.
* **`RB.tsum_wmin_shift_padic`** — the shifted family, `= −3xₙ`.

## References

* [AF17] Adamczewski, Faverjon. *Méthode de Mahler …* Proc. LMS **115** (2017), 55–90.
  (Cor 1.8 = why this identity is not a contradiction; Thm 1.4 = the missing `p`-adic analogue.)
* [AFS08] Akiyama, Frougny, Sakarovitch. Israel J. Math. **168** (2008), 53–91.
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.1 (Gate 0's blocking verdict), §2.1 (the
  two readings), WP3 (demoted to bonus), WP5 (the parked input).
-/

namespace RB

/-! ## The 2-adic size of `2/3` -/

/-- `v₂(2/3) = 1`. -/
@[category API, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma padicValRat_two_thirds : padicValRat 2 (2 / 3) = 1 := by
  rw [padicValRat.div (by norm_num : (2 : ℚ) ≠ 0) (by norm_num : (3 : ℚ) ≠ 0)]
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by norm_num)
  have h3 : padicValRat 2 (3 : ℚ) = 0 := by
    have e : ((3 : ℤ) : ℚ) = (3 : ℚ) := by norm_num
    rw [← e, padicValRat.of_int, padicValInt, show ((3 : ℤ)).natAbs = 3 from rfl,
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ (2 ∣ 3))]
    rfl
  rw [h2, h3]; norm_num

/-- **`‖2/3‖₂ = 1/2`** — the contraction that makes the 2-adic series converge and the orbit
term vanish.  (Contrast the archimedean `|2/3| = 2/3`.) -/
@[category API, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma norm_two_thirds : ‖(2 / 3 : ℚ_[2])‖ = 1 / 2 := by
  have hc : ((2 / 3 : ℚ) : ℚ_[2]) = (2 / 3 : ℚ_[2]) := by push_cast; ring
  rw [← hc, Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by norm_num : (2 / 3 : ℚ) ≠ 0), padicValRat_two_thirds]
  norm_num

/-- Naturals are 2-adic integers. -/
@[category API, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma norm_natCast_le_one (n : ℕ) : ‖(n : ℚ_[2])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := 2) (n : ℤ)

/-- The uniform term bound `‖n·(2/3)ʲ‖₂ ≤ 2⁻ʲ`, used for both convergence and the limit. -/
@[category API, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma norm_term_le (n j : ℕ) : ‖(n : ℚ_[2]) * (2 / 3) ^ j‖ ≤ (1 / 2 : ℝ) ^ j := by
  rw [norm_mul, norm_pow, norm_two_thirds]
  have h1 := norm_natCast_le_one n
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  nlinarith [norm_nonneg ((n : ℚ_[2]))]

/-! ## The identity -/

@[category API, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma two_mul_x_succ_padic (x₀ n : ℕ) :
    2 * (x x₀ (n + 1) : ℚ_[2]) = 3 * x x₀ n + wmin x₀ n := by
  exact_mod_cast congrArg (Nat.cast (R := ℚ_[2])) (two_mul_x_succ x₀ n)

/-- The partial-sum identity over `ℚ₂` — the same induction as `RB.x_mul_pow`, which needs only
that `2` and `3` are invertible. -/
@[category research solved, AMS 11 68, ref "AFS08" "B1E2", group "rb_rational_base"]
theorem x_mul_pow_padic (x₀ n : ℕ) :
    (x x₀ n : ℚ_[2]) * (2 / 3) ^ n
      = x₀ + (1 / 3) * ∑ j ∈ Finset.range n, (2 / 3 : ℚ_[2]) ^ j * wmin x₀ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := two_mul_x_succ_padic x₀ n
    have e : ((2 : ℚ_[2]) / 3) ^ (n + 1) = (2 / 3) * (2 / 3) ^ n := by ring
    rw [e]
    linear_combination ih + ((2 : ℚ_[2]) / 3) ^ n / 3 * h

@[category API, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma tendsto_geom_half : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- **The 2-adic collapse**: `‖(2/3)ⁿxₙ‖₂ ≤ 2⁻ⁿ → 0`.  This is the whole difference from the
archimedean reading, where the same expression tends to a nonzero limit. -/
@[category research solved, AMS 11 68, ref "B1E2", group "rb_rational_base"]
theorem tendsto_x_mul_pow_padic (x₀ : ℕ) :
    Filter.Tendsto (fun n => (x x₀ n : ℚ_[2]) * (2 / 3) ^ n) Filter.atTop (nhds 0) :=
  squeeze_zero_norm (fun n => norm_term_le (x x₀ n) n) tendsto_geom_half

@[category API, AMS 11 68, ref "B1E2", group "rb_rational_base"]
theorem summable_wmin_padic (x₀ : ℕ) : Summable (fun j => (2 / 3 : ℚ_[2]) ^ j * wmin x₀ j) := by
  refine Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ j)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) (fun j => ?_)
  have h := norm_term_le (wmin x₀ j) j
  rwa [mul_comm] at h

/-- **The `ℚ₂` identity** ([B1E2] §2.1): `∑ⱼ wⱼ(2/3)ʲ = −3x₀` in `ℚ₂`.

The word's 2-adic value is pinned to an *integer* determined by the initial condition alone.
Read the module doc before drawing a transcendence conclusion from this: `−3x₀ ∈ ℚ` is the
branch [AF17] Cor 1.8 **permits**. -/
@[category research solved, AMS 11 68, ref "AFS08" "B1E2", group "rb_rational_base"]
theorem tsum_wmin_padic (x₀ : ℕ) : ∑' j, (2 / 3 : ℚ_[2]) ^ j * wmin x₀ j = -3 * x₀ := by
  have hs := summable_wmin_padic x₀
  refine (hs.hasSum_iff_tendsto_nat.mpr ?_).tsum_eq
  have hpart : ∀ n, ∑ j ∈ Finset.range n, (2 / 3 : ℚ_[2]) ^ j * wmin x₀ j
      = 3 * ((x x₀ n : ℚ_[2]) * (2 / 3) ^ n) - 3 * x₀ := by
    intro n
    have h := x_mul_pow_padic x₀ n
    linear_combination (-3 : ℚ_[2]) * h
  simp only [hpart]
  have h0 := (tendsto_x_mul_pow_padic x₀).const_mul (3 : ℚ_[2])
  simpa using h0.sub_const (3 * (x₀ : ℚ_[2]))

/-- **The shifted family** ([B1E2] §2.1): `∑ⱼ w_{n+j}(2/3)ʲ = −3xₙ` in `ℚ₂`, for every `n`.
Immediate from `tsum_wmin_padic` at initial condition `xₙ`, by shift-invariance
(`RB.wmin_add`). -/
@[category research solved, AMS 11 68, ref "AFS08" "B1E2", group "rb_rational_base"]
theorem tsum_wmin_shift_padic (x₀ n : ℕ) :
    ∑' j, (2 / 3 : ℚ_[2]) ^ j * wmin x₀ (n + j) = -3 * x x₀ n := by
  simpa [wmin_add] using tsum_wmin_padic (x x₀ n)

end RB
