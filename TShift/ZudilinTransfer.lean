/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.HabsiegerTransfer
import CITED.ZudilinPade

/-!
# The record rate at a shifted target: `0.5803`, transported to every multiplier

`‖D·(3/2)^k‖ ≥ (0.5803)^k` for every `k` beyond a threshold — and, in the uniform form,
simultaneously for every multiplier `1 ≤ D ≤ (1 + 1.3·10⁻³)^k`.  Hence, by the multiplier
reduction of `TShift.Basic`, exponential repulsion of the orbit `(3/2)ⁿ` from **every** cycle
target `A/(3^p − 2^p)`, of every period, at the current record rate.

This is the second engine in the socket of `TShift/MultiplierTransfer.lean`.  Nothing in the
transfer lemma moved: `Zudilin.PadeData` supplies two independent content-bearing forms exactly as
`Habsieger.PadeData` does, and the same `TShift.le_distToNearestInt_pow` consumes them.  That was
plan-Tshift-S1's risk R4, and this file discharges it by instance rather than by argument.

## What is new here, and what is not

The rate `0.5803` at `D = 1` is [Zud07] Theorem 1 — the record for `‖(3/2)^k‖`, unbeaten since
2007.  What is not in the literature is that it **transports to every multiplier**: `D` never
enters the Padé construction, only the error column of the elimination step, where it is charged
once, against condition (26).  The charge is an additive `O(log D)` on the threshold and nothing
on the exponent, exactly as in `TShift/HabsiegerTransfer.lean`.

## The one thing this file cannot do, and why

**Every date here is existentially quantified**, and that is inherited, not conceded.  [Zud07]
proves its estimates through the limits (19), (20), (21) and states Theorem 1 as "for `k ≥ K`,
where `K` is a certain effective constant" — effective, and never computed.  So
`Zudilin.padeData` quantifies over its threshold, and no theorem below exhibits a first date.
Contrast `TShift.le_distToNearestInt_habsieger`, which names `k₀ = 64 440 001` at the smaller rate
`0.57434`.  **The two statements are incomparable, and both are worth having**: this file has the
better constant, that one the computed threshold.

The *arithmetic* thresholds this file adds are explicit and small on that scale — `m ≥ 6 548 000`
(i.e. `k ≥ 3.7·10⁸`) to absorb the block constant, and `m ≥ 25·3⁵⁷·D` to make the error term
harmless.  What is missing is only the source's own `N₁, N₂(δ)`; making *those* explicit needs an
explicit lower bound for `Φ(9m, 19m, 9m)` at finite `m` and explicit versions of (19)/(20), which
is a research task ([Pup09] Theorem 2 does it and lands at the smaller `0.5795`, with a printed
threshold `k ≥ 871 387 440 264 = 8.71·10¹¹`).  See `plans/note-Tshift-S1-WP7.html` §3.

## The chain

Dates are blocked as `k = 3(βm + 1) + j = 57m + 3 + j` with `0 ≤ j < 57` ([Zud07] p. 320), so
every `k ≥ 3` sits in exactly one block.  With `N = 57m + 3`:

1. **the block** — `2^j·D·(3/2)^{N+j} = (3^j·D)·(3/2)^N`, so a bound at the block head `N` with
   multiplier `3^j D` gives one at the date `k = N + j` after dividing by `2^j`
   (`TShift.distToNearestInt_ascent`);
2. **the elimination** — `TShift.le_distToNearestInt_pow` at `X = 2^N`, `Y = 3^N`, `c = 3^j D`,
   content `contentBase^m`, error `2^N·3^{m+1}·errorBase^m`, coefficient `denomBase^m`;
3. **the error term** — `3^{j+1}·D·(3·errorBase)^m ≤ contentBase^m/2`, which is *precisely*
   [Zud07]'s condition (26) `C₀ − C₂ + (β − 2α)log 3 < 0` with the multiplier charged into it
   (`TShift.zud_error_small`).  The validity region of the transfer lemma and the validity
   condition of the paper are the same inequality;
4. **the rate** — `denomBase·0.5803^57 ≤ contentBase`, with `1.0002732` per `m` of margin left
   over, which absorbs the block constant `2^{j+1}·0.5803^{3+j} ≤ 1638`
   (`TShift.zud_rate_step`).

Steps 3 and 4 are the two rational inequalities of the whole file; both are decided by `norm_num`
on the frozen surrogates of `CITED/ZudilinPade.lean`.

## Honesty

`0.5803 < 2/3` (`TShift.thetaZud_lt_two_thirds`), so `κ = 1.342 > 1` and **no instance of
`TShift.TShiftProblem` is settled** — the gap this file does not close is exactly `0.5803 → 2/3`,
which is the open problem.  What it does close is the *multiplier* gap at the record rate, and it
improves the corpus' effective rate at every cycle target from `0.57434` to `0.5803`
(`TShift.thetaHab_lt_thetaZud`) at the price of the threshold.

## References

* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)^k‖`*, J. Théor. Nombres Bordeaux **19**
  (2007), 311–323.  In repo: `papers/Zudilin2007.pdf`.  The engine; the bundle is
  `CITED/ZudilinPade.lean`.
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003),
  299–308 — the effective-threshold lane, `TShift/HabsiegerTransfer.lean`.
* [Pup09] Yu. A. Pupyrev, *Effectivization of a lower bound for `‖(4/3)^k‖`*, Mat. Zametki **85**:6
  (2009), 927–935 — its Theorem 2 is the effective version of [Zud07] at `0.5795`, for
  `k ≥ 871 387 440 264`.
* `plans/note-Tshift-S1-WP7.html` — the source audit; `plans/plan-Tshift-S1.html` §4 WP7.
-/

set_option exponentiation.threshold 2000

namespace TShift

open Zudilin

/-! ## 1. The rate, and where it sits -/

/-- The record rate, `[Zud07]` Theorem 1: `‖(3/2)^k‖ > 0.5803^k` for all large `k`. -/
noncomputable def thetaZud : ℝ := 5803 / 10000

/-- The admissible-multiplier base of the uniform form, `1 + 1.3·10⁻³`.  It is the analogue of
`TShift.bHab = 1 + 8.227·10⁻⁴` and it is **larger**: the multiplier budget is the (26) margin
`0.0786079` nats per `m` spread over `3β = 57` dates instead of Habsieger's over `6`. -/
noncomputable def bZud : ℝ := 10013 / 10000

@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem thetaZud_pos : 0 < thetaZud := by rw [thetaZud]; norm_num

@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem one_le_bZud : (1 : ℝ) ≤ bZud := by rw [bZud]; norm_num

/-- **Honesty lemma.**  The record rate does not reach the `2/3` threshold either: the gap
`0.5803 → 2/3` is the open problem, and nothing here touches it. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem thetaZud_lt_two_thirds : thetaZud < 2 / 3 := by rw [thetaZud]; norm_num

/-- The rate improves on the transported [Hab03] rate of `TShift/HabsiegerTransfer.lean`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem thetaHab_lt_thetaZud : thetaHab < thetaZud := by rw [thetaHab, thetaZud]; norm_num

/-- …and so does the admissible-multiplier base of the uniform form. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem bHab_lt_bZud : bHab < bZud := by rw [bHab, bZud]; norm_num

/-! ## 2. The two rational inequalities

Everything analytic in [Zud07] enters through these; both are decided on the frozen surrogates. -/

/-- **Condition (26)**, `C₀ − C₂ + (β − 2α)log 3 < 0`, in surrogate form and with the `8 %` of
margin the Bernoulli step below uses: the paper's margin is `e^{0.0786079} = 1.08178`. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem zud_validity : (27 / 25 : ℝ) * (3 * errorBase) ≤ contentBase := by
  rw [errorBase, contentBase]; norm_num

/-- **The rate**, `e^{−(C₁−C₂)/3β} > 0.5803`, in surrogate form and with the margin named:
`1 + 1/4000` per `m` is left over, against the `1.0002732` the exact constants leave. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem zud_rate : (1 + 1 / 4000 : ℝ) * (denomBase * thetaZud ^ 57) ≤ contentBase := by
  rw [denomBase, contentBase, thetaZud]; norm_num

/-- The same, with the admissible multiplier of the uniform form charged against (26). -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem zud_validity_uniform :
    (1 + 1 / 360 : ℝ) * (bZud ^ 57 * (3 * errorBase)) ≤ contentBase := by
  rw [bZud, errorBase, contentBase]; norm_num

/-! ## 3. The Bernoulli steps

Three, all of the form "a base above `1` beats a constant once `m` is large"; no `r^m` is ever
evaluated. -/

/-- The block constant: `2^{j+1}·θ^{3+j} = 2θ³·(2θ)^j ≤ 2θ³·(2θ)⁵⁶ ≤ 1638`.  It is bounded only
because `2θ = 1.1606` barely exceeds `1` — this is why the block is read *upwards* from its head
`N = 57m + 3`, as [Zud07] reads it, and not downwards from the next one. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem zud_block_constant {j : ℕ} (hj : j < 57) :
    (2 : ℝ) ^ (j + 1) * thetaZud ^ (3 + j) ≤ 1638 := by
  have hrw : (2 : ℝ) ^ (j + 1) * thetaZud ^ (3 + j)
      = 2 * thetaZud ^ 3 * (2 * thetaZud) ^ j := by
    rw [pow_succ, pow_add, mul_pow]; ring
  have hmono : (2 * thetaZud) ^ j ≤ (2 * thetaZud) ^ 56 :=
    pow_le_pow_right₀ (by rw [thetaZud]; norm_num) (by omega)
  have hpos : (0 : ℝ) ≤ 2 * thetaZud ^ 3 := by rw [thetaZud]; norm_num
  have hfin : 2 * thetaZud ^ 3 * (2 * thetaZud) ^ 56 ≤ 1638 := by
    rw [thetaZud]; norm_num
  calc (2 : ℝ) ^ (j + 1) * thetaZud ^ (3 + j)
      = 2 * thetaZud ^ 3 * (2 * thetaZud) ^ j := hrw
    _ ≤ 2 * thetaZud ^ 3 * (2 * thetaZud) ^ 56 := by
        exact mul_le_mul_of_nonneg_left hmono hpos
    _ ≤ 1638 := hfin

/-- `(1 + 1/4000)^m ≥ 1638` once `m ≥ 6 548 000`, i.e. `k ≥ 3.7·10⁸`.  This is the whole
arithmetic threshold of the rate step. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem zud_const_absorb {m : ℕ} (hm : 6548000 ≤ m) : (1638 : ℝ) ≤ (1 + 1 / 4000) ^ m := by
  have hb : (1 : ℝ) + (m : ℝ) * (1 / 4000) ≤ (1 + 1 / 4000) ^ m :=
    one_add_mul_le_pow (by norm_num) m
  have hmR : (6548000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

/-- **The error term is at most half the main term** — the only place the multiplier is charged,
and the charge is exactly (26).  `2·3^{j+1}·D ≤ (27/25)^m` suffices, and Bernoulli gives it from
`m ≥ 25·3⁵⁷·D`. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem zud_error_small {m j D : ℕ} (hj : j < 57) (hm : 25 * 3 ^ 57 * D ≤ m) :
    2 * 3 ^ (j + 1) * (D : ℝ) * (3 * errorBase) ^ m ≤ contentBase ^ m := by
  have hepos : (0 : ℝ) ≤ (3 * errorBase) ^ m := by
    have := errorBase_pos
    positivity
  have hbern : (1 : ℝ) + (m : ℝ) * (2 / 25) ≤ (27 / 25) ^ m := by
    have h := one_add_mul_le_pow (a := (2 : ℝ) / 25) (by norm_num) m
    calc (1 : ℝ) + (m : ℝ) * (2 / 25) ≤ (1 + 2 / 25) ^ m := h
      _ = ((27 : ℝ) / 25) ^ m := by norm_num
  have hmR : (25 : ℝ) * 3 ^ 57 * (D : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h3j : (3 : ℝ) ^ (j + 1) ≤ 3 ^ 57 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hDpos : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hcst : 2 * (3 : ℝ) ^ (j + 1) * (D : ℝ) ≤ (27 / 25) ^ m := by
    have h1 : 2 * (3 : ℝ) ^ (j + 1) * (D : ℝ) ≤ 2 * 3 ^ 57 * (D : ℝ) := by nlinarith
    nlinarith
  calc 2 * (3 : ℝ) ^ (j + 1) * (D : ℝ) * (3 * errorBase) ^ m
      ≤ (27 / 25) ^ m * (3 * errorBase) ^ m := by
        exact mul_le_mul_of_nonneg_right hcst hepos
    _ = ((27 / 25) * (3 * errorBase)) ^ m := (mul_pow (27 / 25 : ℝ) (3 * errorBase) m).symm
    _ ≤ contentBase ^ m := by
        refine pow_le_pow_left₀ ?_ zud_validity m
        have := errorBase_pos
        positivity

/-- The uniform version: the multiplier is no longer fixed but bounded by `bZud^k`, and the same
(26) margin pays for it — `bZud^57` eats `1.0769` of the `1.08178`, leaving `1 + 1/360`. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem zud_error_small_uniform {m j D : ℕ} (hj : j < 57) (hm : 1440 * 3 ^ 57 ≤ m)
    (hD : (D : ℝ) ≤ bZud ^ (57 * m + 3 + j)) :
    2 * 3 ^ (j + 1) * (D : ℝ) * (3 * errorBase) ^ m ≤ contentBase ^ m := by
  have hepos : (0 : ℝ) ≤ (3 * errorBase) ^ m := by
    have := errorBase_pos
    positivity
  have hbz : (0 : ℝ) < bZud := lt_of_lt_of_le zero_lt_one one_le_bZud
  -- the multiplier, split into a constant and the per-`m` factor
  have hDsplit : (D : ℝ) ≤ bZud ^ 59 * (bZud ^ 57) ^ m := by
    refine le_trans hD ?_
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ one_le_bZud (by omega)
  have hb59 : bZud ^ 59 ≤ 2 := by rw [bZud]; norm_num
  have h3j : (3 : ℝ) ^ (j + 1) ≤ 3 ^ 57 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hbern : (1 : ℝ) + (m : ℝ) * (1 / 360) ≤ (1 + 1 / 360) ^ m :=
    one_add_mul_le_pow (by norm_num) m
  have hmR : (1440 : ℝ) * 3 ^ 57 ≤ (m : ℝ) := by exact_mod_cast hm
  have hcst : 2 * (3 : ℝ) ^ (j + 1) * (bZud ^ 59) ≤ (1 + 1 / 360) ^ m := by
    nlinarith [pow_pos hbz 59]
  have hbzm : (0 : ℝ) < (bZud ^ 57) ^ m := pow_pos (pow_pos hbz 57) m
  calc 2 * (3 : ℝ) ^ (j + 1) * (D : ℝ) * (3 * errorBase) ^ m
      ≤ 2 * (3 : ℝ) ^ (j + 1) * (bZud ^ 59 * (bZud ^ 57) ^ m) * (3 * errorBase) ^ m := by
        have hpos : (0 : ℝ) ≤ 2 * 3 ^ (j + 1) := by positivity
        have := mul_le_mul_of_nonneg_left hDsplit hpos
        exact mul_le_mul_of_nonneg_right this hepos
    _ = (2 * (3 : ℝ) ^ (j + 1) * bZud ^ 59) * ((bZud ^ 57) ^ m * (3 * errorBase) ^ m) := by ring
    _ ≤ (1 + 1 / 360) ^ m * ((bZud ^ 57) ^ m * (3 * errorBase) ^ m) := by
        refine mul_le_mul_of_nonneg_right hcst ?_
        positivity
    _ = ((1 + 1 / 360) * (bZud ^ 57 * (3 * errorBase))) ^ m := by
        rw [← mul_pow, ← mul_pow]
    _ ≤ contentBase ^ m := by
        refine pow_le_pow_left₀ ?_ zud_validity_uniform m
        have := errorBase_pos
        positivity

/-! ## 4. The block, the elimination and the endgame -/

/-- `(3^j·D)·(3/2)^{N} = 2^j·(D·(3/2)^{N+j})`, so a bound at the block head ascends to the date
`k = N + j` at the cost of `2^j`.  The mirror of `TShift.distToNearestInt_descent`, which is what
[Hab03]'s downward blocking `k = 6m − δ` needs. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem distToNearestInt_ascent (D j N : ℕ) :
    distToNearestInt ((3 : ℝ) ^ j * (D : ℝ) * ((3 : ℝ) / 2) ^ N)
      ≤ 2 ^ j * distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ (N + j)) := by
  have hrw : (3 : ℝ) ^ j * (D : ℝ) * ((3 : ℝ) / 2) ^ N
      = ((2 ^ j : ℕ) : ℝ) * ((D : ℝ) * ((3 : ℝ) / 2) ^ (N + j)) := by
    have h32 : (2 : ℝ) ^ j * ((3 : ℝ) / 2) ^ j = 3 ^ j := by rw [← mul_pow]; norm_num
    push_cast
    rw [pow_add, ← h32]
    ring
  rw [hrw]
  have h := distToNearestInt_mul_le (D := 2 ^ j) (by positivity)
    ((D : ℝ) * ((3 : ℝ) / 2) ^ (N + j)) 0
  simpa using h

/-- **The master bound.**  One `m`, one date of its block, one multiplier: the elimination step of
`TShift/MultiplierTransfer.lean` run on `Zudilin.PadeData`, with the error term already discharged
by the hypothesis. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem le_dist_master {m j D : ℕ} (F : Zudilin.PadeData m) (hD : 0 < D)
    (herr : 2 * 3 ^ (j + 1) * (D : ℝ) * (3 * errorBase) ^ m ≤ contentBase ^ m) :
    contentBase ^ m / (2 ^ (j + 1) * denomBase ^ m)
      ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ (57 * m + 3 + j)) := by
  have hBpos : (0 : ℝ) < denomBase ^ m := denomBase_pow_pos m
  have hepos : (0 : ℝ) < errorBase ^ m := pow_pos errorBase_pos m
  have hDj : 0 < 3 ^ j * D := by positivity
  have hcast : ((3 ^ j * D : ℕ) : ℝ) = 3 ^ j * (D : ℝ) := by push_cast; ring
  have htrans := le_distToNearestInt_pow (N := 57 * m + 3) (v := 0) (D := 3 ^ j * D) hDj hBpos
    F.det_ne_zero F.dvd_a₁ F.dvd_b₁ F.dvd_a₂ F.dvd_b₂ F.content₁_abs F.content₂_abs
    F.size₁ F.size₂ F.coeff₁ F.coeff₂
  rw [hcast] at htrans
  simp only [pow_zero, one_mul] at htrans
  -- the numerator, with the error term discharged
  have hnum : contentBase ^ m / 2
      ≤ contentBase ^ m - 3 ^ j * (D : ℝ) * (3 ^ (m + 1) * errorBase ^ m) := by
    have h1 : (3 : ℝ) ^ (m + 1) = 3 ^ m * 3 := pow_succ 3 m
    have h2 : (3 : ℝ) ^ (j + 1) = 3 ^ j * 3 := pow_succ 3 j
    have h3 : (3 * errorBase : ℝ) ^ m = 3 ^ m * errorBase ^ m := mul_pow 3 errorBase m
    rw [h2, h3] at herr
    rw [h1]
    linarith
  -- the column `2^N` cancels out of the fraction
  have hfrac : (contentBase ^ m * 2 ^ (57 * m + 3)
        - 3 ^ j * (D : ℝ) * (2 ^ (57 * m + 3) * 3 ^ (m + 1) * errorBase ^ m))
        / (denomBase ^ m * 2 ^ (57 * m + 3))
      = (contentBase ^ m - 3 ^ j * (D : ℝ) * (3 ^ (m + 1) * errorBase ^ m)) / denomBase ^ m := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hfrac] at htrans
  have hleft : contentBase ^ m / (2 * denomBase ^ m)
      ≤ (contentBase ^ m - 3 ^ j * (D : ℝ) * (3 ^ (m + 1) * errorBase ^ m)) / denomBase ^ m := by
    rw [div_le_div_iff₀ (by positivity) hBpos]
    linarith [mul_le_mul_of_nonneg_right hnum (le_of_lt hBpos)]
  -- the right-hand side, ascended to the date `k`
  have hright := distToNearestInt_ascent D j (57 * m + 3)
  have hchain : contentBase ^ m / (2 * denomBase ^ m)
      ≤ 2 ^ j * distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ (57 * m + 3 + j)) :=
    le_trans hleft (le_trans htrans hright)
  rw [div_le_iff₀ (by positivity)] at hchain ⊢
  have hsucc : (2 : ℝ) ^ j * distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ (57 * m + 3 + j))
        * (2 * denomBase ^ m)
      = distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ (57 * m + 3 + j))
        * (2 ^ (j + 1) * denomBase ^ m) := by
    rw [pow_succ]; ring
  linarith [hchain, hsucc]

/-- **The rate step.**  `1638` of block constant against `(1 + 1/4000)^m` of margin. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem zud_rate_step {m j : ℕ} (hj : j < 57) (hm : 6548000 ≤ m) :
    thetaZud ^ (57 * m + 3 + j) ≤ contentBase ^ m / (2 ^ (j + 1) * denomBase ^ m) := by
  have hBpos : (0 : ℝ) < denomBase ^ m := denomBase_pow_pos m
  have hθpos : (0 : ℝ) < thetaZud := thetaZud_pos
  have hsplit : thetaZud ^ (57 * m + 3 + j) = (thetaZud ^ 57) ^ m * thetaZud ^ (3 + j) := by
    rw [← pow_mul, ← pow_add, ← Nat.add_assoc]
  have hgrow : ((1 + 1 / 4000 : ℝ) * (denomBase * thetaZud ^ 57)) ^ m ≤ contentBase ^ m := by
    refine pow_le_pow_left₀ ?_ zud_rate m
    have := denomBase_pos
    positivity
  have hexp : ((1 + 1 / 4000 : ℝ) * (denomBase * thetaZud ^ 57)) ^ m
      = (1 + 1 / 4000 : ℝ) ^ m * (denomBase ^ m * (thetaZud ^ 57) ^ m) := by
    rw [mul_pow, mul_pow]
  have habs := zud_const_absorb hm
  have hblk := zud_block_constant hj
  have hposm : (0 : ℝ) < (thetaZud ^ 57) ^ m := by positivity
  rw [le_div_iff₀ (by positivity), hsplit]
  -- `2^{j+1}·θ^{3+j} ≤ 1638 ≤ (1+1/4000)^m`
  have hstep : (thetaZud ^ 57) ^ m * thetaZud ^ (3 + j) * (2 ^ (j + 1) * denomBase ^ m)
      = (2 ^ (j + 1) * thetaZud ^ (3 + j)) * (denomBase ^ m * (thetaZud ^ 57) ^ m) := by ring
  rw [hstep]
  calc (2 ^ (j + 1) * thetaZud ^ (3 + j)) * (denomBase ^ m * (thetaZud ^ 57) ^ m)
      ≤ 1638 * (denomBase ^ m * (thetaZud ^ 57) ^ m) := by
        refine mul_le_mul_of_nonneg_right hblk ?_
        positivity
    _ ≤ (1 + 1 / 4000 : ℝ) ^ m * (denomBase ^ m * (thetaZud ^ 57) ^ m) := by
        refine mul_le_mul_of_nonneg_right habs ?_
        positivity
    _ = ((1 + 1 / 4000 : ℝ) * (denomBase * thetaZud ^ 57)) ^ m := hexp.symm
    _ ≤ contentBase ^ m := hgrow

/-! ## 5. The transported bound -/

/-- **The transported record rate, uniformly in the multiplier.**  `‖D·(3/2)^k‖ ≥ (0.5803)^k` for
every `k` beyond some threshold, *simultaneously* for every `1 ≤ D ≤ (1 + 1.3·10⁻³)^k`.

The threshold is existential and that is [Zud07]'s, not ours: see the module docstring. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem le_dist_zudilin_uniform :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ D : ℕ, 0 < D → (D : ℝ) ≤ bZud ^ k →
      thetaZud ^ k ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) := by
  obtain ⟨M, hM⟩ := Zudilin.padeData
  refine ⟨57 * (max M (max (1440 * 3 ^ 57) 6548000) + 2), fun k hk D hD hDk => ?_⟩
  set M' := max M (max (1440 * 3 ^ 57) 6548000) with hM'def
  obtain ⟨m, j, hj, hmM, hkeq⟩ :
      ∃ m j : ℕ, j < 57 ∧ M' < m ∧ k = 57 * m + 3 + j :=
    ⟨(k - 3) / 57, (k - 3) % 57, Nat.mod_lt _ (by norm_num), by omega, by omega⟩
  have hMm : M < m := lt_of_le_of_lt (le_max_left _ _) hmM
  have h1 : 1440 * 3 ^ 57 ≤ m :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right M _)) hmM)
  have h2 : 6548000 ≤ m :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right M _)) hmM)
  obtain ⟨F⟩ := hM m hMm
  subst hkeq
  exact le_trans (zud_rate_step hj h2)
    (le_dist_master F hD (zud_error_small_uniform hj h1 hDk))

/-- **The transported record rate at a fixed multiplier.**  `‖D·(3/2)^k‖ ≥ (0.5803)^k` for every
`k` beyond a threshold depending on `D` — the direct form, which charges `D` against (26) rather
than routing it through `bZud`. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem le_dist_zudilin {D : ℕ} (hD : 0 < D) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      thetaZud ^ k ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) := by
  obtain ⟨M, hM⟩ := Zudilin.padeData
  refine ⟨57 * (max M (max (25 * 3 ^ 57 * D) 6548000) + 2), fun k hk => ?_⟩
  set M' := max M (max (25 * 3 ^ 57 * D) 6548000) with hM'def
  obtain ⟨m, j, hj, hmM, hkeq⟩ :
      ∃ m j : ℕ, j < 57 ∧ M' < m ∧ k = 57 * m + 3 + j :=
    ⟨(k - 3) / 57, (k - 3) % 57, Nat.mod_lt _ (by norm_num), by omega, by omega⟩
  have hMm : M < m := lt_of_le_of_lt (le_max_left _ _) hmM
  have h1 : 25 * 3 ^ 57 * D ≤ m :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right M _)) hmM)
  have h2 : 6548000 ≤ m :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right M _)) hmM)
  obtain ⟨F⟩ := hM m hMm
  subst hkeq
  exact le_trans (zud_rate_step hj h2) (le_dist_master F hD (zud_error_small hj h1))

/-! ## 6. Corollaries in the corpus' vocabulary -/

/-- The multiplier form: `TShift.IsRepelledMul` at the record rate `0.5803`, for **every**
positive multiplier, with `c = 1`.  The predicate is existential in its threshold, which is exactly
what [Zud07] supplies — so the record rate reaches the corpus without any loss. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem isRepelledMul_zudilin {D : ℕ} (hD : 0 < D) : IsRepelledMul thetaZud D := by
  obtain ⟨K, hK⟩ := le_dist_zudilin hD
  exact ⟨1, one_pos, K, fun n hn => by simpa using hK n hn⟩

/-- The `D = 5` instance: the period-2 cycle denominator, at the record rate. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem isRepelledMul_five_zudilin : IsRepelledMul thetaZud 5 :=
  isRepelledMul_zudilin (by norm_num)

/-- **Corollary A′ at the record rate.**  For every period `p ≥ 1` and every numerator `A`, the
orbit `(3/2)ⁿ` is repelled from the cycle target `A/(3^p − 2^p)` at rate `0.5803`, uniformly in
`A`.  This supersedes `TShift.isRepelled_cycle` in the rate and is superseded by it in the
threshold. -/
@[category research solved, AMS 11, ref "Zud07" "TshiftS1", group "tshift_s1"]
theorem isRepelled_cycle_zudilin {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    IsRepelled thetaZud ((A : ℝ) / Z32.cycleDenom p) :=
  (isRepelledMul_zudilin (Z32.cycleDenom_pos hp)).isRepelled (Z32.cycleDenom_pos hp) A

/-- **Honesty lemma, in problem form.**  The record rate is still below `2/3`, so the sojourn cap
stays `≥ 1` and no instance of `TShift.TShiftProblem` follows. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem one_le_kappa_thetaZud : 1 ≤ kappa thetaZud := by
  by_contra hcon
  push Not at hcon
  exact absurd ((kappa_lt_one_iff thetaZud_pos).mp hcon)
    (not_lt.mpr (le_of_lt thetaZud_lt_two_thirds))

end TShift
