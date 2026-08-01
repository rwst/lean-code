/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LineCover
import CITED.BugeaudEvertseRidout

/-!
# The general effective Mahler line cover: `‖δ(p/q)ⁿ‖ < cⁿ` for all coprime `(p, q)` and `c < 1`

The `(3, 2, 3/4)` line theorem of `BB13/LineCover.lean`, stated where it actually lives: for
**every** coprime pair `p > q ≥ 2`, **every** rate `0 < c < 1` and **every** rational multiplier
`δ`, the `n` with `‖δ(p/q)ⁿ‖ < cⁿ` above an explicit height lie on at most `K(ε(p,c))` lines
through the origin, with

`ε(p, c) = log(1/c)/log p`  (`BB13.epsilon`, the sharp gap exponent of the elementary layer).

This is item C.8 (general effective Mahler count) and C.9 (multipliers) of `plans/report-BB13.md`,
the first `W-opt` package of `plans/plan2-BB13.html`; the plan carried out here is
`plans/plan-BB13-generalize.html`.

## The frame

For `m = round(δ(p/q)ⁿ)` the frame point is `(x, y) = (m·qⁿ, pⁿ)`, and the three conditions of
the Bugeaud–Evertse system (5.11) read

* `|δ − x/y| = ‖δ(p/q)ⁿ‖·(q/p)ⁿ < (cq/p)ⁿ = y^{−f_∞}`, `f_∞ = log(p/(cq))/log p` (`BB13.fArch`);
* `|x|_l ≤ l^{−n·v_l(q)}` for `l ∣ q`, total exponent `θ = log q/log p`  (`qⁿ ∣ x`);
* `|y|_l = l^{−n·v_l(p)}` for `l ∣ p`, total exponent `1`  (`y = pⁿ`).

The budget (5.10) is met exactly:

`f_∞ + θ + 1 = (1 + ε − θ) + θ + 1 = 2 + ε`  (`BB13.fArch_budget`),

generalizing the identity `θ + θ + 1 = 2 + ε*` of the headline case, which is the instance
`(p, q, c) = (3, 2, 3/4)` where `f_∞ = θ` (`BB13.fArch_three_two`).  The per-prime bookkeeping is
done once in `BugeaudEvertse.ridout_line_cover_pow`.

## The threshold, in closed form

The height condition (5.12) is `pⁿ > max(2H(δ), 2^{4/ε})`, and substituting `ε = log(1/c)/log p`
turns its second half into

`cⁿ < 1/16`,

**independent of `p` and `q`** (`BB13.threshold_of_pow_lt`).  At `c = 3/4` this is `n ≥ 10`, the
threshold of `BB13/LineCover.lean`, recovered.  The multiplier costs nothing in the constant and
only shifts the first half from `pⁿ > 2` to `pⁿ > 2·max(|num δ|, den δ)` — worth stating, since
the *retired* effective axiom had suggested a factor `|num δ| + den δ` in the count itself.

## Contents

* `MnumMul`, `IsFailureMul`, `frameXMul`, `linePointMul` — the `δ`-multiplied objects; `δ = 1`
  returns the objects of `BB13/Basic.lean` and `BB13/LineCover.lean` (`linePointMul_one_3_2`).
* `fArch`, `fArch_budget`, `fArch_nonneg` — the archimedean exponent and its budget identity.
* `mahler_line_cover` — the headline; `mahler_lines_card_le` its counting form.
* `failures_line_cover_of_general` — `BB13.failures_line_cover` re-derived as the instance
  `(1, 3, 2, 3/4)`, as a consistency check on the general statement.

Footprint: `std3 + BugeaudEvertse.ridout_line_cover`.

## `K(ε(p,c))` at a few bases (mpmath, 60 dps, 2026-07-22)

| `(p, q, c)`  | `ε(p,c)`   | `θ = log q/log p` | `f_∞`    | `K(ε)`             | least `n` with `cⁿ < 1/16` |
|--------------|------------|-------------------|----------|--------------------|----------------------------|
| `(3, 2, 3/4)`| 0.26185951 | 0.630930          | 0.630930 | 1 856 360 182 227  | 10 |
| `(3, 2, 4/5)`| 0.20311401 | 0.630930          | 0.572184 | 3 777 794 902 419  | 13 |
| `(3, 2, 9/10)`|0.09590327 | 0.630930          | 0.464974 | 34 669 429 434 220 | 27 |
| `(4, 3, 3/4)`| 0.20751875 | 0.792481          | 0.415037 | 3 554 366 852 077  | 10 |
| `(5, 3, 3/4)`| 0.17874692 | 0.682606          | 0.496141 | 5 449 831 243 823  | 10 |
| `(5, 2, 1/2)`| 0.43067656 | 0.430677          | 1.000000 |   503 202 329 681  |  5 |
| `(7, 5, 5/6)`| 0.09369475 | 0.827087          | 0.266607 | 37 215 458 132 544 | 16 |

The first row is `BB13/Constants.lean`'s certified `K(ε*)`; certified bounds for the others are
not attempted here (each needs its own rational log bounds).

## References

* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957), 122–124 — the ineffective finiteness this makes quantitative (up to the per-line
  problem; see `BB13/MahlerCount.lean`).
* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — `CITED/BugeaudEvertseRidout.lean`.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* `plans/plan-BB13-generalize.html` (G3); `plans/report-BB13.md` §3, items C.8 and C.9.
-/

namespace BB13

open scoped Real

/-! ### The multiplied sequence `δ(p/q)ⁿ` and its frame point -/

/-- The **nearest-integer numerator of the multiplied sequence**, `m = round(δ(p/q)ⁿ)`.  At
`δ = 1` this is `BB13.Mnum` (`MnumMul_one`). -/
noncomputable def MnumMul (δ : ℚ) (p q n : ℕ) : ℤ := round ((δ : ℝ) * ((p : ℝ) / q) ^ n)

/-- A **failure of the multiplied sequence**: `‖δ(p/q)ⁿ‖ < cⁿ`.  At `δ = 1` this is
`BB13.IsFailure` (`isFailureMul_one`), whose exact-integer form `|kₙ| < (cq)ⁿ` is what the
elementary layer runs on. -/
noncomputable def IsFailureMul (δ : ℚ) (p q : ℕ) (c : ℝ) (n : ℕ) : Prop :=
  distToNearestInt ((δ : ℝ) * ((p : ℝ) / q) ^ n) < c ^ n

/-- The `x`-coordinate `x = m·qⁿ` of the frame point of `n`.  The `y`-coordinate is `pⁿ`. -/
noncomputable def frameXMul (δ : ℚ) (p q n : ℕ) : ℤ := MnumMul δ p q n * (q : ℤ) ^ n

/-- The **slope** `x/y = m·qⁿ/pⁿ` of the frame point: the one-dimensional subspace of `ℚ²` it
spans, coordinatized.  Two failures share a line exactly when their `linePointMul`s agree. -/
noncomputable def linePointMul (δ : ℚ) (p q n : ℕ) : ℚ := (frameXMul δ p q n : ℚ) / (p : ℚ) ^ n

/-- The frame point is `qⁿ`-divisible by construction — the whole `S₁`-side of the system. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem frameXMul_dvd (δ : ℚ) (p q n : ℕ) : (q : ℤ) ^ n ∣ frameXMul δ p q n :=
  ⟨MnumMul δ p q n, by rw [frameXMul]; ring⟩

/-! ### The archimedean exponent -/

/-- The **archimedean exponent** `f_∞ = 1 + ε(p,c) − log q/log p = log(p/(cq))/log p` of the
general frame: the quality `|δ − x/y| < (cq/p)ⁿ = y^{−f_∞}` that a failure buys.  At
`(p, q, c) = (3, 2, 3/4)` it equals `θ = log 2/log 3` (`fArch_three_two`). -/
noncomputable def fArch (p q : ℕ) (c : ℝ) : ℝ := 1 + epsilon p c - Real.log q / Real.log p

/-- **The budget identity** `f_∞ + θ + 1 = 2 + ε`: the general frame meets (5.10) exactly, with no
slack, for every `(p, q, c)`.  The `(3, 2, 3/4)` instance is `theta_add_theta_add_one`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem fArch_budget (p q : ℕ) (c : ℝ) :
    fArch p q c + Real.log q / Real.log p + 1 = 2 + epsilon p c := by
  rw [fArch]; ring

/-- `f_∞ = log(p/(cq))/log p`: the closed form of the archimedean exponent. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem fArch_eq_log_div {p q : ℕ} {c : ℝ} (hp : 1 < p) (hq : 0 < q) (hc0 : 0 < c) :
    fArch p q c = Real.log ((p : ℝ) / (c * q)) / Real.log p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hp
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlp : Real.log p ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  rw [fArch, epsilon, Real.log_div (ne_of_gt hp0) (by positivity), Real.log_mul (ne_of_gt hc0)
    (ne_of_gt hq0), Real.log_div one_ne_zero (ne_of_gt hc0), Real.log_one]
  field_simp
  ring

/-- `f_∞ ≥ 0` — automatic in the Mahler setting, where `c·q < q < p`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem fArch_nonneg {p q : ℕ} {c : ℝ} (hp : 1 < p) (hq : 0 < q) (hc0 : 0 < c)
    (hcq : c * q ≤ p) : 0 ≤ fArch p q c := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  rw [fArch_eq_log_div hp hq hc0]
  refine div_nonneg (Real.log_nonneg ?_) hlp.le
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `ε(p, c) > 0` for `p ≥ 2` and `c < 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem epsilon_pos {p : ℕ} {c : ℝ} (hp : 1 < p) (hc0 : 0 < c) (hc1 : c < 1) :
    0 < epsilon p c := by
  rw [epsilon]
  refine div_pos (Real.log_pos ?_) (Real.log_pos (by exact_mod_cast hp))
  rw [lt_div_iff₀ hc0]; linarith

/-! ### The three conditions of the system (5.11) -/

/-- **The archimedean quantity of the general frame, computed**:
`|δ − x/pⁿ| = ‖δ(p/q)ⁿ‖·(q/p)ⁿ`.  Every smallness event of `δ(p/q)ⁿ` enters the subspace frame
through this identity; the `(3, 2, 3/4, 1)` case is `BB13.frame_arch_eq`. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_arch_mul_eq {p q : ℕ} (δ : ℚ) (n : ℕ) (hp : 0 < p) (hq : 0 < q) :
    |(δ : ℝ) - (frameXMul δ p q n : ℝ) / (p : ℝ) ^ n|
      = distToNearestInt ((δ : ℝ) * ((p : ℝ) / q) ^ n) * ((q : ℝ) / p) ^ n := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  have h1 : ((p : ℝ) / q) ^ n * ((q : ℝ) / p) ^ n = 1 := by
    rw [← mul_pow]; field_simp; exact one_pow n
  have hkey : (δ : ℝ) - (frameXMul δ p q n : ℝ) / (p : ℝ) ^ n
      = ((δ : ℝ) * ((p : ℝ) / q) ^ n - (MnumMul δ p q n : ℝ)) * ((q : ℝ) / p) ^ n := by
    rw [sub_mul, mul_assoc, h1, mul_one, frameXMul, div_pow]
    push_cast
    ring
  rw [hkey, abs_mul, distToNearestInt, show round ((δ : ℝ) * ((p : ℝ) / q) ^ n)
    = MnumMul δ p q n from rfl, abs_of_pos (by positivity : (0 : ℝ) < ((q : ℝ) / p) ^ n)]

/-- **The archimedean condition.**  A failure of `δ(p/q)ⁿ` at rate `cⁿ` gives
`|δ − x/pⁿ| ≤ (pⁿ)^{−f_∞}`: the failure inequality, weighted by `(q/p)ⁿ`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_archimedean_mul {p q : ℕ} {c : ℝ} {δ : ℚ} {n : ℕ} (hp : 1 < p) (hq : 0 < q)
    (hc0 : 0 < c) (hnf : IsFailureMul δ p q c n) :
    |(δ : ℝ) - (frameXMul δ p q n : ℝ) / (p : ℝ) ^ n| ≤ ((p : ℝ) ^ n) ^ (-fArch p q c) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hp
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hb : (0 : ℝ) < (p : ℝ) / (c * q) := by positivity
  -- the right-hand side is `(cq/p)ⁿ`
  have hrhs : ((p : ℝ) ^ n) ^ (-fArch p q c) = (c * q / p) ^ n := by
    rw [fArch_eq_log_div hp hq hc0,
      show -(Real.log ((p : ℝ) / (c * q)) / Real.log p)
        = -((1 : ℝ) * Real.log ((p : ℝ) / (c * q)) / Real.log p) by ring,
      BugeaudEvertse.rpow_pow_logRatio hp hb 1 n, one_mul,
      Real.rpow_neg hb.le, Real.rpow_natCast, ← inv_pow, inv_div]
  rw [frame_arch_mul_eq δ n (Nat.zero_lt_of_lt hp) hq, hrhs]
  calc distToNearestInt ((δ : ℝ) * ((p : ℝ) / q) ^ n) * ((q : ℝ) / p) ^ n
      ≤ c ^ n * ((q : ℝ) / p) ^ n :=
        mul_le_mul_of_nonneg_right hnf.le (by positivity)
    _ = (c * q / p) ^ n := by rw [← mul_pow]; congr 1; ring

/-! ### The height threshold, in closed form -/

/-- **The height threshold of (5.12), for the general frame**: `2^{4/ε(p,c)} < pⁿ` as soon as
`cⁿ < 1/16`.  Substituting `ε(p,c) = log(1/c)/log p` makes `log p` cancel, so the condition on `n`
depends on the rate `c` **alone** — at `c = 3/4` it is `n ≥ 10`, the threshold of
`BB13/LineCover.lean`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem threshold_of_pow_lt {p : ℕ} {c : ℝ} {n : ℕ} (hp : 1 < p) (hc0 : 0 < c) (hc1 : c < 1)
    (h : c ^ n < 1 / 16) : (2 : ℝ) ^ ((4 : ℝ) / epsilon p c) < (p : ℝ) ^ n := by
  refine two_rpow_four_div_lt_base hp (epsilon_pos hp hc0 hc1) ?_
  have hlp : Real.log p ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  have hkey : epsilon p c * Real.log p = Real.log (1 / c) := by
    rw [epsilon]; field_simp
  have hlog : Real.log (c ^ n) < Real.log (1 / 16 : ℝ) :=
    Real.log_lt_log (by positivity) h
  rw [Real.log_pow] at hlog
  have h16 : Real.log (1 / 16 : ℝ) = -(4 * Real.log 2) := by
    rw [Real.log_div one_ne_zero (by norm_num), Real.log_one,
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast; ring
  have hcinv : Real.log (1 / c) = -Real.log c := by
    rw [Real.log_div one_ne_zero (ne_of_gt hc0), Real.log_one]; ring
  rw [hkey, hcinv, mul_neg]
  rw [h16] at hlog
  linarith

/-! ### The general line cover -/

/-- **The general effective Mahler line theorem** (report C.8 + C.9).  For coprime bases
`p > q ≥ 1`, any rate `0 < c < 1` and any rational multiplier `δ`, the exponents `n` with

`‖δ(p/q)ⁿ‖ < cⁿ`,  `cⁿ < 1/16`,  `pⁿ > 2·H(δ)`

lie on at most `K(ε(p,c))` lines through the origin, where `ε(p,c) = log(1/c)/log p` is the sharp
gap exponent of the elementary layer and `K = BugeaudEvertse.lineBound`.

The three exponents of the Bugeaud–Evertse system are `(f_∞, θ, 1)` with
`f_∞ = log(p/(cq))/log p` and `θ = log q/log p`, whose sum is `2 + ε(p,c)` exactly
(`fArch_budget`) — so, as in the headline case, **the exponent is forced and nothing is given
away**.  The multiplier `δ` enters only as the point `ξ` being approximated: it costs nothing in
the constant and merely raises the height threshold from `pⁿ > 2` to `pⁿ > 2·max(|num δ|, den δ)`.

The `(δ, p, q, c) = (1, 3, 2, 3/4)` instance is `BB13.failures_line_cover`
(`failures_line_cover_of_general`).  Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Mah57" "Bug12", group "bugeaud_10_13"]
theorem mahler_line_cover (δ : ℚ) (p q : ℕ) (c : ℝ) (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound (epsilon p c) ∧
      ∀ n : ℕ, c ^ n < 1 / 16 → 2 * (BugeaudEvertse.ratHeight δ : ℝ) < (p : ℝ) ^ n →
        IsFailureMul δ p q c n → linePointMul δ p q n ∈ R := by
  have hp : 1 < p := lt_of_le_of_lt hq hqp
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqp' : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqp.le
  have hcq : c * q ≤ p := by nlinarith
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover_pow δ (epsilon p c) (fArch p q c) p q
    hp hq hcop (epsilon_pos hp hc0 hc1) (fArch_nonneg hp hq hc0 hcq) (fArch_budget p q c)
  refine ⟨R, hcard, fun n hthr hht hnf => ?_⟩
  exact hR n (frameXMul δ p q n) (frameXMul_dvd δ p q n)
    (max_lt hht (threshold_of_pow_lt hp hc0 hc1 hthr))
    (frame_archimedean_mul hp hq hc0 hnf)

/-- **The counting form**: the failures of `δ(p/q)ⁿ` above the threshold span at most
`K(ε(p,c))` scaling families.  This is the sharp statement the quantitative literature supports —
a bound on the number of *lines*, not on the number of failures (for which see
`BB13/MahlerCount.lean`). -/
@[category research solved, AMS 11, ref "BE08" "Mah57" "Bug12", group "bugeaud_10_13"]
theorem mahler_lines_card_le (δ : ℚ) (p q : ℕ) (c : ℝ) (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hc0 : 0 < c) (hc1 : c < 1) :
    {r : ℚ | ∃ n : ℕ, c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight δ : ℝ) < (p : ℝ) ^ n ∧
        IsFailureMul δ p q c n ∧ linePointMul δ p q n = r}.ncard
      ≤ BugeaudEvertse.lineBound (epsilon p c) := by
  obtain ⟨R, hcard, hR⟩ := mahler_line_cover δ p q c hq hqp hcop hc0 hc1
  have hsub : {r : ℚ | ∃ n : ℕ, c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight δ : ℝ) < (p : ℝ) ^ n ∧
      IsFailureMul δ p q c n ∧ linePointMul δ p q n = r} ⊆ ↑R := by
    rintro r ⟨n, h1, h2, h3, rfl⟩; exact hR n h1 h2 h3
  calc _ ≤ (↑R : Set ℚ).ncard := Set.ncard_le_ncard hsub R.finite_toSet
    _ = R.card := Set.ncard_coe_finset R
    _ ≤ BugeaudEvertse.lineBound (epsilon p c) := hcard

/-! ### Consistency with the headline case `(δ, p, q, c) = (1, 3, 2, 3/4)`

The general theorem must reproduce `BB13/LineCover.lean`, and does: the objects agree at `δ = 1`,
the exponent `f_∞` becomes `θ`, `ε(3, 3/4)` becomes `ε*`, and the threshold `cⁿ < 1/16` becomes
`n ≥ 10`. -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem MnumMul_one (p q n : ℕ) : MnumMul 1 p q n = Mnum p q n := by
  rw [MnumMul, Mnum]; norm_num

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem isFailureMul_one (p q : ℕ) (c : ℝ) (n : ℕ) (hq : 0 < q) :
    IsFailureMul 1 p q c n ↔ IsFailure p q c n := by
  rw [IsFailureMul, isFailure_iff p q c n hq]; norm_num

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linePointMul_one_3_2 (n : ℕ) : linePointMul 1 3 2 n = linePoint n := by
  rw [linePointMul, linePoint, frameXMul, frameX, MnumMul_one, frameY]
  push_cast
  ring

/-- `f_∞ = θ` at `(p, q, c) = (3, 2, 3/4)`: the general frame degenerates to the symmetric
`(θ, θ, 1)` of `BB13/LineCover.lean`, because `1 + ε* − θ = θ` is the budget identity. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem fArch_three_two : fArch 3 2 (3 / 4) = theta := by
  have h := theta_add_theta_add_one
  rw [fArch, ← epsStar_eq_epsilon, theta]
  rw [theta] at h
  push_cast
  linarith

/-- `(3/4)ⁿ < 1/16` for `n ≥ 10` — the headline threshold, in the general form. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem three_quarters_pow_lt {n : ℕ} (hn : 10 ≤ n) : (3 / 4 : ℝ) ^ n < 1 / 16 := by
  have h1 : (3 / 4 : ℝ) ^ n ≤ (3 / 4 : ℝ) ^ 10 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  norm_num at h1 ⊢
  linarith

/-- **`BB13.failures_line_cover` is the `(1, 3, 2, 3/4)` instance of `mahler_line_cover`** — the
consistency check that keeps the general and the headline developments honest.  The original proof
in `BB13/LineCover.lean` stays: it carries the certified constant of `BB13/Constants.lean`. -/
@[category test, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_of_general :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound epsStar ∧
      ∀ n : ℕ, 10 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := mahler_line_cover 1 3 2 (3 / 4) (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num)
  rw [← epsStar_eq_epsilon] at hcard
  refine ⟨R, hcard, fun n hn hnf => ?_⟩
  rw [← linePointMul_one_3_2]
  refine hR n (three_quarters_pow_lt hn) ?_
    ((isFailureMul_one 3 2 (3 / 4) n (by norm_num)).mpr hnf)
  rw [BugeaudEvertse.ratHeight_one]
  have h1 : (3 : ℝ) ^ 10 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at h1 ⊢
  linarith

/-! ### Two instances beyond the headline

Worked cases of `mahler_line_cover`, to exercise the general statement.  The constants are
`K(ε(5, 3/4)) = 5 449 831 243 823` and `K(ε*) = 1 856 360 182 227` (module docstring table). -/

/-- `‖(5/3)ⁿ‖ < (3/4)ⁿ` for `n` with `(3/4)ⁿ < 1/16` (i.e. `n ≥ 10`): at most `K(ε(5, 3/4))`
lines. -/
@[category research solved, AMS 11, ref "BE08" "Mah57", group "bugeaud_10_13"]
theorem line_cover_five_three :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound (epsilon 5 (3 / 4)) ∧
      ∀ n : ℕ, 10 ≤ n → IsFailureMul 1 5 3 (3 / 4) n → linePointMul 1 5 3 n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := mahler_line_cover 1 5 3 (3 / 4) (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num)
  refine ⟨R, hcard, fun n hn hnf => hR n (three_quarters_pow_lt hn) ?_ hnf⟩
  rw [BugeaudEvertse.ratHeight_one]
  have h1 : (5 : ℝ) ^ 10 ≤ (5 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at h1 ⊢
  linarith

/-- **A multiplier instance** (report C.9): the `n` with `‖½·(3/2)ⁿ‖ < (3/4)ⁿ` — nearness of
`(3/2)ⁿ` to a *half-integer* — also lie on at most `K(ε*)` lines.  The multiplier is free in the
constant; it only raises the height threshold to `3ⁿ > 2·H(1/2) = 4`. -/
@[category research solved, AMS 11, ref "BE08" "Mah57", group "bugeaud_10_13"]
theorem line_cover_half_multiplier :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound epsStar ∧
      ∀ n : ℕ, 10 ≤ n → IsFailureMul (1 / 2) 3 2 (3 / 4) n → linePointMul (1 / 2) 3 2 n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := mahler_line_cover (1 / 2) 3 2 (3 / 4) (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num)
  rw [← epsStar_eq_epsilon] at hcard
  refine ⟨R, hcard, fun n hn hnf => hR n (three_quarters_pow_lt hn) ?_ hnf⟩
  have hH : BugeaudEvertse.ratHeight (1 / 2 : ℚ) = 2 := by
    simp [BugeaudEvertse.ratHeight]
    decide
  rw [hH]
  have h1 : (3 : ℝ) ^ 10 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at h1 ⊢
  linarith

end BB13
