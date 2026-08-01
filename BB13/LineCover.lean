/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.Subspace
import CITED.BugeaudEvertseRidout

/-!
# The line cover: failures `‖(3/2)ⁿ‖ < (3/4)ⁿ` span few lines (W2 of plan2-BB13)

The quantitative half of the Diophantine layer, stated as what the literature proves: the
failures of Problem 10.13 lie on an **explicitly bounded number of lines through the origin**.

## The reduction

A failure `n` is turned into a solution of the Bugeaud–Evertse system (5.11) at `ξ = 1`,
`S₁ = {2}`, `S₂ = {3}` by the frame point
`(x, y) = (mₙ·2ⁿ, 3ⁿ)`, `mₙ = round((3/2)ⁿ)`:

* `|1 − x/y| = |kₙ|/3ⁿ < (3/2)ⁿ/3ⁿ = 2⁻ⁿ = y^{−θ}`  (the failure itself);
* `|x|₂ ≤ 2⁻ⁿ = y^{−θ}`  (`2ⁿ ∣ x`);
* `|y|₃ = 3⁻ⁿ = y^{−1}`.

The exponent budget is `θ + θ + 1 = 2 + ε*` (`BB13.theta_add_theta_add_one`) — an identity, both
sides being `log 12/log 3.` So the frame meets (5.10) at `ε = ε*` with nothing to spare and
nothing to give away: **the sharp exponent is forced**, and the halved `ε*/2` of the first version
of this development was needless.  The height condition (5.12) reads `3ⁿ > max(2, 2^{4/ε*})` and
holds from `n = 10` on (`BB13.two_rpow_four_div_epsStar_lt`).

## What is proved, and what is not

* `failures_line_cover` — there is a set `R` of at most `lineBound ε*` slopes containing
  `linePoint n` for every failure `n ≥ 10`; equivalently `towersAbove_card_le`: the failures
  `n ≥ 10` lie in at most `lineBound ε*` **scaling families**.  At `ε*` the constant is
  `K(ε*) = 1 856 360 182 227 < 1.86 · 10¹²`.
* Nothing here bounds the number of failures.  Passing from lines to a count needs a bound on the
  number of failures per line — the open per-line problem (`BB13/LineTower.lean` collects what is
  elementary about it, `BB13/FailureCount.lean` the conditional counts).

Footprint: `std3 + BugeaudEvertse.ridout_line_cover`.  In particular the qualitative Subspace
axiom `Subspace.evertseSchlickewei` is **not** used — the cover is finite by construction.

## The general statement

Everything here is the `(δ, p, q, c) = (1, 3, 2, 3/4)` instance of `BB13/MahlerFrame.lean`'s
`mahler_line_cover`, which covers `‖δ(p/q)ⁿ‖ < cⁿ` for every coprime `p > q ≥ 2`, every
`0 < c < 1` and every rational multiplier `δ`, at `ε(p,c) = log(1/c)/log p`
(`BB13.failures_line_cover_of_general` is the machine-checked instantiation).  This file is kept
separate because it is the case that carries certified numerics (`BB13/Constants.lean`), a kernel
census (`BB13/Census.lean`) and the Waring application.

## References

* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — `CITED/BugeaudEvertseRidout.lean`.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* `plans/plan2-BB13.html` (W1, W2) — the repair this file implements.
-/

namespace BB13

open scoped Real

/-! ### The frame point of a failure -/

/-- The `x`-coordinate `x = mₙ·2ⁿ` of the frame point of `n`. -/
noncomputable def frameX (n : ℕ) : ℤ := Mnum 3 2 n * 2 ^ n

/-- The `y`-coordinate `y = 3ⁿ` of the frame point of `n` — the height in (5.11). -/
def frameY (n : ℕ) : ℤ := 3 ^ n

/-- The **slope** `x/y = mₙ·2ⁿ/3ⁿ` of the frame point: the one-dimensional subspace of `ℚ²` it
spans, coordinatized.  Two failures share a line exactly when their `linePoint`s agree.

(`BB13.failPoint` stores the same two integers in the opposite order, `(3ⁿ, mₙ·2ⁿ)`; the
dictionary is `BB13.linePoint_eq_iff_collinear`.) -/
noncomputable def linePoint (n : ℕ) : ℚ := (frameX n : ℚ) / (frameY n : ℚ)

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem frameY_pos (n : ℕ) : 0 < frameY n := by
  rw [frameY]; positivity

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem frameY_cast (n : ℕ) : ((frameY n : ℤ) : ℝ) = (3 : ℝ) ^ n := by
  rw [frameY]; push_cast; ring

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem frameX_cast (n : ℕ) : ((frameX n : ℤ) : ℝ) = (Mnum 3 2 n : ℝ) * (2 : ℝ) ^ n := by
  rw [frameX]; push_cast; ring

/-! ### The three conditions of the system (5.11) -/

/-- **The archimedean quantity of the frame, computed**: `|1 − x/y| = |kₙ|/3ⁿ = ‖(3/2)ⁿ‖·(2/3)ⁿ`.
Every smallness event for `‖(3/2)ⁿ‖` — the `(3/4)ⁿ` failures of Problem 10.13, the `(3/4)ⁿ⁻¹`
Waring events of `BB13/Waring.lean` — enters the subspace frame through this identity. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_arch_eq (n : ℕ) :
    |(1 : ℝ) - (frameX n : ℝ) / (frameY n : ℝ)|
      = |((resid 3 2 n : ℤ) : ℝ)| / (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hres : ((resid 3 2 n : ℤ) : ℝ) = (3 : ℝ) ^ n - (Mnum 3 2 n : ℝ) * (2 : ℝ) ^ n := by
    rw [resid]; push_cast; ring
  have hval : (1 : ℝ) - (frameX n : ℝ) / (frameY n : ℝ) = ((resid 3 2 n : ℤ) : ℝ) / (3 : ℝ) ^ n := by
    rw [frameX_cast, frameY_cast, hres]; field_simp
  rw [hval, abs_div, abs_of_pos h3]

/-- The residue bound carried by a failure: `|kₙ| < (3/2)ⁿ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem abs_resid_lt_of_isFailure {n : ℕ} (hnf : IsFailure 3 2 (3 / 4) n) :
    |((resid 3 2 n : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ n := by
  simp only [IsFailure] at hnf
  norm_num at hnf
  exact hnf

/-- **The archimedean condition.**  A failure at `n` gives `|1 − x/y| < 2⁻ⁿ = y^{−θ}`: the
approximation quality of the frame point is the failure inequality, divided by `3ⁿ`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_archimedean {n : ℕ} (hnf : IsFailure 3 2 (3 / 4) n) :
    |(1 : ℝ) - (frameX n : ℝ) / (frameY n : ℝ)| ≤ ((frameY n : ℤ) : ℝ) ^ (-theta) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  rw [frame_arch_eq, frameY_cast, rpow_neg_theta]
  have hstep : |((resid 3 2 n : ℤ) : ℝ)| / (3 : ℝ) ^ n < (3 / 2 : ℝ) ^ n / (3 : ℝ) ^ n := by
    gcongr
    exact abs_resid_lt_of_isFailure hnf
  have hpow : (3 / 2 : ℝ) ^ n / (3 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← div_pow]; norm_num
  linarith [hpow ▸ hstep]

/-- **The `2`-adic condition.**  `2ⁿ ∣ mₙ·2ⁿ`, so `|x|₂ ≤ 2⁻ⁿ = y^{−θ}`.  No failure hypothesis
is needed: the frame point is `2`-adically small by construction. -/
@[category research solved, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem frame_two_adic (n : ℕ) :
    ((padicNorm 2 ((frameX n : ℤ) : ℚ) : ℚ) : ℝ) ≤ ((frameY n : ℤ) : ℝ) ^ (-theta) := by
  have hdvd : ((2 ^ n : ℕ) : ℤ) ∣ frameX n := by
    rw [frameX]; push_cast; exact dvd_mul_left _ _
  have h := padicNorm.dvd_iff_norm_le.mp hdvd
  have hcast : (((2 : ℚ) ^ (-(n : ℤ)) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ n := by
    push_cast; rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [frameY_cast, rpow_neg_theta, ← hcast]
  exact_mod_cast h

/-- **The `3`-adic condition.**  `|y|₃ = 3⁻ⁿ = y^{−1}`: the whole exponent `1` is spent at `3`. -/
@[category research solved, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem frame_three_adic (n : ℕ) :
    ((padicNorm 3 ((frameY n : ℤ) : ℚ) : ℚ) : ℝ) ≤ ((frameY n : ℤ) : ℝ) ^ (-(1 : ℝ)) := by
  have hdvd : ((3 ^ n : ℕ) : ℤ) ∣ frameY n := by rw [frameY]; push_cast; exact dvd_rfl
  have h := padicNorm.dvd_iff_norm_le.mp hdvd
  have hcast : (((3 : ℚ) ^ (-(n : ℤ)) : ℚ) : ℝ) = ((3 : ℝ) ^ n)⁻¹ := by
    push_cast; rw [zpow_neg, zpow_natCast]
  rw [frameY_cast, Real.rpow_neg (by positivity), Real.rpow_one, ← hcast]
  exact_mod_cast h

/-- **The height condition** (5.12) at `ξ = 1`: `max(2H(1), 2^{4/ε*}) < 3ⁿ` for `n ≥ 10`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem frame_height {n : ℕ} (hn : 10 ≤ n) :
    max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / epsStar))
      < ((frameY n : ℤ) : ℝ) := by
  rw [frameY_cast, BugeaudEvertse.ratHeight_one]
  refine max_lt ?_ (two_rpow_four_div_epsStar_lt hn)
  have h1 : (3 : ℝ) ^ 10 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at h1 ⊢
  linarith

/-! ### The line cover -/

/-- **The line theorem** (the honest replacement of the retired effective count): the failures
`‖(3/2)ⁿ‖ < (3/4)ⁿ` with `n ≥ 10` lie on at most `lineBound ε*` lines through the origin, i.e.
their frame points span at most

`K(ε*) = ⌈2³²(1 + 1/ε*)³ log 6 · log((1 + 1/ε*) log 6)⌉ = 1 856 360 182 227`

one-dimensional subspaces of `ℚ²`.  Direct instance of [BE08] Cor. 5.2 through the frame
`(f_∞, f₂, f₃) = (θ, θ, 1)`, whose budget `2 + ε*` is exact.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound epsStar ∧
      ∀ n : ℕ, 10 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover_23 1 epsStar theta theta 1
    epsStar_pos theta_pos.le theta_pos.le zero_le_one theta_add_theta_add_one
  refine ⟨R, hcard, fun n hn hnf => ?_⟩
  refine hR (frameX n) (frameY n) (frameY_pos n) (frame_height hn) ?_
    (frame_two_adic n) (frame_three_adic n)
  simpa using frame_archimedean hnf

/-- **The failures `n ≥ 10` span at most `K(ε*)` scaling families** — `failures_line_cover` in
counting form.  This is the sharp statement the quantitative literature supports: a bound on the
number of *lines*, not on the number of failures. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem towersAbove_card_le :
    {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard
      ≤ BugeaudEvertse.lineBound epsStar := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover
  have hsub : {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r} ⊆ ↑R := by
    rintro r ⟨n, hn, hnf, rfl⟩; exact hR n hn hnf
  calc {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard
      ≤ (↑R : Set ℚ).ncard := Set.ncard_le_ncard hsub R.finite_toSet
    _ = R.card := Set.ncard_coe_finset R
    _ ≤ BugeaudEvertse.lineBound epsStar := hcard

end BB13
