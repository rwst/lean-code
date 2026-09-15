/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.RouteANormalForm
import CITED.LedrappierYoung
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M3 Corollary 13: entropy alone cannot beat Route A

`note-1061-M3.html` Corollary 13 states that the Ledrappier–Young entropy floor decides no `α`
that Route A does not already decide: invariance, `h ≤ log 2` and hyperbolicity together yield
exactly `A(α) < 1` and nothing more, so the **entropy budget** `log 2 - h_min(α)` is positive
precisely when Route A fails.

The reason is an identity between two constants that, until this file, never met anywhere in
the repository.  With `ρ = |β|`,

* `A(α) = log 2 / log α + log 2 / log (1/ρ)`  — `BB61/Criterion.lean`'s `routeAExponent`, the
  sum of the two box dimensions of M1 Corollary 5;
* `h_min(α) = (1 / log α + 1 / log (1/ρ))⁻¹`  — `CITED/LedrappierYoung.lean`'s `LY.hMin`, the
  floor of M3 Theorem 11.

They are the same number twice: `A(α)` is `log 2` times the sum whose inverse is `h_min(α)`.
Hence

`A(α) · h_min(α) = log 2`  (`routeAExponent_mul_hMin`),

and Corollary 13 falls out as

`A(α) < 1  ↔  log 2 < h_min(α)`  (`routeAExponent_lt_one_iff_log_two_lt_hMin`),

equivalently `0 < log 2 - h_min(α) ↔ 1 < A(α)` (`zero_lt_entropyBudget_iff`).

## Why it is worth stating

The floor is the root's only cited axiom, and the whole M3/M4 pressure lane exists to exploit
it.  Corollary 13 is the exact statement of what that lane may **not** hope for: the floor by
itself, without a Fourier or partition potential to spend it against, is Route A's criterion
written in entropy units.  M3 checked this numerically to 200 digits over the 42 candidates of
`m0_gapsweep.json`; here it is an identity, valid at every `QuadSetup` with `β ≠ 0`.

Two consequences are recorded.  At a quadratic unit the floor is `½ log α`
(`LY.hMin_eq_of_unit`), so the threshold is `α > 4` (`log_two_lt_hMin_iff_four_lt_of_unit`) —
M2 Proposition 1's `routeAExponent_lt_one_iff_four_lt` read on the other lane.  Running that
backwards gives `routeAExponent_lt_one_iff_four_lt_of_floor`, a third proof of the unit
threshold that goes through the entropy floor instead of through `logb` normal forms.

Nothing here consumes `LY.entropyRate_floor`: only the *definition* `LY.hMin` is used, so every
statement in this file is axiom-free.

## References

* `note-1061-M3.html` Corollary 13 and Lemma 2 (the numerical form, `log 2 < h_min ↔ A < 1` on
  all 42 candidates); `note-1061-M3.html` §2.3, which Corollary 13 makes quantitative.
* `note-1061-M1.html` Corollary 5 (the exponent), `note-1061-M2.html` §3 (the normal form).
-/

namespace BB61

namespace QuadSetup

variable (P : QuadSetup)

/-! ## The two logarithms, in natural-log form

`BB61/RouteANormalForm.lean` works in `logb 2`; `LY.hMin` works in `Real.log`.  These are the
two positivity facts the identity needs. -/

/-- `log α > 0`, from the structure field `1 < α`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem log_alpha_pos : 0 < Real.log P.α := Real.log_pos P.one_lt

/-- `log (1/ρ) > 0` whenever the setup is genuinely quadratic.  The natural-log twin of
`QuadSetup.logRhoInv_pos`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem log_abs_beta_inv_pos (hβ : P.β ≠ 0) : 0 < Real.log |P.β|⁻¹ :=
  Real.log_pos (one_lt_inv_iff₀.mpr ⟨abs_pos.mpr hβ, P.abs_beta_lt_one⟩)

/-! ## The identity `A(α) · h_min(α) = log 2` -/

/-- The Route A exponent is `log 2` times the sum of the two reciprocal logarithms. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_eq_log_two_mul :
    P.routeAExponent = Real.log 2 * ((Real.log P.α)⁻¹ + (Real.log |P.β|⁻¹)⁻¹) := by
  rw [routeAExponent]; ring

/-- The entropy floor is the inverse of that same sum.  Only `one_div`: `LY.hMin` is written
with `1 / x`, `routeAExponent` with `x⁻¹`. -/
@[category API, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem hMin_eq_inv_add_inv :
    LY.hMin P = ((Real.log P.α)⁻¹ + (Real.log |P.β|⁻¹)⁻¹)⁻¹ := by
  simp only [LY.hMin, one_div]

/-- The floor is positive at every genuinely quadratic setup. -/
@[category API, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem hMin_pos (hβ : P.β ≠ 0) : 0 < LY.hMin P := by
  rw [P.hMin_eq_inv_add_inv]
  exact inv_pos.mpr
    (add_pos (inv_pos.mpr P.log_alpha_pos) (inv_pos.mpr (P.log_abs_beta_inv_pos hβ)))

/-- **The identity behind M3 Corollary 13.**  `A(α) · h_min(α) = log 2`: the Route A exponent
and the Ledrappier–Young floor are reciprocal, up to the factor `log 2`. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_mul_hMin (hβ : P.β ≠ 0) :
    P.routeAExponent * LY.hMin P = Real.log 2 := by
  have hS : (Real.log P.α)⁻¹ + (Real.log |P.β|⁻¹)⁻¹ ≠ 0 :=
    (add_pos (inv_pos.mpr P.log_alpha_pos) (inv_pos.mpr (P.log_abs_beta_inv_pos hβ))).ne'
  rw [P.routeAExponent_eq_log_two_mul, P.hMin_eq_inv_add_inv, mul_assoc,
    mul_inv_cancel₀ hS, mul_one]

/-- The identity in division form. -/
@[category API, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_eq_log_two_div_hMin (hβ : P.β ≠ 0) :
    P.routeAExponent = Real.log 2 / LY.hMin P := by
  rw [eq_div_iff (P.hMin_pos hβ).ne', P.routeAExponent_mul_hMin hβ]

/-! ## Corollary 13 -/

/-- **M3 Corollary 13.**  `A(α) < 1 ↔ log 2 < h_min(α)`.  Route A fires exactly when the
entropy floor of a hypothetical counterexample would exceed the entropy `log 2` available on
the full `2`-shift — so the floor, used alone, decides precisely the `α` that Route A decides,
and the M3/M4 pressure lane can only gain by spending a potential against it. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_lt_one_iff_log_two_lt_hMin (hβ : P.β ≠ 0) :
    P.routeAExponent < 1 ↔ Real.log 2 < LY.hMin P := by
  rw [P.routeAExponent_eq_log_two_div_hMin hβ, div_lt_one (P.hMin_pos hβ)]

/-- **M3 Corollary 13, the budget phrasing.**  The entropy budget `log 2 - h_min(α)` that a
potential must consume is strictly positive exactly when Route A fails. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem zero_lt_entropyBudget_iff (hβ : P.β ≠ 0) :
    0 < Real.log 2 - LY.hMin P ↔ 1 < P.routeAExponent := by
  rw [sub_pos, P.routeAExponent_eq_log_two_div_hMin hβ, lt_div_iff₀ (P.hMin_pos hβ), one_mul]

/-! ## The unit threshold, on both lanes -/

/-- **Corollary 13 at a quadratic unit.**  `log 2 < h_min(α) ↔ α > 4`: M2 Proposition 1's
threshold `routeAExponent_lt_one_iff_four_lt`, transported to the floor. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem log_two_lt_hMin_iff_four_lt_of_unit (hunit : P.b = 1 ∨ P.b = -1) :
    Real.log 2 < LY.hMin P ↔ 4 < P.α := by
  have hb : |P.b| = 1 := by rcases hunit with h | h <;> simp [h]
  have hb0 : P.b ≠ 0 := by rcases hunit with h | h <;> omega
  rw [← P.routeAExponent_lt_one_iff_log_two_lt_hMin (P.beta_ne_zero_of_b_ne_zero hb0),
    P.routeAExponent_lt_one_iff_four_lt hb]

/-- **The unit threshold, reproved through the entropy floor.**  `A(α) < 1 ↔ α > 4` for a
quadratic unit, obtained from `LY.hMin_eq_of_unit` (`h_min = ½ log α`) and Corollary 13 rather
than from the `logb` normal form.  A third proof of `routeAExponent_lt_one_iff_four_lt`, and
the cross-check that the two lanes agree. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_lt_one_iff_four_lt_of_floor (hunit : P.b = 1 ∨ P.b = -1) :
    P.routeAExponent < 1 ↔ 4 < P.α := by
  have hb0 : P.b ≠ 0 := by rcases hunit with h | h <;> omega
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [P.routeAExponent_lt_one_iff_log_two_lt_hMin (P.beta_ne_zero_of_b_ne_zero hb0),
    LY.hMin_eq_of_unit P P.one_lt hunit]
  constructor
  · intro h
    have hlog : Real.log 4 < Real.log P.α := by rw [h4]; linarith
    exact (Real.log_lt_log_iff (by norm_num) P.alpha_pos).mp hlog
  · intro h
    have hlog : Real.log 4 < Real.log P.α :=
      (Real.log_lt_log_iff (by norm_num) P.alpha_pos).mpr h
    rw [h4] at hlog; linarith

end QuadSetup

end BB61
