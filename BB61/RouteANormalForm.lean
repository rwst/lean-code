/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.RouteACeiling
import BB61.RouteAConstants
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M2 Proposition 1: the normal form of the Route A criterion

`BB61/Criterion.lean` proves Problem 10.61 at every `α` with

`A(α) = log 2 / log α + log 2 / log (1/ρ) < 1`   (`QuadSetup.routeAExponent`),

`ρ := |β|`, and `BB61/RouteACeiling.lean` proves the ceiling `A(α) ≥ d·log2/log α` that
bounds where the criterion can fire at all.  Both files state the criterion in the mixed
`log`-quotient shape it is derived in.  This file puts it in **normal form**, which is
Proposition 1 of `note-1061-M2.html` — the one clause of §3 that the Lean development had
only in prose (the `Criterion.lean` module docstring asserts the first equivalence without
proving it).  Writing

`L := log₂ α`  (`QuadSetup.logAlpha`),   `R := log₂ (1/ρ)`  (`QuadSetup.logRhoInv`),

so that `A(α) = 1/L + 1/R`, the four statements

* `A(α) < 1`,
* `(L - 1)(R - 1) > 1`,
* `R > L/(L - 1)`,
* `ρ < 2^(-L/(L-1))`

are equivalent (`QuadSetup.routeAExponent_lt_one_iff_one_lt_normalForm`,
`…_iff_threshold_lt_logRhoInv`, `…_iff_abs_beta_lt_rpow`), and

`A(α) · log₂ α = 1 + L/R`   (`QuadSetup.routeAExponent_mul_logAlpha`).

The point of the normal form is that it is a **hyperbola in the `(L, R)`-plane with
asymptotes `L = 1` and `R = 1`**: a large base buys tolerance of a slow conjugate and vice
versa, but neither `L → ∞` nor `R → ∞` alone suffices, because the marginal costs are
governed by the product.  That is stated here as theorems, not as a picture:

* `one_lt_div_sub_one` — the threshold `L/(L-1)` is `> 1` for every `L > 1`;
* `div_sub_one_lt_div_sub_one` — it is strictly decreasing in `L`;
* `tendsto_div_sub_one_atTop` — and decreases to `1`, never below it.

So `R > 1` is necessary however large `α` is (`QuadSetup.one_lt_logRhoInv_of_lt_one`), and
by the symmetry of `(L-1)(R-1) > 1` the same holds with the roles exchanged.

## What it buys

Three consumer forms of M1 Corollary 5, each an immediate composition with
`BB61/Criterion.lean`: `QuadSetup.not_equidistributed_of_normalForm` and
`QuadSetup.not_equidistributed_of_abs_beta_lt_rpow` prove Problem 10.61 from the normal
form and from the threshold on `ρ` directly, and `QuadSetup.confCircle_ne_univ_of_normalForm`
gives the same as M1 Proposition 4.

And **M2 Corollary 6**, the complete quadratic answer, which is Proposition 1 with
`R = L - log₂|b|`: at degree two `αβ = -b`, hence `ρ = |b|/α` exactly
(`QuadSetup.abs_beta_eq_div`), so

`A(α) < 1  ↔  (log₂ α - 1)(log₂(α/|b|) - 1) > 1`
  (`QuadSetup.routeAExponent_lt_one_iff_quadratic`),

and for units `|b| = 1` this collapses to `α > 4`
(`QuadSetup.routeAExponent_lt_one_iff_four_lt`).  The forward half of the unit statement is
`BB61/RouteACeiling.lean`'s `four_lt_alpha_of_routeAExponent_lt_one`; the converse is new
here, so the two together say that on quadratic units **Route A covers exactly `(4, ∞)`** —
`α = 2 + √5` of `BB61/RouteA.lean` being the first Pisot number in that range, and the hard
slice `2 < α ≤ 4` (which is where all of M0's certificates live, `1 + √2` included) being
outside it by a theorem.

Everything here is elementary algebra on two positive reals plus the `Real.logb` API: the
note's own §13 records that "Proposition 1 uses nothing", and the Lean file honours that —
no covering, no dynamics, no citation.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M2.html` §3 Proposition 1 and §5 Corollary 6; numerics `BB61/m2_verify.py`
  checks P3 (both equivalences and the `ρ`-threshold against `A < 1` on all 9287 enumerated
  Pisot numbers) and C6 (the quadratic form on all 440 enumerated quadratics).
-/

noncomputable section

namespace BB61

open Filter Topology

/-! ## The normal form, as algebra on two positive reals

The whole of Proposition 1 lives here, with no reference to `α`: `L` and `R` are arbitrary.
-/

variable {L R : ℝ}

/-- **Proposition 1, first equivalence.**  `1/L + 1/R < 1 ↔ (L-1)(R-1) > 1`.  Both sides
are `L + R < LR` after clearing denominators; the left side factors.  No hypothesis beyond
positivity is needed — in particular `R ≤ 1` is allowed, and then both sides are false. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_add_inv_lt_one_iff (hL : 0 < L) (hR : 0 < R) :
    L⁻¹ + R⁻¹ < 1 ↔ 1 < (L - 1) * (R - 1) := by
  have hLR : (0 : ℝ) < L * R := mul_pos hL hR
  rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ hL.ne' hR.ne', div_lt_one hLR]
  constructor <;> intro h <;> nlinarith

/-- **Proposition 1, second equivalence.**  For `L > 1`, `(L-1)(R-1) > 1 ↔ R > L/(L-1)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_lt_mul_sub_one_iff (hL : 1 < L) :
    1 < (L - 1) * (R - 1) ↔ L / (L - 1) < R := by
  have h : (0 : ℝ) < L - 1 := by linarith
  rw [div_lt_iff₀ h]
  constructor <;> intro hh <;> nlinarith

/-- The threshold `L/(L-1)` never drops to `1`: the asymptote `R = 1` of the hyperbola. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_lt_div_sub_one (hL : 1 < L) : 1 < L / (L - 1) :=
  (one_lt_div (by linarith)).mpr (by linarith)

/-- The threshold is strictly decreasing in `L`: a larger base buys tolerance of a slower
conjugate. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem div_sub_one_lt_div_sub_one {L₁ L₂ : ℝ} (h1 : 1 < L₁) (h : L₁ < L₂) :
    L₂ / (L₂ - 1) < L₁ / (L₁ - 1) := by
  have h1' : (0 : ℝ) < L₁ - 1 := by linarith
  have h2' : (0 : ℝ) < L₂ - 1 := by linarith
  rw [div_lt_div_iff₀ h2' h1']
  nlinarith

/-- …and decreases to `1`.  Together with `one_lt_div_sub_one` this is the precise sense in
which `L → ∞` alone does not suffice: the requirement `R > 1` survives every base. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_div_sub_one_atTop :
    Tendsto (fun L : ℝ => L / (L - 1)) atTop (nhds 1) := by
  have hev : (fun L : ℝ => L / (L - 1)) =ᶠ[atTop] fun L : ℝ => 1 + (L - 1)⁻¹ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    have hne : L - 1 ≠ 0 := by intro hz; rw [sub_eq_zero] at hz; exact absurd hz.symm hL.ne
    field_simp
    ring
  have hsub : Tendsto (fun L : ℝ => L - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ) Filter.tendsto_id
  refine Tendsto.congr' hev.symm ?_
  simpa using tendsto_const_nhds.add hsub.inv_tendsto_atTop

/-- **Proposition 1, third equivalence.**  With `R = log₂(1/ρ)`, the threshold `R > t`
reads `ρ < 2^(-t)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_logb_two_inv_iff_lt_rpow {ρ t : ℝ} (hρ : 0 < ρ) :
    t < Real.logb 2 ρ⁻¹ ↔ ρ < (2 : ℝ) ^ (-t) := by
  rw [Real.logb_inv, lt_neg, Real.logb_lt_iff_lt_rpow one_lt_two hρ]

/-- **Proposition 1, the closing identity.**  `(1/L + 1/R)·L = 1 + L/R`.  Only `L ≠ 0` is
needed; at `R = 0` both sides read `1` under Lean's junk convention. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_add_inv_mul_eq (hL : L ≠ 0) : (L⁻¹ + R⁻¹) * L = 1 + L / R := by
  rw [add_mul, inv_mul_cancel₀ hL, inv_mul_eq_div]

/-! ## The two logarithms of a `QuadSetup` -/

namespace QuadSetup

variable (P : QuadSetup)

/-- `R = log₂ (1/ρ)` with `ρ = |β|`, the second coordinate: the reciprocal of the box
dimension bound for the window `K`. -/
def logRhoInv : ℝ := Real.logb 2 |P.β|⁻¹

/-- The Route A exponent is `1/L + 1/R`.  This is only `log 2 / log x = (log₂ x)⁻¹`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_eq_inv_add_inv :
    P.routeAExponent = P.logAlpha⁻¹ + P.logRhoInv⁻¹ := by
  simp only [routeAExponent, logAlpha, logRhoInv, Real.logb, inv_div]

/-- `α > 2` is exactly `L > 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_lt_logAlpha_iff : 1 < P.logAlpha ↔ 2 < P.α := by
  simp only [logAlpha]
  rw [Real.lt_logb_iff_rpow_lt one_lt_two P.alpha_pos, Real.rpow_one]

/-- `α > 2 ⇒ L > 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_lt_logAlpha (h2 : 2 < P.α) : 1 < P.logAlpha := P.one_lt_logAlpha_iff.mpr h2

/-- `L > 0` already at `α > 1`, which is a field of the structure. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem logAlpha_pos : 0 < P.logAlpha := Real.logb_pos one_lt_two P.one_lt

/-- `R > 0` whenever the setup is genuinely quadratic, i.e. `β ≠ 0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem logRhoInv_pos (hβ : P.β ≠ 0) : 0 < P.logRhoInv :=
  Real.logb_pos one_lt_two (one_lt_inv_iff₀.mpr ⟨abs_pos.mpr hβ, P.abs_beta_lt_one⟩)

/-! ## Proposition 1 -/

/-- **M2 Proposition 1, first equivalence: the normal form of the Route A criterion.**
`A(α) < 1 ↔ (L - 1)(R - 1) > 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_lt_one_iff_one_lt_normalForm (hβ : P.β ≠ 0) :
    P.routeAExponent < 1 ↔ 1 < (P.logAlpha - 1) * (P.logRhoInv - 1) := by
  rw [P.routeAExponent_eq_inv_add_inv]
  exact inv_add_inv_lt_one_iff P.logAlpha_pos (P.logRhoInv_pos hβ)

/-- **M2 Proposition 1, second equivalence.**  `A(α) < 1 ↔ R > L/(L-1)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_lt_one_iff_threshold_lt_logRhoInv (h2 : 2 < P.α) (hβ : P.β ≠ 0) :
    P.routeAExponent < 1 ↔ P.logAlpha / (P.logAlpha - 1) < P.logRhoInv := by
  rw [P.routeAExponent_lt_one_iff_one_lt_normalForm hβ]
  exact one_lt_mul_sub_one_iff (P.one_lt_logAlpha h2)

/-- **M2 Proposition 1, third equivalence.**  `A(α) < 1 ↔ ρ < 2^(-L/(L-1))`: at a fixed
base, Route A fires exactly below an explicit threshold on the conjugate. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_lt_one_iff_abs_beta_lt_rpow (h2 : 2 < P.α) (hβ : P.β ≠ 0) :
    P.routeAExponent < 1 ↔ |P.β| < (2 : ℝ) ^ (-(P.logAlpha / (P.logAlpha - 1))) := by
  rw [P.routeAExponent_lt_one_iff_threshold_lt_logRhoInv h2 hβ]
  simp only [logRhoInv]
  exact lt_logb_two_inv_iff_lt_rpow (abs_pos.mpr hβ)

/-- **M2 Proposition 1, the closing identity.**  `A(α)·log₂ α = 1 + L/R`.  This is the
quantity bounded below by the degree in `BB61/RouteACeiling.lean`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_mul_logAlpha :
    P.routeAExponent * P.logAlpha = 1 + P.logAlpha / P.logRhoInv := by
  rw [P.routeAExponent_eq_inv_add_inv]
  exact inv_add_inv_mul_eq P.logAlpha_pos.ne'

/-- The asymptote `R = 1`, read on the criterion: a slow conjugate cannot be compensated by
any base at all.  `R ≤ 1` kills Route A however large `α` is. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_lt_logRhoInv_of_lt_one (h2 : 2 < P.α) (hβ : P.β ≠ 0)
    (h : P.routeAExponent < 1) : 1 < P.logRhoInv :=
  lt_trans (one_lt_div_sub_one (P.one_lt_logAlpha h2))
    ((P.routeAExponent_lt_one_iff_threshold_lt_logRhoInv h2 hβ).mp h)

/-! ## Problem 10.61 from the normal form

The three consumer forms, each one composition with `BB61/Criterion.lean`.
-/

/-- **Problem 10.61 from the normal form.**  `(L-1)(R-1) > 1` proves 10.61 at `α`, in the
strong (non-dense) form. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_normalForm (hβ : P.β ≠ 0)
    (h : 1 < (P.logAlpha - 1) * (P.logRhoInv - 1)) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  P.not_equidistributed_of_routeAExponent_lt_one hβ
    ((P.routeAExponent_lt_one_iff_one_lt_normalForm hβ).mpr h)

/-- **Problem 10.61 from the threshold on `ρ`.**  `|β| < 2^(-L/(L-1))` proves 10.61 at
`α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_abs_beta_lt_rpow (h2 : 2 < P.α) (hβ : P.β ≠ 0)
    (h : |P.β| < (2 : ℝ) ^ (-(P.logAlpha / (P.logAlpha - 1)))) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  P.not_equidistributed_of_routeAExponent_lt_one hβ
    ((P.routeAExponent_lt_one_iff_abs_beta_lt_rpow h2 hβ).mpr h)

/-- **The normal form, read as M1 Proposition 4.**  `(L-1)(R-1) > 1` forces the confinement
set `X(α) = (C(α) - K) mod 1` to be a proper subset of the circle. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_ne_univ_of_normalForm (hβ : P.β ≠ 0)
    (h : 1 < (P.logAlpha - 1) * (P.logRhoInv - 1)) : P.confCircle ≠ Set.univ :=
  P.confCircle_ne_univ_of_routeAExponent_lt_one hβ
    ((P.routeAExponent_lt_one_iff_one_lt_normalForm hβ).mpr h)

/-! ## M2 Corollary 6: the complete quadratic answer

At degree two `αβ = -b`, so `ρ = |b|/α` exactly and `R = L - log₂|b|`.  Proposition 1 then
reads entirely in terms of `α` and the constant coefficient.
-/

/-- `β = 0` exactly when `b = 0`: the converse of `b_ne_zero_of_beta_ne_zero`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.β ≠ 0 := by
  intro h
  have := P.alpha_mul_beta
  rw [h, mul_zero] at this
  exact hb (by exact_mod_cast neg_eq_zero.mp this.symm)

/-- **`ρ = |b|/α` exactly**, the degree-two norm identity.  `BB61/RouteACeiling.lean`
derives the inequality `1 ≤ α|β|` from it; here the identity itself is what Corollary 6
consumes. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_beta_eq_div : |P.β| = |(P.b : ℝ)| / P.α := by
  have h : P.α * |P.β| = |(P.b : ℝ)| := by
    rw [← abs_of_pos P.alpha_pos, ← abs_mul, P.alpha_mul_beta, abs_neg]
  rw [eq_div_iff P.alpha_pos.ne']
  linear_combination h

/-- **`R = L - log₂|b|`.**  The second coordinate of the normal form is a function of the
base and the norm alone. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem logRhoInv_eq_sub (hb : P.b ≠ 0) :
    P.logRhoInv = P.logAlpha - Real.logb 2 |(P.b : ℝ)| := by
  have hb' : |(P.b : ℝ)| ≠ 0 := by
    simpa using (Int.cast_ne_zero (α := ℝ)).mpr hb
  simp only [logRhoInv, logAlpha]
  rw [P.abs_beta_eq_div, inv_div, Real.logb_div P.alpha_pos.ne' hb']

/-- **M2 Corollary 6, the complete quadratic answer.**
`A(α) < 1 ↔ (log₂ α - 1)(log₂(α/|b|) - 1) > 1`, with `|b| = |N(α)|` the norm. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_lt_one_iff_quadratic (hb : P.b ≠ 0) :
    P.routeAExponent < 1 ↔
      1 < (P.logAlpha - 1) * (P.logAlpha - Real.logb 2 |(P.b : ℝ)| - 1) := by
  rw [P.routeAExponent_lt_one_iff_one_lt_normalForm (P.beta_ne_zero_of_b_ne_zero hb),
    P.logRhoInv_eq_sub hb]

/-- **M2 Corollary 6 at units.**  For `|b| = 1` — the quadratic Pisot units — Route A fires
exactly on `α > 4`.  The forward implication is `four_lt_alpha_of_routeAExponent_lt_one` of
`BB61/RouteACeiling.lean`, proved there for every `b`; the converse is the content here, and
the two together pin the quadratic-unit landscape: `2 + √5` (`BB61/RouteA.lean`) is the
first Pisot number Route A reaches, and the hard slice `2 < α ≤ 4` — `1 + √2` included — is
outside its range by a theorem. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_lt_one_iff_four_lt (hb : |P.b| = 1) :
    P.routeAExponent < 1 ↔ 4 < P.α := by
  have hb0 : P.b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have habs : |(P.b : ℝ)| = 1 := by
    rw [← Int.cast_abs, hb]; norm_num
  have hlog : Real.logb 2 |(P.b : ℝ)| = 0 := by rw [habs, Real.logb_one]
  rw [P.routeAExponent_lt_one_iff_quadratic hb0, hlog, sub_zero]
  have hL : 0 < P.logAlpha := P.logAlpha_pos
  have hiff : 1 < (P.logAlpha - 1) * (P.logAlpha - 1) ↔ 2 < P.logAlpha := by
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    norm_num
  rw [hiff]
  simp only [logAlpha]
  rw [Real.lt_logb_iff_rpow_lt one_lt_two P.alpha_pos, h4]

end QuadSetup

end BB61

end
