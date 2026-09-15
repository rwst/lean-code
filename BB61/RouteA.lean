/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Covering
import BB61.Confinement
import BB61.Criterion
import BB61.BoxDim
import Mathlib.Analysis.Real.Sqrt
import ForMathlib.Analysis.Equidistribution.ModOne
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Route A fires at `α = 2 + √5`: Problem 10.61 holds there, in the strong form

The capstone of the `BB61/` root (M2 Corollary 3(a) of `note-1061-M2.html`):
`α = 2 + √5`, the root of `X² - 4X - 1`, is the **smallest Pisot number of degree ≥ 2
at which Route A fires** — over all degrees, since a firing of degree `d` needs
`α > 2^d` and the complete quadratic enumeration below `2+√5` contains none.

The theorems:

* `routeA_two_add_sqrt5` — **one explicit open interval `J ⊆ (0,1)`, uniform in
  `ξ ∈ C(α)` and `n`, with `{ξ αⁿ} ∉ J` for every `ξ` and every `n`**;
* `two_add_sqrt5_not_denseModuloOne` — no `(ξ αⁿ)` with `ξ ∈ C(α)` is dense mod one;
* `two_add_sqrt5_not_equidistributed` — none is uniformly distributed mod one:
  **Problem 10.61 holds at `2 + √5`**;
* `goldenFive_confCircle_ne_univ` — the same certificate read as M1 Proposition 4: the
  confinement set `X(2+√5) = (C(α) - K) mod 1` of `BB61/Confinement.lean` is not the whole
  circle.  By `confCircle_ne_univ_of_avoided` and
  `not_denseModuloOne_of_confCircle_ne_univ` the two statements are equivalent, so Route A
  is exactly a proof that `X(α) ≠ 𝕋`.

The numeric certificate is discharged at covering depth `(M, M') = (70, 70)` with
integer-part bound `K = 3` by `norm_num` — exact rational arithmetic in the kernel,
the Lean shadow of `BB61/m2_verify.py` check T1a (which certifies depth `(17,17)`
against the sharper mod-1 tiling count; the engine here pays a factor `2K+1 = 7`
for the simpler integer-shift bookkeeping and compensates with deeper truncation).

Everything is elementary: the only inputs are `√5` bounds to seven decimals and the
engine of `BB61/Covering.lean`.  No axiom beyond the standard three, no citation.
-/

namespace BB61

open QuadSetup

/-! ## `√5` bounds -/

theorem sqrt5_lt : Real.sqrt 5 < 2.2360680 :=
  (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)

theorem lt_sqrt5 : (2.2360679 : ℝ) < Real.sqrt 5 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

theorem two_lt_sqrt5 : (2 : ℝ) < Real.sqrt 5 := lt_trans (by norm_num) lt_sqrt5

/-! ## The setup at `α = 2 + √5` -/

/-- `α = 2 + √5`, the root of `X² - 4X - 1`: trace 4, norm `-1`, conjugate `2 - √5`. -/
noncomputable def goldenFive : QuadSetup where
  a := 4
  b := 1
  α := 2 + Real.sqrt 5
  root := by
    have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    push_cast
    nlinarith [h]
  one_lt := by
    have := Real.sqrt_nonneg 5
    linarith
  conj_lt := by
    have h1 := two_lt_sqrt5
    have h2 : Real.sqrt 5 < 3 := lt_trans sqrt5_lt (by norm_num)
    rw [abs_lt]
    push_cast
    constructor <;> linarith

theorem goldenFive_alpha : goldenFive.α = 2 + Real.sqrt 5 := rfl

theorem goldenFive_beta : goldenFive.β = 2 - Real.sqrt 5 := by
  show ((4 : ℤ) : ℝ) - (2 + Real.sqrt 5) = 2 - Real.sqrt 5
  push_cast
  ring

theorem abs_goldenFive_beta : |goldenFive.β| = Real.sqrt 5 - 2 := by
  rw [goldenFive_beta, abs_of_nonpos (by linarith [two_lt_sqrt5])]
  ring

/-! ## The numeric certificate at depth `(70, 70)`, `K = 3` -/

theorem goldenFive_absBeta_le : |goldenFive.β| ≤ 0.236068 := by
  rw [abs_goldenFive_beta]
  have := sqrt5_lt
  linarith

theorem goldenFive_K : (1 + |goldenFive.β|) / (1 - |goldenFive.β|) + 1 ≤ ((3 : ℕ) : ℝ) := by
  have hρ := goldenFive_absBeta_le
  have hρ0 : (0 : ℝ) ≤ |goldenFive.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |goldenFive.β| := by linarith
  have h2 : (1 + |goldenFive.β|) / (1 - |goldenFive.β|) ≤ 2 := by
    rw [div_le_iff₀ hden]
    linarith
  push_cast
  linarith

theorem goldenFive_inv_le : goldenFive.α⁻¹ ≤ 0.236068 := by
  have hpos := goldenFive.alpha_pos
  rw [inv_eq_one_div, div_le_iff₀ hpos, goldenFive_alpha]
  have := lt_sqrt5
  linarith

theorem goldenFive_delta_le :
    goldenFive.delta 70 70 ≤ (0.236068 : ℝ) ^ 70 * 2.62 := by
  have hρ := goldenFive_absBeta_le
  have hρ0 : (0 : ℝ) ≤ |goldenFive.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |goldenFive.β| := by linarith
  have hq0 : (0 : ℝ) ≤ (0.236068 : ℝ) ^ 70 := by positivity
  have h1 : (goldenFive.α⁻¹) ^ 70 ≤ (0.236068 : ℝ) ^ 70 :=
    pow_le_pow_left₀ (inv_nonneg.mpr goldenFive.alpha_pos.le) goldenFive_inv_le 70
  have h2 : |goldenFive.β| ^ 70 ≤ (0.236068 : ℝ) ^ 70 :=
    pow_le_pow_left₀ hρ0 goldenFive_absBeta_le 70
  have h4 : (1 - |goldenFive.β|)⁻¹ ≤ 1.31 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hterm2 : (1 + |goldenFive.β|) * |goldenFive.β| ^ 70 / (1 - |goldenFive.β|)
      ≤ 1.236068 * (0.236068 : ℝ) ^ 70 * 1.31 := by
    rw [div_eq_mul_inv]
    have hb70 : (0 : ℝ) ≤ |goldenFive.β| ^ 70 := pow_nonneg (abs_nonneg _) 70
    have hinv0 : (0 : ℝ) ≤ (1 - |goldenFive.β|)⁻¹ := inv_nonneg.mpr hden.le
    calc (1 + |goldenFive.β|) * |goldenFive.β| ^ 70 * (1 - |goldenFive.β|)⁻¹
        ≤ 1.236068 * (0.236068 : ℝ) ^ 70 * (1 - |goldenFive.β|)⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ hinv0
          exact mul_le_mul (by linarith) h2 hb70 (by norm_num)
    _ ≤ 1.236068 * (0.236068 : ℝ) ^ 70 * 1.31 := by
          refine mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [QuadSetup.delta]
  calc (goldenFive.α⁻¹) ^ 70
        + (1 + |goldenFive.β|) * |goldenFive.β| ^ 70 / (1 - |goldenFive.β|)
      ≤ (0.236068 : ℝ) ^ 70 + 1.236068 * (0.236068 : ℝ) ^ 70 * 1.31 :=
        add_le_add h1 hterm2
  _ ≤ (0.236068 : ℝ) ^ 70 * 2.62 := by nlinarith [hq0]

/-- The certificate: `(2^70 · 2^70 · 7) · 2δ < 1`, by exact rational arithmetic. -/
theorem goldenFive_cert :
    ((2 ^ 70 * 2 ^ 70 * (2 * 3 + 1) : ℕ) : ℝ) * (2 * goldenFive.delta 70 70) < 1 := by
  have hδ := goldenFive_delta_le
  have hδ0 := goldenFive.delta_nonneg 70 70
  calc ((2 ^ 70 * 2 ^ 70 * (2 * 3 + 1) : ℕ) : ℝ) * (2 * goldenFive.delta 70 70)
      ≤ ((2 ^ 70 * 2 ^ 70 * (2 * 3 + 1) : ℕ) : ℝ) * (2 * ((0.236068 : ℝ) ^ 70 * 2.62)) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  _ < 1 := by norm_num

/-! ## The capstone -/

/-- **Route A fires at `α = 2 + √5` (M2 Corollary 3(a)): Problem 10.61 holds there, in
the strong form.**  There is one explicit open interval `J ⊆ (0,1)`, uniform in
`ξ ∈ C(α)` and in `n`, such that `{ξ αⁿ}` misses `J` for *every* `ξ ∈ C(α)` and
*every* `n ≥ 0`.  `2 + √5` is the smallest Pisot number of degree ≥ 2 with this
provenance: a Route A firing of degree `d` needs `α > 2^d` (M1 Cor. 5), and the
complete quadratic enumeration below `4.236` contains no firing
(`BB61/m2_verify.py`, check P4). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeA_two_add_sqrt5 :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ ξ ∈ cantorSet (2 + Real.sqrt 5), ∀ n : ℕ,
        Int.fract (ξ * (2 + Real.sqrt 5) ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  obtain ⟨x, r, hr, hsub, havoid⟩ :=
    goldenFive.exists_avoided_interval 70 70 3 goldenFive_K goldenFive_cert
  refine ⟨x, r, hr, hsub, ?_⟩
  rintro ξ ⟨ε, rfl⟩ n
  exact havoid ε n

/-- No `(ξ αⁿ)` with `ξ ∈ C(2+√5)` is dense modulo one. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_add_sqrt5_not_denseModuloOne
    (ξ : ℝ) (hξ : ξ ∈ cantorSet (2 + Real.sqrt 5)) :
    ¬ IsDenseModuloOne (fun n : ℕ => ξ * (2 + Real.sqrt 5) ^ n) := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := routeA_two_add_sqrt5
  exact not_denseModuloOne_of_avoided hr hsub (havoid ξ hξ)

/-- **Problem 10.61 at `α = 2 + √5`**: no `(ξ αⁿ)` with `ξ ∈ C(α)` is uniformly
distributed modulo one — a fortiori, since not even dense. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_add_sqrt5_not_equidistributed
    (ξ : ℝ) (hξ : ξ ∈ cantorSet (2 + Real.sqrt 5)) :
    ¬ IsEquidistributedModuloOne (fun n : ℕ => ξ * (2 + Real.sqrt 5) ^ n) := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := routeA_two_add_sqrt5
  exact not_equidistributed_of_avoided hr hsub (havoid ξ hξ)

/-- **The certificate at `2 + √5`, read as M1 Proposition 4.**  The confinement set
`X(α) = (C(α) - K) mod 1` of `BB61/Confinement.lean` is not the whole circle.  This is the
form in which the note states Route A, and by `not_denseModuloOne_of_confCircle_ne_univ` it
implies the two theorems above; by `confCircle_ne_univ_of_avoided` it is implied by them, so
nothing is lost either way. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_confCircle_ne_univ : goldenFive.confCircle ≠ Set.univ := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := routeA_two_add_sqrt5
  exact goldenFive.confCircle_ne_univ_of_avoided hr hsub fun ε n => havoid _ ⟨ε, rfl⟩ n

/-! ## The same conclusion from the criterion, at `(p, q) = (1, 1)`

`BB61/Criterion.lean` replaces the numeric certificate by the two geometric ratios of M1
Corollary 5.  At `2 + √5` they are `4/α` and `4|β|`, and both are below one at the smallest
possible parameters `p = q = 1`, because `α > 4` and `|β| < 1/4` — a pair of two-line
`√5` estimates in place of the depth-`(70,70)` rational arithmetic above.  The engine then
finds its own depth along the diagonal ray `(M, M') = (n, n)`. -/

/-- The first ratio at `2 + √5`: `2^{1+1} α^{-1} < 1`, i.e. `α > 4`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_ratio_alpha : (2 : ℝ) ^ (1 + 1) * (goldenFive.α⁻¹) ^ 1 < 1 := by
  have h4 : (2 : ℝ) ^ (1 + 1) = 4 := by norm_num
  rw [pow_one, ← div_eq_mul_inv, div_lt_one goldenFive.alpha_pos, goldenFive_alpha, h4]
  linarith [two_lt_sqrt5]

/-- The second ratio at `2 + √5`: `2^{1+1} |β| < 1`, i.e. `|β| < 1/4`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_ratio_beta : (2 : ℝ) ^ (1 + 1) * |goldenFive.β| ^ 1 < 1 := by
  have h4 : (2 : ℝ) ^ (1 + 1) = 4 := by norm_num
  rw [pow_one, abs_goldenFive_beta, h4]
  linarith [sqrt5_lt]

/-- **Route A at `2 + √5`, from the criterion.**  Same statement as `routeA_two_add_sqrt5`,
proved from `exists_avoided_interval_of_geom` at `(p, q) = (1, 1)` instead of from the
depth-`(70,70)` certificate. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeA_two_add_sqrt5_of_geom :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ ξ ∈ cantorSet (2 + Real.sqrt 5), ∀ n : ℕ,
        Int.fract (ξ * (2 + Real.sqrt 5) ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  obtain ⟨x, r, hr, hsub, havoid⟩ :=
    goldenFive.exists_avoided_interval_of_geom goldenFive_ratio_alpha goldenFive_ratio_beta
  refine ⟨x, r, hr, hsub, ?_⟩
  rintro ξ ⟨ε, rfl⟩ n
  exact havoid ε n

/-! ## M1 Corollary 5 at `2 + √5`: the box dimensions

`BB61/BoxDim.lean` states the dimensions of M1 Lemma 1(iii), Lemma 3 and Corollary 5.  At
`2 + √5` they are as sharp as the criterion: the norm is `-1`, so `ρ = 1/α` and the two
summands of `A(α)` coincide, `A(α) = log 4 / log α`, which is below one for exactly the
same reason as the first geometric ratio above — `α > 4`. -/

/-- At `2 + √5` the norm is `-1`, so `ρ = 1/α`: the window contracts at the same rate as the
Cantor set. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_inv_absBeta : |goldenFive.β|⁻¹ = goldenFive.α := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 5 - 2 ≠ 0 := by linarith [two_lt_sqrt5]
  rw [abs_goldenFive_beta, goldenFive_alpha, inv_eq_iff_eq_inv, eq_comm, inv_eq_iff_eq_inv]
  field_simp
  nlinarith [h]

/-- `A(2+√5) = 2 log 2 / log α`, the two summands being equal. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_routeAExponent :
    goldenFive.routeAExponent = 2 * Real.log 2 / Real.log goldenFive.α := by
  rw [QuadSetup.routeAExponent, goldenFive_inv_absBeta]
  ring

/-- **M1 Corollary 5 fires at `2 + √5`**: `A(α) = log 4 / log α < 1` because `α > 4`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_routeAExponent_lt_one : goldenFive.routeAExponent < 1 := by
  have h4 : (4 : ℝ) < goldenFive.α := by rw [goldenFive_alpha]; linarith [two_lt_sqrt5]
  have hlog : 0 < Real.log goldenFive.α := Real.log_pos (by linarith)
  have hlt : Real.log 4 < Real.log goldenFive.α := Real.log_lt_log (by norm_num) h4
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [goldenFive_routeAExponent, div_lt_one hlog]
  linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_beta_ne_zero : goldenFive.β ≠ 0 := by
  intro h
  have := abs_goldenFive_beta
  rw [h, abs_zero] at this
  linarith [two_lt_sqrt5]

/-- **M1 Lemma 1(iii) at `2 + √5`**: the box dimension of `C(2+√5)` exists and is
`log 2 / log(2+√5) ≈ 0.48`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_upperBoxDim_cantorSet :
    Metric.upperBoxDim (cantorSet goldenFive.α)
      = ((Real.log 2 / Real.log goldenFive.α : ℝ) : EReal) :=
  upperBoxDim_cantorSet (by rw [goldenFive_alpha]; linarith [two_lt_sqrt5])

/-- **M1 Corollary 5 at `2 + √5`**: `dim_B X(α) ≤ A(α) = 2 log 2 / log α < 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_upperBoxDim_confSet_lt_one :
    Metric.upperBoxDim goldenFive.confSet < 1 := by
  refine lt_of_le_of_lt (goldenFive.upperBoxDim_confSet_le ?_ goldenFive_beta_ne_zero) ?_
  · rw [goldenFive_alpha]; linarith [two_lt_sqrt5]
  · exact_mod_cast goldenFive_routeAExponent_lt_one

/-- **M1 Corollary 5 at `2 + √5`**, the measure form: `Leb(X(2+√5)) = 0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenFive_volume_confSet : MeasureTheory.volume goldenFive.confSet = 0 :=
  Real.volume_eq_zero_of_upperBoxDim_lt_one goldenFive_upperBoxDim_confSet_lt_one

/-- **Route A at `2 + √5` by the note's own route**: the box dimension of `X(α)` is below
one, so `X(α)` is null, so it is not the whole circle — and Problem 10.61 holds at `2 + √5`.
This is a third proof of `goldenFive_confCircle_ne_univ`, after the depth-`(70,70)`
certificate and the `(p,q) = (1,1)` criterion. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_add_sqrt5_not_equidistributed_of_boxDim :
    ∀ ξ ∈ cantorSet (2 + Real.sqrt 5), ¬ IsEquidistributedModuloOne
      fun n : ℕ => ξ * (2 + Real.sqrt 5) ^ n :=
  goldenFive.not_equidistributed_of_confCircle_ne_univ
    (goldenFive.confCircle_ne_univ_of_volume_confSet_eq_zero goldenFive_volume_confSet)

end BB61
