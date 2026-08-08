/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.AnchoredRational
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The homogeneous one-power wall, via Schmidt's Theorem 1D′ (report B1E2a-v2, WP-G)

`RB/AnchoredRational.lean` proves the **inhomogeneous** one-power wall
`RB.InhomOnePower (δ(3/2)^b)` — finiteness of `{d | ‖δ_b((3/2)^d − 1)‖ ≤ θ^d}` — from the cited
axiom `Subspace.schmidt1D'`.  This file proves its **homogeneous** sibling:

  **`RB.onePower_finite_of_irrational` : for an algebraic irrational `δ` and every scale
  `θ ∈ (0,1)`, only finitely many `a` bring `δ(3/2)^a` within `θ^a` of an integer.**

That statement is the one every CZ *slice* theorem of `RB/AlgebraicKernel.lean` actually needs:
a fixed-gap slice at gap `s₀` is `‖δ((3/2)^{a+s₀} − (3/2)^a)‖ = ‖δ'(3/2)^a‖` with the algebraic
irrational multiplier `δ' = δ((3/2)^{s₀} − 1)`.  Until now those slices were bought from the
cited axiom `CZ.pseudoPisot_approx_alg` ([CZ04]'s Main Theorem for algebraic multipliers,
transcribed with its pseudo-Pisot exclusion clause, `CITED/CorvajaZannierAlgebraic.lean`).
With the wall proved here they are a two-line consequence of `Subspace.schmidt1D'`, and that
axiom lane loses its last consumer (2026-08-07).

## Why the homogeneous case is the easy one

Everything the anchored run computes about the *rational* data is reused verbatim: the same
primitive triple `X = (m·2^a, 3^a, 2^a)` (`RB.anchoredVec`), the same local norms
(`RB.anchoredVec_localNorm_real`, `RB.anchoredVec_localNorm_padic`), the same naive height
`M = max(|m|·2^a, 3^a)` (`RB.mulHeight_anchoredVec`), the same `{2,3}`-contribution `≤ 12^{-a}`
(`RB.finite_factor_le`) and the same gate `θ·3^ε < 1` (`RB.exists_eps_ratGate`).  Only the
coefficients at the distinguished place change: `γ₁ = δ`, `γ₂ = 0` instead of `γ₁ = −γ₂ = δ_b`,
so the approximation form evaluates to `δ·3^a − m·2^a = 2^a(δ(3/2)^a − m)`.  The third
coordinate `2^a` is now carried only to keep the triple primitive — which is exactly what makes
the `n = 3` route cheaper than a bespoke `n = 2` one, where `3 ∣ m` would shrink the height and
the finite places would have to compensate.

The escape step is the homogeneous analogue of `RB.escape_of_linear_relation`
(`RB.escape_of_linear_relation_hom`): a nontrivial relation `m_a·A₀ + (3/2)^a·A₁ + A₂ = 0`
forces `δ(3/2)^a − m_a = u(3/2)^a + w`, and each of the four cases is elementary — the
degenerate one (`u = w = 0`) makes `δ(3/2)^a` an integer, hence `δ` rational.

## Contents

* `RB.onePowerDefect`, `RB.onePowerNearest`, `RB.abs_onePowerDefect_nearest`,
  `RB.onePowerNearest_max_le` — the data at a violating exponent.
* **`RB.escape_of_linear_relation_hom`** — the escape, field-agnostic.
* `RB.approxForms_apply_zero/one/two`, `RB.genMultiplier_zero_coe`,
  **`RB.prod_approxForms_realPlace_hom`**, **`RB.schmidt_lhs_le_hom`** — the local bookkeeping.
* `RB.escape_subspace_finite_hom` — each proper `ℚ`-subspace catches finitely many exponents.
* **`RB.onePower_finite_of_irrational`** — the wall, at every scale `θ < 1`.

## References

* [B1E2a2] `plans/report-B1E2a-v2.html` (2026-08-06): §4 N3 (the one-power extraction), §7 WP-G.
* [S] W. M. Schmidt, LNM **1467**, Theorem 1D′ (`CITED/SchmidtSubspace.lean`).
* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004) — the statement this route replaces for the
  algebraic-multiplier slices (`CITED/CorvajaZannierAlgebraic.lean`).
* [NKR25] Nair–Kumar–Rout, arXiv:2506.02898v3 — the `ℚ`-template of the place bookkeeping.
-/

namespace RB

open NumberField IntermediateField Subspace Rat.AbsoluteValue Height

attribute [local instance] Classical.propDecidable

/-! ## The data at a violating exponent -/

/-- **The homogeneous one-power defect** `Λ = δ(3/2)^a − m`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_rational_base"]
noncomputable def onePowerDefect (δ : ℝ) (m : ℤ) (a : ℕ) : ℝ := δ * (3 / 2 : ℝ) ^ a - m

/-- The integer the derivation feeds to the Subspace Theorem: the nearest integer to
`δ(3/2)^a`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_rational_base"]
noncomputable def onePowerNearest (δ : ℝ) (a : ℕ) : ℤ := round (δ * (3 / 2 : ℝ) ^ a)

/-- At the nearest integer the defect *is* the distance to `ℤ`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_rational_base"]
theorem abs_onePowerDefect_nearest (δ : ℝ) (a : ℕ) :
    |onePowerDefect δ (onePowerNearest δ a) a| = distToNearestInt (δ * (3 / 2 : ℝ) ^ a) := rfl

/-- The height base grows at most like `3^a`: `|m| ≤ |δ|(3/2)^a + 1`, so
`M = max(|m|·2^a, 3^a) ≤ (|δ| + 1)·3^a`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_rational_base"]
theorem onePowerNearest_max_le (δ : ℝ) (a : ℕ) :
    max (|((onePowerNearest δ a : ℤ) : ℝ)| * 2 ^ a) (3 ^ a) ≤ (|δ| + 1) * 3 ^ a := by
  set y : ℝ := δ * (3 / 2 : ℝ) ^ a with hy
  have hround : |y - (round y : ℝ)| ≤ 1 / 2 := abs_sub_round y
  have hyabs : |y| = |δ| * (3 / 2 : ℝ) ^ a := by
    rw [hy, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3 / 2 : ℝ) ^ a)]
  have hm : |((round y : ℤ) : ℝ)| ≤ |δ| * (3 / 2 : ℝ) ^ a + 1 := by
    have h3 := abs_sub_abs_le_abs_sub ((round y : ℤ) : ℝ) y
    have h2 : |((round y : ℤ) : ℝ) - y| ≤ 1 / 2 := by
      rw [abs_sub_comm]; exact hround
    linarith
  have h23 : (2:ℝ) ^ a ≤ 3 ^ a := by gcongr; norm_num
  refine max_le ?_ ?_
  · calc |((onePowerNearest δ a : ℤ) : ℝ)| * 2 ^ a ≤ (|δ| * (3 / 2 : ℝ) ^ a + 1) * 2 ^ a := by
          gcongr
          exact hm
      _ = |δ| * 3 ^ a + 2 ^ a := by
          rw [div_pow]
          field_simp
      _ ≤ (|δ| + 1) * 3 ^ a := by nlinarith [abs_nonneg δ]
  · nlinarith [abs_nonneg δ, pow_pos (show (0:ℝ) < 3 by norm_num) a]

/-! ## The escape from a fixed subspace -/

/-- **The homogeneous escape step**: a nontrivial linear relation
`m_a·A₀ + (3/2)^a·A₁ + A₂ = 0` between the coordinates of the approximation triples is
compatible with the smallness `|δ'(3/2)^a − m_a| ≤ θ^a` for only finitely many `a`.

The homogeneous sibling of `RB.escape_of_linear_relation`, with the same four cases; the
degenerate one forces `δ'(3/2)^a = m_a` and hence the rationality of `δ'`. -/
@[category research solved, AMS 11, ref "NKR25" "B1E2a2", group "rb_rational_base"]
theorem escape_of_linear_relation_hom (δ' : ℝ) (hδ' : Irrational δ') {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (m : ℕ → ℤ) (A : Fin 3 → ℝ) (hA : A ≠ 0) :
    {a : ℕ | |δ' * (3 / 2 : ℝ) ^ a - (m a : ℝ)| ≤ (θ : ℝ) ^ a ∧
      ((m a : ℝ)) * A 0 + (3 / 2 : ℝ) ^ a * A 1 + A 2 = 0}.Finite := by
  have hθ0' : (0:ℝ) < (θ:ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ:ℝ) < 1 := by exact_mod_cast hθ1
  have hmono : StrictMono (fun n : ℕ => (3 / 2 : ℝ) ^ n) := pow_right_strictMono₀ (by norm_num)
  by_cases hA0 : A 0 = 0
  · by_cases hA1 : A 1 = 0
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro a ⟨-, hrel⟩
      exfalso
      rw [hA0, hA1] at hrel
      simp only [mul_zero, add_zero, zero_add] at hrel
      exact hA (funext fun i => by fin_cases i <;> simp [hA0, hA1, hrel])
    · refine Set.Subsingleton.finite ?_
      rintro a ⟨-, hrel⟩ e ⟨-, hrel'⟩
      rw [hA0] at hrel hrel'
      have h1 : (3 / 2 : ℝ) ^ a * A 1 = (3 / 2 : ℝ) ^ e * A 1 := by linarith
      exact hmono.injective (mul_right_cancel₀ hA1 h1)
  · set u : ℝ := δ' + A 1 / A 0 with hu_def
    set w : ℝ := A 2 / A 0 with hw_def
    have hkey : ∀ a : ℕ, ((m a : ℝ)) * A 0 + (3 / 2 : ℝ) ^ a * A 1 + A 2 = 0 →
        δ' * (3 / 2 : ℝ) ^ a - (m a : ℝ) = u * (3 / 2 : ℝ) ^ a + w := by
      intro a hrel
      have hm : (m a : ℝ) = -((3 / 2 : ℝ) ^ a * A 1 + A 2) / A 0 := by
        field_simp
        linarith
      rw [hm, hu_def, hw_def]
      field_simp
      ring
    by_cases hu : u = 0
    · by_cases hw : w = 0
      · -- the defect vanishes, so `δ'` would be rational
        refine Set.Finite.subset Set.finite_empty ?_
        rintro a ⟨-, hrel⟩
        exfalso
        have h0 : δ' * (3 / 2 : ℝ) ^ a - (m a : ℝ) = 0 := by
          rw [hkey a hrel, hu, hw]; ring
        have hq : ((3 / 2 : ℚ) ^ a) ≠ 0 := by positivity
        have hirr : Irrational (δ' * (((3 / 2 : ℚ) ^ a : ℚ) : ℝ)) := hδ'.mul_ratCast hq
        have hcast : ((((3 / 2 : ℚ) ^ a : ℚ)) : ℝ) = (3 / 2 : ℝ) ^ a := by
          push_cast; ring
        rw [hcast] at hirr
        have heq : δ' * (3 / 2 : ℝ) ^ a = (m a : ℝ) := by linarith
        rw [heq] at hirr
        simp at hirr
      · -- `0 < |w| ≤ θ^a` bounds `a`
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (abs_pos.mpr hw) hθ1'
        refine Set.Finite.subset (Set.finite_Iio N) ?_
        rintro a ⟨hle, hrel⟩
        by_contra haN
        simp only [Set.mem_Iio, not_lt] at haN
        rw [hkey a hrel, hu, zero_mul, zero_add] at hle
        have : (θ:ℝ) ^ a ≤ (θ:ℝ) ^ N := pow_le_pow_of_le_one hθ0'.le hθ1'.le haN
        linarith
    · -- the defect grows like `|u|(3/2)^a`
      obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((1 + |w|) / |u|) (show (1:ℝ) < 3 / 2 by norm_num)
      refine Set.Finite.subset (Set.finite_Iio N) ?_
      rintro a ⟨hle, hrel⟩
      by_contra haN
      simp only [Set.mem_Iio, not_lt] at haN
      rw [hkey a hrel] at hle
      have hθa : (θ:ℝ) ^ a ≤ 1 := pow_le_one₀ hθ0'.le hθ1'.le
      have h2 : |u * (3 / 2 : ℝ) ^ a| = |u| * (3 / 2 : ℝ) ^ a := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3 / 2 : ℝ) ^ a)]
      have h3 := abs_sub_abs_le_abs_sub (u * (3 / 2 : ℝ) ^ a) (-w)
      simp only [abs_neg, sub_neg_eq_add] at h3
      rw [h2] at h3
      have hupos : 0 < |u| := abs_pos.mpr hu
      have hdiv : (3 / 2 : ℝ) ^ a ≤ (1 + |w|) / |u| := by
        rw [le_div_iff₀ hupos]
        linarith
      have hlt : (3 / 2 : ℝ) ^ N ≤ (3 / 2 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) haN
      linarith

/-! ## The approximation forms at the homogeneous coefficients -/

section Forms

variable {F : Type*} [Field F]

/-- The approximation form of `RB.approxForms`, evaluated. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_rational_base"]
lemma approxForms_apply_zero (γ₁ γ₂ : F) (x : Fin 3 → F) :
    approxForms γ₁ γ₂ 0 x = γ₁ * x 1 + γ₂ * x 2 - x 0 := by
  simp [approxForms, smul_eq_mul]

/-- The second form of `RB.approxForms` is the coordinate `X₁`. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_rational_base"]
lemma approxForms_apply_one (γ₁ γ₂ : F) (x : Fin 3 → F) :
    approxForms γ₁ γ₂ 1 x = x 1 := by
  simp [approxForms]

/-- The third form of `RB.approxForms` is the coordinate `X₂`. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_rational_base"]
lemma approxForms_apply_two (γ₁ γ₂ : F) (x : Fin 3 → F) :
    approxForms γ₁ γ₂ 2 x = x 2 := by
  simp [approxForms]

end Forms

section Field

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The anchor-`0` multiplier is `δ` itself. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_rational_base"]
lemma genMultiplier_zero_coe : ((genMultiplier δ 0 : ℚ⟮δ⟯) : ℝ) = δ := by
  rw [genMultiplier_coe]
  norm_num

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The distinguished-place numerator of the homogeneous instance: `|Λ|·12^a`, with
`Λ = δ(3/2)^a − m`. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_rational_base"]
theorem prod_approxForms_realPlace_hom (m : ℤ) (a : ℕ) :
    (∏ i, realPlace δ (approxForms (genMultiplier δ 0) 0 i
        (fun j ↦ ((anchoredVec m a j : ℚ) : ℚ⟮δ⟯))))
      = |onePowerDefect δ m a| * 12 ^ a := by
  have hcast : (fun j ↦ ((anchoredVec m a j : ℚ) : ℚ⟮δ⟯))
      = fun j ↦ ((anchoredTripleInt m a j : ℤ) : ℚ⟮δ⟯) := by
    funext j
    rw [anchoredVec_eq_cast]
    push_cast
    ring
  rw [hcast, Fin.prod_univ_three, approxForms_apply_zero, approxForms_apply_one,
    approxForms_apply_two]
  simp only [anchoredTripleInt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have hcoe : ((genMultiplier δ 0 * (((3 ^ a : ℤ)) : ℚ⟮δ⟯) + 0 * (((2 ^ a : ℤ)) : ℚ⟮δ⟯)
      - (((m * 2 ^ a : ℤ)) : ℚ⟮δ⟯) : ℚ⟮δ⟯) : ℝ) = 2 ^ a * onePowerDefect δ m a := by
    rw [onePowerDefect]
    push_cast
    rw [show ((3 : ℚ⟮δ⟯) : ℝ) = 3 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 3,
      show ((2 : ℚ⟮δ⟯) : ℝ) = 2 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 2, genMultiplier_zero_coe]
    simp only [div_pow]
    have h2 : (2 : ℝ) ^ a ≠ 0 := by positivity
    field_simp
    ring
  have h3a : ((((3 ^ a : ℤ)) : ℚ⟮δ⟯) : ℝ) = (3:ℝ) ^ a := by
    push_cast
    rw [show ((3 : ℚ⟮δ⟯) : ℝ) = 3 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 3]
  have h2a : ((((2 ^ a : ℤ)) : ℚ⟮δ⟯) : ℝ) = (2:ℝ) ^ a := by
    push_cast
    rw [show ((2 : ℚ⟮δ⟯) : ℝ) = 2 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 2]
  rw [realPlace_apply, realPlace_apply, realPlace_apply, hcoe, h3a, h2a, abs_mul,
    abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) a),
    abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) a),
    show (12 : ℝ) = 2 * 3 * 2 by norm_num, mul_pow, mul_pow]
  ring

omit [NumberField ↥ℚ⟮δ⟯] in
/-- **The Schmidt-1D′ left-hand side of the homogeneous triple is at most `|Λ|/M³`** — the
`{2,3}`-part cancels the `12^a` of the archimedean part exactly. -/
@[category research solved, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_rational_base"]
theorem schmidt_lhs_le_hom (m : ℤ) (a : ℕ) :
    (∏ i, realPlace δ (approxForms (genMultiplier δ 0) 0 i
          (fun j ↦ ((anchoredVec m a j : ℚ) : ℚ⟮δ⟯))) / localNorm real (anchoredVec m a))
        * approxProduct {padic 2, padic 3} (fun _ ↦ coordForms) (anchoredVec m a)
      ≤ |onePowerDefect δ m a| / (max (|(m : ℝ)| * 2 ^ a) (3 ^ a)) ^ 3 := by
  have harch : (∏ i, realPlace δ (approxForms (genMultiplier δ 0) 0 i
        (fun j ↦ ((anchoredVec m a j : ℚ) : ℚ⟮δ⟯))) / localNorm real (anchoredVec m a))
      = |onePowerDefect δ m a| * 12 ^ a / (max (|(m : ℝ)| * 2 ^ a) (3 ^ a)) ^ 3 := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      prod_approxForms_realPlace_hom δ m a, anchoredVec_localNorm_real]
  rw [harch]
  have hfin := finite_factor_le m a
  have hnn : (0:ℝ) ≤ |onePowerDefect δ m a| * 12 ^ a
      / (max (|(m : ℝ)| * 2 ^ a) (3 ^ a)) ^ 3 := by positivity
  calc |onePowerDefect δ m a| * 12 ^ a / (max (|(m : ℝ)| * 2 ^ a) (3 ^ a)) ^ 3
        * approxProduct {padic 2, padic 3} (fun _ ↦ coordForms) (anchoredVec m a)
      ≤ |onePowerDefect δ m a| * 12 ^ a / (max (|(m : ℝ)| * 2 ^ a) (3 ^ a)) ^ 3
          * (1 / 12 : ℝ) ^ a := mul_le_mul_of_nonneg_left hfin hnn
    _ = |onePowerDefect δ m a| / (max (|(m : ℝ)| * 2 ^ a) (3 ^ a)) ^ 3 := by
        rw [div_pow, one_pow]
        field_simp

end Field

/-! ## The escape, over `ℚ` -/

/-- **Each proper `ℚ`-subspace catches only finitely many exponents** — the homogeneous
analogue of `RB.escape_subspace_finite_rat`. -/
@[category research solved, AMS 11, ref "NKR25" "B1E2a2", group "rb_rational_base"]
theorem escape_subspace_finite_hom (δ : ℝ) (hδ : Irrational δ) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {W : Submodule ℚ (Fin 3 → ℚ)} (hW : W ≠ ⊤) :
    {a : ℕ | distToNearestInt (δ * (3 / 2 : ℝ) ^ a) ≤ (θ : ℝ) ^ a ∧
        anchoredTriple (onePowerNearest δ a) a ∈ W}.Finite := by
  obtain ⟨c, hc0, hcrel⟩ := exists_coeffs_of_ne_top hW
  have hA : (fun i => ((c i : ℚ) : ℝ)) ≠ 0 := by
    intro h
    refine hc0 (funext fun i => ?_)
    have hi : ((c i : ℚ) : ℝ) = 0 := congrFun h i
    exact_mod_cast hi
  refine Set.Finite.subset (escape_of_linear_relation_hom δ hδ hθ0 hθ1
    (fun a => onePowerNearest δ a) (fun i => ((c i : ℚ) : ℝ)) hA) ?_
  rintro a ⟨hdist, hmem⟩
  refine ⟨?_, ?_⟩
  · rw [← abs_onePowerDefect_nearest δ a] at hdist
    exact hdist
  · exact real_relation_of_sum_eq_zero_rat _ a c (hcrel _ hmem)

/-! ## The wall, at every scale -/

section Wall

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

/-- **The homogeneous one-power wall, unconditionally** ([B1E2a2] §4 N3, §7 WP-G, via [S] Thm
1D′): for an algebraic irrational `δ` and *every* geometric scale `θ ∈ (0,1)`, only finitely
many `a` bring `δ(3/2)^a` within `θ^a` of an integer.

This is the statement the CZ slices of `RB/AlgebraicKernel.lean` consume; proving it here
replaces the cited axiom `CZ.pseudoPisot_approx_alg` in those derivations.  Footprint:
std3 + `Subspace.schmidt1D'`. -/
@[category research solved, AMS 11, ref "S" "CZ04" "B1E2a2", group "rb_rational_base"]
theorem onePower_finite_of_irrational (hδ : Irrational δ) {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    {a : ℕ | distToNearestInt (δ * (3 / 2 : ℝ) ^ a) ≤ (θ : ℝ) ^ a}.Finite := by
  classical
  have hθ0' : (0:ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  obtain ⟨ε, hε, hgate⟩ := exists_eps_ratGate hθ1'
  -- the Subspace conclusion for the homogeneous forms
  obtain ⟨T, hT, hsol⟩ := Subspace.schmidt1D' (n := 3) (K := ℚ⟮δ⟯) (by norm_num)
    real (realPlace δ) (realPlace_extends_real δ)
    (approxForms (genMultiplier δ 0) 0)
    (approxForms_linearIndependent _ _)
    {padic 2, padic 3}
    (by simp [CZ.real_ne_padic2, CZ.real_ne_padic3])
    (fun _ ↦ coordForms) (fun _ _ ↦ coordForms_linearIndependent) ε hε
  -- the analytic gate
  have hC1 : (1:ℝ) ≤ |δ| + 1 := by
    have := abs_nonneg δ
    linarith
  obtain ⟨N, hN⟩ := exists_pow_le_target (θ := (θ : ℝ)) (C := |δ| + 1) hθ0'.le hC1 hgate
  refine Set.Finite.subset (Set.Finite.union (Set.finite_Iio N)
    (Set.Finite.biUnion T.finite_toSet fun W hW =>
      escape_subspace_finite_hom δ hδ hθ0 hθ1 (hT W hW))) ?_
  intro a hdist
  simp only [Set.mem_setOf_eq] at hdist
  rcases lt_or_ge a N with haN | haN
  · exact Or.inl haN
  refine Or.inr ?_
  -- the triple solves the Subspace inequality
  have hΛ : |onePowerDefect δ (onePowerNearest δ a) a| ≤ (θ : ℝ) ^ a := by
    rw [abs_onePowerDefect_nearest]
    exact hdist
  have hM0 : (0:ℝ) < max (|((onePowerNearest δ a : ℤ) : ℝ)| * 2 ^ a) (3 ^ a) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hle : (∏ i, realPlace δ (approxForms (genMultiplier δ 0) 0 i
          (fun j ↦ ((anchoredVec (onePowerNearest δ a) a j : ℚ) : ℚ⟮δ⟯)))
          / localNorm real (anchoredVec (onePowerNearest δ a) a))
        * approxProduct {padic 2, padic 3} (fun _ ↦ coordForms)
            (anchoredVec (onePowerNearest δ a) a)
      ≤ mulHeight (anchoredVec (onePowerNearest δ a) a) ^ (-(3 : ℝ) - ε) := by
    rw [mulHeight_anchoredVec]
    refine (schmidt_lhs_le_hom δ _ a).trans ?_
    exact defect_le_target hΛ hM0 (onePowerNearest_max_le δ a) (by linarith) hε (hN a haN)
  obtain ⟨W, hWT, hWmem⟩ :=
    hsol (anchoredVec (onePowerNearest δ a) a) (anchoredVec_ne_zero _ a) (by exact_mod_cast hle)
  -- the triple spans the same line as the primitive vector
  refine Set.mem_biUnion hWT ⟨hdist, ?_⟩
  have hsmul : anchoredTriple (onePowerNearest δ a) a
      = (((2 : ℚ) ^ a)⁻¹) • anchoredVec (onePowerNearest δ a) a := by
    rw [anchoredVec_eq_smul, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rw [hsmul]
  exact W.smul_mem _ hWmem

end Wall

end RB
