/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.AnchoredEscape
import CITED.SchmidtSubspace
import CITED.NairKumarRoutLemmas
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The anchored wall at every scale, via Schmidt's Theorem 1D′ (report B1E2a-v2, WP-G)

`RB/AnchoredEscape.lean` runs the anchored endgame against `Subspace.evertseSchlickewei`, the
*number-field* form of the Subspace Theorem, and obtains the wall only below the threshold
`θ < (3/2)^{n_∞+1−2D} ≤ 2/3`.  That deficit is not a feature of the problem: it is the price of
putting **rational** data in front of a theorem whose height is measured over `K = ℚ(δ)`, where
`H_K(x) = H_ℚ(x)^{[K:ℚ]}` (`NumberField.mulHeight_ratCast`) inflates the right-hand side while the
approximation is small at one place only.

`CITED/SchmidtSubspace.lean` records the classical tool for exactly this situation — Schmidt's
Theorem 1D′, with **algebraic coefficients and rational points**.  This file re-runs the endgame
against it, and the threshold disappears:

  **`RB.inhomOnePower_of_irrational` : for every algebraic irrational `δ` and every anchor `b`,
  `RB.InhomOnePower (δ(3/2)^b)` holds — at every scale `θ ∈ (0,1)`.**

## Why the loss disappears

Over `ℚ` the place set is `{∞, 2, 3}` and the primitive triple `X = (m·2^d, 3^d, 2^d)` has local
norm `1` at `2` and `3` (coprimality) and `M = max(|m|·2^d, 3^d)` at `∞`, which is also its naive
height.  The three factors are then

* `∞`: `|Λ|·2^d · 3^d · 2^d / M³ = |Λ|·12^d/M³` — the algebraic coefficients `δ_b` enter only
  here, through the chosen real embedding of `ℚ(δ)` (`RB.realPlace`);
* `2`: `|m|₂·2^{-2d}`, and `3`: `|m|₃·3^{-d}` — jointly `≤ 12^{-d}`,

so the whole product is at most `|Λ|/M³` and the Subspace hypothesis reads `|Λ| ≤ M^{-ε}`.  With
`|Λ| ≤ θ^d` and `M ≤ C·3^d` that holds for all large `d` as soon as `θ·3^ε < 1` — and for *any*
`θ < 1` such an `ε > 0` exists (`RB.exists_eps_ratGate`).  No `n_∞`, no `D`: the conjugate places
of `ℚ(δ)`, which were the source of the loss, simply do not occur.

## What is reused unchanged

The escape step is field-agnostic and needs no adaptation: `RB.escape_of_linear_relation` (a
statement about real numbers) and `RB.exists_coeffs_of_ne_top` (now at `F = ℚ`) close the argument
exactly as before, and `RB.anchoredNearest`, `RB.abs_anchoredDefect_nearest`,
`RB.anchoredNearest_max_le` supply the data.  The `ℚ`-side place bookkeeping comes from the
`CZ`/`NKR` machinery (`NKR.localNorm_triple`, `NKR.padic_max3_of_gcd_eq_one`).

## Contents

* `RB.anchoredVec` — the primitive triple as a rational vector, with `RB.anchoredVec_localNorm_real`,
  `RB.anchoredVec_localNorm_padic`, `RB.mulHeight_anchoredVec`.
* `RB.padic_two_factor`, `RB.padic_three_factor`, **`RB.finite_factor_le`** — the `{2,3}` part.
* **`RB.schmidt_lhs_le`** — the whole left-hand side is `≤ |Λ|/M³`.
* `RB.exists_eps_ratGate`, `RB.exists_pow_le_target` — the gate, available for every `θ < 1`.
* **`RB.inhomOnePower_of_irrational`** — the wall, at every scale.
* **`RB.anchoredViolators_finite_of_irrational`** — the anchored family is finite, unconditionally.

## References

* [B1E2a2] `plans/report-B1E2a-v2.html` (2026-08-06): §4 N4, §6 P3, §7 WP-G.
* [S] W. M. Schmidt, LNM **1467**, Theorem 1D′ (`CITED/SchmidtSubspace.lean`).
* [NKR25] Nair–Kumar–Rout, arXiv:2506.02898v3 — the `ℚ`-template of this bookkeeping.
-/

namespace RB

open NumberField IntermediateField Subspace Rat.AbsoluteValue Height

attribute [local instance] Classical.propDecidable

/-! ## The primitive triple as a rational vector -/

/-- The primitive integer triple `(m·2^d, 3^d, 2^d)` as a vector of rationals, in the shape the
`ℚ`-place machinery of `CITED/NairKumarRoutLemmas.lean` consumes. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
def anchoredVec (m : ℤ) (d : ℕ) : Fin 3 → ℚ :=
  ![((m * 2 ^ d : ℤ) : ℚ), ((3 ^ d : ℤ) : ℚ), ((2 ^ d : ℤ) : ℚ)]

/-- `RB.anchoredVec` is the coordinatewise cast of `RB.anchoredTripleInt`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem anchoredVec_eq_cast (m : ℤ) (d : ℕ) :
    anchoredVec m d = fun i ↦ ((anchoredTripleInt m d i : ℤ) : ℚ) := by
  funext i
  fin_cases i <;> rfl

/-- `RB.anchoredVec` is `2^d` times `RB.anchoredTriple`, so the two have the same height and span
the same line. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem anchoredVec_eq_smul (m : ℤ) (d : ℕ) :
    anchoredVec m d = ((2 : ℚ) ^ d) • anchoredTriple m d := by
  funext i
  fin_cases i <;>
    simp only [anchoredVec, anchoredTriple, Pi.smul_apply, smul_eq_mul] <;>
    push_cast <;> [ring; (rw [div_pow]; field_simp); ring]

/-- The triple is nonzero. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem anchoredVec_ne_zero (m : ℤ) (d : ℕ) : anchoredVec m d ≠ 0 := by
  intro h
  have h2 : anchoredVec m d 2 = 0 := by rw [h]; rfl
  simp only [anchoredVec, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  have : (2:ℚ) ^ d ≠ 0 := by positivity
  exact this (by exact_mod_cast h2)

/-- At the archimedean place the local norm is `M = max(|m|·2^d, 3^d)`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem anchoredVec_localNorm_real (m : ℤ) (d : ℕ) :
    localNorm real (anchoredVec m d) = max (|(m : ℝ)| * 2 ^ d) (3 ^ d) := by
  rw [anchoredVec, NKR.localNorm_triple, NKR.real_intCast_natAbs, NKR.real_intCast_natAbs,
    NKR.real_intCast_natAbs]
  have e0 : ((m * 2 ^ d : ℤ).natAbs : ℝ) = |(m : ℝ)| * 2 ^ d := by
    rw [Nat.cast_natAbs]
    push_cast
    rw [abs_mul, abs_pow, abs_two]
  have e1 : ((3 ^ d : ℤ).natAbs : ℝ) = 3 ^ d := by
    rw [Nat.cast_natAbs]
    push_cast
    rw [abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
  have e2 : ((2 ^ d : ℤ).natAbs : ℝ) = 2 ^ d := by
    rw [Nat.cast_natAbs]
    push_cast
    rw [abs_pow, abs_two]
  rw [e0, e1, e2, max_eq_left]
  exact le_trans (by gcongr; norm_num) (le_max_right _ _)

/-- At `2` and `3` the local norm is `1`: the triple is primitive. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem anchoredVec_localNorm_padic (p : ℕ) [Fact p.Prime] (m : ℤ) (d : ℕ) :
    localNorm (padic p) (anchoredVec m d) = 1 := by
  rw [anchoredVec, NKR.localNorm_triple]
  simpa [anchoredTripleInt] using
    NKR.padic_max3_of_gcd_eq_one p (anchoredTripleInt m d) (anchoredTripleInt_gcd m d)

/-- The height of the triple is `M` — over `ℚ` the naive height, with no degree factor. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem mulHeight_anchoredVec (m : ℤ) (d : ℕ) :
    mulHeight (anchoredVec m d) = max (|(m : ℝ)| * 2 ^ d) (3 ^ d) := by
  rw [anchoredVec_eq_smul, mulHeight_smul_eq_mulHeight _ (by positivity : ((2:ℚ) ^ d) ≠ 0),
    mulHeight_anchoredTriple_rat]

/-! ## The finite places -/

/-- `|2|₂ = 1/2`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem padic_two_apply_two : padic 2 (2 : ℚ) = 1 / 2 := by
  rw [padic_eq_padicNorm, show (2:ℚ) = ((2:ℕ):ℚ) by norm_num, padicNorm.padicNorm_p_of_prime]
  norm_num

/-- `|3|₂ = 1`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem padic_two_apply_three : padic 2 (3 : ℚ) = 1 := by
  have h : padicNorm 2 (3 : ℚ) = 1 := by
    rw [show (3:ℚ) = ((3:ℤ):ℚ) by norm_num]
    exact (padicNorm.int_eq_one_iff 3).mpr (by norm_num)
  rw [padic_eq_padicNorm, h]
  norm_num

/-- `|2|₃ = 1`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem padic_three_apply_two : padic 3 (2 : ℚ) = 1 := by
  have h : padicNorm 3 (2 : ℚ) = 1 := by
    rw [show (2:ℚ) = ((2:ℤ):ℚ) by norm_num]
    exact (padicNorm.int_eq_one_iff 2).mpr (by norm_num)
  rw [padic_eq_padicNorm, h]
  norm_num

/-- `|3|₃ = 1/3`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem padic_three_apply_three : padic 3 (3 : ℚ) = 1 / 3 := by
  rw [padic_eq_padicNorm, show (3:ℚ) = ((3:ℕ):ℚ) by norm_num, padicNorm.padicNorm_p_of_prime]
  norm_num

/-- A finite place contracts integers. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem padic_intCast_le_one (p : ℕ) [Fact p.Prime] (n : ℤ) : padic p ((n : ℚ)) ≤ 1 := by
  rw [padic_eq_padicNorm]
  exact_mod_cast padicNorm.of_int n

/-- The `2`-adic factor of the approximation product: `|m|₂·2^{-2d} ≤ 2^{-2d}`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem padic_two_factor (m : ℤ) (d : ℕ) :
    (∏ i, padic 2 (anchoredVec m d i)) ≤ (1 / 2 : ℝ) ^ (2 * d) := by
  rw [Fin.prod_univ_three]
  simp only [anchoredVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  push_cast
  simp only [map_mul, map_pow]
  rw [padic_two_apply_two, padic_two_apply_three, one_pow, mul_one]
  have hm := padic_intCast_le_one 2 m
  calc padic 2 ((m : ℚ)) * (1 / 2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d
      ≤ 1 * (1 / 2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d := by gcongr
    _ = (1 / 2 : ℝ) ^ (2 * d) := by rw [two_mul, pow_add]; ring

/-- The `3`-adic factor of the approximation product: `|m|₃·3^{-d} ≤ 3^{-d}`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem padic_three_factor (m : ℤ) (d : ℕ) :
    (∏ i, padic 3 (anchoredVec m d i)) ≤ (1 / 3 : ℝ) ^ d := by
  rw [Fin.prod_univ_three]
  simp only [anchoredVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  push_cast
  simp only [map_mul, map_pow]
  rw [padic_three_apply_two, padic_three_apply_three, one_pow, mul_one]
  have hm := padic_intCast_le_one 3 m
  calc padic 3 ((m : ℚ)) * 1 * (1 / 3 : ℝ) ^ d ≤ 1 * 1 * (1 / 3 : ℝ) ^ d := by gcongr
    _ = (1 / 3 : ℝ) ^ d := by ring

/-- **The finite places contribute at most `12^{-d}`** — the `S`-unit product formula in its
`ℚ`-form, where it is just multiplicativity. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem finite_factor_le (m : ℤ) (d : ℕ) :
    approxProduct {padic 2, padic 3} (fun _ ↦ coordForms) (anchoredVec m d)
      ≤ (1 / 12 : ℝ) ^ d := by
  have hp2 : (0:ℝ) < 2 := by norm_num
  rw [approxProduct, show ({padic 2, padic 3} : Finset (AbsoluteValue ℚ ℝ))
      = insert (padic 2) {padic 3} from rfl,
    Finset.prod_insert (by simp [CZ.padic2_ne_padic3]), Finset.prod_singleton]
  have hLN2 := anchoredVec_localNorm_padic 2 m d
  have hLN3 := anchoredVec_localNorm_padic 3 m d
  have hcoord : ∀ (v : AbsoluteValue ℚ ℝ) (i : Fin 3),
      v (coordForms i (anchoredVec m d)) = v (anchoredVec m d i) := by
    intro v i
    fin_cases i <;> rfl
  simp only [hcoord, hLN2, hLN3, div_one]
  calc (∏ i, padic 2 (anchoredVec m d i)) * ∏ i, padic 3 (anchoredVec m d i)
      ≤ (1 / 2 : ℝ) ^ (2 * d) * (1 / 3 : ℝ) ^ d := by
        refine mul_le_mul (padic_two_factor m d) (padic_three_factor m d)
          (Finset.prod_nonneg fun i _ ↦ apply_nonneg _ _) (by positivity)
    _ = (1 / 12 : ℝ) ^ d := by
        rw [two_mul, pow_add, ← mul_pow, ← mul_pow]
        norm_num

/-! ## The distinguished place and the assembled bound -/

section Field

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

omit [NumberField ↥ℚ⟮δ⟯] in
/-- `RB.realPlace` extends the archimedean absolute value of `ℚ`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem realPlace_extends_real (q : ℚ) : realPlace δ ((q : ℚ⟮δ⟯)) = real q := by
  rw [realPlace_apply, real_eq_abs, SubfieldClass.coe_ratCast]
  norm_num

omit [NumberField ↥ℚ⟮δ⟯] in
/-- At the distinguished place `RB.nkForms` is the approximation triple. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem nkForms_self (γ₁ γ₂ : ℚ⟮δ⟯) (w₀ : AbsoluteValue ℚ⟮δ⟯ ℝ) :
    nkForms γ₁ γ₂ w₀ w₀ = approxForms γ₁ γ₂ := by
  unfold nkForms
  rw [if_pos rfl]

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The distinguished-place numerator: `|Λ|·12^d`, exactly as in the number-field run. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem prod_approxForms_realPlace (b : ℕ) (m : ℤ) (d : ℕ) :
    (∏ i, realPlace δ (approxForms (genMultiplier δ b) (-(genMultiplier δ b)) i
        (fun j ↦ ((anchoredVec m d j : ℚ) : ℚ⟮δ⟯))))
      = |anchoredDefect δ b m d| * 12 ^ d := by
  have hcast : (fun j ↦ ((anchoredVec m d j : ℚ) : ℚ⟮δ⟯))
      = fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯) := by
    funext j
    rw [anchoredVec_eq_cast]
    push_cast
    ring
  rw [hcast, ← nkForms_self δ _ _ (realPlace δ)]
  exact prod_nkForms_realPlace δ b m d

omit [NumberField ↥ℚ⟮δ⟯] in
/-- **The Schmidt-1D′ left-hand side of the anchored triple is at most `|Λ|/M³`** — the
`{2,3}`-part cancels the `12^d` of the archimedean part exactly. -/
@[category research solved, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_anchored"]
theorem schmidt_lhs_le (b : ℕ) (m : ℤ) (d : ℕ) :
    (∏ i, realPlace δ (approxForms (genMultiplier δ b) (-(genMultiplier δ b)) i
          (fun j ↦ ((anchoredVec m d j : ℚ) : ℚ⟮δ⟯))) / localNorm real (anchoredVec m d))
        * approxProduct {padic 2, padic 3} (fun _ ↦ coordForms) (anchoredVec m d)
      ≤ |anchoredDefect δ b m d| / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 := by
  have hM0 : (0:ℝ) < max (|(m : ℝ)| * 2 ^ d) (3 ^ d) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have harch : (∏ i, realPlace δ (approxForms (genMultiplier δ b) (-(genMultiplier δ b)) i
        (fun j ↦ ((anchoredVec m d j : ℚ) : ℚ⟮δ⟯))) / localNorm real (anchoredVec m d))
      = |anchoredDefect δ b m d| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      prod_approxForms_realPlace δ b m d, anchoredVec_localNorm_real]
  rw [harch]
  have hfin := finite_factor_le m d
  have hnn : (0:ℝ) ≤ |anchoredDefect δ b m d| * 12 ^ d
      / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 := by positivity
  calc |anchoredDefect δ b m d| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3
        * approxProduct {padic 2, padic 3} (fun _ ↦ coordForms) (anchoredVec m d)
      ≤ |anchoredDefect δ b m d| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3
          * (1 / 12 : ℝ) ^ d := by
        exact mul_le_mul_of_nonneg_left hfin hnn
    _ = |anchoredDefect δ b m d| / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 := by
        rw [div_pow, one_pow]
        field_simp

end Field

/-! ## The escape, over `ℚ` -/

/-- The subspace relation carried to `ℝ`, for the rational triple. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem real_relation_of_sum_eq_zero_rat (m : ℤ) (d : ℕ) (a : Fin 3 → ℚ)
    (h : ∑ i, anchoredTriple m d i * a i = 0) :
    ((m : ℝ)) * ((a 0 : ℚ) : ℝ) + (3 / 2 : ℝ) ^ d * ((a 1 : ℚ) : ℝ) + ((a 2 : ℚ) : ℝ) = 0 := by
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Fin.sum_univ_three, anchoredTriple, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  push_cast at h2
  linarith [h2]

/-- **Each proper `ℚ`-subspace catches only finitely many exponents** — the `ℚ`-form of
`RB.escape_subspace_finite`, with the same field-agnostic core
(`RB.escape_of_linear_relation`). -/
@[category research solved, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
theorem escape_subspace_finite_rat (δ : ℝ) (hδ : Irrational δ) (b : ℕ) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {W : Submodule ℚ (Fin 3 → ℚ)} (hW : W ≠ ⊤) :
    {d : ℕ | 0 < d ∧
        distToNearestInt (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1)) ≤ (θ : ℝ) ^ d ∧
        anchoredTriple (anchoredNearest δ b d) d ∈ W}.Finite := by
  obtain ⟨a, ha0, harel⟩ := exists_coeffs_of_ne_top hW
  have hA : (fun i => ((a i : ℚ) : ℝ)) ≠ 0 := by
    intro h
    refine ha0 (funext fun i => ?_)
    have hi : ((a i : ℚ) : ℝ) = 0 := congrFun h i
    exact_mod_cast hi
  refine Set.Finite.subset (escape_of_linear_relation (δ * (3 / 2 : ℝ) ^ b)
    (anchored_multiplier_irrational hδ b) hθ0 hθ1 (fun d => anchoredNearest δ b d)
    (fun i => ((a i : ℚ) : ℝ)) hA) ?_
  rintro d ⟨hd, hdist, hmem⟩
  refine ⟨hd, ?_, ?_⟩
  · rw [← abs_anchoredDefect_nearest δ b d] at hdist
    exact hdist
  · exact real_relation_of_sum_eq_zero_rat _ d a (harel _ hmem)

/-! ## The gate: every scale below `1` is admissible -/

/-- For every `θ < 1` there is an `ε > 0` with `θ·3^ε < 1` — the whole gate of the `ℚ`-run. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem exists_eps_ratGate {θ : ℝ} (hθ1 : θ < 1) : ∃ ε > (0:ℝ), θ * (3:ℝ) ^ ε < 1 := by
  have hcont : ContinuousAt (fun t : ℝ => θ * (3:ℝ) ^ t) 0 := by
    fun_prop (disch := norm_num)
  have hev : ∀ᶠ t in nhds (0:ℝ), θ * (3:ℝ) ^ t < 1 := by
    refine hcont.eventually_lt_const ?_
    simpa using hθ1
  obtain ⟨t, ht1, ht2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0))).exists
  exact ⟨t, ht2, ht1⟩

/-- Under the gate `θ·3^ε < 1` the defect bound clears the Subspace threshold for all large
`d`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem exists_pow_le_target {θ C ε : ℝ} (hθ0 : 0 ≤ θ) (hC1 : 1 ≤ C)
    (hgate : θ * (3:ℝ) ^ ε < 1) :
    ∃ N : ℕ, ∀ d ≥ N, θ ^ d ≤ (C * 3 ^ d) ^ (-ε) := by
  have hCe : (0:ℝ) < C ^ (-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hτ0 : (0:ℝ) ≤ θ * (3:ℝ) ^ ε := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hCe hgate
  refine ⟨N, fun d hd => ?_⟩
  have hτd : (θ * (3:ℝ) ^ ε) ^ d ≤ (θ * (3:ℝ) ^ ε) ^ N :=
    pow_le_pow_of_le_one hτ0 hgate.le hd
  have hsplit : (C * 3 ^ d) ^ (-ε) = C ^ (-ε) * (((3:ℝ) ^ ε) ^ d)⁻¹ := by
    rw [Real.mul_rpow (by linarith) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (3:ℝ) d, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
      ← Real.rpow_natCast ((3:ℝ) ^ ε) d, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
      ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring
  rw [hsplit, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc θ ^ d * ((3:ℝ) ^ ε) ^ d = (θ * (3:ℝ) ^ ε) ^ d := by rw [mul_pow]
    _ ≤ (θ * (3:ℝ) ^ ε) ^ N := hτd
    _ ≤ C ^ (-ε) := hN.le

/-- The defect bound `|Λ|/M³` clears the Subspace threshold `M^{-3-ε}` once `|Λ| ≤ θ^d` and
`θ^d ≤ (C·3^d)^{-ε}` with `M ≤ C·3^d`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem defect_le_target {Λ M C : ℝ} {d : ℕ} {θ ε : ℝ} (hΛ : |Λ| ≤ θ ^ d) (hM0 : 0 < M)
    (hMC : M ≤ C * 3 ^ d) (hC0 : 0 < C) (hε : 0 < ε) (hsmall : θ ^ d ≤ (C * 3 ^ d) ^ (-ε)) :
    |Λ| / M ^ 3 ≤ M ^ (-(3:ℝ) - ε) := by
  have hMe : M ^ (-(3:ℝ) - ε) = (M ^ 3)⁻¹ * M ^ (-ε) := by
    rw [show -(3:ℝ) - ε = (-3 : ℝ) + -ε by ring, Real.rpow_add hM0,
      show (-3 : ℝ) = -((3:ℕ) : ℝ) by norm_num, Real.rpow_neg hM0.le, Real.rpow_natCast]
  have hstep : (C * 3 ^ d) ^ (-ε) ≤ M ^ (-ε) := by
    rw [Real.rpow_neg hM0.le, Real.rpow_neg (by positivity)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hM0 _) (Real.rpow_le_rpow hM0.le hMC hε.le)
  have hkey : |Λ| ≤ M ^ (-ε) := hΛ.trans (hsmall.trans hstep)
  have hM3 : (0:ℝ) < M ^ 3 := by positivity
  calc |Λ| / M ^ 3 ≤ M ^ (-ε) / M ^ 3 := by gcongr
    _ = (M ^ 3)⁻¹ * M ^ (-ε) := by ring
    _ = M ^ (-(3:ℝ) - ε) := hMe.symm

/-! ## The wall, at every scale -/

section Wall

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

/-- **The anchored wall, unconditionally** ([B1E2a2] §7 WP-G, via [S] Thm 1D′): for an algebraic
irrational `δ` and *every* geometric scale `θ ∈ (0,1)`, only finitely many `d` bring
`δ(3/2)^b((3/2)^d − 1)` within `θ^d` of an integer.

The threshold of `RB.inhomOnePower_of_lt_threshold` is gone: with the points rational and only the
coefficients algebraic, the height carries no degree factor, the conjugate places of `ℚ(δ)` never
appear, and the gate `θ·3^ε < 1` is satisfiable for every `θ < 1`. -/
@[category research solved, AMS 11, ref "S" "NKR25" "B1E2a2", group "rb_anchored"]
theorem inhomOnePower_of_irrational (hδ : Irrational δ) (b : ℕ) :
    InhomOnePower (δ * (3 / 2 : ℝ) ^ b) := by
  classical
  intro θ hθ0 hθ1
  have hθ0' : (0:ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  obtain ⟨ε, hε, hgate⟩ := exists_eps_ratGate hθ1'
  -- the Subspace conclusion for the anchored forms
  obtain ⟨T, hT, hsol⟩ := Subspace.schmidt1D' (n := 3) (K := ℚ⟮δ⟯) (by norm_num)
    real (realPlace δ) (realPlace_extends_real δ)
    (approxForms (genMultiplier δ b) (-(genMultiplier δ b)))
    (approxForms_linearIndependent _ _)
    {padic 2, padic 3}
    (by simp [CZ.real_ne_padic2, CZ.real_ne_padic3])
    (fun _ ↦ coordForms) (fun _ _ ↦ coordForms_linearIndependent) ε hε
  -- the analytic gate
  have hC1 : (1:ℝ) ≤ |δ * (3 / 2 : ℝ) ^ b| + 1 := by
    have := abs_nonneg (δ * (3 / 2 : ℝ) ^ b)
    linarith
  obtain ⟨N, hN⟩ := exists_pow_le_target (θ := (θ : ℝ)) (C := |δ * (3 / 2 : ℝ) ^ b| + 1)
    hθ0'.le hC1 hgate
  refine Set.Finite.subset (Set.Finite.union (Set.finite_Iio N)
    (Set.Finite.biUnion T.finite_toSet fun W hW =>
      escape_subspace_finite_rat δ hδ b hθ0 hθ1 (hT W hW))) ?_
  rintro d ⟨hd, hdist⟩
  rcases lt_or_ge d N with hdN | hdN
  · exact Or.inl hdN
  refine Or.inr ?_
  -- the triple solves the Subspace inequality
  have hΛ : |anchoredDefect δ b (anchoredNearest δ b d) d| ≤ (θ : ℝ) ^ d := by
    rw [abs_anchoredDefect_nearest]
    exact hdist
  have hM0 : (0:ℝ) < max (|((anchoredNearest δ b d : ℤ) : ℝ)| * 2 ^ d) (3 ^ d) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hle : (∏ i, realPlace δ (approxForms (genMultiplier δ b) (-(genMultiplier δ b)) i
          (fun j ↦ ((anchoredVec (anchoredNearest δ b d) d j : ℚ) : ℚ⟮δ⟯)))
          / localNorm real (anchoredVec (anchoredNearest δ b d) d))
        * approxProduct {padic 2, padic 3} (fun _ ↦ coordForms)
            (anchoredVec (anchoredNearest δ b d) d)
      ≤ mulHeight (anchoredVec (anchoredNearest δ b d) d) ^ (-(3 : ℝ) - ε) := by
    rw [mulHeight_anchoredVec]
    refine (schmidt_lhs_le δ b _ d).trans ?_
    exact defect_le_target hΛ hM0 (anchoredNearest_max_le δ b d) (by linarith) hε (hN d hdN)
  obtain ⟨W, hWT, hWmem⟩ :=
    hsol (anchoredVec (anchoredNearest δ b d) d) (anchoredVec_ne_zero _ d) (by exact_mod_cast hle)
  -- the anchored triple spans the same line, so it lies in the same subspace
  refine Set.mem_biUnion hWT ⟨hd, hdist, ?_⟩
  have hsmul : anchoredTriple (anchoredNearest δ b d) d
      = (((2 : ℚ) ^ d)⁻¹) • anchoredVec (anchoredNearest δ b d) d := by
    rw [anchoredVec_eq_smul, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rw [hsmul]
  exact W.smul_mem _ hWmem

/-- **The anchored family is finite, unconditionally** — the anchored analogue of the RPF
conclusion, at every geometric scale, for every algebraic irrational `δ`. -/
@[category research solved, AMS 11, ref "S" "NKR25" "B1E2a2", group "rb_anchored"]
theorem anchoredViolators_finite_of_irrational (hδ : Irrational δ) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (B : ℕ) :
    (anchoredViolators δ θ B).Finite :=
  anchoredViolators_finite_of_inhomOnePower δ hθ0 hθ1 B
    (fun b _ => inhomOnePower_of_irrational δ hδ b)

end Wall

end RB
