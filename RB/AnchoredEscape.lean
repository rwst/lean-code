/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.AnchoredPlaces
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The subspace-escape endgame of the anchored family (report B1E2a-v2, WP-G bill item 3)

`RB/Anchored.lean` puts the anchored family at `ℚ⟮δ⟯` in front of the Subspace Theorem,
`RB/AnchoredHeight.lean` computes the height of its data and `RB/AnchoredPlaces.lean` computes
the approximation product, leaving `RB.anchored_rehearsal_defect`: *if* the elementary inequality

  `(|Λ|·12^d/M³)·(|m|·12^d/M³)^{n_∞−1}/12^{dD} ≤ M^{D(−3−ε)}`

holds — with `Λ = δ(3/2)^b((3/2)^d − 1) − m` the defect and `M = max(|m|·2^d, 3^d)` — then the
triple `(m, (3/2)^d, 1)` lies in one of finitely many proper subspaces of `ℚ(δ)³`.  This file
closes the last item of the WP-G bill: it discharges that inequality and escapes the subspaces.

## The escape (`RB.escape_of_linear_relation`)

A proper subspace is contained in the kernel of a nonzero functional, i.e. imposes
`m·A₀ + (3/2)^d·A₁ + A₂ = 0` with `(A₀, A₁, A₂) ≠ 0` real (the coefficients live in `ℚ(δ)`, and
the defining embedding carries them to `ℝ`).  Four cases, all elementary:

* `A₀ = A₁ = 0` forces `A₂ = 0` — impossible, so the set is empty;
* `A₀ = 0 ≠ A₁` pins `(3/2)^d`, hence `d`;
* `A₀ ≠ 0` makes `m` an affine function of `(3/2)^d`, so the defect becomes `u(3/2)^d + w` with
  `u = δ_b + A₁/A₀`, `w = −δ_b + A₂/A₀`.  If `u ≠ 0` the defect grows geometrically and only
  finitely many `d` keep it below `θ^d ≤ 1`; if `u = 0 ≠ w` then `|w| ≤ θ^d` bounds `d`; and if
  `u = w = 0` the defect *vanishes*, making `δ_b = m/((3/2)^d − 1)` rational — impossible.

The last case is where the irrationality of `δ` is finally used: it is the "ratio-distinctness"
step of the [NKR25] template, and it is what makes the anchored wall a statement about *algebraic
irrational* multipliers.

## The gate, and the threshold it imposes

Feeding `|Λ| ≤ θ^d`, `|m|·2^d ≤ M` and `M ≥ 3^d` into the computed approximation product gives
`(4θ/9)^d` for the distinguished factor and `(2/3)^d` for each of the other `n_∞ − 1` infinite
places (`RB.defect_factor_le`, `RB.coordinate_factor_le`), so the whole left-hand side is at most
`ρ^d` with

  `ρ = RB.escapeBase δ θ = (4θ/9)·(2/3)^{n_∞−1}/12^D`.

The right-hand side is at least `(C·3^d)^{D(−3−ε)}` with `C = |δ_b| + 1`, because the nearest
integer obeys `M ≤ C·3^d`.  So the Subspace hypothesis holds for all large `d` as soon as

  **`RB.escapeRatio δ θ ε = ρ · 3^{D(3+ε)} < 1`**,

and `RB.escapeBase_mul_pow_eq` turns that gate into the readable threshold

  **`θ · (3/2)^{2D} < (3/2)^{n_∞+1}`,  i.e.  `θ < (3/2)^{n_∞+1−2D}`.**

For `ℚ` (`n_∞ = D = 1`) the threshold is `1` and every `θ < 1` passes; but `δ` is irrational, so
`D ≥ 2` and the threshold is at most `2/3` — `2/3` for a real quadratic field, `4/9` for a totally
real cubic one, and so on.  **The full wall `RB.InhomOnePower` (all `θ < 1`) is therefore *not*
what this route yields**; what it yields is `RB.inhomOnePower_of_lt_threshold`, the wall at every
scale below the degree-dependent threshold, which is exactly what
`RB.anchoredViolators_finite_of_wall` (the per-scale reduction) consumes.  This quantifies the
"Step-3 uniform-`ε`" risk flagged in the plan: it is not the choice of `ε` that fails but the
range of `θ`, and the deficit is the factor `(3/2)^{2D−n_∞−1}` by which the *degree* of `ℚ(δ)`
inflates the height of rational data (`NumberField.mulHeight_ratCast`).

## Contents

* **`RB.escape_of_linear_relation`** — the real-analytic escape (std3).
* `RB.defect_factor_le`, `RB.coordinate_factor_le`, `RB.explicit_le_pow`,
  `RB.pow_le_rpow_target`, `RB.exists_pow_mul_le_one` — the analytic gate (std3).
* `RB.anchoredNearest`, `RB.abs_anchoredDefect_nearest`, `RB.anchoredNearest_max_le`.
* `RB.exists_coeffs_of_ne_top`, **`RB.escape_subspace_finite`**.
* `RB.escapeBase`, `RB.escapeRatio`, **`RB.inhomOnePower_of_gate`**,
  `RB.escapeBase_mul_pow_eq`, `RB.exists_eps_escapeRatio_lt_one`,
  **`RB.inhomOnePower_of_lt_threshold`**, **`RB.anchoredViolators_finite_of_lt_threshold`**.
* **`RB.lt_two_thirds_of_lt_threshold`** — the negative half: for `D ≥ 2` the threshold is below
  `2/3`, so this route cannot reach the scales `θ ∈ [2/3, 1)`; `RB.lt_threshold_of_quadratic`
  is the matching positive statement for a real quadratic field, where *every* `θ < 2/3` passes.

## References

* [B1E2a2] `plans/report-B1E2a-v2.html` (2026-08-06): §4 N4, §6 P3, §7 WP-G (gate bill item 3).
* [NKR25] Nair, Kumar, Rout, arXiv:2506.02898v3 — the `ℚ`-template of the escape step.
* [Schmidt91] W. M. Schmidt, LNM 1467, Thm 1D′ — `Subspace.evertseSchlickewei`.
-/

namespace RB

open NumberField IntermediateField

/-! ## The escape from a fixed subspace -/

/-- **The escape step** ([B1E2a2] §7 WP-G, bill item 3): a nontrivial linear relation
`m_d·A₀ + (3/2)^d·A₁ + A₂ = 0` between the coordinates of the approximation triples is compatible
with the smallness `|δ'((3/2)^d − 1) − m_d| ≤ θ^d` for only finitely many `d`.

All four cases are elementary; the one that uses the irrationality of `δ'` is the degenerate one,
where the relation forces the defect to vanish and hence `δ' = m_d/((3/2)^d − 1)`. -/
@[category research solved, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
theorem escape_of_linear_relation (δ' : ℝ) (hδ' : Irrational δ') {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (m : ℕ → ℤ) (A : Fin 3 → ℝ) (hA : A ≠ 0) :
    {d : ℕ | 0 < d ∧ |δ' * ((3 / 2 : ℝ) ^ d - 1) - (m d : ℝ)| ≤ (θ : ℝ) ^ d ∧
      ((m d : ℝ)) * A 0 + (3 / 2 : ℝ) ^ d * A 1 + A 2 = 0}.Finite := by
  have hθ0' : (0:ℝ) < (θ:ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ:ℝ) < 1 := by exact_mod_cast hθ1
  have hmono : StrictMono (fun n : ℕ => (3 / 2 : ℝ) ^ n) := pow_right_strictMono₀ (by norm_num)
  by_cases hA0 : A 0 = 0
  · by_cases hA1 : A 1 = 0
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro d ⟨-, -, hrel⟩
      exfalso
      rw [hA0, hA1] at hrel
      simp only [mul_zero, add_zero, zero_add] at hrel
      exact hA (funext fun i => by fin_cases i <;> simp [hA0, hA1, hrel])
    · refine Set.Subsingleton.finite ?_
      rintro d ⟨-, -, hrel⟩ e ⟨-, -, hrel'⟩
      rw [hA0] at hrel hrel'
      have h1 : (3 / 2 : ℝ) ^ d * A 1 = (3 / 2 : ℝ) ^ e * A 1 := by linarith
      exact hmono.injective (mul_right_cancel₀ hA1 h1)
  · set u : ℝ := δ' + A 1 / A 0 with hu_def
    set w : ℝ := -δ' + A 2 / A 0 with hw_def
    have hkey : ∀ d : ℕ, ((m d : ℝ)) * A 0 + (3 / 2 : ℝ) ^ d * A 1 + A 2 = 0 →
        δ' * ((3 / 2 : ℝ) ^ d - 1) - (m d : ℝ) = u * (3 / 2 : ℝ) ^ d + w := by
      intro d hrel
      have hm : (m d : ℝ) = -((3 / 2 : ℝ) ^ d * A 1 + A 2) / A 0 := by
        field_simp
        linarith
      rw [hm, hu_def, hw_def]
      field_simp
      ring
    by_cases hu : u = 0
    · by_cases hw : w = 0
      · -- the defect vanishes, so `δ'` would be rational
        refine Set.Finite.subset Set.finite_empty ?_
        rintro d ⟨hd, -, hrel⟩
        exfalso
        have h0 : δ' * ((3 / 2 : ℝ) ^ d - 1) - (m d : ℝ) = 0 := by
          rw [hkey d hrel, hu, hw]; ring
        have hq : ((3 / 2 : ℚ) ^ d - 1) ≠ 0 := by
          have h1 : (1:ℚ) < (3 / 2 : ℚ) ^ d := one_lt_pow₀ (by norm_num) (by omega)
          intro h
          linarith
        have hirr : Irrational (δ' * (((3 / 2 : ℚ) ^ d - 1 : ℚ) : ℝ)) := hδ'.mul_ratCast hq
        have hcast : ((((3 / 2 : ℚ) ^ d - 1 : ℚ)) : ℝ) = (3 / 2 : ℝ) ^ d - 1 := by
          push_cast; ring
        rw [hcast] at hirr
        have heq : δ' * ((3 / 2 : ℝ) ^ d - 1) = (m d : ℝ) := by linarith
        rw [heq] at hirr
        simp at hirr
      · -- `0 < |w| ≤ θ^d` bounds `d`
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (abs_pos.mpr hw) hθ1'
        refine Set.Finite.subset (Set.finite_Iio N) ?_
        rintro d ⟨-, hle, hrel⟩
        by_contra hdN
        simp only [Set.mem_Iio, not_lt] at hdN
        rw [hkey d hrel, hu, zero_mul, zero_add] at hle
        have : (θ:ℝ) ^ d ≤ (θ:ℝ) ^ N := pow_le_pow_of_le_one hθ0'.le hθ1'.le hdN
        linarith
    · -- the defect grows like `|u|(3/2)^d`
      obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((1 + |w|) / |u|) (show (1:ℝ) < 3 / 2 by norm_num)
      refine Set.Finite.subset (Set.finite_Iio N) ?_
      rintro d ⟨-, hle, hrel⟩
      by_contra hdN
      simp only [Set.mem_Iio, not_lt] at hdN
      rw [hkey d hrel] at hle
      have hθd : (θ:ℝ) ^ d ≤ 1 := pow_le_one₀ hθ0'.le hθ1'.le
      have h2 : |u * (3 / 2 : ℝ) ^ d| = |u| * (3 / 2 : ℝ) ^ d := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3 / 2 : ℝ) ^ d)]
      have h3 := abs_sub_abs_le_abs_sub (u * (3 / 2 : ℝ) ^ d) (-w)
      simp only [abs_neg, sub_neg_eq_add] at h3
      rw [h2] at h3
      have hupos : 0 < |u| := abs_pos.mpr hu
      have hdiv : (3 / 2 : ℝ) ^ d ≤ (1 + |w|) / |u| := by
        rw [le_div_iff₀ hupos]
        linarith
      have hlt : (3 / 2 : ℝ) ^ N ≤ (3 / 2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hdN
      linarith

/-! ## The analytic gate -/

section Analytic

/-- The distinguished factor of the approximation product is at most `(4θ/9)^d`: the defect is
`≤ θ^d` and the local norm is `≥ 3^d`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem defect_factor_le {Λ θ : ℝ} (hθ0 : 0 ≤ θ) (m : ℤ) (d : ℕ) (hΛ : |Λ| ≤ θ ^ d) :
    |Λ| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 ≤ (4 * θ / 9) ^ d := by
  have hM3 : (3:ℝ) ^ d ≤ max (|(m : ℝ)| * 2 ^ d) (3 ^ d) := le_max_right _ _
  have h3pos : (0:ℝ) < (3:ℝ) ^ d := by positivity
  calc |Λ| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3
      ≤ (θ ^ d * 12 ^ d) / ((3:ℝ) ^ d) ^ 3 := by gcongr
    _ = (4 * θ / 9) ^ d := by
        rw [← mul_pow, ← pow_mul, mul_comm d 3, pow_mul, ← div_pow]
        norm_num
        ring_nf

/-- Each remaining infinite place contributes at most `(2/3)^d`: `|m|·2^d ≤ M` and `M ≥ 3^d`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem coordinate_factor_le (m : ℤ) (d : ℕ) :
    |(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 ≤ (2 / 3 : ℝ) ^ d := by
  set M : ℝ := max (|(m : ℝ)| * 2 ^ d) (3 ^ d) with hM
  have hM3 : (3:ℝ) ^ d ≤ M := le_max_right _ _
  have h3pos : (0:ℝ) < (3:ℝ) ^ d := by positivity
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le h3pos hM3
  have hnum : |(m : ℝ)| * 12 ^ d ≤ M * 6 ^ d := by
    have h12 : (12:ℝ) ^ d = 2 ^ d * 6 ^ d := by
      rw [show (12:ℝ) = 2 * 6 by norm_num, mul_pow]
    rw [h12, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  calc |(m : ℝ)| * 12 ^ d / M ^ 3 ≤ (M * 6 ^ d) / M ^ 3 := by gcongr
    _ = 6 ^ d / M ^ 2 := by field_simp
    _ ≤ 6 ^ d / ((3:ℝ) ^ d) ^ 2 := by gcongr
    _ = (2 / 3 : ℝ) ^ d := by
        rw [← pow_mul, mul_comm d 2, pow_mul, ← div_pow]
        norm_num

/-- **The approximation product is geometric**: the whole left-hand side of the Subspace
hypothesis is at most `ρ^d` with `ρ = (4θ/9)·(2/3)^n/12^D` (here `n = n_∞ − 1`). -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem explicit_le_pow {Λ θ : ℝ} (hθ0 : 0 ≤ θ) (m : ℤ) (d n D : ℕ) (hΛ : |Λ| ≤ θ ^ d) :
    (|Λ| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
        * (|(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3) ^ n
        / 12 ^ (d * D)
      ≤ ((4 * θ / 9) * (2 / 3 : ℝ) ^ n / 12 ^ D) ^ d := by
  have hM3 : (0:ℝ) < max (|(m : ℝ)| * 2 ^ d) (3 ^ d) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have h1 := defect_factor_le hθ0 m d hΛ
  have h2 := coordinate_factor_le m d
  have hf1 : (0:ℝ) ≤ |Λ| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 := by positivity
  have hf2 : (0:ℝ) ≤ |(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 := by positivity
  calc (|Λ| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
        * (|(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3) ^ n / 12 ^ (d * D)
      ≤ (4 * θ / 9) ^ d * ((2 / 3 : ℝ) ^ d) ^ n / 12 ^ (d * D) := by gcongr
    _ = ((4 * θ / 9) * (2 / 3 : ℝ) ^ n / 12 ^ D) ^ d := by ring

/-- The right-hand side of the Subspace hypothesis, bounded below through `M ≤ C·3^d`: a
geometric bound `ρ^d` clears it as soon as `ρ^d·C^{D(3+ε)}·(3^{D(3+ε)})^d ≤ 1`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem pow_le_rpow_target {ρ C M : ℝ} {d D : ℕ} {ε : ℝ} (hρ0 : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hC1 : 1 ≤ C) (hM0 : 0 < M) (hMC : M ≤ C * 3 ^ d)
    (hsmall : ρ ^ d * (C ^ ((D : ℝ) * (3 + ε)) * ((3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ d) ≤ 1) :
    ρ ^ d ≤ M ^ ((D : ℝ) * (-3 - ε)) := by
  have hy0 : (0:ℝ) ≤ (D : ℝ) * (3 + ε) := by positivity
  have hexp : (D : ℝ) * (-3 - ε) = -((D : ℝ) * (3 + ε)) := by ring
  rw [hexp, Real.rpow_neg hM0.le]
  have hMy0 : (0:ℝ) < M ^ ((D : ℝ) * (3 + ε)) := Real.rpow_pos_of_pos hM0 _
  have hCd : (C * (3:ℝ) ^ d) ^ ((D : ℝ) * (3 + ε))
      = C ^ ((D : ℝ) * (3 + ε)) * ((3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ d := by
    rw [Real.mul_rpow (by linarith) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast ((3:ℝ) ^ ((D : ℝ) * (3 + ε))) d, ← Real.rpow_natCast (3:ℝ) d,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hMy : M ^ ((D : ℝ) * (3 + ε))
      ≤ C ^ ((D : ℝ) * (3 + ε)) * ((3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ d := by
    rw [← hCd]
    exact Real.rpow_le_rpow hM0.le hMC hy0
  rw [← one_div, le_div_iff₀ hMy0]
  calc ρ ^ d * M ^ ((D : ℝ) * (3 + ε))
      ≤ ρ ^ d * (C ^ ((D : ℝ) * (3 + ε)) * ((3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ d) := by gcongr
    _ ≤ 1 := hsmall

/-- Under the gate `ρ·3^{D(3+ε)} < 1` the product of the geometric bound with the constant
`C^{D(3+ε)}` drops below `1` for all large `d`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem exists_pow_mul_le_one {ρ C : ℝ} {D : ℕ} {ε : ℝ} (hC1 : 1 ≤ C)
    (hgate : ρ * (3:ℝ) ^ ((D : ℝ) * (3 + ε)) < 1) (hρ0 : 0 ≤ ρ) :
    ∃ N : ℕ, ∀ d ≥ N,
      ρ ^ d * (C ^ ((D : ℝ) * (3 + ε)) * ((3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ d) ≤ 1 := by
  have hCy : (0:ℝ) < C ^ ((D : ℝ) * (3 + ε)) := Real.rpow_pos_of_pos (by linarith) _
  have hτ0 : (0:ℝ) ≤ ρ * (3:ℝ) ^ ((D : ℝ) * (3 + ε)) := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hCy) hgate
  refine ⟨N, fun d hd => ?_⟩
  have hτd : (ρ * (3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ d ≤ (ρ * (3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ N :=
    pow_le_pow_of_le_one hτ0 hgate.le hd
  calc ρ ^ d * (C ^ ((D : ℝ) * (3 + ε)) * ((3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ d)
      = (ρ * (3:ℝ) ^ ((D : ℝ) * (3 + ε))) ^ d * C ^ ((D : ℝ) * (3 + ε)) := by
        rw [mul_pow]; ring
    _ ≤ (C ^ ((D : ℝ) * (3 + ε)))⁻¹ * C ^ ((D : ℝ) * (3 + ε)) := by
        gcongr
        exact le_trans hτd hN.le
    _ = 1 := inv_mul_cancel₀ hCy.ne'

end Analytic

/-! ## The anchored data at a violating exponent -/

/-- The integer the anchored derivation feeds to the Subspace Theorem: the nearest integer to the
inhomogeneous one-power quantity `δ(3/2)^b((3/2)^d − 1)`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
noncomputable def anchoredNearest (δ : ℝ) (b d : ℕ) : ℤ :=
  round (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1))

/-- At the nearest integer the defect *is* the distance to `ℤ` — the quantity the wall bounds. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem abs_anchoredDefect_nearest (δ : ℝ) (b d : ℕ) :
    |anchoredDefect δ b (anchoredNearest δ b d) d|
      = distToNearestInt (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1)) := rfl

/-- The height base of the anchored data grows at most like `3^d`: the nearest integer satisfies
`|m| ≤ |δ_b|(3/2)^d + 1`, so `M = max(|m|·2^d, 3^d) ≤ (|δ_b| + 1)·3^d`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem anchoredNearest_max_le (δ : ℝ) (b d : ℕ) :
    max (|((anchoredNearest δ b d : ℤ) : ℝ)| * 2 ^ d) (3 ^ d)
      ≤ (|δ * (3 / 2 : ℝ) ^ b| + 1) * 3 ^ d := by
  set δ' : ℝ := δ * (3 / 2 : ℝ) ^ b with hδ'
  set x : ℝ := δ' * ((3 / 2 : ℝ) ^ d - 1) with hx
  have hround : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
  have h0 : (1:ℝ) ≤ (3 / 2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hxabs : |x| ≤ |δ'| * (3 / 2 : ℝ) ^ d := by
    rw [hx, abs_mul]
    have h1 : |(3 / 2 : ℝ) ^ d - 1| ≤ (3 / 2 : ℝ) ^ d := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hm : |((round x : ℤ) : ℝ)| ≤ |δ'| * (3 / 2 : ℝ) ^ d + 1 := by
    have h3 := abs_sub_abs_le_abs_sub ((round x : ℤ) : ℝ) x
    have h2 : |((round x : ℤ) : ℝ) - x| ≤ 1 / 2 := by
      rw [abs_sub_comm]; exact hround
    linarith
  have h23 : (2:ℝ) ^ d ≤ 3 ^ d := by gcongr; norm_num
  refine max_le ?_ ?_
  · calc |((anchoredNearest δ b d : ℤ) : ℝ)| * 2 ^ d ≤ (|δ'| * (3 / 2 : ℝ) ^ d + 1) * 2 ^ d := by
          gcongr
          exact hm
      _ = |δ'| * 3 ^ d + 2 ^ d := by
          rw [div_pow]
          field_simp
      _ ≤ (|δ'| + 1) * 3 ^ d := by nlinarith [abs_nonneg δ']
  · nlinarith [abs_nonneg δ', pow_pos (show (0:ℝ) < 3 by norm_num) d]

/-! ## Escaping a single subspace -/

section Subspace

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

set_option maxRecDepth 4000 in
/-- A proper subspace of `F³` lies in the kernel of a nonzero linear form: it imposes a
nontrivial linear relation on the coordinates of every triple it contains.  Used at `F = ℚ⟮δ⟯`
for the number-field instantiation and at `F = ℚ` for the `1D′` one. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem exists_coeffs_of_ne_top {F : Type*} [Field F] {W : Submodule F (Fin 3 → F)}
    (hW : W ≠ ⊤) :
    ∃ a : Fin 3 → F, a ≠ 0 ∧ ∀ x ∈ W, ∑ i, x i * a i = 0 := by
  classical
  obtain ⟨f, hf0, hfW⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (R := F) (M := Fin 3 → F) (p := W)
      (lt_top_iff_ne_top.mpr hW) inferInstance
  refine ⟨fun i => f (fun j => if i = j then (1 : F) else 0), ?_, ?_⟩
  · intro h
    refine hf0 (LinearMap.ext fun x => ?_)
    have hz : ∀ i, f (fun j => if i = j then (1 : F) else 0) = 0 := fun i => congrFun h i
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ f x]
    exact Finset.sum_eq_zero fun i _ => by rw [hz i, smul_zero]
  · intro x hx
    have hfx : f x = 0 := by
      have hmem : f x ∈ W.map f := Submodule.mem_map_of_mem hx
      rw [hfW] at hmem
      exact Submodule.mem_bot _ |>.mp hmem
    rw [LinearMap.pi_apply_eq_sum_univ f x] at hfx
    simp only [smul_eq_mul] at hfx
    exact hfx

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The relation carried to `ℝ` by the defining embedding of `ℚ(δ)`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem real_relation_of_sum_eq_zero (m : ℤ) (d : ℕ) (a : Fin 3 → ℚ⟮δ⟯)
    (h : ∑ i, ((anchoredTriple m d i : ℚ) : ℚ⟮δ⟯) * a i = 0) :
    ((m : ℝ)) * ((a 0 : ℚ⟮δ⟯) : ℝ) + (3 / 2 : ℝ) ^ d * ((a 1 : ℚ⟮δ⟯) : ℝ)
      + ((a 2 : ℚ⟮δ⟯) : ℝ) = 0 := by
  have h2 := congrArg (fun z : ℚ⟮δ⟯ => (z : ℝ)) h
  simp only [Fin.sum_univ_three, anchoredTriple, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  push_cast at h2
  rw [show ((3 : ℚ⟮δ⟯) : ℝ) = 3 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 3,
    show ((2 : ℚ⟮δ⟯) : ℝ) = 2 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 2] at h2
  linarith [h2]

omit [NumberField ↥ℚ⟮δ⟯] in
/-- **Each of the finitely many subspaces catches only finitely many exponents**: the anchored
triples that both approximate (`|Λ| ≤ θ^d`) and lie in a fixed proper subspace form a finite
set. -/
@[category research solved, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
theorem escape_subspace_finite (hδ : Irrational δ) (b : ℕ) {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {W : Submodule ℚ⟮δ⟯ (Fin 3 → ℚ⟮δ⟯)} (hW : W ≠ ⊤) :
    {d : ℕ | 0 < d ∧
        distToNearestInt (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1)) ≤ (θ : ℝ) ^ d ∧
        (fun i ↦ ((anchoredTriple (anchoredNearest δ b d) d i : ℚ) : ℚ⟮δ⟯)) ∈ W}.Finite := by
  obtain ⟨a, ha0, harel⟩ := exists_coeffs_of_ne_top hW
  have hA : (fun i => ((a i : ℚ⟮δ⟯) : ℝ)) ≠ 0 := by
    intro h
    refine ha0 (funext fun i => ?_)
    have : ((a i : ℚ⟮δ⟯) : ℝ) = 0 := congrFun h i
    exact_mod_cast this
  refine Set.Finite.subset (escape_of_linear_relation (δ * (3 / 2 : ℝ) ^ b)
    (anchored_multiplier_irrational hδ b) hθ0 hθ1 (fun d => anchoredNearest δ b d)
    (fun i => ((a i : ℚ⟮δ⟯) : ℝ)) hA) ?_
  rintro d ⟨hd, hdist, hmem⟩
  refine ⟨hd, ?_, ?_⟩
  · rw [← abs_anchoredDefect_nearest δ b d] at hdist
    exact hdist
  · exact real_relation_of_sum_eq_zero δ _ d a (harel _ hmem)

end Subspace

/-! ## The wall below the threshold -/

section Wall

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

/-- The geometric ratio of the anchored approximation product:
`ρ = (4θ/9)·(2/3)^{n_∞−1}/12^D`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
noncomputable def escapeBase (θ : ℚ) : ℝ :=
  (4 * (θ : ℝ) / 9) * (2 / 3 : ℝ) ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) - 1)
    / 12 ^ Module.finrank ℚ ℚ⟮δ⟯

/-- The gate quantity of the endgame: the Subspace hypothesis holds for all large `d` exactly
when `RB.escapeRatio δ θ ε < 1`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
noncomputable def escapeRatio (θ : ℚ) (ε : ℝ) : ℝ :=
  escapeBase δ θ * (3:ℝ) ^ ((Module.finrank ℚ ℚ⟮δ⟯ : ℝ) * (3 + ε))

/-- The geometric ratio is nonnegative. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem escapeBase_nonneg {θ : ℚ} (hθ0 : 0 < θ) : 0 ≤ escapeBase δ θ := by
  have : (0:ℝ) ≤ (θ : ℝ) := by exact_mod_cast hθ0.le
  unfold escapeBase
  positivity

/-- **The wall below the gate** ([B1E2a2] §7 WP-G, bill item 3): if the gate
`RB.escapeRatio δ θ ε < 1` holds for some `ε > 0`, then only finitely many `d` bring
`δ(3/2)^b((3/2)^d − 1)` within `θ^d` of an integer.  Large `d` satisfy the Subspace hypothesis
(`RB.explicit_le_pow`, `RB.pow_le_rpow_target`), the Subspace Theorem confines their triples to
finitely many proper subspaces (`RB.anchored_rehearsal_defect`), and each subspace catches only
finitely many `d` (`RB.escape_subspace_finite`). -/
@[category research solved, AMS 11, ref "Schmidt91" "NKR25" "B1E2a2", group "rb_anchored"]
theorem inhomOnePower_of_gate (hδ : Irrational δ) (b : ℕ) {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ε : ℝ} (hε : 0 < ε) (hgate : escapeRatio δ θ ε < 1) :
    {d : ℕ | 0 < d ∧
      distToNearestInt (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1)) ≤ (θ : ℝ) ^ d}.Finite := by
  classical
  obtain ⟨T, hT, hsol⟩ := anchored_rehearsal_defect δ ε hε b
  have hC1 : (1:ℝ) ≤ |δ * (3 / 2 : ℝ) ^ b| + 1 := by
    have := abs_nonneg (δ * (3 / 2 : ℝ) ^ b)
    linarith
  obtain ⟨N, hN⟩ := exists_pow_mul_le_one (ρ := escapeBase δ θ) (C := |δ * (3 / 2 : ℝ) ^ b| + 1)
    (D := Module.finrank ℚ ℚ⟮δ⟯) (ε := ε) hC1 hgate (escapeBase_nonneg δ hθ0)
  refine Set.Finite.subset (Set.Finite.union (Set.finite_Iio N)
    (Set.Finite.biUnion T.finite_toSet fun W hW =>
      escape_subspace_finite δ hδ b hθ0 hθ1 (hT W hW))) ?_
  rintro d ⟨hd, hdist⟩
  rcases lt_or_ge d N with hdN | hdN
  · exact Or.inl hdN
  refine Or.inr ?_
  have hΛ : |anchoredDefect δ b (anchoredNearest δ b d) d| ≤ (θ : ℝ) ^ d := by
    rw [abs_anchoredDefect_nearest]
    exact hdist
  have hM0 : (0:ℝ) < max (|((anchoredNearest δ b d : ℤ) : ℝ)| * 2 ^ d) (3 ^ d) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hθ0' : (0:ℝ) ≤ (θ : ℝ) := by exact_mod_cast hθ0.le
  have hle := (explicit_le_pow (Λ := anchoredDefect δ b (anchoredNearest δ b d) d) hθ0'
      (anchoredNearest δ b d) d (Fintype.card (InfinitePlace ℚ⟮δ⟯) - 1)
      (Module.finrank ℚ ℚ⟮δ⟯) hΛ).trans
    (pow_le_rpow_target (escapeBase_nonneg δ hθ0) hε.le hC1 hM0
      (anchoredNearest_max_le δ b d) (hN d hdN))
  obtain ⟨W, hWT, hWmem⟩ := hsol (anchoredNearest δ b d) d hle
  exact Set.mem_biUnion hWT ⟨hd, hdist, hWmem⟩

/-- The gate in closed form: `ρ·3^{3D}·(3/2)^{n_∞+1} = θ·(3/2)^{2D}`.  Dividing by the positive
factor `(3/2)^{n_∞+1}` turns `RB.escapeRatio δ θ 0 < 1` into `θ < (3/2)^{n_∞+1−2D}`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem escapeBase_mul_pow_eq (θ : ℚ) {k : ℕ}
    (hk : Fintype.card (InfinitePlace ℚ⟮δ⟯) = k + 1) :
    escapeBase δ θ * 3 ^ (3 * Module.finrank ℚ ℚ⟮δ⟯)
        * (3 / 2 : ℝ) ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) + 1)
      = (θ : ℝ) * (3 / 2 : ℝ) ^ (2 * Module.finrank ℚ ℚ⟮δ⟯) := by
  set D := Module.finrank ℚ ℚ⟮δ⟯
  rw [escapeBase, hk]
  simp only [Nat.add_sub_cancel]
  have h12 : (0:ℝ) < 12 ^ D := by positivity
  have hkk : ((2:ℝ) / 3) ^ k * ((3:ℝ) / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
  have h27 : (3:ℝ) ^ (3 * D) = 27 ^ D := by rw [pow_mul]; norm_num
  have h94 : ((3:ℝ) / 2) ^ (2 * D) = (9 / 4 : ℝ) ^ D := by rw [pow_mul]; norm_num
  have hdiv : (27:ℝ) ^ D / 12 ^ D = (9 / 4 : ℝ) ^ D := by rw [← div_pow]; norm_num
  calc (4 * (θ : ℝ) / 9) * (2 / 3 : ℝ) ^ k / 12 ^ D * 3 ^ (3 * D) * (3 / 2 : ℝ) ^ (k + 1 + 1)
      = (4 * (θ : ℝ) / 9) * ((2 / 3 : ℝ) ^ k * (3 / 2 : ℝ) ^ k) * ((3:ℝ) ^ (3 * D) / 12 ^ D)
          * (3 / 2 : ℝ) ^ 2 := by
        rw [show k + 1 + 1 = k + 2 from rfl, pow_add]
        field_simp
    _ = (4 * (θ : ℝ) / 9) * 1 * ((27:ℝ) ^ D / 12 ^ D) * (9 / 4 : ℝ) := by
        rw [hkk, h27]; norm_num
    _ = (θ : ℝ) * (9 / 4 : ℝ) ^ D := by rw [hdiv]; ring
    _ = (θ : ℝ) * (3 / 2 : ℝ) ^ (2 * D) := by rw [h94]

/-- Below the threshold there is an admissible `ε`: continuity of `ε ↦ 3^{Dε}` at `0`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem exists_eps_escapeRatio_lt_one {θ : ℚ}
    (hthr : (θ : ℝ) * (3 / 2 : ℝ) ^ (2 * Module.finrank ℚ ℚ⟮δ⟯)
      < (3 / 2 : ℝ) ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) + 1)) :
    ∃ ε > (0:ℝ), escapeRatio δ θ ε < 1 := by
  obtain ⟨v₀, -⟩ := realPlace_isInfinitePlace δ
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card (InfinitePlace ℚ⟮δ⟯) = k + 1 :=
    ⟨Fintype.card (InfinitePlace ℚ⟮δ⟯) - 1,
      (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.mpr ⟨v₀⟩)).symm⟩
  set D := Module.finrank ℚ ℚ⟮δ⟯ with hD
  set n := Fintype.card (InfinitePlace ℚ⟮δ⟯) with hn
  -- the `ε = 0` gate
  have hpos : (0:ℝ) < (3 / 2 : ℝ) ^ (n + 1) := by positivity
  have hρ₀ : escapeBase δ θ * 3 ^ (3 * D) < 1 := by
    have hid := escapeBase_mul_pow_eq δ θ hk
    rw [← hn, ← hD] at hid
    nlinarith [hid, hpos, hthr]
  -- absorb the `ε`-factor by continuity
  have hcont : ContinuousAt
      (fun t : ℝ => (escapeBase δ θ * 3 ^ (3 * D)) * (3:ℝ) ^ ((D : ℝ) * t)) 0 := by
    fun_prop (disch := norm_num)
  have hev : ∀ᶠ t in nhds (0:ℝ),
      (escapeBase δ θ * 3 ^ (3 * D)) * (3:ℝ) ^ ((D : ℝ) * t) < 1 := by
    refine hcont.eventually_lt_const ?_
    simpa using hρ₀
  obtain ⟨t, ht1, ht2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0))).exists
  refine ⟨t, ht2, ?_⟩
  have hsplit : (3:ℝ) ^ ((D : ℝ) * (3 + t)) = 3 ^ (3 * D) * (3:ℝ) ^ ((D : ℝ) * t) := by
    rw [show (D : ℝ) * (3 + t) = ((3 * D : ℕ) : ℝ) + (D : ℝ) * t by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_natCast]
  rw [escapeRatio, ← hD, hsplit, ← mul_assoc]
  exact ht1

/-- **The anchored wall below the threshold** ([B1E2a2] §7 WP-G, bill item 3): for an algebraic
irrational `δ` and every scale `θ` with

  `θ · (3/2)^{2[ℚ(δ):ℚ]} < (3/2)^{n_∞+1}`,

only finitely many `d` bring `δ(3/2)^b((3/2)^d − 1)` within `θ^d` of an integer.  This is
`RB.InhomOnePower` restricted to the scales below `(3/2)^{n_∞+1−2D}`; the restriction is real —
see the module doc — and it is the form `RB.anchoredViolators_finite_of_wall` consumes. -/
@[category research solved, AMS 11, ref "Schmidt91" "NKR25" "B1E2a2", group "rb_anchored"]
theorem inhomOnePower_of_lt_threshold (hδ : Irrational δ) (b : ℕ) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hthr : (θ : ℝ) * (3 / 2 : ℝ) ^ (2 * Module.finrank ℚ ℚ⟮δ⟯)
      < (3 / 2 : ℝ) ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) + 1)) :
    {d : ℕ | 0 < d ∧
      distToNearestInt (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1)) ≤ (θ : ℝ) ^ d}.Finite := by
  obtain ⟨ε, hε, hgate⟩ := exists_eps_escapeRatio_lt_one δ hthr
  exact inhomOnePower_of_gate δ hδ b hθ0 hθ1 hε hgate

/-- **The threshold never exceeds `2/3` for an algebraic irrational `δ`**: `n_∞ ≤ D` always, so
`D ≥ 2` (which irrationality of `δ` forces) gives `n_∞ + 1 ≤ 2D − 1`, i.e. the admissible scales
are confined to `θ < 2/3`.  This is the exact cost of running the argument over `ℚ(δ)` rather
than over `ℚ`, and it is why `RB.InhomOnePower` (all `θ < 1`) is out of reach here. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem lt_two_thirds_of_lt_threshold (hD : 2 ≤ Module.finrank ℚ ℚ⟮δ⟯) {θ : ℚ}
    (hthr : (θ : ℝ) * (3 / 2 : ℝ) ^ (2 * Module.finrank ℚ ℚ⟮δ⟯)
      < (3 / 2 : ℝ) ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) + 1)) :
    (θ : ℝ) < 2 / 3 := by
  set D := Module.finrank ℚ ℚ⟮δ⟯ with hDdef
  set n := Fintype.card (InfinitePlace ℚ⟮δ⟯) with hndef
  have hnD : n ≤ D := by
    have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := ℚ⟮δ⟯)
    have h2 := InfinitePlace.card_add_two_mul_card_eq_rank (K := ℚ⟮δ⟯)
    rw [← hDdef] at h2
    omega
  have hle : (3 / 2 : ℝ) ^ (n + 1) ≤ (3 / 2 : ℝ) ^ (2 * D - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hsplit : (3 / 2 : ℝ) ^ (2 * D) = (3 / 2 : ℝ) ^ (2 * D - 1) * (3 / 2) := by
    rw [← pow_succ]
    congr 1
    omega
  have hpos : (0:ℝ) < (3 / 2 : ℝ) ^ (2 * D - 1) := by positivity
  nlinarith [hthr, hle, hsplit, hpos]

/-- The threshold made concrete for a **real quadratic** `ℚ(δ)` (`D = n_∞ = 2`): every scale
`θ < 2/3` is admissible, and by `RB.lt_two_thirds_of_lt_threshold` none above it is. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem lt_threshold_of_quadratic {θ : ℚ} (hD : Module.finrank ℚ ℚ⟮δ⟯ = 2)
    (hn : Fintype.card (InfinitePlace ℚ⟮δ⟯) = 2) (hθ : (θ : ℝ) < 2 / 3) :
    (θ : ℝ) * (3 / 2 : ℝ) ^ (2 * Module.finrank ℚ ℚ⟮δ⟯)
      < (3 / 2 : ℝ) ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) + 1) := by
  rw [hD, hn]
  norm_num
  linarith

/-- **The anchored family is finite below the threshold**: combining
`RB.inhomOnePower_of_lt_threshold` at each of the `B+1` anchors with the per-scale reduction
`RB.anchoredViolators_finite_of_wall`.  This is the anchored analogue of the RPF conclusion, at
every geometric scale the degree of `ℚ(δ)` allows. -/
@[category research solved, AMS 11, ref "Schmidt91" "NKR25" "B1E2a2", group "rb_anchored"]
theorem anchoredViolators_finite_of_lt_threshold (hδ : Irrational δ) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hthr : (θ : ℝ) * (3 / 2 : ℝ) ^ (2 * Module.finrank ℚ ℚ⟮δ⟯)
      < (3 / 2 : ℝ) ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) + 1)) (B : ℕ) :
    (anchoredViolators δ θ B).Finite :=
  anchoredViolators_finite_of_wall δ hθ0 hθ1 B
    (fun b _ => inhomOnePower_of_lt_threshold δ hδ b hθ0 hθ1 hthr)

end Wall

end RB
