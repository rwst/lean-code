/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Anchored
import ForMathlib.NumberTheory.HeightExtension
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The height of the anchored Subspace triple over `ℚ(δ)` (report B1E2a-v2, WP-G bill item 2)

`RB/Anchored.lean` instantiates `Subspace.evertseSchlickewei` at the field `ℚ⟮δ⟯` and the forms
`RB.nkForms` (`RB.anchored_rehearsal`).  Its conclusion is quantified over *all* nonzero
`x : Fin 3 → ℚ⟮δ⟯` satisfying

  `Subspace.approxProduct S L x ≤ Height.mulHeight x ^ (−3 − ε)`,

whereas the derivation feeds it the **rational** triples `x = (m, (3/2)^d, 1)` coming from the
inhomogeneous one-power problem `‖δ_b((3/2)^d − 1)‖ ≤ θ^d` (`RB.InhomOnePower`).  Turning the
abstract right-hand side into a number therefore needs the height of a rational triple
*computed in `ℚ⟮δ⟯`* — the second item of the WP-G gate bill, and the reason for
`ForMathlib/NumberTheory/HeightExtension.lean`: Mathlib's height is the **relative** one, so
passing from `ℚ` to a number field `K` raises it to the power `D = [K : ℚ]`
(`NumberField.mulHeight_ratCast`; in logarithmic form `h_K = D · h_ℚ`).

This file computes that height exactly and packages the rehearsal with it.

## Contents

* `RB.anchoredTriple m d = (m, (3/2)^d, 1)` over `ℚ`, and its primitive integer scaling
  `RB.anchoredTripleInt m d = (m·2^d, 3^d, 2^d)` (`RB.anchoredTripleInt_gcd`,
  `RB.anchoredTriple_eq_smul`, `RB.anchoredTriple_ne_zero`).
* **`RB.mulHeight_anchoredTriple`** — over *any* number field `K`,
  `H_K(m, (3/2)^d, 1) = max(|m|·2^d, 3^d)^{[K:ℚ]}`; `RB.logHeight_anchoredTriple` is its
  logarithmic twin and `RB.mulHeight_anchoredTriple_rat` the `ℚ`-case (`D = 1`), which is the
  naive height of the data.
* `RB.mulHeight_anchoredTriple_le` — the shape the endgame uses: if `|m| ≤ C(3/2)^d` with
  `1 ≤ C` (what "`m` is the nearest integer to `δ_b((3/2)^d − 1)`" supplies), then
  `H_K ≤ (C·3^d)^{[K:ℚ]}` — the height grows like `3^d` and no faster, so the Subspace
  exponent `−3 − ε` is worth `3^{−D(3+ε)d}`.
* **`RB.anchored_rehearsal_triple`** — `RB.anchored_rehearsal` with the height hypothesis
  replaced by the explicit numerical one
  `approxProduct ≤ max(|m|·2^d, 3^d)^{[ℚ⟮δ⟯:ℚ]·(−3−ε)}`.

Nothing here narrows the *remaining* bill: item 1 (place values of the `S`-units `2^x3^y` over
`𝓞_{ℚ(δ)}`) and item 3 (the subspace-escape endgame) are untouched, and no axiom is added —
the footprint is `std3 + Subspace.evertseSchlickewei`, inherited from `RB.anchored_rehearsal`.

## References

* [B1E2a2] `plans/report-B1E2a-v2.html` (2026-08-06): §4 N4, §6 P3, §7 WP-G (gate bill item 2).
* [Schmidt91] W. M. Schmidt, LNM 1467, Thm 1D′ — `Subspace.evertseSchlickewei`.
* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, CUP 2006, §1.5 (the
  degree-`D` normalization of the relative height).
-/

namespace RB

open Finset Height

/-! ## The triple and its primitive integer form -/

/-- The rational triple of the anchored `n = 3` Subspace application: `x = (m, (3/2)^d, 1)`,
whose distinguished form evaluates to `δ_b(3/2)^d − δ_b − m` (`RB.nkForms_apply_self` with
`γ₁ = −γ₂ = δ_b`). -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
def anchoredTriple (m : ℤ) (d : ℕ) : Fin 3 → ℚ := ![(m : ℚ), (3 / 2 : ℚ) ^ d, 1]

/-- The primitive integer representative of `RB.anchoredTriple`: clearing the denominator
`2^d` gives `(m·2^d, 3^d, 2^d)`, a coprime triple. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
def anchoredTripleInt (m : ℤ) (d : ℕ) : Fin 3 → ℤ := ![m * 2 ^ d, 3 ^ d, 2 ^ d]

/-- The integer triple is primitive: its last two entries are already coprime, whatever `m`
is.  This is what makes the finite places invisible in the height computation. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma anchoredTripleInt_gcd (m : ℤ) (d : ℕ) :
    Finset.univ.gcd (anchoredTripleInt m d) = 1 := by
  have hcop : IsCoprime ((3 : ℤ) ^ d) ((2 : ℤ) ^ d) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)).pow
  have hunit : IsUnit (Finset.univ.gcd (anchoredTripleInt m d)) := by
    refine hcop.isUnit_of_dvd' ?_ ?_
    · simpa [anchoredTripleInt] using
        Finset.gcd_dvd (f := anchoredTripleInt m d) (Finset.mem_univ (1 : Fin 3))
    · simpa [anchoredTripleInt] using
        Finset.gcd_dvd (f := anchoredTripleInt m d) (Finset.mem_univ (2 : Fin 3))
  have hnorm : normalize (Finset.univ.gcd (anchoredTripleInt m d)) = 1 :=
    normalize_eq_one.mpr hunit
  rwa [Finset.normalize_gcd] at hnorm

/-- The triple is the `(2^d)⁻¹`-multiple of its primitive integer form, in any field of
characteristic zero.  Since `Height.mulHeight` is scaling-invariant, the height computation
may be done on the integer form. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma anchoredTriple_eq_smul {K : Type*} [Field K] [CharZero K] (m : ℤ) (d : ℕ) :
    (fun i ↦ ((anchoredTriple m d i : ℚ) : K))
      = (((2 : K) ^ d)⁻¹) • (fun i ↦ ((anchoredTripleInt m d i : ℤ) : K)) := by
  have h2 : ((2 : K) ^ d) ≠ 0 := pow_ne_zero _ two_ne_zero
  funext i
  fin_cases i
  · simp only [anchoredTriple, anchoredTripleInt, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  · simp only [anchoredTriple, anchoredTripleInt, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [div_pow]
    field_simp
  · simp only [anchoredTriple, anchoredTripleInt, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp

/-- The triple is nonzero — its last coordinate is `1`.  This discharges the `x ≠ 0` side
condition of `RB.nk_subspace` / `RB.anchored_rehearsal`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma anchoredTriple_ne_zero {K : Type*} [Field K] [CharZero K] (m : ℤ) (d : ℕ) :
    (fun i ↦ ((anchoredTriple m d i : ℚ) : K)) ≠ 0 := by
  intro h
  have hc := congrFun h 2
  simp [anchoredTriple] at hc

/-! ## The height -/

/-- The maximum of the absolute values of the primitive triple is `max(|m|·2^d, 3^d)`; the
third entry `2^d` never wins. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma iSup_abs_anchoredTripleInt (m : ℤ) (d : ℕ) :
    (⨆ i, |((anchoredTripleInt m d i : ℤ) : ℝ)|) = max (|(m : ℝ)| * 2 ^ d) (3 ^ d) := by
  have h23 : (2 : ℝ) ^ d ≤ 3 ^ d := by gcongr; norm_num
  have e0 : |((anchoredTripleInt m d 0 : ℤ) : ℝ)| = |(m : ℝ)| * 2 ^ d := by
    simp only [anchoredTripleInt, Matrix.cons_val_zero]
    push_cast
    rw [abs_mul, abs_pow, abs_two]
  have e1 : |((anchoredTripleInt m d 1 : ℤ) : ℝ)| = 3 ^ d := by
    simp only [anchoredTripleInt, Matrix.cons_val_one]
    push_cast
    rw [abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
  refine le_antisymm (ciSup_le fun i ↦ ?_) (max_le ?_ ?_)
  · fin_cases i
    · simp [anchoredTripleInt, abs_mul, abs_pow]
    · simp [anchoredTripleInt, abs_pow]
    · simpa [anchoredTripleInt, abs_pow] using
        h23.trans (le_max_right (|(m : ℝ)| * 2 ^ d) ((3 : ℝ) ^ d))
  · exact Finite.le_ciSup_of_le 0 (le_of_eq e0.symm)
  · exact Finite.le_ciSup_of_le 1 (le_of_eq e1.symm)

variable {K : Type*} [Field K] [NumberField K]

/-- **The height of the anchored triple over a number field** `K` of degree `D = [K : ℚ]`:

  `H_K(m, (3/2)^d, 1) = max(|m|·2^d, 3^d)^D`.

The `D`-th power is the relative normalization of Mathlib's height
(`NumberField.mulHeight_ratCast`); over `ℚ` it disappears
(`RB.mulHeight_anchoredTriple_rat`). -/
@[category research solved, AMS 11, ref "B1E2a2" "BG06", group "rb_anchored"]
theorem mulHeight_anchoredTriple (m : ℤ) (d : ℕ) :
    mulHeight (fun i ↦ ((anchoredTriple m d i : ℚ) : K))
      = (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ Module.finrank ℚ K := by
  have h2 : (((2 : K) ^ d)⁻¹) ≠ 0 := inv_ne_zero (pow_ne_zero _ two_ne_zero)
  rw [anchoredTriple_eq_smul, mulHeight_smul_eq_mulHeight _ h2,
    NumberField.mulHeight_intCast_of_gcd_eq_one (anchoredTripleInt_gcd m d),
    iSup_abs_anchoredTripleInt]

/-- The `ℚ`-case of `RB.mulHeight_anchoredTriple`: the naive height of the triple is
`max(|m|·2^d, 3^d)`. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem mulHeight_anchoredTriple_rat (m : ℤ) (d : ℕ) :
    mulHeight (anchoredTriple m d) = max (|(m : ℝ)| * 2 ^ d) (3 ^ d) := by
  have hh := mulHeight_anchoredTriple (K := ℚ) m d
  simp only [Rat.cast_id, Module.finrank_self, pow_one] at hh
  exact hh

/-- The logarithmic form: `h_K(m, (3/2)^d, 1) = D · log max(|m|·2^d, 3^d)`. -/
@[category research solved, AMS 11, ref "B1E2a2" "BG06", group "rb_anchored"]
theorem logHeight_anchoredTriple (m : ℤ) (d : ℕ) :
    logHeight (fun i ↦ ((anchoredTriple m d i : ℚ) : K))
      = Module.finrank ℚ K * Real.log (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_anchoredTriple, Real.log_pow]

/-- The height at a real exponent, the shape in which `Subspace.evertseSchlickewei` consumes
it: `H_K(x)^r = max(|m|·2^d, 3^d)^{D·r}` (an `rpow` on the right). -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma mulHeight_anchoredTriple_rpow (m : ℤ) (d : ℕ) (r : ℝ) :
    (mulHeight (fun i ↦ ((anchoredTriple m d i : ℚ) : K))) ^ r
      = (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ ((Module.finrank ℚ K : ℝ) * r) := by
  have hM : (0 : ℝ) ≤ max (|(m : ℝ)| * 2 ^ d) (3 ^ d) :=
    le_trans (by positivity) (le_max_right _ _)
  rw [mulHeight_anchoredTriple, ← Real.rpow_natCast (max (|(m : ℝ)| * 2 ^ d) (3 ^ d))
    (Module.finrank ℚ K), ← Real.rpow_mul hM]

/-- **The height grows like `3^d`**: if the integer coordinate obeys the bound the
nearest-integer construction supplies, `|m| ≤ C(3/2)^d` with `1 ≤ C`, then
`H_K(m, (3/2)^d, 1) ≤ (C·3^d)^D`.  This is the form the subspace-escape endgame consumes:
the height of the data is controlled by the *single* parameter `d`. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem mulHeight_anchoredTriple_le {m : ℤ} {d : ℕ} {C : ℝ} (hC : 1 ≤ C)
    (hm : |(m : ℝ)| ≤ C * (3 / 2 : ℝ) ^ d) :
    mulHeight (fun i ↦ ((anchoredTriple m d i : ℚ) : K)) ≤ (C * 3 ^ d) ^ Module.finrank ℚ K := by
  rw [mulHeight_anchoredTriple]
  have hbase : max (|(m : ℝ)| * 2 ^ d) (3 ^ d) ≤ C * 3 ^ d := by
    refine max_le ?_ ?_
    · calc |(m : ℝ)| * 2 ^ d ≤ (C * (3 / 2 : ℝ) ^ d) * 2 ^ d := by gcongr
        _ = C * 3 ^ d := by
            rw [mul_assoc, div_pow, div_mul_cancel₀]
            positivity
    · nlinarith [pow_pos (show (0:ℝ) < 3 by norm_num) d]
  have h0 : (0 : ℝ) ≤ max (|(m : ℝ)| * 2 ^ d) (3 ^ d) :=
    le_trans (by positivity) (le_max_right _ _)
  gcongr

/-! ## The rehearsal with the height made explicit -/

section Rehearsal

open IntermediateField

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

/-- **The anchored rehearsal, with the height computed** ([B1E2a2] §7 WP-G, bill item 2).
`RB.anchored_rehearsal` says that the solutions of the Subspace inequality at `ℚ⟮δ⟯` lie in
finitely many proper subspaces; here the abstract bound `Height.mulHeight x ^ (−3 − ε)` is
replaced, for the rational triples `x = (m, (3/2)^d, 1)` that the anchored derivation actually
produces, by the explicit numerical bound

  `max(|m|·2^d, 3^d) ^ ([ℚ⟮δ⟯ : ℚ]·(−3 − ε))`,

the degree factor being the relative normalization of Mathlib's height.  Footprint:
`std3 + Subspace.evertseSchlickewei`, unchanged from `RB.anchored_rehearsal`. -/
@[category research solved, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_anchored"]
theorem anchored_rehearsal_triple (ε : ℝ) (hε : 0 < ε) (b : ℕ) :
    ∃ T : Finset (Submodule ℚ⟮δ⟯ (Fin 3 → ℚ⟮δ⟯)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ (m : ℤ) (d : ℕ),
        Subspace.approxProduct (anchoredPlaces δ)
            (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ))
            (fun i ↦ ((anchoredTriple m d i : ℚ) : ℚ⟮δ⟯))
          ≤ (max (|(m : ℝ)| * 2 ^ d) (3 ^ d))
              ^ ((Module.finrank ℚ ℚ⟮δ⟯ : ℝ) * (-(3 : ℝ) - ε)) →
        ∃ W ∈ T, (fun i ↦ ((anchoredTriple m d i : ℚ) : ℚ⟮δ⟯)) ∈ W := by
  obtain ⟨T, hT, hsol⟩ := anchored_rehearsal δ ε hε b
  refine ⟨T, hT, fun m d hle ↦ hsol _ (anchoredTriple_ne_zero m d) ?_⟩
  rwa [mulHeight_anchoredTriple_rpow]

end Rehearsal

end RB
