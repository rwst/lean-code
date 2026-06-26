/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.HoverWiring
import Mathlib.LinearAlgebra.Dual.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The archimedean (`∞`-place) factor of the `Φ`-side Subspace product (Route (i))

This file discharges the **last plumbing piece** of `hover`
([[b3-automatic-cc-corpus-root]], `B3.subspace_contradiction_of_rate`): the archimedean factor of the
Subspace product. At the `∞`-place Adamczewski–Bugeaud use the **coordinate forms** `(x, y, z)`, and for
those the factor is bounded by `1` — so it contributes no gain (all the over-approximation is at the
place `2`, `B3.PlaceTwoProduct`), and the full two-place product is bounded by the place-`2` factor alone.

## The `∞`-place bound

`infFactor_le_one`: for **any** absolute value `v` and the coordinate forms `coordForms = (proj₀, proj₁,
proj₂)`, the factor

> `∏ᵢ v(xᵢ) / (⨆ⱼ v(xⱼ)) ≤ 1`

since each term `v(xᵢ)/(⨆ⱼ v(xⱼ)) ≤ 1` (the numerator is one of the terms of the supremum). So the
archimedean factor is `O(1)` — in fact `≤ 1`.

## Assembling the two-place product

`twoPlace_product_le`: for a two-element place set `{v∞, v₂}` with coordinate forms at `v∞`, the Subspace
product `∏_{v∈{v∞,v₂}} ∏ᵢ v(Lᵢ,ᵥ(x))/|x|ᵥ` is `≤` the place-`v₂` factor (the `∞`-factor `≤ 1` is absorbed,
`Finset.prod_pair`). Specialised to the `Φ`-side forms `phiForms n` (coordinate forms at `v∞`,
`B3.placeForms n` at `2`), `phi_twoPlace_product_le` then bounds the whole product by the place-`2` factor;
and `conditionStar_hover` traces this back to the construction: from `Φ v = n` and `ConditionStar`, the
**full two-place Subspace product** is `≤ 2^{−Nₖ}` with `Nₖ → ∞`. This is exactly `hover` over the place
set `S = {v∞, 2}`.

## What remains

The product bound is now complete. To plug into `B3.subspace_contradiction_of_rate` literally, two things
remain (both flagged before): identifying `v∞`/`Rat.AbsoluteValue.padic 2` as the `archAbsVal`/
`nonarchAbsVal` representatives of `subspace_theorem_E`'s place set (Mathlib `IsFinitePlace` plumbing), and
the height bridge `Height.mulHeight xₖ ≤ 3^{cₖ}` so the height-vs-rate estimate (`B3.HeightVsRate`, proved
against `3^c`) applies to the *real* height. Neither is the `∞`-factor; the genuinely open input remains
non-confinement (`B3.phiPoints_nonConfined`).

No new `axiom`s.

## Contents
* `coordForms`, `coordForms_linearIndependent` — the `∞`-place coordinate forms and their rank `3`.
* `infFactor_le_one` — the archimedean factor is `≤ 1`.
* `twoPlace_product_le` — the two-place product `≤` the place-`2` factor.
* `phiForms`, `phi_twoPlace_product_le`, `conditionStar_hover` — the `Φ`-side specialisation and the full
  two-place `hover` traced to the construction.
* `infFactor_le_invSup`, `twoPlace_product_le_invSup`, `phi_twoPlace_product_le_invSup` — the **sharpened**
  archimedean factor `≤ (⨆ⱼ v xⱼ)⁻¹` (using the `−1` middle coordinate) and its two-place propagation —
  the arch-saving `H⁻¹` of `B3.subspace_contradiction_of_rate_sharp` (Tier 2.1).

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6: the trivial `∞`-place forms in the Subspace application).
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311 (the height-normalised Subspace inequality, all places).
-/

namespace B3

open Function Filter

open scoped Classical

/-! ### The `∞`-place coordinate forms -/

/-- The **coordinate forms** `(x, y, z) = (proj₀, proj₁, proj₂)` — the trivial linear forms
Adamczewski–Bugeaud use at the archimedean place. -/
noncomputable def coordForms : Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) := fun i => LinearMap.proj i

/-- **The coordinate forms have rank `3` (proved).** `coordForms` is `ℚ`-linearly independent (it is the
dual of the standard basis) — the rank hypothesis `subspace_theorem_E` needs at the `∞`-place. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem coordForms_linearIndependent : LinearIndependent ℚ coordForms := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun (congrArg DFunLike.coe hg) (Pi.single i 1)
  simpa [coordForms, Finset.sum_apply, Pi.single_apply] using h

/-! ### The archimedean factor is `≤ 1` -/

/-- **The archimedean factor is `≤ 1` (proved).** For any absolute value `v` and the coordinate forms, the
place-`v` factor `∏ᵢ v(xᵢ) / (⨆ⱼ v(xⱼ)) ≤ 1`: each term `v(xᵢ) / (⨆ⱼ v(xⱼ)) ≤ 1` because `v(xᵢ)` is one of
the suprema's terms (and the `⨆ = 0` case is vacuous, `v(xᵢ)/0 = 0`). So the `∞`-place contributes no gain
to the Subspace product. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem infFactor_le_one (v : AbsoluteValue ℚ ℝ) (x : Fin 3 → ℚ) :
    (∏ i, v (coordForms i x) / (⨆ j, v (x j))) ≤ 1 := by
  apply Finset.prod_le_one
  · intro i _
    exact div_nonneg (v.nonneg _) (Real.iSup_nonneg (fun j => v.nonneg _))
  · intro i _
    have hSnn : (0 : ℝ) ≤ ⨆ j, v (x j) := Real.iSup_nonneg (fun j => v.nonneg _)
    rcases eq_or_lt_of_le hSnn with h | h
    · rw [← h, div_zero]; exact zero_le_one
    · rw [div_le_one h]
      show v (x i) ≤ ⨆ j, v (x j)
      exact le_ciSup_of_le (Set.finite_range _).bddAbove i le_rfl

/-! ### The two-place product -/

/-- **The two-place product is bounded by the place-`v₂` factor (proved).** For a two-element place set
`{v∞, v₂}` (`v∞ ≠ v₂`) whose forms at `v∞` are the coordinate forms (`hLinf`), the Subspace product
`∏_{v∈{v∞,v₂}} ∏ᵢ v(Lᵢ,ᵥ(x))/|x|ᵥ` is `≤` the place-`v₂` factor: the product splits
(`Finset.prod_pair`), and the `∞`-factor `≤ 1` (`infFactor_le_one`) is absorbed. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem twoPlace_product_le (vinf v2 : AbsoluteValue ℚ ℝ) (hne : vinf ≠ v2)
    (L : AbsoluteValue ℚ ℝ → Fin 3 → Module.Dual ℚ (Fin 3 → ℚ)) (hLinf : L vinf = coordForms)
    (x : Fin 3 → ℚ) (r : ℝ)
    (h2 : (∏ i, v2 (L v2 i x) / (⨆ j, v2 (x j))) ≤ r) :
    (∏ v ∈ {vinf, v2}, ∏ i, v (L v i x) / (⨆ j, v (x j))) ≤ r := by
  rw [Finset.prod_pair hne]
  have hinf : (∏ i, vinf (L vinf i x) / (⨆ j, vinf (x j))) ≤ 1 := by
    rw [hLinf]; exact infFactor_le_one vinf x
  have h2nn : 0 ≤ (∏ i, v2 (L v2 i x) / (⨆ j, v2 (x j))) :=
    Finset.prod_nonneg fun i _ => div_nonneg (v2.nonneg _) (Real.iSup_nonneg fun j => v2.nonneg _)
  calc (∏ i, vinf (L vinf i x) / (⨆ j, vinf (x j))) * (∏ i, v2 (L v2 i x) / (⨆ j, v2 (x j)))
      ≤ 1 * r := mul_le_mul hinf h2 h2nn zero_le_one
    _ = r := one_mul r

/-! ### The `Φ`-side specialisation and the full two-place `hover` -/

/-- The **`Φ`-side place-dependent forms**: the place-`2` forms `placeForms n` at the `2`-adic place, and
the coordinate forms `coordForms` at every other place (in particular the archimedean `v∞`). -/
noncomputable def phiForms (n : ℤ) : AbsoluteValue ℚ ℝ → Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) :=
  fun v => if v = Rat.AbsoluteValue.padic 2 then placeForms n else coordForms

/-- **The `Φ`-side two-place product is bounded by the place-`2` factor (proved).** With `phiForms n`
(coordinate forms at `v∞ ≠ 2`, `placeForms n` at `2`), the Subspace product over `{v∞, 2}` is `≤` the
place-`2` factor of `placeForms n`. (`twoPlace_product_le`, unfolding `phiForms`.) -/
@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem phi_twoPlace_product_le (vinf : AbsoluteValue ℚ ℝ)
    (hne : vinf ≠ Rat.AbsoluteValue.padic 2) (n : ℤ) (x : Fin 3 → ℚ) (r : ℝ)
    (h2 : (∏ i, Rat.AbsoluteValue.padic 2 (placeForms n i x) /
      (⨆ j, Rat.AbsoluteValue.padic 2 (x j))) ≤ r) :
    (∏ v ∈ {vinf, Rat.AbsoluteValue.padic 2},
        ∏ i, v (phiForms n v i x) / (⨆ j, v (x j))) ≤ r := by
  refine twoPlace_product_le vinf (Rat.AbsoluteValue.padic 2) hne (phiForms n) ?_ x r ?_
  · show (if vinf = Rat.AbsoluteValue.padic 2 then placeForms n else coordForms) = coordForms
    rw [if_neg hne]
  · have : phiForms n (Rat.AbsoluteValue.padic 2) = placeForms n := if_pos rfl
    rw [this]; exact h2

/-! ### The sharpened archimedean factor (`≤ H⁻¹`, the arch-saving)

The bound `infFactor_le_one` (`≤ 1`) *discards* the archimedean contribution. But the Subspace point
`(D, −1, P)` has a `−1` middle coordinate, and for the **coordinate forms** the middle factor is exactly
`v(−1)/(⨆ⱼ v(xⱼ)) = 1/(⨆ⱼ v(xⱼ))` while the outer two factors are `≤ 1`. So the archimedean factor is in
fact `≤ (⨆ⱼ v(xⱼ))⁻¹`, and at the archimedean place `⨆ⱼ v(xⱼ) = H(x)` (the finite local heights are `1`,
`B3.sup_vinf_placePoint_eq_mulHeight`). Threading this `H⁻¹` through the two-place product lets the
height-vs-rate input drop one power of `H` — the threshold `τ: 3 → 2` of
`B3.subspace_contradiction_of_rate_sharp` (Tier 2.1 of `B3/plan2.md`). -/

/-- **The archimedean factor is `≤ (⨆ⱼ v xⱼ)⁻¹` (proved, the arch-saving).** When the middle coordinate is
`x 1 = −1`, the place-`v` factor of the coordinate forms is `≤ (⨆ⱼ v(xⱼ))⁻¹`: the middle factor is exactly
`v(−1)/(⨆ⱼ v(xⱼ)) = (⨆ⱼ v(xⱼ))⁻¹`, and the two outer factors `v(x₀)/(⨆), v(x₂)/(⨆)` are each `≤ 1`. This
sharpens `infFactor_le_one` (`≤ 1`): the `−1` coordinate that was placed for general position *is* a free
factor of `(⨆ⱼ v(xⱼ))⁻¹`, recovered here. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem infFactor_le_invSup (v : AbsoluteValue ℚ ℝ) (x : Fin 3 → ℚ) (hx1 : x 1 = -1) :
    (∏ i, v (coordForms i x) / (⨆ j, v (x j))) ≤ (⨆ j, v (x j))⁻¹ := by
  set S : ℝ := ⨆ j, v (x j) with hS
  have hSnn : (0 : ℝ) ≤ S := Real.iSup_nonneg fun j => v.nonneg _
  have hv1 : v (x 1) = 1 := by rw [hx1]; simp
  have hSpos : 0 < S := by
    have : (1 : ℝ) ≤ S := by rw [← hv1]; exact le_ciSup_of_le (Set.finite_range _).bddAbove 1 le_rfl
    linarith
  have hle : ∀ i, v (x i) ≤ S := fun i => le_ciSup_of_le (Set.finite_range _).bddAbove i le_rfl
  have e : ∀ i, coordForms i x = x i := fun i => rfl
  simp only [e]
  rw [Fin.prod_univ_three]
  have h0 : v (x 0) / S ≤ 1 := by rw [div_le_one hSpos]; exact hle 0
  have h2 : v (x 2) / S ≤ 1 := by rw [div_le_one hSpos]; exact hle 2
  have hmid : v (x 1) / S = S⁻¹ := by rw [hv1, inv_eq_one_div]
  have hnn2 : 0 ≤ v (x 2) / S := div_nonneg (v.nonneg _) hSnn
  rw [hmid]
  nlinarith [inv_nonneg.mpr hSnn, h0, h2, mul_le_one₀ h0 hnn2 h2]

/-- **The sharpened two-place product (proved, the arch-saving).** As `twoPlace_product_le`, but with the
`−1` middle coordinate (`hx1`) the `∞`-factor `≤ (⨆ⱼ vinf(xⱼ))⁻¹` (`infFactor_le_invSup`) is retained
rather than discarded: the two-place product is `≤ (⨆ⱼ vinf(xⱼ))⁻¹ · r`. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem twoPlace_product_le_invSup (vinf v2 : AbsoluteValue ℚ ℝ) (hne : vinf ≠ v2)
    (L : AbsoluteValue ℚ ℝ → Fin 3 → Module.Dual ℚ (Fin 3 → ℚ)) (hLinf : L vinf = coordForms)
    (x : Fin 3 → ℚ) (hx1 : x 1 = -1) (r : ℝ)
    (h2 : (∏ i, v2 (L v2 i x) / (⨆ j, v2 (x j))) ≤ r) :
    (∏ v ∈ {vinf, v2}, ∏ i, v (L v i x) / (⨆ j, v (x j))) ≤ (⨆ j, vinf (x j))⁻¹ * r := by
  rw [Finset.prod_pair hne]
  have hinf : (∏ i, vinf (L vinf i x) / (⨆ j, vinf (x j))) ≤ (⨆ j, vinf (x j))⁻¹ := by
    rw [hLinf]; exact infFactor_le_invSup vinf x hx1
  exact mul_le_mul hinf h2
    (Finset.prod_nonneg fun i _ => div_nonneg (v2.nonneg _) (Real.iSup_nonneg fun j => v2.nonneg _))
    (inv_nonneg.mpr (Real.iSup_nonneg fun j => vinf.nonneg _))

/-- **The `Φ`-side sharpened two-place product (proved, the arch-saving).** As `phi_twoPlace_product_le`,
but with the `−1` middle coordinate (`hx1`) the `∞`-factor `≤ (⨆ⱼ vinf(xⱼ))⁻¹` is retained: the product
over `{v∞, 2}` is `≤ (⨆ⱼ vinf(xⱼ))⁻¹ · r`. After `B3.sup_vinf_placePoint_eq_mulHeight` identifies
`⨆ⱼ vinf(xⱼ) = H(x)`, this is the sharpened `hover` (`≤ H⁻¹ · 2^{−Nₖ}`) that
`B3.subspace_contradiction_of_rate_sharp` consumes. -/
@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem phi_twoPlace_product_le_invSup (vinf : AbsoluteValue ℚ ℝ)
    (hne : vinf ≠ Rat.AbsoluteValue.padic 2) (n : ℤ) (x : Fin 3 → ℚ) (hx1 : x 1 = -1) (r : ℝ)
    (h2 : (∏ i, Rat.AbsoluteValue.padic 2 (placeForms n i x) /
      (⨆ j, Rat.AbsoluteValue.padic 2 (x j))) ≤ r) :
    (∏ v ∈ {vinf, Rat.AbsoluteValue.padic 2},
        ∏ i, v (phiForms n v i x) / (⨆ j, v (x j))) ≤ (⨆ j, vinf (x j))⁻¹ * r := by
  refine twoPlace_product_le_invSup vinf (Rat.AbsoluteValue.padic 2) hne (phiForms n) ?_ x hx1 r ?_
  · show (if vinf = Rat.AbsoluteValue.padic 2 then placeForms n else coordForms) = coordForms
    rw [if_neg hne]
  · have : phiForms n (Rat.AbsoluteValue.padic 2) = placeForms n := if_pos rfl
    rw [this]; exact h2

/-- **The full two-place `hover`, traced to the construction (capstone, proved).** Given an archimedean
place `v∞ ≠ 2` and the construction data (`Φ v = n`, `ConditionStar w`, `w > 1`), there is a family of
odd-denominator points `placePoint (D m) (P m)` and window lengths `N m → ∞` such that the **full Subspace
product** over `{v∞, 2}` with the `Φ`-side forms is `≤ 2^{−N m}`. *Proof:* `conditionStar_place_two_hover`
gives the place-`2` factors `≤ 2^{−N m}`; `phi_twoPlace_product_le` absorbs the `∞`-factor `≤ 1`.

This is `hover` (the over-approximation input of `B3.subspace_contradiction_of_rate`) over the place set
`S = {v∞, 2}`, now fully proved and traced to the construction — modulo only identifying `S` with
`subspace_theorem_E`'s `archAbsVal`/`nonarchAbsVal` places and the height bridge. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem conditionStar_hover (vinf : AbsoluteValue ℚ ℝ) (hne : vinf ≠ Rat.AbsoluteValue.padic 2)
    {v : ℤ_[2]} {n : ℕ} (hv : BL.Φ v = (n : ℤ_[2])) {w : ℝ} (hw : 1 < w)
    (hCS : AB.ConditionStar w (binaryDigit v)) :
    ∃ (D P : ℕ → ℤ) (N : ℕ → ℕ), Tendsto N atTop atTop ∧ (∀ m, Odd (D m)) ∧
      ∀ m, (∏ v' ∈ {vinf, Rat.AbsoluteValue.padic 2},
          ∏ i, v' (phiForms (n : ℤ) v' i (placePoint (D m : ℚ) (P m : ℚ))) /
            (⨆ j, v' (placePoint (D m : ℚ) (P m : ℚ) j))) ≤ (2 : ℝ) ^ (-(N m : ℤ)) := by
  obtain ⟨D, P, N, hN, hDodd, hfac⟩ := conditionStar_place_two_hover hv hw hCS
  exact ⟨D, P, N, hN, hDodd, fun m => phi_twoPlace_product_le vinf hne (n : ℤ) _ _ (hfac m)⟩

end B3
