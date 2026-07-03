import B3.HoverWiring
import Mathlib.LinearAlgebra.Dual.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open Function Filter

open scoped Classical

noncomputable def coordForms : Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) := fun i => LinearMap.proj i

@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem coordForms_linearIndependent : LinearIndependent ℚ coordForms := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun (congrArg DFunLike.coe hg) (Pi.single i 1)
  simpa [coordForms, Finset.sum_apply, Pi.single_apply] using h

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

noncomputable def phiForms (n : ℤ) : AbsoluteValue ℚ ℝ → Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) :=
  fun v => if v = Rat.AbsoluteValue.padic 2 then placeForms n else coordForms

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
