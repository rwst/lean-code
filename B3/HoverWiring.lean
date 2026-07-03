import B3.PlaceTwoProduct
import B3.BlockConstruction
import BL.ConjugacyMap
import Mathlib.NumberTheory.Padics.WithVal
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function Filter

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem hover_place_two_of_ratInt (n : ℤ) {x : ℤ_[2]} (hx : x ∈ RatInt)
    (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    ∃ D P : ℤ, Odd D ∧
      (∏ i : Fin 3, Rat.AbsoluteValue.padic 2 (placeForms n i (placePoint (D : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint (D : ℚ) (P : ℚ) j))) ≤ r := by
  obtain ⟨q, hq⟩ := hx
  have hDodd : Odd ((q.den : ℤ)) := ratInt_odd_den q hq
  have hDq : ((q.den : ℤ) : ℚ) * q = -((-q.num : ℤ) : ℚ) := by
    push_cast; rw [mul_comm, Rat.mul_den_eq_num]; ring
  refine ⟨(q.den : ℤ), -q.num, hDodd, ?_⟩
  exact placeFactor_le_of_ratInt n ((q.den : ℤ) : ℚ) ((-q.num : ℤ) : ℚ) q hDq
    (padicTwo_odd_eq_one (q.den : ℤ) hDodd) (padicTwo_intCast_le_one (-q.num)) hq r hbound

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem conditionStar_place_two_hover {v : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2]))
    {w : ℝ} (hw : 1 < w) (hCS : ConditionStar w (binaryDigit v)) :
    ∃ (D P : ℕ → ℤ) (N : ℕ → ℕ), Tendsto N atTop atTop ∧ (∀ m, Odd (D m)) ∧
      ∀ m, (∏ i : Fin 3, Rat.AbsoluteValue.padic 2
          (placeForms (n : ℤ) i (placePoint (D m : ℚ) (P m : ℚ))) /
          (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint (D m : ℚ) (P m : ℚ) j)))
        ≤ (2 : ℝ) ^ (-(N m : ℤ)) := by
  obtain ⟨α, N, hN, hRat, hbound, _⟩ := conditionStar_tooWellApproximated hv hw hCS
  have hext : ∀ m, ∃ D P : ℤ, Odd D ∧
      (∏ i : Fin 3, Rat.AbsoluteValue.padic 2 (placeForms (n : ℤ) i (placePoint (D : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint (D : ℚ) (P : ℚ) j))) ≤ (2 : ℝ) ^ (-(N m : ℤ)) := by
    intro m
    refine hover_place_two_of_ratInt (n : ℤ) (hRat m) _ ?_
    rw [Int.cast_natCast]
    exact hbound m
  choose D P hDodd hfac using hext
  exact ⟨D, P, N, hN, hDodd, hfac⟩

end B3
