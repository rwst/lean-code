import B3.SubspaceInstantiation
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Dual.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open Function

noncomputable def placeForms (n : ℤ) : Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) :=
  ![LinearMap.proj 0, LinearMap.proj 1, (n : ℚ) • LinearMap.proj 0 + LinearMap.proj 2]

def placePoint (D P : ℚ) : Fin 3 → ℚ := ![D, -1, P]

@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem placeForms_linearIndependent (n : ℤ) : LinearIndependent ℚ (placeForms n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun (congrArg DFunLike.coe hg) (Pi.single 0 1)
  have h1 := congrFun (congrArg DFunLike.coe hg) (Pi.single 1 1)
  have h2 := congrFun (congrArg DFunLike.coe hg) (Pi.single 2 1)
  simp only [placeForms, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.zero_apply, Pi.single_eq_same, smul_eq_mul] at h0 h1 h2
  intro i
  fin_cases i <;> simp_all

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_eq (v : AbsoluteValue ℚ ℝ) (n : ℤ) (D P : ℚ) (hD : v D = 1) (hPle : v P ≤ 1) :
    (∏ i : Fin 3, v (placeForms n i (placePoint D P)) / (⨆ j, v (placePoint D P j)))
      = v ((n : ℚ) * D + P) := by
  have hneg1 : v (-1 : ℚ) = 1 := by rw [AbsoluteValue.map_neg, map_one]
  have hbound : ∀ j, v (placePoint D P j) ≤ 1 := by
    intro j
    fin_cases j
    · show v D ≤ 1; rw [hD]
    · show v (-1 : ℚ) ≤ 1; rw [hneg1]
    · show v P ≤ 1; exact hPle
  have hsup : (⨆ j, v (placePoint D P j)) = 1 := by
    apply le_antisymm (ciSup_le hbound)
    exact le_ciSup_of_le (Set.finite_range _).bddAbove 0 (le_of_eq hD.symm)
  rw [hsup]
  have e0 : placeForms n 0 (placePoint D P) = D := by simp [placeForms, placePoint]
  have e1 : placeForms n 1 (placePoint D P) = -1 := by simp [placeForms, placePoint]
  have e2 : placeForms n 2 (placePoint D P) = (n : ℚ) * D + P := by
    simp [placeForms, placePoint, smul_eq_mul]
  simp only [div_one, Fin.prod_univ_three, e0, e1, e2, hD, hneg1]
  ring

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_eq_sub (v : AbsoluteValue ℚ ℝ) (n : ℤ) (D P q : ℚ)
    (hq : D * q = -P) (hD : v D = 1) (hPle : v P ≤ 1) :
    (∏ i : Fin 3, v (placeForms n i (placePoint D P)) / (⨆ j, v (placePoint D P j)))
      = v ((n : ℚ) - q) := by
  rw [placeFactor_eq v n D P hD hPle]
  have hid : (n : ℚ) * D + P = D * ((n : ℚ) - q) := by rw [mul_sub, hq]; ring
  rw [hid, map_mul, hD, one_mul]

@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem padicTwo_intCast_le_one (z : ℤ) : Rat.AbsoluteValue.padic 2 ((z : ℤ) : ℚ) ≤ 1 :=
  Rat.AbsoluteValue.padic_le_one 2 z

@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem padicTwo_odd_eq_one (m : ℤ) (hodd : Odd m) : Rat.AbsoluteValue.padic 2 ((m : ℤ) : ℚ) = 1 := by
  have h2 : ¬ (2 : ℤ) ∣ m := Int.two_dvd_ne_zero.mpr (Int.odd_iff.mp hodd)
  have hpn : padicNorm 2 (m : ℚ) = 1 := (padicNorm.int_eq_one_iff (p := 2) m).mpr h2
  rw [Rat.AbsoluteValue.padic_eq_padicNorm, hpn, Rat.cast_one]

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem padicTwo_subspaceDen_eq_one (c p : ℕ) (hp : 0 < p) :
    Rat.AbsoluteValue.padic 2 ((subspaceDen c p : ℤ) : ℚ) = 1 :=
  padicTwo_odd_eq_one (subspaceDen c p) (subspaceDen_odd c p hp)

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_subspaceDen_eq_sub (n : ℤ) (c p : ℕ) (hp : 0 < p) (P : ℤ) (q : ℚ)
    (hq : ((subspaceDen c p : ℤ) : ℚ) * q = -(P : ℚ)) :
    (∏ i : Fin 3, Rat.AbsoluteValue.padic 2
        (placeForms n i (placePoint ((subspaceDen c p : ℤ) : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint ((subspaceDen c p : ℤ) : ℚ) (P : ℚ) j)))
      = Rat.AbsoluteValue.padic 2 ((n : ℚ) - q) :=
  placeFactor_eq_sub (Rat.AbsoluteValue.padic 2) n _ (P : ℚ) q hq
    (padicTwo_subspaceDen_eq_one c p hp) (padicTwo_intCast_le_one P)

@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem padicTwo_eq_norm (r : ℚ) : Rat.AbsoluteValue.padic 2 r = ‖(r : ℚ_[2])‖ := by
  rw [Rat.AbsoluteValue.padic_eq_padicNorm, Padic.eq_padicNorm]

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem padicTwo_sub_ratInt_le (n : ℤ) {x : ℤ_[2]} (q : ℚ) (hq : (x : ℚ_[2]) = (q : ℚ_[2]))
    (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    Rat.AbsoluteValue.padic 2 ((n : ℚ) - q) ≤ r := by
  have key : (((n : ℚ) - q : ℚ) : ℚ_[2]) = (((n : ℤ_[2]) - x : ℤ_[2]) : ℚ_[2]) := by
    push_cast; rw [← hq]
  rw [padicTwo_eq_norm, key, PadicInt.padic_norm_e_of_padicInt]
  exact hbound

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_le_of_ratInt (n : ℤ) (D P q : ℚ) {x : ℤ_[2]} (hDq : D * q = -P)
    (hD : Rat.AbsoluteValue.padic 2 D = 1) (hPle : Rat.AbsoluteValue.padic 2 P ≤ 1)
    (hx : (x : ℚ_[2]) = (q : ℚ_[2])) (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    (∏ i : Fin 3, Rat.AbsoluteValue.padic 2 (placeForms n i (placePoint D P)) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint D P j))) ≤ r := by
  rw [placeFactor_eq_sub (Rat.AbsoluteValue.padic 2) n D P q hDq hD hPle]
  exact padicTwo_sub_ratInt_le n q hx r hbound

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_subspaceDen_le (n : ℤ) (c p : ℕ) (hp : 0 < p) (P : ℤ) (q : ℚ) {x : ℤ_[2]}
    (hDq : ((subspaceDen c p : ℤ) : ℚ) * q = -(P : ℚ)) (hx : (x : ℚ_[2]) = (q : ℚ_[2]))
    (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    (∏ i : Fin 3, Rat.AbsoluteValue.padic 2
        (placeForms n i (placePoint ((subspaceDen c p : ℤ) : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint ((subspaceDen c p : ℤ) : ℚ) (P : ℚ) j))) ≤ r :=
  placeFactor_le_of_ratInt n _ (P : ℚ) q hDq (padicTwo_subspaceDen_eq_one c p hp)
    (padicTwo_intCast_le_one P) hx r hbound

end B3
