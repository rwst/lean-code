import B3.PlaceTwoProduct
import B3.HeightVsRate
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open Function

noncomputable def repForms (n : ℤ) : Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) :=
  ![LinearMap.proj 0, LinearMap.proj 1,
    (n : ℚ) • LinearMap.proj 0 + (n : ℚ) • LinearMap.proj 1 + LinearMap.proj 2]

@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem repForms_linearIndependent (n : ℤ) : LinearIndependent ℚ (repForms n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun (congrArg DFunLike.coe hg) (Pi.single 0 1)
  have h1 := congrFun (congrArg DFunLike.coe hg) (Pi.single 1 1)
  have h2 := congrFun (congrArg DFunLike.coe hg) (Pi.single 2 1)
  simp only [repForms, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.zero_apply, Pi.single_eq_same, smul_eq_mul] at h0 h1 h2
  intro i
  fin_cases i <;> simp_all

def repPoint (A B P : ℚ) : Fin 3 → ℚ := ![A, B, P]

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem repPlaceFactor_eq (v : AbsoluteValue ℚ ℝ) (n : ℤ) (A B P : ℚ)
    (hA : v A = 1) (hB : v B ≤ 1) (hP : v P ≤ 1) :
    (∏ i : Fin 3, v (repForms n i (repPoint A B P)) / (⨆ j, v (repPoint A B P j)))
      = v B * v ((n : ℚ) * A + (n : ℚ) * B + P) := by
  have hbound : ∀ j, v (repPoint A B P j) ≤ 1 := by
    intro j; fin_cases j
    · show v A ≤ 1; rw [hA]
    · show v B ≤ 1; exact hB
    · show v P ≤ 1; exact hP
  have hsup : (⨆ j, v (repPoint A B P j)) = 1 := by
    apply le_antisymm (ciSup_le hbound)
    exact le_ciSup_of_le (Set.finite_range _).bddAbove 0 (le_of_eq hA.symm)
  rw [hsup]
  have e0 : repForms n 0 (repPoint A B P) = A := by simp [repForms, repPoint]
  have e1 : repForms n 1 (repPoint A B P) = B := by simp [repForms, repPoint]
  have e2 : repForms n 2 (repPoint A B P) = (n : ℚ) * A + (n : ℚ) * B + P := by
    simp [repForms, repPoint, smul_eq_mul]
  simp only [div_one, Fin.prod_univ_three, e0, e1, e2, hA]
  rw [one_mul]

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem repPlaceFactor_eq_sub (v : AbsoluteValue ℚ ℝ) (n : ℤ) (A B P q : ℚ)
    (hAB : v (A + B) = 1) (hq : (A + B) * q = -P) (hA : v A = 1) (hB : v B ≤ 1) (hP : v P ≤ 1) :
    (∏ i : Fin 3, v (repForms n i (repPoint A B P)) / (⨆ j, v (repPoint A B P j)))
      = v B * v ((n : ℚ) - q) := by
  rw [repPlaceFactor_eq v n A B P hA hB hP]
  have hid : (n : ℚ) * A + (n : ℚ) * B + P = (A + B) * ((n : ℚ) - q) := by rw [mul_sub, hq]; ring
  rw [hid, map_mul, hAB, one_mul]

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem repPlaceFactor_subspaceDen_le (n : ℤ) (c p : ℕ) (hp : 0 < p) (P : ℤ) (q : ℚ) {x : ℤ_[2]}
    (hDq : ((subspaceDen c p : ℤ) : ℚ) * q = -(P : ℚ)) (hx : (x : ℚ_[2]) = (q : ℚ_[2]))
    (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    (∏ i : Fin 3, Rat.AbsoluteValue.padic 2
        (repForms n i (repPoint ((3 ^ c : ℤ) : ℚ) ((-(2 ^ p : ℤ)) : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (repPoint ((3 ^ c : ℤ) : ℚ) ((-(2 ^ p : ℤ)) : ℚ) (P : ℚ) j)))
      ≤ (1 / 2 : ℝ) ^ p * r := by
  have hAB_eq : ((3 ^ c : ℤ) : ℚ) + ((-(2 ^ p : ℤ)) : ℚ) = ((subspaceDen c p : ℤ) : ℚ) := by
    unfold subspaceDen; push_cast; ring
  have hvA : Rat.AbsoluteValue.padic 2 ((3 ^ c : ℤ) : ℚ) = 1 :=
    padicTwo_odd_eq_one (3 ^ c) (Odd.pow (by decide))
  have hvAB : Rat.AbsoluteValue.padic 2 (((3 ^ c : ℤ) : ℚ) + ((-(2 ^ p : ℤ)) : ℚ)) = 1 := by
    rw [hAB_eq]; exact padicTwo_subspaceDen_eq_one c p hp
  have hvB : Rat.AbsoluteValue.padic 2 ((-(2 ^ p : ℤ)) : ℚ) ≤ 1 := by
    rw [show ((-(2 ^ p : ℤ)) : ℚ) = -(((2 ^ p : ℤ)) : ℚ) by push_cast; ring, AbsoluteValue.map_neg]
    exact padicTwo_intCast_le_one (2 ^ p)
  have hvP : Rat.AbsoluteValue.padic 2 ((P : ℤ) : ℚ) ≤ 1 := padicTwo_intCast_le_one P
  rw [repPlaceFactor_eq_sub (Rat.AbsoluteValue.padic 2) n ((3 ^ c : ℤ) : ℚ) ((-(2 ^ p : ℤ)) : ℚ) (P : ℚ) q
    hvAB (by rw [hAB_eq]; exact hDq) hvA hvB hvP]
  have hvBval : Rat.AbsoluteValue.padic 2 ((-(2 ^ p : ℤ)) : ℚ) = (1 / 2 : ℝ) ^ p := by
    rw [show ((-(2 ^ p : ℤ)) : ℚ) = -((2 : ℚ) ^ p) by push_cast; ring, AbsoluteValue.map_neg, map_pow]
    congr 1
    rw [Rat.AbsoluteValue.padic_eq_padicNorm,
      show padicNorm 2 (2 : ℚ) = 2⁻¹ by simp [padicNorm, padicValRat, padicValInt, padicValNat]]
    norm_num
  rw [hvBval]
  exact mul_le_mul_of_nonneg_left (padicTwo_sub_ratInt_le n q hx r hbound) (by positivity)

@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem rep_w_threshold_gt_arch (ε : ℝ) :
    (2 + ε) * Real.log 3 / Real.log 2 < (3 + ε) * Real.log 3 / Real.log 2 - 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [lt_sub_iff_add_lt, div_add' _ _ _ hlog2.ne', div_lt_div_iff_of_pos_right hlog2]
  nlinarith [hlog23]

end B3
