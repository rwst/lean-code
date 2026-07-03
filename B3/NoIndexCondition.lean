import B3.PlaceTwoProduct
import B3.SubspaceConfinement
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open Filter

@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem mulHeight_placePoint (D P : ℤ) :
    Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) = ((⨆ i, |(![D, -1, P] : Fin 3 → ℤ) i| : ℤ) : ℝ) := by
  have hgcd : Finset.univ.gcd (![D, -1, P] : Fin 3 → ℤ) = 1 := by
    have hdvd : Finset.univ.gcd (![D, -1, P] : Fin 3 → ℤ) ∣ (![D, -1, P] : Fin 3 → ℤ) 1 :=
      Finset.gcd_dvd (Finset.mem_univ 1)
    have hd1 : Finset.univ.gcd (![D, -1, P] : Fin 3 → ℤ) ∣ (-1 : ℤ) := by simpa using hdvd
    rw [← Finset.normalize_gcd]
    exact normalize_eq_one.mpr (isUnit_of_dvd_unit hd1 isUnit_one.neg)
  have hpt : placePoint (D : ℚ) (P : ℚ) = ((↑) : ℤ → ℚ) ∘ (![D, -1, P] : Fin 3 → ℤ) := by
    ext i; fin_cases i <;> simp [placePoint]
  rw [hpt]; exact Rat.mulHeight_eq_max_abs_of_gcd_eq_one hgcd

@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem mulHeight_placePoint_le (D P : ℤ) {B : ℝ} (h1 : 1 ≤ B)
    (hD : |(D : ℝ)| ≤ B) (hP : |(P : ℝ)| ≤ B) :
    Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) ≤ B := by
  rw [mulHeight_placePoint, Finite.map_iSup_of_monotone _ Int.cast_mono]
  apply ciSup_le
  intro i
  fin_cases i <;> simp_all [Int.cast_abs]

@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem mulHeight_placePoint_pos (D P : ℤ) :
    0 < Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) := by
  rw [mulHeight_placePoint]
  have h1 : (1 : ℤ) ≤ ⨆ i, |(![D, -1, P] : Fin 3 → ℤ) i| := by
    have := le_ciSup (f := fun i => |(![D, -1, P] : Fin 3 → ℤ) i|) (Set.finite_range _).bddAbove 1
    simpa using this
  exact_mod_cast lt_of_lt_of_le one_pos h1

@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem sup_vinf_placePoint_eq_mulHeight (D P : ℤ) (vinf : AbsoluteValue ℚ ℝ)
    (hvinf : ∀ q : ℚ, vinf q = ((|q| : ℚ) : ℝ)) :
    (⨆ j, vinf (placePoint (D : ℚ) (P : ℚ) j)) = Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) := by
  rw [mulHeight_placePoint, Finite.map_iSup_of_monotone _ Int.cast_mono]
  refine iSup_congr fun j => ?_
  fin_cases j <;> simp only [placePoint, hvinf, Int.cast_abs] <;> push_cast <;> ring_nf

@[category API, AMS 11 37, ref "AB07" "BL96"]
def phiExp (D P : ℕ → ℤ) : ℕ → ℕ :=
  fun k => Nat.clog 3 (max (D k).natAbs (max (P k).natAbs 1))

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem ratInt_liouville_two_adic (n : ℕ) (D P : ℤ) (hDodd : Odd D) (hDpos : 1 ≤ D)
    (q : ℚ) (hq : (D : ℚ) * q = -(P : ℚ)) (hqn : q ≠ (n : ℚ)) :
    (((n : ℝ) + 1) * Height.mulHeight (placePoint (D : ℚ) (P : ℚ)))⁻¹ ≤
      Rat.AbsoluteValue.padic 2 ((n : ℚ) - q) := by
  set m : ℤ := (n : ℤ) * D + P with hm_def
  have hDpos' : (0 : ℤ) < D := by omega
  have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos'.ne'
  have hmq : ((m : ℤ) : ℚ) = (D : ℚ) * ((n : ℚ) - q) := by
    rw [mul_sub, hq, hm_def]; push_cast; ring
  have hmne : m ≠ 0 := by
    intro h
    apply hqn
    have h0 : (D : ℚ) * ((n : ℚ) - q) = 0 := by rw [← hmq, h]; simp
    have hnq : (n : ℚ) - q = 0 := (mul_eq_zero.mp h0).resolve_left hDne
    linarith
  have hval : Rat.AbsoluteValue.padic 2 ((m : ℤ) : ℚ)
      = Rat.AbsoluteValue.padic 2 ((n : ℚ) - q) := by
    rw [hmq, map_mul, padicTwo_odd_eq_one D hDodd, one_mul]
  have hlow : (1 : ℝ) / (|m| : ℝ) ≤ Rat.AbsoluteValue.padic 2 ((m : ℤ) : ℚ) := by
    have hzq : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hmne
    set k := padicValInt 2 m with hk
    have hdvd : (2 : ℤ) ^ k ∣ m := padicValInt_dvd m
    have hzabs : (0 : ℤ) < |m| := abs_pos.mpr hmne
    have hle : (2 : ℤ) ^ k ≤ |m| := Int.le_of_dvd hzabs ((dvd_abs _ _).mpr hdvd)
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hcast : (2 : ℝ) ^ k ≤ (|m| : ℝ) := by exact_mod_cast hle
    rw [Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.eq_zpow_of_nonzero hzq, padicValRat.of_int]
    push_cast
    rw [zpow_neg, zpow_natCast, one_div]
    exact inv_anti₀ h2k hcast
  have hEint : |m| ≤ ((n : ℤ) + 1) * (⨆ i, |(![D, -1, P] : Fin 3 → ℤ) i|) := by
    rw [hm_def]
    set S := ⨆ i, |(![D, -1, P] : Fin 3 → ℤ) i| with hS
    have hbdd : BddAbove (Set.range (fun i => |(![D, -1, P] : Fin 3 → ℤ) i|)) :=
      (Set.finite_range _).bddAbove
    have hsupD : (D : ℤ) ≤ S := by
      have := le_ciSup hbdd 0
      simpa [abs_of_pos hDpos'] using this
    have hsupP : |P| ≤ S := by simpa using le_ciSup hbdd 2
    calc |(n : ℤ) * D + P|
        ≤ |(n : ℤ) * D| + |P| := abs_add_le _ _
      _ = (n : ℤ) * D + |P| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (n : ℤ)), abs_of_pos hDpos']
      _ ≤ (n : ℤ) * S + S := by gcongr
      _ = ((n : ℤ) + 1) * S := by ring
  have hmpos : (0 : ℝ) < (|m| : ℝ) := by exact_mod_cast abs_pos.mpr hmne
  have hE : (|m| : ℝ) ≤ ((n : ℝ) + 1) * Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) := by
    rw [mulHeight_placePoint]; exact_mod_cast hEint
  rw [← hval]
  calc (((n : ℝ) + 1) * Height.mulHeight (placePoint (D : ℚ) (P : ℚ)))⁻¹
      ≤ (|m| : ℝ)⁻¹ := inv_anti₀ hmpos hE
    _ = 1 / (|m| : ℝ) := (one_div _).symm
    _ ≤ Rat.AbsoluteValue.padic 2 ((m : ℤ) : ℚ) := hlow

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem not_indexCondition_of_bounds (n : ℕ) (D P : ℕ → ℤ) (N : ℕ → ℕ) (q : ℕ → ℚ)
    (τ ε : ℝ) (hτ : 1 < τ) (hε : 0 < ε)
    (hDodd : ∀ m, Odd (D m)) (hDpos : ∀ m, 1 ≤ D m)
    (hrel : ∀ m, (D m : ℚ) * q m = -(P m : ℚ))
    (hbound : ∀ m, Rat.AbsoluteValue.padic 2 ((n : ℚ) - q m) ≤ (2 : ℝ) ^ (-(N m : ℤ)))
    (htend : Tendsto (fun m => Rat.AbsoluteValue.padic 2 ((n : ℚ) - q m)) atTop (nhds 0))
    (hdist : ∀ m, q m ≠ (n : ℚ)) :
    ¬ IndexConditionExpFreq τ (phiExp D P) N ε := by
  intro hidx
  replace hidx : ∃ᶠ m in atTop,
      (τ + ε) * (phiExp D P m : ℝ) * Real.log 3 ≤ (N m : ℝ) * Real.log 2 := hidx
  set f : ℕ → ℝ := fun m => Rat.AbsoluteValue.padic 2 ((n : ℚ) - q m) with hf
  set H : ℕ → ℝ := fun m => Height.mulHeight (placePoint (D m : ℚ) (P m : ℚ)) with hH
  have hHpos : ∀ m, 0 < H m := fun m => mulHeight_placePoint_pos (D m) (P m)
  have hLiou : ∀ m, (((n : ℝ) + 1) * H m)⁻¹ ≤ f m := fun m =>
    ratInt_liouville_two_adic n (D m) (P m) (hDodd m) (hDpos m) (q m) (hrel m) (hdist m)
  have hheight : ∀ m, H m ≤ (3 : ℝ) ^ (phiExp D P m) := by
    intro m
    show Height.mulHeight (placePoint (D m : ℚ) (P m : ℚ)) ≤ (3 : ℝ) ^ (phiExp D P m)
    rw [mulHeight_placePoint]
    have hsup_le : (⨆ i, |(![D m, -1, P m] : Fin 3 → ℤ) i|)
        ≤ ((max (D m).natAbs (max (P m).natAbs 1) : ℕ) : ℤ) := by
      apply ciSup_le
      intro i
      fin_cases i <;>
      · simp only [Int.abs_eq_natAbs]
        push_cast
        omega
    calc ((⨆ i, |(![D m, -1, P m] : Fin 3 → ℤ) i| : ℤ) : ℝ)
        ≤ (((max (D m).natAbs (max (P m).natAbs 1) : ℕ) : ℤ) : ℝ) := Int.cast_le.mpr hsup_le
      _ = ((max (D m).natAbs (max (P m).natAbs 1) : ℕ) : ℝ) := Int.cast_natCast _
      _ ≤ (3 : ℝ) ^ (phiExp D P m) := by
          simp only [phiExp]
          exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hτε : 0 < τ - 1 + ε := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set C : ℝ := Real.log ((n : ℝ) + 1) / (τ - 1 + ε) with hC
  set δ : ℝ := (((n : ℝ) + 1) * Real.exp C)⁻¹ with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have h_ev : ∀ᶠ m in atTop, f m < δ := htend.eventually (Iio_mem_nhds hδpos)
  have h_freq : ∃ᶠ m in atTop, δ ≤ f m := by
    refine hidx.mono ?_
    intro m hm
    have hHmpos := hHpos m
    have hchain := (hLiou m).trans (hbound m)
    rw [zpow_neg, zpow_natCast] at hchain
    have hpow2pos : (0 : ℝ) < (2 : ℝ) ^ (N m) := by positivity
    have hnHpos : (0 : ℝ) < ((n : ℝ) + 1) * H m := by positivity
    have h2N_le : (2 : ℝ) ^ (N m) ≤ ((n : ℝ) + 1) * H m :=
      (inv_le_inv₀ hnHpos hpow2pos).mp hchain
    have hlogchain : (N m : ℝ) * Real.log 2 ≤ Real.log (((n : ℝ) + 1) * H m) := by
      calc (N m : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (N m)) := (Real.log_pow _ _).symm
        _ ≤ Real.log (((n : ℝ) + 1) * H m) := Real.log_le_log hpow2pos h2N_le
    have hlogH : Real.log (H m) ≤ (phiExp D P m : ℝ) * Real.log 3 := by
      calc Real.log (H m) ≤ Real.log ((3 : ℝ) ^ (phiExp D P m)) :=
            Real.log_le_log hHmpos (hheight m)
        _ = (phiExp D P m : ℝ) * Real.log 3 := Real.log_pow _ _
    have hlogmul : Real.log (((n : ℝ) + 1) * H m)
        = Real.log ((n : ℝ) + 1) + Real.log (H m) := Real.log_mul (by positivity) (by positivity)
    have hcombine : (τ + ε) * (phiExp D P m : ℝ) * Real.log 3
        ≤ Real.log ((n : ℝ) + 1) + (phiExp D P m : ℝ) * Real.log 3 := by
      calc (τ + ε) * (phiExp D P m : ℝ) * Real.log 3 ≤ (N m : ℝ) * Real.log 2 := hm
        _ ≤ Real.log (((n : ℝ) + 1) * H m) := hlogchain
        _ = Real.log ((n : ℝ) + 1) + Real.log (H m) := hlogmul
        _ ≤ Real.log ((n : ℝ) + 1) + (phiExp D P m : ℝ) * Real.log 3 := by linarith [hlogH]
    have hbound_c : (τ - 1 + ε) * ((phiExp D P m : ℝ) * Real.log 3)
        ≤ Real.log ((n : ℝ) + 1) := by nlinarith [hcombine]
    have hlogHle : Real.log (H m) ≤ C := by
      have h1 : (phiExp D P m : ℝ) * Real.log 3 ≤ C := by
        rw [hC, le_div_iff₀ hτε, mul_comm]; exact hbound_c
      linarith [hlogH, h1]
    have hHm_le : H m ≤ Real.exp C := by
      have := Real.exp_le_exp.mpr hlogHle
      rwa [Real.exp_log hHmpos] at this
    calc δ = (((n : ℝ) + 1) * Real.exp C)⁻¹ := hδ
      _ ≤ (((n : ℝ) + 1) * H m)⁻¹ := inv_anti₀ (by positivity) (by gcongr)
      _ ≤ f m := hLiou m
  obtain ⟨m, hm1, hm2⟩ := (h_freq.and_eventually h_ev).exists
  exact absurd hm1 (not_le.mpr hm2)

end B3
