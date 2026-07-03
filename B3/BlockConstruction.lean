import B3.PeriodicMatching
import AB.StammeringSequences
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.List.GetD
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function Filter PadicInt

@[category API, AMS 11 68, ref "AB07"]
theorem sum_range_length_getD (L : List ℕ) (f : ℕ → ℕ) :
    ∑ r ∈ Finset.range L.length, f (L.getD r 0) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, add_comm]

@[category API, AMS 11 68, ref "AB07"]
def blockCard (B : ℕ) : ℕ := B.bitIndices.length

@[category API, AMS 11 68, ref "AB07"]
def blockOffset (B : ℕ) (r : ℕ) : ℕ := B.bitIndices.getD r 0

@[category API, AMS 11 68, ref "AB07"]
theorem blockFirst_blockOffset (B : ℕ) : blockFirst (blockCard B) (blockOffset B) = B := by
  unfold blockFirst blockCard blockOffset
  rw [sum_range_length_getD B.bitIndices (fun i => 2 ^ i)]
  exact B.sum_map_two_pow_bitIndices

@[category API, AMS 11 68, ref "AB07"]
theorem blockOffset_strictMono (B : ℕ) :
    ∀ r r', r < r' → r' < blockCard B → blockOffset B r < blockOffset B r' := by
  intro r r' hrr hr'
  unfold blockOffset blockCard at *
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hr']
  exact Nat.bitIndices_sorted.getElem_lt_getElem_of_lt hrr

@[category API, AMS 11 68, ref "AB07"]
theorem blockOffset_lt {B p : ℕ} (hB : B < 2 ^ p) :
    ∀ r, r < blockCard B → blockOffset B r < p := by
  intro r hr
  unfold blockOffset blockCard at *
  rw [List.getD_eq_getElem _ _ hr]
  have h2 : 2 ^ B.bitIndices[r] ≤ B := Nat.two_pow_le_of_mem_bitIndices (List.getElem_mem hr)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h2 hB)

@[category API, AMS 11 37, ref "BL96"]
theorem dvd_sub_appr (x : ℤ_[2]) (t : ℕ) : (2 : ℤ_[2]) ^ t ∣ x - ((appr x t : ℕ) : ℤ_[2]) := by
  simpa using Ideal.mem_span_singleton.mp (appr_spec t x)

@[category API, AMS 11 37, ref "BL96" "AB07"]
noncomputable def truncApprox (v : ℤ_[2]) (t p : ℕ) : ℤ_[2] :=
  prefixBlockVal (appr v t) t (blockCard (appr (S^[t] v) p)) p (blockOffset (appr (S^[t] v) p))

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_truncApprox_mem_ratInt (v : ℤ_[2]) (t p : ℕ) (hp : 0 < p) :
    Φ (truncApprox v t p) ∈ RatInt := by
  unfold truncApprox
  exact Φ_prefixBlockVal_mem_ratInt hp (blockOffset_lt (appr_lt (S^[t] v) p))
    (blockOffset_strictMono (appr (S^[t] v) p)) t (appr v t) (appr_lt v t)

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem truncApprox_mem_ratInt (v : ℤ_[2]) (t p : ℕ) (hp : 0 < p) : truncApprox v t p ∈ RatInt := by
  unfold truncApprox prefixBlockVal
  exact ratInt_add ⟨(appr v t : ℚ), by norm_cast⟩
    (ratInt_mul ⟨(2 : ℚ) ^ t, by norm_cast⟩
      (blockVal_mem_ratInt hp (blockOffset_lt (appr_lt (S^[t] v) p))
        (blockOffset_strictMono (appr (S^[t] v) p))))

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem binaryDigit_truncApprox_agreement (v : ℤ_[2]) (t p : ℕ) (hp : 0 < p) {N : ℕ}
    (hper : ∀ i, t + p ≤ i → i < N → binaryDigit v i = binaryDigit v (i - p)) :
    ∀ k, k < N → binaryDigit v k = binaryDigit (truncApprox v t p) k := by
  unfold truncApprox
  refine binaryDigit_window_agreement hp (blockOffset_lt (appr_lt (S^[t] v) p))
    (blockOffset_strictMono (appr (S^[t] v) p)) (appr_lt v t) (dvd_sub_appr v t) ?_ hper
  rw [blockFirst_blockOffset]
  exact dvd_sub_appr (S^[t] v) p

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem conditionStar_tooWellApproximated {v : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2]))
    {w : ℝ} (hw : 1 < w) (hCS : ConditionStar w (binaryDigit v)) :
    ∃ (α : ℕ → ℤ_[2]) (N : ℕ → ℕ), Tendsto N atTop atTop ∧
      (∀ m, Φ (α m) ∈ RatInt) ∧
      (∀ m, ‖(n : ℤ_[2]) - Φ (α m)‖ ≤ (2 : ℝ) ^ (-(N m : ℤ))) ∧
      Tendsto (fun m => ‖(n : ℤ_[2]) - Φ (α m)‖) atTop (nhds 0) ∧
      (∀ m, α m ∈ RatInt) := by
  obtain ⟨_hnep, r, s, hs_pos, hper, _hbound, hs_mono⟩ := hCS

  have hmN : ∀ m, m ≤ r m + ⌊w * (s m : ℝ)⌋₊ := by
    intro m
    have h1 : m ≤ s m := hs_mono.le_apply
    have hsm : (0 : ℝ) ≤ (s m : ℝ) := Nat.cast_nonneg (s m)
    have hle : (s m : ℝ) ≤ w * (s m : ℝ) := by nlinarith [hsm, hw.le]
    have h2 : s m ≤ ⌊w * (s m : ℝ)⌋₊ := Nat.le_floor hle
    omega
  have hN : Tendsto (fun m => r m + ⌊w * (s m : ℝ)⌋₊) atTop atTop :=
    tendsto_atTop_mono hmN tendsto_id

  have hagree : ∀ m, ∀ k, k < r m + ⌊w * (s m : ℝ)⌋₊ →
      binaryDigit v k = binaryDigit (truncApprox v (r m) (s m)) k := by
    intro m
    refine binaryDigit_truncApprox_agreement v (r m) (s m) (hs_pos m) ?_
    intro i hi1 hi2
    exact hper m i hi1 hi2
  refine ⟨fun m => truncApprox v (r m) (s m), fun m => r m + ⌊w * (s m : ℝ)⌋₊, hN, ?_⟩
  obtain ⟨hB, hC, hD⟩ := tooWellApproximated_of_agreement hv hN
    (fun m => Φ_truncApprox_mem_ratInt v (r m) (s m) (hs_pos m)) hagree
  exact ⟨hB, hC, hD, fun m => truncApprox_mem_ratInt v (r m) (s m) (hs_pos m)⟩

end B3
