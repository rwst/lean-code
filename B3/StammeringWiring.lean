import B3.BlockApproximants
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function Filter

@[category API, AMS 11 37, ref "BL96"]
theorem binaryDigit_zero (x : ℤ_[2]) : binaryDigit x 0 = parity x := by
  simp only [binaryDigit, Function.iterate_zero_apply]

@[category API, AMS 11 37, ref "BL96"]
theorem binaryDigit_succ (x : ℤ_[2]) (k : ℕ) : binaryDigit x (k + 1) = binaryDigit (S x) k := by
  simp only [binaryDigit, Function.iterate_succ_apply]

@[category API, AMS 11 37, ref "BL96"]
theorem dvd_two_pow_sub_of_binaryDigit_agree : ∀ (N : ℕ) (x y : ℤ_[2]),
    (∀ k, k < N → binaryDigit x k = binaryDigit y k) → (2 : ℤ_[2]) ^ N ∣ x - y
  | 0, x, y, _ => by simp
  | N + 1, x, y, h => by
    have hpar : (parity x : ℤ_[2]) = (parity y : ℤ_[2]) := by
      have h0 := h 0 (Nat.succ_pos N)
      rw [binaryDigit_zero, binaryDigit_zero] at h0
      rw [h0]
    have hxy : x - y = 2 * (S x - S y) := by
      have hx := parity_add_two_mul_S x
      have hy := parity_add_two_mul_S y
      linear_combination hy - hx + hpar
    have hSdvd : (2 : ℤ_[2]) ^ N ∣ S x - S y :=
      dvd_two_pow_sub_of_binaryDigit_agree N (S x) (S y) (fun k hk => by
        have hk1 := h (k + 1) (Nat.succ_lt_succ hk)
        rwa [binaryDigit_succ, binaryDigit_succ] at hk1)
    rw [hxy, pow_succ']
    exact mul_dvd_mul_left 2 hSdvd

@[category API, AMS 11 37, ref "BL96"]
theorem toZModPow_eq_of_binaryDigit_agree (x y : ℤ_[2]) (N : ℕ)
    (h : ∀ k, k < N → binaryDigit x k = binaryDigit y k) :
    PadicInt.toZModPow N x = PadicInt.toZModPow N y :=
  (toZModPow_eq_iff_dvd_sub x y N).mpr (dvd_two_pow_sub_of_binaryDigit_agree N x y h)

@[category API, AMS 11 37, ref "AB07"]
theorem tendsto_two_pow_neg (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun m => (2 : ℝ) ^ (-(N m : ℤ))) atTop (nhds 0) := by
  have hbase : Tendsto (fun k : ℕ => (2 : ℝ) ^ (-(k : ℤ))) atTop (nhds 0) := by
    have heq : (fun k : ℕ => (2 : ℝ) ^ (-(k : ℤ))) = (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) := by
      funext k; rw [zpow_neg, zpow_natCast, inv_pow]
    rw [heq]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact hbase.comp hN

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem tooWellApproximated_of_agreement {v : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2]))
    {α : ℕ → ℤ_[2]} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hrat : ∀ m, Φ (α m) ∈ RatInt)
    (hagree : ∀ m, ∀ k, k < N m → binaryDigit v k = binaryDigit (α m) k) :
    (∀ m, Φ (α m) ∈ RatInt) ∧
    (∀ m, ‖(n : ℤ_[2]) - Φ (α m)‖ ≤ (2 : ℝ) ^ (-(N m : ℤ))) ∧
    Tendsto (fun m => ‖(n : ℤ_[2]) - Φ (α m)‖) atTop (nhds 0) := by
  have hbound : ∀ m, ‖(n : ℤ_[2]) - Φ (α m)‖ ≤ (2 : ℝ) ^ (-(N m : ℤ)) := fun m =>
    approximant_distance_bound hv (toZModPow_eq_of_binaryDigit_agree v (α m) (N m) (hagree m))
  exact ⟨hrat, hbound, squeeze_zero (fun m => norm_nonneg _) hbound (tendsto_two_pow_neg N hN)⟩

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem blockVal_tooWellApproximated {v : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2]))
    {cc pp : ℕ → ℕ} {ee : ℕ → ℕ → ℕ} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hp : ∀ m, 0 < pp m)
    (he_lt : ∀ m r, r < cc m → ee m r < pp m)
    (he_mono : ∀ m r r', r < r' → r' < cc m → ee m r < ee m r')
    (hagree : ∀ m, ∀ k, k < N m →
      binaryDigit v k = binaryDigit (blockVal (cc m) (pp m) (ee m)) k) :
    (∀ m, Φ (blockVal (cc m) (pp m) (ee m)) ∈ RatInt) ∧
    (∀ m, ‖(n : ℤ_[2]) - Φ (blockVal (cc m) (pp m) (ee m))‖ ≤ (2 : ℝ) ^ (-(N m : ℤ))) ∧
    Tendsto (fun m => ‖(n : ℤ_[2]) - Φ (blockVal (cc m) (pp m) (ee m))‖) atTop (nhds 0) :=
  tooWellApproximated_of_agreement hv hN
    (fun m => Φ_blockValue_mem_ratInt (hp m) (he_lt m) (he_mono m)) hagree

end B3
