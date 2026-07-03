import B3.Approximants
import BL.ForwardFormula
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function Filter

@[category API, AMS 11 37, ref "BL96"]
def blockPos (c p : ℕ) (e : ℕ → ℕ) (i : ℕ) : ℕ := (i / c) * p + e (i % c)

@[category API, AMS 11 37, ref "BL96"]
theorem blockPos_eq_of_lt {c p : ℕ} {e : ℕ → ℕ} {i : ℕ} (hi : i < c) :
    blockPos c p e i = e i := by
  simp only [blockPos, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.zero_mul, Nat.zero_add]

@[category API, AMS 11 37, ref "BL96"]
theorem blockPos_add_period {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c) (i : ℕ) :
    blockPos c p e (i + c) = blockPos c p e i + p := by
  simp only [blockPos, Nat.add_div_right i hc, Nat.add_mod_right]
  ring

@[category API, AMS 11 37, ref "BL96"]
theorem blockPos_strictMono {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    StrictMono (blockPos c p e) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hsplit : c * (i / c) + i % c = i := Nat.div_add_mod i c
  have hmod_lt : i % c < c := Nat.mod_lt i hc
  rcases Nat.lt_or_ge (i % c + 1) c with hlt | hge
  ·
    have hrep : i + 1 = c * (i / c) + (i % c + 1) := by omega
    have hd : (i + 1) / c = i / c := by
      rw [hrep, Nat.mul_add_div hc, Nat.div_eq_of_lt hlt, add_zero]
    have hm : (i + 1) % c = i % c + 1 := by
      rw [hrep, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hlt_e : e (i % c) < e (i % c + 1) := he_mono (i % c) (i % c + 1) (Nat.lt_succ_self _) hlt
    simp only [blockPos, hd, hm]
    omega
  ·
    have hbc : i % c + 1 = c := by omega
    have hrep : i + 1 = c * (i / c) + c := by omega
    have hd : (i + 1) / c = i / c + 1 := by
      rw [hrep, Nat.mul_add_div hc, Nat.div_self hc]
    have hm : (i + 1) % c = 0 := by
      rw [hrep, Nat.mul_add_mod, Nat.mod_self]
    have hlt_e : e (i % c) < p := he_lt _ hmod_lt
    have hmul : (i / c + 1) * p = (i / c) * p + p := by ring
    simp only [blockPos, hd, hm]
    omega

@[category API, AMS 11 37, ref "BL96"]
noncomputable def blockPoly (c : ℕ) (e : ℕ → ℕ) : ℤ_[2] :=
  ∑ r ∈ Finset.range c, Ring.inverse 3 ^ r * 2 ^ e r

@[category API, AMS 11 37, ref "BL96"]
noncomputable def blockVal (c p : ℕ) (e : ℕ → ℕ) : ℤ_[2] :=
  if 0 < c then ∑' i, (2 : ℤ_[2]) ^ blockPos c p e i else 0

@[category API, AMS 11 37, ref "BL96"]
theorem blockVal_of_pos {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c) :
    blockVal c p e = ∑' i, (2 : ℤ_[2]) ^ blockPos c p e i := by
  unfold blockVal; exact if_pos hc

@[category API, AMS 11 37, ref "BL96"]
theorem blockVal_zero {p : ℕ} {e : ℕ → ℕ} : blockVal 0 p e = 0 := by
  unfold blockVal; exact if_neg (lt_irrefl 0)

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_blockValue {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c) (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    Φ (blockVal c p e) =
      -(Ring.inverse 3 * blockPoly c e * Ring.inverse (1 - Ring.inverse 3 ^ c * 2 ^ p)) := by
  have hmono := blockPos_strictMono hc he_lt he_mono
  rw [blockVal_of_pos hc, Φ_eq_neg_tsum (blockPos c p e) hmono]
  congr 1
  set R : ℤ_[2] := Ring.inverse 3 ^ c * 2 ^ p with hR_def
  set F : ℕ → ℤ_[2] := fun i => Ring.inverse 3 ^ (i + 1) * 2 ^ blockPos c p e i with hF_def
  have hinv3norm : ‖Ring.inverse (3 : ℤ_[2])‖ = 1 :=
    PadicInt.isUnit_iff.mp (IsUnit.of_mul_eq_one 3 (by rw [mul_comm]; exact three_mul_inverse))
  have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hRnorm : ‖R‖ < 1 := by
    rw [hR_def, norm_mul, norm_pow, norm_pow, hinv3norm, one_pow, one_mul]
    calc ‖(2 : ℤ_[2])‖ ^ p ≤ ‖(2 : ℤ_[2])‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt1) hp
      _ = ‖(2 : ℤ_[2])‖ := pow_one _
      _ < 1 := h2lt1
  have hunit : IsUnit (1 - R) := isUnit_one_sub_of_norm_lt_one hRnorm
  have hsummable : Summable F := by
    apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt1)
    intro i
    have hge : i ≤ blockPos c p e i := hmono.le_apply
    simp only [hF_def, norm_mul, norm_pow, hinv3norm, one_pow, one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt1) hge
  have hshift : ∀ i, R * F i = F (i + c) := by
    intro i
    simp only [hF_def, hR_def, blockPos_add_period hc i]
    rw [pow_add (2 : ℤ_[2]) (blockPos c p e i) p,
        show i + c + 1 = (i + 1) + c from by ring, pow_add (Ring.inverse (3 : ℤ_[2])) (i + 1) c]
    ring
  have hfirst : ∑ i ∈ Finset.range c, F i = Ring.inverse 3 * blockPoly c e := by
    rw [blockPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [hF_def, blockPos_eq_of_lt hi]
    rw [pow_succ']
    ring
  have hmul : ∑' i, R * F i = R * ∑' i, F i := Summable.tsum_mul_left R hsummable
  have hregroup : (∑ i ∈ Finset.range c, F i) + ∑' i, F (i + c) = ∑' i, F i :=
    hsummable.sum_add_tsum_nat_add c
  have hshift_sum : ∑' i, F (i + c) = R * ∑' i, F i := by
    rw [← hmul]; exact (tsum_congr hshift).symm
  have key : (1 - R) * ∑' i, F i = ∑ i ∈ Finset.range c, F i := by
    rw [hshift_sum] at hregroup
    linear_combination -hregroup
  have hunit_inv : Ring.inverse (1 - R) * (1 - R) = 1 := Ring.inverse_mul_cancel _ hunit
  calc ∑' i, F i
      = Ring.inverse (1 - R) * ((1 - R) * ∑' i, F i) := by rw [← mul_assoc, hunit_inv, one_mul]
    _ = Ring.inverse (1 - R) * (Ring.inverse 3 * blockPoly c e) := by rw [key, hfirst]
    _ = Ring.inverse 3 * blockPoly c e * Ring.inverse (1 - R) := by ring

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_blockValue_linear_relation {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c) (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    ((3 : ℤ_[2]) ^ c - 2 ^ p) * Φ (blockVal c p e)
      = - ∑ r ∈ Finset.range c, (3 : ℤ_[2]) ^ (c - 1 - r) * 2 ^ e r := by
  rw [Φ_blockValue hc hp he_lt he_mono]
  set R : ℤ_[2] := Ring.inverse 3 ^ c * 2 ^ p with hR_def
  have h3κ : (3 : ℤ_[2]) ^ c * Ring.inverse 3 ^ c = 1 := by
    rw [← mul_pow, three_mul_inverse, one_pow]
  have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hinv3norm : ‖Ring.inverse (3 : ℤ_[2])‖ = 1 :=
    PadicInt.isUnit_iff.mp (IsUnit.of_mul_eq_one 3 (by rw [mul_comm]; exact three_mul_inverse))
  have hRnorm : ‖R‖ < 1 := by
    rw [hR_def, norm_mul, norm_pow, norm_pow, hinv3norm, one_pow, one_mul]
    calc ‖(2 : ℤ_[2])‖ ^ p ≤ ‖(2 : ℤ_[2])‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt1) hp
      _ = ‖(2 : ℤ_[2])‖ := pow_one _
      _ < 1 := h2lt1
  have hunit : IsUnit (1 - R) := isUnit_one_sub_of_norm_lt_one hRnorm
  have hfact : (3 : ℤ_[2]) ^ c - 2 ^ p = 3 ^ c * (1 - R) := by
    rw [hR_def, mul_sub, mul_one, ← mul_assoc, h3κ, one_mul]
  have hc1 : c - 1 + 1 = c := Nat.succ_pred_eq_of_pos hc
  have h3cκ : (3 : ℤ_[2]) ^ c * Ring.inverse 3 = 3 ^ (c - 1) := by
    conv_lhs => rw [← hc1, pow_succ]
    rw [mul_assoc, three_mul_inverse, mul_one]
  rw [hfact, mul_neg]
  congr 1
  rw [show (3 : ℤ_[2]) ^ c * (1 - R) *
        (Ring.inverse 3 * blockPoly c e * Ring.inverse (1 - R))
      = (3 ^ c * Ring.inverse 3) * blockPoly c e * ((1 - R) * Ring.inverse (1 - R)) from by ring,
      Ring.mul_inverse_cancel _ hunit, mul_one, h3cκ, blockPoly, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hrle : r ≤ c - 1 := by omega
  have hsplit : (3 : ℤ_[2]) ^ (c - 1) = 3 ^ (c - 1 - r) * 3 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrle]
  rw [← mul_assoc]
  congr 1
  rw [hsplit, mul_assoc, ← mul_pow, three_mul_inverse, one_pow, mul_one]

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_blockValue_mem_ratInt {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    Φ (blockVal c p e) ∈ RatInt := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [blockVal_zero, Φ_apply_zero]; exact ⟨0, by norm_cast⟩
  set x := Φ (blockVal c p e) with hx
  set N : ℕ := ∑ r ∈ Finset.range c, 3 ^ (c - 1 - r) * 2 ^ e r with hN
  have hrel : ((3 : ℤ_[2]) ^ c - 2 ^ p) * x = -(N : ℤ_[2]) := by
    rw [hx, Φ_blockValue_linear_relation hc hp he_lt he_mono, hN]
    push_cast
    ring
  have hk0 : (3 : ℤ) ^ c - 2 ^ p ≠ 0 := by
    have hodd : Odd ((3 : ℤ) ^ c - 2 ^ p) :=
      (Odd.pow ⟨1, by ring⟩).sub_even (Int.even_pow.mpr ⟨even_two, hp.ne'⟩)
    rintro h
    rw [h, Int.odd_iff] at hodd
    omega
  have hk0Q : (3 : ℚ_[2]) ^ c - 2 ^ p ≠ 0 := by
    have he : (3 : ℚ_[2]) ^ c - 2 ^ p = (((3 ^ c - 2 ^ p : ℤ)) : ℚ_[2]) := by push_cast; ring
    rw [he]; exact_mod_cast hk0
  have hkzQ : ((3 : ℚ_[2]) ^ c - 2 ^ p) * (x : ℚ_[2]) = -(N : ℚ_[2]) := by
    have h := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hrel
    push_cast at h; exact h
  refine ⟨(-(N : ℚ)) / ((3 : ℚ) ^ c - 2 ^ p), ?_⟩
  push_cast
  rw [eq_div_iff hk0Q]
  linear_combination hkzQ

end B3
