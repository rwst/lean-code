import B3.BlockDigits
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function Filter

@[category API, AMS 11 37, ref "BL96"]
theorem toZMod_two : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
  have hc2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_cast
  rw [← hc2, map_natCast]; exact ZMod.natCast_self 2

@[category API, AMS 11 37, ref "BL96"]
theorem Φ_two_mul (x : ℤ_[2]) : Φ (2 * x) = 2 * Φ x := by
  have hSx : S (2 * x) = x := by simpa using S_natCast_add_two_mul 0 (by norm_num) x
  have hconj : T₂ (Φ (2 * x)) = Φ x := by
    have h := Φ_semiconj (2 * x); rw [hSx] at h; exact h.symm
  have hpar : parity (Φ (2 * x)) = 0 := by
    unfold parity
    rw [Φ_mod_two, map_mul, toZMod_two, zero_mul, ZMod.val_zero]
  have h2T := two_mul_T₂ (Φ (2 * x))
  simp only [numer, hpar, pow_zero, mul_one, Nat.cast_zero, add_zero] at h2T
  rw [hconj] at h2T
  exact h2T.symm

@[category API, AMS 11 37, ref "BL96"]
theorem Φ_one_add_two_mul (x : ℤ_[2]) :
    Φ (1 + 2 * x) = (2 * Φ x - 1) * Ring.inverse 3 := by
  have hSx : S (1 + 2 * x) = x := by simpa using S_natCast_add_two_mul 1 (by norm_num) x
  have hconj : T₂ (Φ (1 + 2 * x)) = Φ x := by
    have h := Φ_semiconj (1 + 2 * x); rw [hSx] at h; exact h.symm
  have hpar : parity (Φ (1 + 2 * x)) = 1 := by
    unfold parity
    rw [Φ_mod_two, map_add, map_one, map_mul, toZMod_two, zero_mul, add_zero]
    decide
  have h2T := two_mul_T₂ (Φ (1 + 2 * x))
  simp only [numer, hpar, pow_one, Nat.cast_one] at h2T
  rw [hconj] at h2T
  have hkey : Φ (1 + 2 * x) * 3 = 2 * Φ x - 1 := by linear_combination -h2T
  calc Φ (1 + 2 * x)
      = Φ (1 + 2 * x) * (3 * Ring.inverse 3) := by rw [three_mul_inverse, mul_one]
    _ = (Φ (1 + 2 * x) * 3) * Ring.inverse 3 := by ring
    _ = (2 * Φ x - 1) * Ring.inverse 3 := by rw [hkey]

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_add {y z : ℤ_[2]} (hy : y ∈ RatInt) (hz : z ∈ RatInt) : y + z ∈ RatInt := by
  obtain ⟨q, hq⟩ := hy; obtain ⟨r, hr⟩ := hz
  exact ⟨q + r, by push_cast; rw [hq, hr]⟩

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_sub {y z : ℤ_[2]} (hy : y ∈ RatInt) (hz : z ∈ RatInt) : y - z ∈ RatInt := by
  obtain ⟨q, hq⟩ := hy; obtain ⟨r, hr⟩ := hz
  exact ⟨q - r, by push_cast; rw [hq, hr]⟩

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_mul {y z : ℤ_[2]} (hy : y ∈ RatInt) (hz : z ∈ RatInt) : y * z ∈ RatInt := by
  obtain ⟨q, hq⟩ := hy; obtain ⟨r, hr⟩ := hz
  exact ⟨q * r, by push_cast; rw [hq, hr]⟩

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_one : (1 : ℤ_[2]) ∈ RatInt := ⟨1, by norm_cast⟩

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_two : (2 : ℤ_[2]) ∈ RatInt := ⟨2, by norm_cast⟩

@[category API, AMS 11 37, ref "BL96"]
theorem coe_inverse_three : ((Ring.inverse (3 : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) = (3 : ℚ_[2])⁻¹ := by
  have key : ((Ring.inverse (3 : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) * (3 : ℚ_[2]) = 1 := by
    have hcancel : (Ring.inverse (3 : ℤ_[2]) * 3 : ℤ_[2]) = 1 :=
      Ring.inverse_mul_cancel 3 isUnit_three
    calc ((Ring.inverse (3 : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) * (3 : ℚ_[2])
        = ((Ring.inverse (3 : ℤ_[2]) * 3 : ℤ_[2]) : ℚ_[2]) := by push_cast; norm_cast
      _ = ((1 : ℤ_[2]) : ℚ_[2]) := by rw [hcancel]
      _ = 1 := by norm_cast
  exact eq_inv_of_mul_eq_one_left key

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_inverse_three : Ring.inverse (3 : ℤ_[2]) ∈ RatInt :=
  ⟨1 / 3, by rw [coe_inverse_three]; norm_num⟩

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_two_mul {y : ℤ_[2]} (hy : y ∈ RatInt) : 2 * y ∈ RatInt :=
  ratInt_mul ratInt_two hy

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_step_one {y : ℤ_[2]} (hy : y ∈ RatInt) :
    (2 * y - 1) * Ring.inverse 3 ∈ RatInt :=
  ratInt_mul (ratInt_sub (ratInt_mul ratInt_two hy) ratInt_one) ratInt_inverse_three

@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_ring_inverse {x : ℤ_[2]} (hx : x ∈ RatInt) (hu : IsUnit x) :
    Ring.inverse x ∈ RatInt := by
  obtain ⟨q, hq⟩ := hx
  have hcoe : ((Ring.inverse x : ℤ_[2]) : ℚ_[2]) = (x : ℚ_[2])⁻¹ := by
    have key : ((Ring.inverse x : ℤ_[2]) : ℚ_[2]) * (x : ℚ_[2]) = 1 := by
      have hcancel : (Ring.inverse x * x : ℤ_[2]) = 1 := Ring.inverse_mul_cancel x hu
      calc ((Ring.inverse x : ℤ_[2]) : ℚ_[2]) * (x : ℚ_[2])
          = ((Ring.inverse x * x : ℤ_[2]) : ℚ_[2]) := by push_cast; ring
        _ = ((1 : ℤ_[2]) : ℚ_[2]) := by rw [hcancel]
        _ = 1 := by norm_cast
    exact eq_inv_of_mul_eq_one_left key
  exact ⟨q⁻¹, by rw [hcoe, hq, Rat.cast_inv]⟩

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem blockVal_mem_ratInt {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    blockVal c p e ∈ RatInt := by
  rcases Nat.eq_zero_or_pos c with hc0 | hc
  · rw [hc0, blockVal_zero]; exact ⟨0, by norm_num⟩
  · have hmono := blockPos_strictMono hc he_lt he_mono
    set F : ℕ → ℤ_[2] := fun i => (2 : ℤ_[2]) ^ blockPos c p e i with hF_def
    have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
    have hRnorm : ‖(2 : ℤ_[2]) ^ p‖ < 1 := by
      rw [norm_pow]
      calc ‖(2 : ℤ_[2])‖ ^ p ≤ ‖(2 : ℤ_[2])‖ ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg _) h2lt1.le hp
        _ = ‖(2 : ℤ_[2])‖ := pow_one _
        _ < 1 := h2lt1
    have hunit : IsUnit (1 - (2 : ℤ_[2]) ^ p) := B3.isUnit_one_sub_of_norm_lt_one hRnorm
    have hsummable : Summable F := by
      apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt1)
      intro i; simp only [hF_def, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) h2lt1.le hmono.le_apply
    have hshift : ∀ i, (2 : ℤ_[2]) ^ p * F i = F (i + c) := by
      intro i; simp only [hF_def, blockPos_add_period hc i]; rw [pow_add]; ring
    have hmul : ∑' i, (2 : ℤ_[2]) ^ p * F i = (2 : ℤ_[2]) ^ p * ∑' i, F i :=
      Summable.tsum_mul_left _ hsummable
    have hregroup : (∑ i ∈ Finset.range c, F i) + ∑' i, F (i + c) = ∑' i, F i :=
      hsummable.sum_add_tsum_nat_add c
    have hshift_sum : ∑' i, F (i + c) = (2 : ℤ_[2]) ^ p * ∑' i, F i := by
      rw [← hmul]; exact (tsum_congr hshift).symm
    have key : (1 - (2 : ℤ_[2]) ^ p) * ∑' i, F i = ∑ i ∈ Finset.range c, F i := by
      rw [hshift_sum] at hregroup; linear_combination -hregroup
    have hbv : blockVal c p e = (∑ i ∈ Finset.range c, F i) * Ring.inverse (1 - (2 : ℤ_[2]) ^ p) := by
      rw [blockVal_of_pos hc, ← key, mul_comm (1 - (2 : ℤ_[2]) ^ p) (∑' i, F i), mul_assoc,
        Ring.mul_inverse_cancel _ hunit, mul_one]
    rw [hbv]
    apply ratInt_mul
    · rw [show (∑ i ∈ Finset.range c, F i)
          = ((∑ i ∈ Finset.range c, 2 ^ blockPos c p e i : ℕ) : ℤ_[2]) by
        simp only [hF_def]; push_cast; ring]
      exact ⟨((∑ i ∈ Finset.range c, 2 ^ blockPos c p e i : ℕ) : ℚ), by norm_cast⟩
    · exact ratInt_ring_inverse (ratInt_sub ratInt_one ⟨(2 : ℚ) ^ p, by norm_cast⟩) hunit

@[category API, AMS 11 37, ref "BL96"]
noncomputable def prefixBlockVal (A t c p : ℕ) (e : ℕ → ℕ) : ℤ_[2] :=
  (A : ℤ_[2]) + 2 ^ t * blockVal c p e

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_prefixBlockVal_mem_ratInt {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (t : ℕ) :
    ∀ A : ℕ, A < 2 ^ t → Φ (prefixBlockVal A t c p e) ∈ RatInt := by
  induction t with
  | zero =>
    intro A hA
    obtain rfl : A = 0 := by simpa using hA
    simp only [prefixBlockVal, Nat.cast_zero, zero_add, pow_zero, one_mul]
    exact Φ_blockValue_mem_ratInt hp he_lt he_mono
  | succ t ih =>
    intro A hA
    have hAhalf : A / 2 < 2 ^ t := by
      have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
      omega
    have hsplit : prefixBlockVal A (t + 1) c p e
        = ((A % 2 : ℕ) : ℤ_[2]) + 2 * prefixBlockVal (A / 2) t c p e := by
      unfold prefixBlockVal
      have hcast : ((A : ℕ) : ℤ_[2]) = ((A % 2 : ℕ) : ℤ_[2]) + 2 * ((A / 2 : ℕ) : ℤ_[2]) := by
        have hm : A = A % 2 + 2 * (A / 2) := by omega
        conv_lhs => rw [hm]
        push_cast; ring
      rw [hcast, pow_succ']; ring
    have hih := ih (A / 2) hAhalf
    have hmod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · rw [hsplit, h0]
      simp only [Nat.cast_zero, zero_add]
      rw [Φ_two_mul]
      exact ratInt_two_mul hih
    · rw [hsplit, h1]
      simp only [Nat.cast_one]
      rw [Φ_one_add_two_mul]
      exact ratInt_step_one hih

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem S_iterate_prefixBlockVal {A t c p : ℕ} {e : ℕ → ℕ} (hA : A < 2 ^ t) :
    S^[t] (prefixBlockVal A t c p e) = blockVal c p e := by
  unfold prefixBlockVal
  exact S_iterate_natCast_add t A (blockVal c p e) hA

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_ge {A t c p : ℕ} {e : ℕ → ℕ} (hA : A < 2 ^ t) {k : ℕ}
    (hk : t ≤ k) :
    binaryDigit (prefixBlockVal A t c p e) k = binaryDigit (blockVal c p e) (k - t) := by
  unfold binaryDigit
  conv_lhs => rw [← Nat.sub_add_cancel hk]
  rw [Function.iterate_add_apply, S_iterate_prefixBlockVal hA]

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_lt {A t c p : ℕ} {e : ℕ → ℕ} {k : ℕ} (hk : k < t) :
    binaryDigit (prefixBlockVal A t c p e) k = binaryDigit ((A : ℕ) : ℤ_[2]) k := by
  refine binaryDigit_agree_of_dvd_two_pow t _ _ ?_ k hk
  unfold prefixBlockVal
  rw [add_sub_cancel_left]
  exact dvd_mul_right _ _

end B3
