/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.ConjugacyMap
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The explicit forward formula `(1.6)` for `Φ` (BL96 §1; [Ber94]) — PROVED

Bernstein's explicit formula for the **forward** 3x+1 conjugacy map: expand `x` in binary by its
`1`-bit positions, `x = ∑ᵢ 2^{dᵢ}` with `0 ≤ d₀ < d₁ < ⋯`; then

  `Φ(x) = − ∑ᵢ 3^{−(i+1)} 2^{dᵢ}`   (`Φ_eq_neg_tsum`).

**Proof idea** (this file discharges what was a cited axiom in `BL.ConjugacyMap`). Write
`bval d = ∑ᵢ 2^{dᵢ}` (the input `x`) and `Φval d = −∑ᵢ 3^{−(i+1)} 2^{dᵢ}` (the claimed value). Since
`Φ = qMap⁻¹` and `Q = qMap = ⇑Φ.symm`, it suffices to show `Q (Φval d) = bval d`. Both the input and the
claimed value satisfy the **same one-step recursion** under the dynamics:

* `S (bval d) = bval (dshift d)` — the shift deletes the lowest binary digit (`bval_shift`);
* `T₂ (Φval d) = Φval (dshift d)` — the 3x+1 map acts on the `3⁻¹`-weighted sum (`Φval_step`);

where `dshift` is the bit-position update (drop `d₀ = 0`, decrement the rest). Iterating, the `j`-th
orbit parity of `Φval d` equals the `j`-th orbit parity of `bval d` under `S`, so by `tsum_parity_S`
(the binary digit expansion), `Q (Φval d) = ∑ⱼ parity (Sʲ (bval d)) · 2ʲ = bval d`.

## References
* [BL96] Bernstein, D. J., and J. C. Lagarias. *The 3x+1 conjugacy map.* Canad. J. Math. 48 (1996).
* [Ber94] Bernstein, D. J. *A noniterative 2-adic statement of the 3N+1 conjecture.* Proc. AMS 121 (1994).
-/

namespace BL

open PadicInt Function Filter

/-- `‖2‖ < 1` in `ℤ₂`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem norm_two_lt_one : ‖(2 : ℤ_[2])‖ < 1 := by
  rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])

/-- `3⁻¹ = Ring.inverse 3` is a unit, so `‖3⁻¹‖ = 1`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem norm_inverse_three : ‖(Ring.inverse (3 : ℤ_[2]))‖ = 1 := by
  rw [← PadicInt.isUnit_iff]
  exact IsUnit.of_mul_eq_one_right 3 three_mul_inverse

/-- The **input** `x = ∑ᵢ 2^{dᵢ}` of the formula `(1.6)` (binary expansion by `1`-bit positions `d`). -/
@[category API, AMS 11 37, ref "BL96" "Ber94"]
noncomputable def bval (d : ℕ → ℕ) : ℤ_[2] := ∑' i, (2 : ℤ_[2]) ^ (d i)

/-- The **claimed value** `Φ(x) = −∑ᵢ 3^{−(i+1)} 2^{dᵢ}` of the formula `(1.6)`. -/
@[category API, AMS 11 37, ref "BL96" "Ber94"]
noncomputable def Φval (d : ℕ → ℕ) : ℤ_[2] := - ∑' i, (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i)

/-- The series for `bval` converges: `‖2^{dᵢ}‖ = ‖2‖^{dᵢ} ≤ ‖2‖ⁱ` (since `dᵢ ≥ i`, `‖2‖ < 1`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem bval_summable {d : ℕ → ℕ} (hd : StrictMono d) :
    Summable (fun i => (2 : ℤ_[2]) ^ (d i)) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (norm_nonneg (2 : ℤ_[2])) norm_two_lt_one)
  intro i
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_two_lt_one.le hd.le_apply

/-- The series for `Φval` converges: `‖3⁻¹‖ = 1`, so `‖(3⁻¹)^{i+1} 2^{dᵢ}‖ = ‖2‖^{dᵢ} ≤ ‖2‖ⁱ`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem wval_summable {d : ℕ → ℕ} (hd : StrictMono d) :
    Summable (fun i => (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i)) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (norm_nonneg (2 : ℤ_[2])) norm_two_lt_one)
  intro i
  rw [norm_mul, norm_pow, norm_pow, norm_inverse_three, one_pow, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_two_lt_one.le hd.le_apply

/-- General convergence: `∑ᵢ 2^{f i}` converges whenever `f i ≥ i`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem two_pow_summable {f : ℕ → ℕ} (hf : ∀ i, i ≤ f i) :
    Summable (fun i => (2 : ℤ_[2]) ^ (f i)) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (norm_nonneg (2 : ℤ_[2])) norm_two_lt_one)
  intro i
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_two_lt_one.le (hf i)

/-- Factor a `2` out of a sum of positive powers: `∑ᵢ 2^{e i} = 2 · ∑ᵢ 2^{e i − 1}` (each `e i ≥ 1`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem tsum_two_pow_eq_two_mul {e : ℕ → ℕ} (hpos : ∀ i, 1 ≤ e i)
    (hsum : Summable (fun i => (2 : ℤ_[2]) ^ (e i - 1))) :
    ∑' i, (2 : ℤ_[2]) ^ (e i) = 2 * ∑' i, (2 : ℤ_[2]) ^ (e i - 1) := by
  rw [← hsum.tsum_mul_left]
  apply tsum_congr
  intro i
  conv_lhs => rw [show e i = 1 + (e i - 1) from by have := hpos i; omega]
  rw [pow_add, pow_one]

/-- A strictly monotone `d : ℕ → ℕ` grows at least linearly off its start: `d 0 + i ≤ d i`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem strictMono_add_le {d : ℕ → ℕ} (hd : StrictMono d) (i : ℕ) : d 0 + i ≤ d i := by
  induction i with
  | zero => simp
  | succ i ih => have := hd (show i < i + 1 by omega); omega

/-- The **bit-position update** of the shift `S`: drop a lowest bit `d₀ = 0`, decrement the rest. -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def dshift (d : ℕ → ℕ) : ℕ → ℕ :=
  if d 0 = 0 then fun i => d (i + 1) - 1 else fun i => d i - 1

/-- `dshift` preserves strict monotonicity. -/
@[category API, AMS 11 37, ref "BL96"]
theorem dshift_strictMono {d : ℕ → ℕ} (hd : StrictMono d) : StrictMono (dshift d) := by
  unfold dshift
  split
  · intro a b hab
    show d (a + 1) - 1 < d (b + 1) - 1
    have h1 : d (a + 1) < d (b + 1) := hd (by omega)
    have h2 : 1 ≤ d (a + 1) := by have := hd (show 0 < a + 1 by omega); omega
    omega
  · rename_i hne
    intro a b hab
    show d a - 1 < d b - 1
    have h1 : d a < d b := hd hab
    have h2 : 1 ≤ d a := by
      rcases Nat.eq_zero_or_pos a with rfl | hpos
      · omega
      · have := hd hpos; omega
    omega

/-- Every entry of `dshift d` is what its `bval`/`Φval` need: each new position `≥ i`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem dshift_le_apply {d : ℕ → ℕ} (hd : StrictMono d) (i : ℕ) : i ≤ dshift d i :=
  (dshift_strictMono hd).le_apply

/-- **Parity of the input** `bval d`: it is `1` iff the lowest bit is present (`d₀ = 0`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_bval {d : ℕ → ℕ} (hd : StrictMono d) :
    parity (bval d) = if d 0 = 0 then 1 else 0 := by
  by_cases h0 : d 0 = 0
  · simp only [h0, if_true]
    have hpeel : bval d = 1 + ∑' i, (2 : ℤ_[2]) ^ (d (i + 1)) := by
      rw [bval, (bval_summable hd).tsum_eq_zero_add, h0, pow_zero]
    have hdvd : (2 : ℤ_[2]) ∣ (bval d - 1) := by
      rw [hpeel, add_sub_cancel_left]
      have hpos : ∀ i, 1 ≤ d (i + 1) := fun i => by have := hd (show 0 < i + 1 by omega); omega
      rw [tsum_two_pow_eq_two_mul hpos (two_pow_summable (fun i => by have := hd.le_apply (x := i + 1); omega))]
      exact Dvd.intro _ rfl
    have hp1 : parity (1 : ℤ_[2]) = 1 := by
      have : (1 : ℤ_[2]) = ((1 : ℕ) : ℤ_[2]) := by norm_num
      rw [this, parity_natCast, CC.X_eq_mod]
    rw [parity_eq_of_two_dvd_sub hdvd, hp1]
  · simp only [h0, if_false]
    have hpos : ∀ i, 1 ≤ d i := fun i => by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · omega
      · have := hd hi; omega
    have hdvd : (2 : ℤ_[2]) ∣ (bval d - 0) := by
      rw [sub_zero, bval,
        tsum_two_pow_eq_two_mul hpos (two_pow_summable (fun i => by have := strictMono_add_le hd i; omega))]
      exact Dvd.intro _ rfl
    have hp0 : parity (0 : ℤ_[2]) = 0 := by simp [parity]
    rw [parity_eq_of_two_dvd_sub hdvd, hp0]

/-- **Input recursion `(B1)`.** The shift `S` deletes the lowest binary digit: `S (bval d) = bval
(dshift d)`. From `2 · S y = y − parity y` (`two_mul_S`), compute `2 · bval (dshift d)` case-split on
`d₀ = 0` and cancel `2`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_forward_formula"]
theorem bval_shift {d : ℕ → ℕ} (hd : StrictMono d) : S (bval d) = bval (dshift d) := by
  have key : (2 : ℤ_[2]) * bval (dshift d) = bval d - (parity (bval d) : ℤ_[2]) := by
    by_cases h0 : d 0 = 0
    · have hp : parity (bval d) = 1 := by rw [parity_bval hd, if_pos h0]
      have hds : dshift d = fun i => d (i + 1) - 1 := by unfold dshift; rw [if_pos h0]
      have hpos : ∀ i, 1 ≤ d (i + 1) := fun i => by have := hd (show 0 < i + 1 by omega); omega
      have hsum : Summable (fun i => (2 : ℤ_[2]) ^ (d (i + 1) - 1)) :=
        two_pow_summable (fun i => by have := hd.le_apply (x := i + 1); omega)
      rw [hp, Nat.cast_one, hds]
      simp only [bval]
      rw [← tsum_two_pow_eq_two_mul hpos hsum, (bval_summable hd).tsum_eq_zero_add, h0, pow_zero,
        add_sub_cancel_left]
    · have hp : parity (bval d) = 0 := by rw [parity_bval hd, if_neg h0]
      have hds : dshift d = fun i => d i - 1 := by unfold dshift; rw [if_neg h0]
      have hpos : ∀ i, 1 ≤ d i := fun i => by have := strictMono_add_le hd i; omega
      have hsum : Summable (fun i => (2 : ℤ_[2]) ^ (d i - 1)) :=
        two_pow_summable (fun i => by have := strictMono_add_le hd i; omega)
      rw [hp, Nat.cast_zero, sub_zero, hds]
      simp only [bval]
      rw [← tsum_two_pow_eq_two_mul hpos hsum]
  have h2S := two_mul_S (bval d)
  rw [← key] at h2S
  exact mul_left_cancel₀ (by norm_num) h2S

/-- Negation preserves the lowest binary digit (in `ZMod 2`, `−a = a`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_neg (z : ℤ_[2]) : parity (-z) = parity z := by
  unfold parity; rw [map_neg, CharTwo.neg_eq]

/-- `‖3⁻ᵏ‖ = 1` (powers of the unit `3⁻¹`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem norm_inv_three_pow (k : ℕ) : ‖(Ring.inverse (3 : ℤ_[2])) ^ k‖ = 1 := by
  rw [norm_pow, norm_inverse_three, one_pow]

/-- Convergence of `∑ᵢ cᵢ · 2^{eᵢ}` when the coefficients are bounded (`‖cᵢ‖ ≤ 1`) and `eᵢ ≥ i`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem coeff_two_pow_summable {c : ℕ → ℤ_[2]} {e : ℕ → ℕ} (hc : ∀ i, ‖c i‖ ≤ 1)
    (he : ∀ i, i ≤ e i) : Summable (fun i => c i * (2 : ℤ_[2]) ^ (e i)) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (norm_nonneg (2 : ℤ_[2])) norm_two_lt_one)
  intro i
  rw [norm_mul, norm_pow]
  exact le_trans (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hc i))
    (pow_le_pow_of_le_one (norm_nonneg _) norm_two_lt_one.le (he i))

/-- A sum of terms with positive `2`-powers is even: `2 ∣ ∑ᵢ cᵢ · 2^{eᵢ}` when every `eᵢ ≥ 1`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem two_dvd_tsum_of_pos {c : ℕ → ℤ_[2]} {e : ℕ → ℕ} (hpos : ∀ i, 1 ≤ e i)
    (hsum : Summable (fun i => c i * (2 : ℤ_[2]) ^ (e i - 1))) :
    (2 : ℤ_[2]) ∣ ∑' i, c i * (2 : ℤ_[2]) ^ (e i) := by
  have h : ∑' i, c i * (2 : ℤ_[2]) ^ (e i) = 2 * ∑' i, c i * (2 : ℤ_[2]) ^ (e i - 1) := by
    rw [← hsum.tsum_mul_left]
    apply tsum_congr; intro i
    conv_lhs => rw [show e i = 1 + (e i - 1) from by have := hpos i; omega]
    rw [pow_add, pow_one]; ring
  rw [h]; exact Dvd.intro _ rfl

/-- **Parity of the claimed value** `Φval d`: `1` iff `d₀ = 0` (same indicator as `bval`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_Φval {d : ℕ → ℕ} (hd : StrictMono d) :
    parity (Φval d) = if d 0 = 0 then 1 else 0 := by
  rw [Φval, parity_neg]
  by_cases h0 : d 0 = 0
  · simp only [h0, if_true]
    have hpeel : (∑' i, (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i))
        = Ring.inverse 3 + ∑' i, (Ring.inverse (3 : ℤ_[2])) ^ (i + 2) * 2 ^ (d (i + 1)) := by
      rw [(wval_summable hd).tsum_eq_zero_add]
      congr 1
      rw [h0, pow_zero, pow_one, mul_one]
    have hdvd : (2 : ℤ_[2]) ∣
        ((∑' i, (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i)) - Ring.inverse 3) := by
      rw [hpeel, add_sub_cancel_left]
      exact two_dvd_tsum_of_pos (fun i => by have := hd (show 0 < i + 1 by omega); omega)
        (coeff_two_pow_summable (fun i => (norm_inv_three_pow _).le)
          (fun i => by have := hd.le_apply (x := i + 1); omega))
    rw [parity_eq_of_two_dvd_sub hdvd, parity_inv_three]
  · simp only [h0, if_false]
    have hdvd : (2 : ℤ_[2]) ∣ ((∑' i, (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i)) - 0) := by
      rw [sub_zero]
      exact two_dvd_tsum_of_pos (fun i => by have := strictMono_add_le hd i; omega)
        (coeff_two_pow_summable (fun i => (norm_inv_three_pow _).le)
          (fun i => by have := strictMono_add_le hd i; omega))
    have hp0 : parity (0 : ℤ_[2]) = 0 := by simp [parity]
    rw [parity_eq_of_two_dvd_sub hdvd, hp0]

/-- **Lemma A**: input and claimed value have the same lowest digit, `parity (Φval d) = parity
(bval d)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_Φval_eq_bval {d : ℕ → ℕ} (hd : StrictMono d) : parity (Φval d) = parity (bval d) := by
  rw [parity_Φval hd, parity_bval hd]

/-- Factor a `2` out (coefficient version): `∑ᵢ cᵢ·2^{eᵢ} = 2·∑ᵢ cᵢ·2^{eᵢ−1}` (each `eᵢ ≥ 1`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem tsum_coeff_eq_two_mul {c : ℕ → ℤ_[2]} {e : ℕ → ℕ} (hpos : ∀ i, 1 ≤ e i)
    (hsum : Summable (fun i => c i * (2 : ℤ_[2]) ^ (e i - 1))) :
    ∑' i, c i * (2 : ℤ_[2]) ^ (e i) = 2 * ∑' i, c i * (2 : ℤ_[2]) ^ (e i - 1) := by
  rw [← hsum.tsum_mul_left]
  apply tsum_congr; intro i
  conv_lhs => rw [show e i = 1 + (e i - 1) from by have := hpos i; omega]
  rw [pow_add, pow_one]; ring

/-- Multiplying the `Φval`-series by `3` lowers every `3⁻¹`-exponent by one (`3 · 3^{−(i+1)} = 3^{−i}`):
`3 · ∑ᵢ 3^{−(i+1)} 2^{dᵢ} = ∑ᵢ 3^{−i} 2^{dᵢ}`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem three_mul_wsum {d : ℕ → ℕ} (hd : StrictMono d) :
    3 * ∑' i, (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i)
      = ∑' i, (Ring.inverse (3 : ℤ_[2])) ^ i * 2 ^ (d i) := by
  rw [← (wval_summable hd).tsum_mul_left]
  apply tsum_congr; intro i
  have h3 : (3 : ℤ_[2]) * (Ring.inverse 3) ^ (i + 1) = (Ring.inverse 3) ^ i := by
    rw [pow_succ', ← mul_assoc, three_mul_inverse, one_mul]
  rw [← mul_assoc, h3]

/-- **Value recursion `(B2)`.** The 3x+1 map acts on the `3⁻¹`-weighted sum exactly as the shift acts on
the binary expansion: `T₂ (Φval d) = Φval (dshift d)`. From `2 · T₂ y = numer y` (`two_mul_T₂`), compute
`numer (Φval d)` case-split on `d₀ = 0` (parity `1`: `(3·Φval d + 1)`; parity `0`: `Φval d`), match it to
`2 · Φval (dshift d)`, and cancel `2`. -/
@[category research solved, AMS 11 37, ref "BL96" "Ber94", group "bl_forward_formula"]
theorem Φval_step {d : ℕ → ℕ} (hd : StrictMono d) : T₂ (Φval d) = Φval (dshift d) := by
  have key : (2 : ℤ_[2]) * Φval (dshift d) = numer (Φval d) := by
    rw [numer]
    by_cases h0 : d 0 = 0
    · have hp : parity (Φval d) = 1 := by rw [parity_Φval hd, if_pos h0]
      have hds : dshift d = fun i => d (i + 1) - 1 := by unfold dshift; rw [if_pos h0]
      have hpos : ∀ i, 1 ≤ d (i + 1) := fun i => by have := hd (show 0 < i + 1 by omega); omega
      have hsumL : Summable (fun i => (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d (i + 1) - 1)) :=
        coeff_two_pow_summable (fun i => (norm_inv_three_pow _).le)
          (fun i => by have := hd.le_apply (x := i + 1); omega)
      have hsumP : Summable (fun i => (Ring.inverse (3 : ℤ_[2])) ^ i * 2 ^ (d i)) :=
        coeff_two_pow_summable (fun i => (norm_inv_three_pow _).le) (fun i => hd.le_apply)
      rw [hp, hds, pow_one, Nat.cast_one]
      simp only [Φval]
      rw [mul_neg, ← tsum_coeff_eq_two_mul hpos hsumL, neg_mul, mul_comm _ (3 : ℤ_[2]),
        three_mul_wsum hd, hsumP.tsum_eq_zero_add, pow_zero, one_mul, h0, pow_zero]
      ring
    · have hp : parity (Φval d) = 0 := by rw [parity_Φval hd, if_neg h0]
      have hds : dshift d = fun i => d i - 1 := by unfold dshift; rw [if_neg h0]
      have hpos : ∀ i, 1 ≤ d i := fun i => by have := strictMono_add_le hd i; omega
      have hsumL : Summable (fun i => (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i - 1)) :=
        coeff_two_pow_summable (fun i => (norm_inv_three_pow _).le)
          (fun i => by have := strictMono_add_le hd i; omega)
      rw [hp, hds, pow_zero, mul_one, Nat.cast_zero, add_zero]
      simp only [Φval]
      rw [mul_neg, ← tsum_coeff_eq_two_mul hpos hsumL]
  have h2T := two_mul_T₂ (Φval d)
  rw [← key] at h2T
  exact mul_left_cancel₀ (by norm_num) h2T

/-- `dshift` iterated preserves strict monotonicity. -/
@[category API, AMS 11 37, ref "BL96"]
theorem dshift_iterate_strictMono (j : ℕ) {d : ℕ → ℕ} (hd : StrictMono d) :
    StrictMono (dshift^[j] d) := by
  induction j with
  | zero => exact hd
  | succ j ih => rw [Function.iterate_succ_apply']; exact dshift_strictMono ih

/-- Iterated value recursion: `T₂ʲ (Φval d) = Φval (dshiftʲ d)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem Φval_iterate {d : ℕ → ℕ} (hd : StrictMono d) (j : ℕ) :
    T₂^[j] (Φval d) = Φval (dshift^[j] d) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' T₂ j (Φval d), ih,
      Φval_step (dshift_iterate_strictMono j hd), Function.iterate_succ_apply' dshift j d]

/-- Iterated input recursion: `Sʲ (bval d) = bval (dshiftʲ d)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem bval_iterate {d : ℕ → ℕ} (hd : StrictMono d) (j : ℕ) :
    S^[j] (bval d) = bval (dshift^[j] d) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' S j (bval d), ih,
      bval_shift (dshift_iterate_strictMono j hd), Function.iterate_succ_apply' dshift j d]

/-- **The parity vector of `Φval d` is the binary expansion of `bval d`**: `Q (Φval d) = bval d`. Each
orbit parity of `Φval d` under `T₂` equals the corresponding orbit parity of `bval d` under `S`
(iterated recursion + `parity_Φval_eq_bval`), so `tsum_parity_S` reconstructs `bval d`. -/
@[category research solved, AMS 11 37, ref "BL96" "Ber94" "Ter76", group "bl_forward_formula"]
theorem Q_Φval {d : ℕ → ℕ} (hd : StrictMono d) : Q (Φval d) = bval d := by
  unfold Q qMap
  rw [← tsum_parity_S (bval d)]
  apply tsum_congr
  intro j
  have hpar : parity (T₂^[j] (Φval d)) = parity (S^[j] (bval d)) := by
    rw [Φval_iterate hd j, parity_Φval_eq_bval (dshift_iterate_strictMono j hd), ← bval_iterate hd j]
  rw [hpar]

/-- **(1.6), PROVED** (was a cited axiom; [Ber94]). For `x = ∑ᵢ 2^{dᵢ}` with `d` strictly increasing,
`Φ(x) = − ∑ᵢ 3^{−(i+1)} 2^{dᵢ}`. Since `Φ⁻¹ = Q` (`Φ_symm_eq_Q`) and `Q (Φval d) = bval d` (`Q_Φval`),
applying `Φ` gives `Φ (bval d) = Φval d`. -/
@[category research solved, AMS 11 37, ref "BL96" "Ber94" "Ter76", group "bl_forward_formula"]
theorem Φ_eq_neg_tsum (d : ℕ → ℕ) (hd : StrictMono d) :
    Φ (∑' i, (2 : ℤ_[2]) ^ (d i)) = - ∑' i, (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i) := by
  show Φ (bval d) = Φval d
  have h := Q_Φval hd
  rw [← Φ_symm_eq_Q] at h
  rw [← h, Φ.apply_symm_apply]

end BL
