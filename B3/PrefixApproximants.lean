/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.BlockDigits
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Pre-period–aware approximants: `Φ` of a prefix-then-periodic value (Route (i), Phase 3)

The Adamczewski–Bugeaud approximant `αₘ` is a finite pre-period `Uₘ` (length `t = rₘ + sₘ`) followed by
the block `Vₘ` repeated forever. As a `2`-adic integer this is

> `prefixBlockVal A t c p e := (A : ℤ₂) + 2^t · blockVal c p e`,

with the pre-period `A < 2^t` an explicit integer and the periodic tail shifted up by `2^t`. The point
of this file is the **rationality of `Φ(prefixBlockVal)`**, which `Φ_blockValue_mem_ratInt` alone does
*not* give: `Φ` is **not additive**, so a pre-period cannot be peeled off the value. Instead we use the
**bit-peel recursion** for `Φ`, derived from the conjugacy `Φ ∘ S = T₂ ∘ Φ` (`BL.Φ_semiconj`):

> `Φ(2·x) = 2·Φ(x)`        (`Φ_two_mul`)
> `Φ(1 + 2·x) = (2·Φ(x) − 1)·3⁻¹`   (`Φ_one_add_two_mul`).

*Proof of the recursion:* `S(b + 2x) = x` (`S_natCast_add_two_mul`), so `T₂(Φ(b + 2x)) = Φ(x)`; and
`parity (Φ(b + 2x)) = b` (`Φ_mod_two`), so the defining identity `2·T₂ y = y·3^{parity y} + parity y`
(`BL.two_mul_T₂`) reads `2·Φ(x) = Φ(b+2x)` for `b = 0` and `2·Φ(x) = 3·Φ(1+2x) + 1` for `b = 1`.

Peeling the pre-period bit by bit (`prefixBlockVal A (t+1) = (A%2) + 2·prefixBlockVal (A/2) t`) and using
that `RatInt = ℚ ∩ ℤ₂` is closed under `x ↦ 2x` and `x ↦ (2x−1)·3⁻¹`, an induction on `t` gives

> `Φ(prefixBlockVal A t c p e) ∈ RatInt`   (`Φ_prefixBlockVal_mem_ratInt`),

bottoming out at `Φ(blockVal) ∈ RatInt` (`Φ_blockValue_mem_ratInt`). This is the general rational
approximant `Φ(αₘ)` of Adamczewski–Bugeaud's Lemma 1 (denominator `2^{rₘ}(3^{sₘ} − 2^{pₘ})`-shaped),
now *with* the pre-period. The digit side is handled by the shift fixed point: `S^[t](prefixBlockVal) =
blockVal` (`S_iterate_prefixBlockVal`, from `S_iterate_natCast_add`), giving
`binaryDigit (prefixBlockVal A t …) k = binaryDigit (blockVal …) (k − t)` for `k ≥ t` and `= A`'s bit for
`k < t` — exactly the structure needed to match `v` (pre-period `Uₘ` then periodic) for `hagree`.

No new `axiom`s.

## Contents
* `Φ_two_mul`, `Φ_one_add_two_mul` — the bit-peel recursion for `Φ`.
* `ratInt_two_mul`, `ratInt_step_one`, `coe_inverse_three` — closure of `RatInt` under the two steps.
* `prefixBlockVal` — the pre-period–aware approximant `(A : ℤ₂) + 2^t · blockVal`.
* `Φ_prefixBlockVal_mem_ratInt` — (proved) `Φ(prefixBlockVal) ∈ RatInt`.
* `S_iterate_prefixBlockVal`, `binaryDigit_prefixBlockVal_ge`, `binaryDigit_prefixBlockVal_lt` — its
  digits: the pre-period `A` then `blockVal`'s digits.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the conjugacy `Φ ∘ S = T₂ ∘ Φ`, the map `T₂`).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§4, Lemma 1: the periodic-completion approximants with pre-period).
-/

namespace B3

open BL AB Function Filter

/-! ### The bit-peel recursion for `Φ` -/

/-- `toZMod (2 : ℤ₂) = 0` (`2` lies in the maximal ideal). -/
@[category API, AMS 11 37, ref "BL96"]
theorem toZMod_two : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
  have hc2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_cast
  rw [← hc2, map_natCast]; exact ZMod.natCast_self 2

/-- **`Φ` doubles on even arguments:** `Φ (2·x) = 2·Φ(x)`. *Proof:* `S(2x) = x` so
`T₂(Φ(2x)) = Φ(x)` (`Φ_semiconj`); `Φ(2x)` is even (`Φ_mod_two`, `parity (Φ(2x)) = 0`), so the defining
identity gives `2·T₂(Φ(2x)) = Φ(2x)`, i.e. `2·Φ(x) = Φ(2x)`. -/
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

/-- **`Φ` on odd arguments:** `Φ (1 + 2·x) = (2·Φ(x) − 1)·3⁻¹` (`3⁻¹ = Ring.inverse 3`). *Proof:* as
`Φ_two_mul`, but `parity (Φ(1+2x)) = 1`, so `2·T₂(Φ(1+2x)) = 3·Φ(1+2x) + 1`, i.e.
`2·Φ(x) = 3·Φ(1+2x) + 1`; solve for `Φ(1+2x)` (multiply by the unit `3⁻¹`). -/
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

/-! ### `RatInt` is closed under the two steps -/

/-- `RatInt` is closed under addition. -/
@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_add {y z : ℤ_[2]} (hy : y ∈ RatInt) (hz : z ∈ RatInt) : y + z ∈ RatInt := by
  obtain ⟨q, hq⟩ := hy; obtain ⟨r, hr⟩ := hz
  exact ⟨q + r, by push_cast; rw [hq, hr]⟩

/-- `RatInt` is closed under subtraction. -/
@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_sub {y z : ℤ_[2]} (hy : y ∈ RatInt) (hz : z ∈ RatInt) : y - z ∈ RatInt := by
  obtain ⟨q, hq⟩ := hy; obtain ⟨r, hr⟩ := hz
  exact ⟨q - r, by push_cast; rw [hq, hr]⟩

/-- `RatInt` is closed under multiplication. -/
@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_mul {y z : ℤ_[2]} (hy : y ∈ RatInt) (hz : z ∈ RatInt) : y * z ∈ RatInt := by
  obtain ⟨q, hq⟩ := hy; obtain ⟨r, hr⟩ := hz
  exact ⟨q * r, by push_cast; rw [hq, hr]⟩

/-- `1 ∈ RatInt`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_one : (1 : ℤ_[2]) ∈ RatInt := ⟨1, by norm_cast⟩

/-- `2 ∈ RatInt`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_two : (2 : ℤ_[2]) ∈ RatInt := ⟨2, by norm_cast⟩

/-- The image of `3⁻¹ = Ring.inverse (3 : ℤ₂)` in `ℚ₂` is `(3 : ℚ₂)⁻¹` (the coercion is a ring hom and
`3` is a unit). -/
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

/-- `3⁻¹ = Ring.inverse 3 ∈ RatInt`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_inverse_three : Ring.inverse (3 : ℤ_[2]) ∈ RatInt :=
  ⟨1 / 3, by rw [coe_inverse_three]; norm_num⟩

/-- `RatInt` is closed under doubling: `y ∈ RatInt → 2·y ∈ RatInt`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_two_mul {y : ℤ_[2]} (hy : y ∈ RatInt) : 2 * y ∈ RatInt :=
  ratInt_mul ratInt_two hy

/-- `RatInt` is closed under the odd step: `y ∈ RatInt → (2·y − 1)·3⁻¹ ∈ RatInt`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem ratInt_step_one {y : ℤ_[2]} (hy : y ∈ RatInt) :
    (2 * y - 1) * Ring.inverse 3 ∈ RatInt :=
  ratInt_mul (ratInt_sub (ratInt_mul ratInt_two hy) ratInt_one) ratInt_inverse_three

/-- **`RatInt` is closed under `Ring.inverse` of units.** If `x ∈ RatInt` is a unit in `ℤ₂` then
`Ring.inverse x ∈ RatInt`: its `ℚ₂`-image is `(x : ℚ₂)⁻¹ = (q : ℚ₂)⁻¹` (where `(x:ℚ₂)=(q:ℚ₂)`), the image
of the rational `q⁻¹`. *Proof:* `Ring.inverse_mul_cancel` casts to `(Ring.inverse x:ℚ₂)·(x:ℚ₂)=1`, so
`(Ring.inverse x:ℚ₂)=(x:ℚ₂)⁻¹` (`eq_inv_of_mul_eq_one_left`); then `Rat.cast_inv`. The `c=1` precursor is
`ratInt_inverse_three`. -/
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

/-- **The periodic completion is a rational `2`-adic number (proved).** `blockVal c p e ∈ RatInt`: the
block value telescopes to `blockVal · (1 − 2^p) = ∑_{r<c} 2^{blockPos r}` (the first block; via
`blockPos_add_period` and `Summable.sum_add_tsum_nat_add`, `1 − 2^p` a unit since `‖2^p‖ < 1`), so
`blockVal = (∑_{r<c} 2^{blockPos r}) · (1 − 2^p)⁻¹` — an integer times `Ring.inverse (1 − 2^p) ∈ RatInt`
(`ratInt_ring_inverse`). This is the `v`-side analogue of `Φ_blockValue_mem_ratInt` (the `Φ`-image
version); unlike that one it does **not** route through `Φ`, so it is the *preimage* rationality the
no-divergence argument needs to certify approximants differ from an irrational limit
(`B3.truncApprox_mem_ratInt`). Empty block `c = 0` ↦ `0 ∈ RatInt` (`blockVal_zero`). -/
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

/-! ### The pre-period–aware approximant and its rationality -/

/-- The **pre-period–aware approximant**: pre-period integer `A` (`A < 2^t`) then the block `Vₘ`
repeated, i.e. `(A : ℤ₂) + 2^t · blockVal c p e`. The Adamczewski–Bugeaud `αₘ = Uₘ Vₘ Vₘ ⋯`. -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def prefixBlockVal (A t c p : ℕ) (e : ℕ → ℕ) : ℤ_[2] :=
  (A : ℤ_[2]) + 2 ^ t * blockVal c p e

/-- **Rationality of the pre-period approximant (proved).** `Φ(prefixBlockVal A t c p e) ∈ RatInt`
(`= ℚ ∩ ℤ₂`) whenever `A < 2^t`. *Proof* by induction on the pre-period length `t`: peel the lowest bit
(`prefixBlockVal A (t+1) = (A%2) + 2·prefixBlockVal (A/2) t`), apply the bit-peel recursion
(`Φ_two_mul` / `Φ_one_add_two_mul`) and `RatInt` closure (`ratInt_two_mul` / `ratInt_step_one`); the base
case is `Φ(blockVal) ∈ RatInt` (`Φ_blockValue_mem_ratInt`). Since `Φ` is *not* additive, this genuinely
needs the recursion, not a split of the value. -/
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

/-! ### The digits of the pre-period approximant -/

/-- The shift collapses the pre-period: `S^[t](prefixBlockVal A t c p e) = blockVal c p e` (for
`A < 2^t`). From `S_iterate_natCast_add`. -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem S_iterate_prefixBlockVal {A t c p : ℕ} {e : ℕ → ℕ} (hA : A < 2 ^ t) :
    S^[t] (prefixBlockVal A t c p e) = blockVal c p e := by
  unfold prefixBlockVal
  exact S_iterate_natCast_add t A (blockVal c p e) hA

/-- Past the pre-period, the digits are `blockVal`'s: for `k ≥ t`,
`binaryDigit (prefixBlockVal A t …) k = binaryDigit (blockVal …) (k − t)`. -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_ge {A t c p : ℕ} {e : ℕ → ℕ} (hA : A < 2 ^ t) {k : ℕ}
    (hk : t ≤ k) :
    binaryDigit (prefixBlockVal A t c p e) k = binaryDigit (blockVal c p e) (k - t) := by
  unfold binaryDigit
  conv_lhs => rw [← Nat.sub_add_cancel hk]
  rw [Function.iterate_add_apply, S_iterate_prefixBlockVal hA]

/-- Within the pre-period, the digits are those of the integer `A`: for `k < t`,
`binaryDigit (prefixBlockVal A t …) k = binaryDigit (A : ℤ₂) k` (`= Nat.testBit A k`). From
`prefixBlockVal ≡ A (mod 2^t)` and `binaryDigit_agree_of_dvd_two_pow`. -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_lt {A t c p : ℕ} {e : ℕ → ℕ} {k : ℕ} (hk : k < t) :
    binaryDigit (prefixBlockVal A t c p e) k = binaryDigit ((A : ℕ) : ℤ_[2]) k := by
  refine binaryDigit_agree_of_dvd_two_pow t _ _ ?_ k hk
  unfold prefixBlockVal
  rw [add_sub_cancel_left]
  exact dvd_mul_right _ _

end B3
