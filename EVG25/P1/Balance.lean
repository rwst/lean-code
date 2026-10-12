/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import EVG25.P1.Window
import EVG25.M0.Prefix

/-!
# Theorem B: balance of the first letter past the horizon (P1 paper, §5)

Plan EVGQ17-M0, §7.4, milestone C3.

For `N₀ ≥ 0` let `β_j(N₀) = #{N₀ ≤ n < N₀ + 2^j : U^j(n) odd} - 2^(j-1)` (`beta`).  Over `2^j`
consecutive seeds, half a period of the letter `b_j`, nothing is forced by counting.

* `zpos_eq` — **window formula, modular form**: for `n` in the window, the residue
  `z(n) = (n - N₀) + 2^j b_j(n) ∈ ℤ/2^(j+1)` is `c + Σ_{t ∈ T(n)} x_t`, with `T(n)` the set of odd
  letters before position `j`.  So `b_j(n) = [z(n) ≥ 2^j]` is a square wave of a subset sum.
* `beta_eq_sum_ghat_mul_SW` — **Fourier form**: `β_j(N₀) = Σ_k ĝ(k) S(k)` over `k ∈ ℤ/2^(j+1)`.
* `SW_eq` — `S(k) = ψ(kc) ∏_{t<j} (1 + ψ(k x_t))`, via the prefix bijection of M0.
* `sum_norm_sq_SW` — **Parseval**: `Σ_k |S(k)|² = 2^(j+1) · 2^j`.
* `ghat_eq_zero_of_even`, `norm_ghat_le` — the square-wave coefficients: `ĝ(k) = 0` for even `k`,
  `|ĝ(k)| ≤ 1/(2 min(k, 2^(j+1) - k))` for odd `k`.
* `norm_prod_le` — **uniform chain decay**: for every odd `k`,
  `|∏_t (1 + ψ(k x_t))| ≤ 2^j cos(π/5)^m` with `m = ⌊log₃((j+4)/4)⌋`; the factors are
  `2|cos π y(3/2)^s / 4|` along the real orbit of an odd integer `y`, so Theorem A′ applies.
* `abs_beta_le` — **Theorem B (Lean form)**: for every `K ≥ 1`,
  `|β_j(N₀)| ≤ 2^j ((K+1) cos(π/5)^m + 1/√K)`.
* `beta_balance` — hence `β_j(N₀) = o(2^j)` uniformly in `N₀`: in every window of `2^j`
  consecutive seeds, the proportion with `U^j(n)` odd tends to `1/2`.

The paper has the sharper exponent `0.2126` and `log K` in place of `K + 1`; the Lean form keeps
the crude constants, which suffice for `o(2^j)`.
-/

open Finset Real CC CC.Base3div2 ZMod
open scoped ComplexConjugate

namespace EVG25.P1

/-! ## Setting -/

/-- `β_j(N₀)`, the signed excess of odd `U^j(n)` over the window `[N₀, N₀ + 2^j)`. -/
noncomputable def beta (j N₀ : ℕ) : ℝ :=
  ∑ n ∈ Ico N₀ (N₀ + 2 ^ j), (((U_iter j n % 2 : ℕ) : ℝ) - 1 / 2)

theorem beta_eq_card (j N₀ : ℕ) :
    beta j N₀ = (((Ico N₀ (N₀ + 2 ^ j)).filter fun n => U_iter j n % 2 = 1).card : ℝ)
      - 2 ^ j / 2 := by
  unfold beta
  rw [sum_sub_distrib, sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
    card_filter, nsmul_eq_mul]
  push_cast
  congr 1
  · refine sum_congr rfl fun n _ => ?_
    rcases Nat.mod_two_eq_zero_or_one (U_iter j n) with h | h <;> simp [h]
  · ring

/-- The square wave on `ℤ/2^(j+1)`: `+1/2` on the upper half, `-1/2` on the lower half. -/
noncomputable def sqWave (j : ℕ) (x : ZMod (2 ^ (j + 1))) : ℂ :=
  if 2 ^ j ≤ x.val then 1 / 2 else -1 / 2

/-- The residue `z(n) = (n - N₀) + 2^j b_j(n)`. -/
def zpos (j N₀ n : ℕ) : ZMod (2 ^ (j + 1)) := ((n - N₀ + 2 ^ j * (U_iter j n % 2) : ℕ) : ZMod _)

theorem zpos_val {j N₀ n : ℕ} (hn : n ∈ Ico N₀ (N₀ + 2 ^ j)) :
    (zpos j N₀ n).val = n - N₀ + 2 ^ j * (U_iter j n % 2) := by
  rw [mem_Ico] at hn
  unfold zpos
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  have : U_iter j n % 2 ≤ 1 := by omega
  have : 2 ^ j * (U_iter j n % 2) ≤ 2 ^ j := by nlinarith
  rw [pow_succ]; omega

theorem sqWave_zpos {j N₀ n : ℕ} (hn : n ∈ Ico N₀ (N₀ + 2 ^ j)) :
    sqWave j (zpos j N₀ n) = ((U_iter j n % 2 : ℕ) : ℂ) - 1 / 2 := by
  unfold sqWave
  rw [zpos_val hn]
  have hlt : n - N₀ < 2 ^ j := by rw [mem_Ico] at hn; omega
  rcases Nat.mod_two_eq_zero_or_one (U_iter j n) with h | h
  · simp only [h, show ¬ (2 ^ j ≤ n - N₀ + 2 ^ j * 0) by omega, ↓reduceIte]; push_cast; ring
  · simp only [h, show 2 ^ j ≤ n - N₀ + 2 ^ j * 1 by omega, ↓reduceIte]; push_cast; ring

theorem zpos_injOn (j N₀ : ℕ) : Set.InjOn (zpos j N₀) (Ico N₀ (N₀ + 2 ^ j) : Set ℕ) := by
  intro n hn n' hn' h
  have hn1 := mem_Ico.1 (Finset.mem_coe.1 hn)
  have hn2 := mem_Ico.1 (Finset.mem_coe.1 hn')
  have h1 := congrArg (fun z => z.val % 2 ^ j) h
  simp only [zpos_val (Finset.mem_coe.1 hn), zpos_val (Finset.mem_coe.1 hn'),
    Nat.add_mul_mod_self_left] at h1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  omega

/-! ## The window formula in `ℤ/2^(j+1)` -/

/-- `3⁻¹` in `ℤ/2^(j+1)`. -/
noncomputable def u3 (j : ℕ) : ZMod (2 ^ (j + 1)) := (3 : ZMod _)⁻¹

theorem three_mul_u3 (j : ℕ) : (3 : ZMod (2 ^ (j + 1))) * u3 j = 1 := by
  have h := ZMod.coe_mul_inv_eq_one (n := 2 ^ (j + 1)) 3
    (Nat.Coprime.pow_right _ (by norm_num))
  simpa [u3] using h

/-- The subset-sum weights `x_t = 3^(-j) 3^(j-1-t) 2^t`. -/
noncomputable def xt (j t : ℕ) : ZMod (2 ^ (j + 1)) := u3 j ^ j * 3 ^ (j - 1 - t) * 2 ^ t

/-- The shift `c`. -/
noncomputable def cst (j N₀ : ℕ) : ZMod (2 ^ (j + 1)) :=
  -(u3 j ^ j * ∑ t ∈ range j, 2 * 3 ^ (j - 1 - t) * 2 ^ t) - N₀

/-- The odd letters before position `j`. -/
def Tset (j n : ℕ) : Finset ℕ := (range j).filter fun t => U_iter t n % 2 = 1

/-- **Window formula, modular form.** `z(n) = c + Σ_{t ∈ T(n)} x_t` in `ℤ/2^(j+1)`. -/
@[category API, AMS 11 37, group "evgq17_p1"]
theorem zpos_eq {j N₀ n : ℕ} (hn : N₀ ≤ n) :
    zpos j N₀ n = cst j N₀ + ∑ t ∈ Tset j n, xt j t := by
  set b := U_iter j n % 2 with hb
  set A := ∑ t ∈ range j, cDigit n t * 3 ^ (j - 1 - t) * 2 ^ t with hA
  have hW := two_pow_mul_U_iter j n
  rw [← hA] at hW
  -- `2^(j+1) ∣ 2^j U^j(n) + 3^j 2^j b`
  have hdvd : 2 ^ (j + 1) ∣ 3 ^ j * n + A + 3 ^ j * 2 ^ j * b := by
    rw [← hW]
    have hodd : 3 ^ j % 2 = 1 := by rw [Nat.pow_mod]; simp
    obtain ⟨q, hq⟩ : 2 ∣ U_iter j n + 3 ^ j * b := by
      have : (U_iter j n + 3 ^ j * b) % 2 = 0 := by
        rw [Nat.add_mod, Nat.mul_mod, hodd, hb]; rcases Nat.mod_two_eq_zero_or_one (U_iter j n) with h | h <;> simp [h]
      exact Nat.dvd_of_mod_eq_zero this
    exact ⟨q, by rw [pow_succ]; linear_combination 2 ^ j * hq⟩
  have key : (3 : ZMod (2 ^ (j + 1))) ^ j * (n : ZMod (2 ^ (j + 1))) + (A : ZMod (2 ^ (j + 1)))
      + 3 ^ j * 2 ^ j * (b : ZMod (2 ^ (j + 1))) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at this; exact this
  have hu : u3 j ^ j * 3 ^ j = 1 := by rw [← mul_pow, mul_comm, three_mul_u3, one_pow]
  -- the appended digits
  have hc : ∀ t, ((cDigit n t : ℕ) : ZMod (2 ^ (j + 1))) = 2 - ((U_iter t n % 2 : ℕ) : ZMod _) := by
    intro t
    have : U_iter t n % 2 ≤ 2 := by omega
    unfold cDigit; push_cast [Nat.cast_sub this]; ring
  have hAc : (A : ZMod (2 ^ (j + 1))) = ∑ t ∈ range j, 2 * 3 ^ (j - 1 - t) * 2 ^ t
      - ∑ t ∈ Tset j n, 3 ^ (j - 1 - t) * 2 ^ t := by
    rw [hA, Tset, sum_filter]; push_cast
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [hc]
    rcases Nat.mod_two_eq_zero_or_one (U_iter t n) with h | h
    · simp [h]
    · simp [h]; ring
  have hz : zpos j N₀ n = (n : ZMod (2 ^ (j + 1))) - N₀ + 2 ^ j * (b : ZMod (2 ^ (j + 1))) := by
    unfold zpos; push_cast [Nat.cast_sub hn]; ring
  rw [hz, cst]
  simp only [xt, mul_assoc (u3 j ^ j)]
  rw [← mul_sum]
  calc (n : ZMod (2 ^ (j + 1))) - N₀ + 2 ^ j * (b : ZMod (2 ^ (j + 1)))
      = u3 j ^ j * 3 ^ j * ((n : ZMod (2 ^ (j + 1))) + 2 ^ j * (b : ZMod (2 ^ (j + 1)))) - N₀ := by rw [hu]; ring
    _ = u3 j ^ j * (-(A : ZMod (2 ^ (j + 1)))) - N₀ := by linear_combination (u3 j ^ j) * key
    _ = _ := by rw [hAc]; ring

/-! ## The Fourier form -/

/-- The square-wave coefficients `ĝ(k) = N⁻¹ (𝓕 g)(k)`, `N = 2^(j+1)`. -/
noncomputable def ghat (j : ℕ) (k : ZMod (2 ^ (j + 1))) : ℂ :=
  ((2 ^ (j + 1) : ℕ) : ℂ)⁻¹ * 𝓕 (sqWave j) k

theorem sqWave_eq_sum (j : ℕ) (x : ZMod (2 ^ (j + 1))) :
    sqWave j x = ∑ k, ghat j k * stdAddChar (k * x) := by
  have h := congrFun (dft.symm_apply_apply (sqWave j)) x
  rw [invDFT_apply] at h
  rw [← h, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [ghat, smul_eq_mul]; ring

/-- The window sum `S(k) = Σ_{n} ψ(k z(n))`. -/
noncomputable def SW (j N₀ : ℕ) (k : ZMod (2 ^ (j + 1))) : ℂ :=
  ∑ n ∈ Ico N₀ (N₀ + 2 ^ j), stdAddChar (k * zpos j N₀ n)

/-- **Fourier form.** `β_j(N₀) = Σ_k ĝ(k) S(k)`. -/
@[category API, AMS 11 37 42, group "evgq17_p1"]
theorem beta_eq_sum_ghat_mul_SW (j N₀ : ℕ) :
    (beta j N₀ : ℂ) = ∑ k, ghat j k * SW j N₀ k := by
  unfold beta SW
  push_cast
  rw [sum_congr rfl fun n hn => (sqWave_zpos hn).symm]
  simp_rw [sqWave_eq_sum, mul_sum]
  exact sum_comm

/-- The prefix bijection: the window `[N₀, N₀ + 2^j)` is in bijection with the subsets of
`range j` via `n ↦ T(n)`. -/
theorem sum_window_Tset {M : Type*} [AddCommMonoid M] (j N₀ : ℕ) (F : Finset ℕ → M) :
    ∑ n ∈ Ico N₀ (N₀ + 2 ^ j), F (Tset j n) = ∑ T ∈ (range j).powerset, F T := by
  classical
  have hinj : Set.InjOn (Tset j) (Ico N₀ (N₀ + 2 ^ j) : Set ℕ) := by
    intro n hn n' hn' h
    have hn1 := mem_Ico.1 (Finset.mem_coe.1 hn)
    have hn2 := mem_Ico.1 (Finset.mem_coe.1 hn')
    have hp : EVG25.M0.uPrefix j n = EVG25.M0.uPrefix j n' := by
      funext i
      have := congrArg (fun T => i.val ∈ T) h
      simp only [Tset, mem_filter, mem_range, i.isLt, true_and, eq_iff_iff] at this
      simp only [EVG25.M0.uPrefix, EVG25.M0.uLetter, this]
    have hm := EVG25.M0.mod_two_pow_eq_of_uPrefix_eq j hp
    rcases le_total n n' with hle | hle
    · have hd := (Nat.modEq_iff_dvd' hle).1 hm
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd := (Nat.modEq_iff_dvd' hle).1 hm.symm
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
  rw [← sum_image hinj]
  congr 1
  apply eq_of_subset_of_card_le
  · intro T hT
    obtain ⟨n, _, rfl⟩ := mem_image.1 hT
    exact mem_powerset.2 (filter_subset _ _)
  · rw [card_image_of_injOn hinj, card_powerset, card_range, Nat.card_Ico, Nat.add_sub_cancel_left]

/-- An additive character maps finite sums to products. -/
theorem addChar_map_sum {A M ι : Type*} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M)
    (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- **Product formula.** `S(k) = ψ(kc) ∏_{t<j} (1 + ψ(k x_t))`. -/
@[category API, AMS 11 37 42, group "evgq17_p1"]
theorem SW_eq (j N₀ : ℕ) (k : ZMod (2 ^ (j + 1))) :
    SW j N₀ k = stdAddChar (k * cst j N₀) * ∏ t ∈ range j, (1 + stdAddChar (k * xt j t)) := by
  unfold SW
  rw [prod_one_add, mul_sum,
    ← sum_window_Tset j N₀ (fun T => stdAddChar (k * cst j N₀) * ∏ t ∈ T, stdAddChar (k * xt j t))]
  refine sum_congr rfl fun n hn => ?_
  rw [zpos_eq (mem_Ico.1 hn).1, mul_add, AddChar.map_add_eq_mul, mul_sum, addChar_map_sum]

/-- **Parseval.** `Σ_k |S(k)|² = 2^(j+1) · 2^j`, because the residues `z(n)` are distinct. -/
@[category API, AMS 11 37 42, group "evgq17_p1"]
theorem sum_norm_sq_SW (j N₀ : ℕ) :
    ∑ k, ‖SW j N₀ k‖ ^ 2 = (2 : ℝ) ^ (j + 1) * 2 ^ j := by
  classical
  set W := Ico N₀ (N₀ + 2 ^ j)
  have hC : ∀ k, ((‖SW j N₀ k‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ W, ∑ n' ∈ W, stdAddChar (k * (zpos j N₀ n - zpos j N₀ n')) := by
    intro k
    rw [Complex.ofReal_pow, ← Complex.mul_conj', SW, map_sum, sum_mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => ?_
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]; ring_nf
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [hC]
  rw [sum_comm]
  have hinner : ∀ n ∈ W, ∑ k, ∑ n' ∈ W, stdAddChar (k * (zpos j N₀ n - zpos j N₀ n'))
      = ((2 ^ (j + 1) : ℕ) : ℂ) := by
    intro n hn
    rw [sum_comm]
    rw [sum_eq_single n]
    · rw [sub_self, AddChar.sum_mulShift _ (isPrimitive_stdAddChar _)]
      simp [ZMod.card]
    · intro n' hn' hne
      have hne' : zpos j N₀ n - zpos j N₀ n' ≠ 0 :=
        fun h0 => hne (zpos_injOn j N₀ hn' hn (sub_eq_zero.1 h0).symm)
      rw [AddChar.sum_mulShift _ (isPrimitive_stdAddChar _)]
      simp [hne']
    · intro h; exact absurd hn h
  rw [sum_congr rfl hinner, sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
  push_cast; ring

/-! ## The square-wave coefficients -/

theorem sum_zmod_eq_sum_range {N : ℕ} [NeZero N] {M : Type*} [AddCommMonoid M]
    (F : ZMod N → M) : ∑ x, F x = ∑ m ∈ range N, F m :=
  sum_nbij' (fun x => x.val) (fun m => (m : ZMod N)) (fun x _ => mem_range.2 (ZMod.val_lt x))
    (fun _ _ => mem_univ _) (fun x _ => ZMod.natCast_zmod_val x)
    (fun _ hm => ZMod.val_natCast_of_lt (mem_range.1 hm)) (fun x _ => by rw [ZMod.natCast_zmod_val])

theorem stdAddChar_natCast {N : ℕ} [NeZero N] (a : ℕ) :
    stdAddChar (a : ZMod N) = Complex.exp (2 * π * Complex.I * a / N) := by
  simpa using stdAddChar_coe (N := N) (a : ℤ)

/-- `ψ(-k)^(2^j) = (-1)^k`. -/
theorem stdAddChar_neg_pow (j : ℕ) (k : ZMod (2 ^ (j + 1))) :
    stdAddChar (-k) ^ 2 ^ j = (-1 : ℂ) ^ k.val := by
  have hk : 2 ^ j • (-k) = (((-(2 ^ j * k.val : ℕ) : ℤ)) : ZMod (2 ^ (j + 1))) := by
    rw [nsmul_eq_mul]; push_cast; rw [ZMod.natCast_zmod_val]; ring
  rw [← AddChar.map_nsmul_eq_pow, hk, stdAddChar_coe]
  have : 2 * π * Complex.I * ((((-(2 ^ j * k.val : ℕ) : ℤ)) : ℂ)) / ((2 ^ (j + 1) : ℕ) : ℂ)
      = (k.val : ℂ) * (-(π * Complex.I)) := by
    push_cast; field_simp; ring
  rw [this, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

theorem dft_sqWave (j : ℕ) (k : ZMod (2 ^ (j + 1))) :
    𝓕 (sqWave j) k
      = 1 / 2 * ((-1 : ℂ) ^ k.val - 1) * ∑ m ∈ range (2 ^ j), stdAddChar (-k) ^ m := by
  have hsum : ∀ f : ℕ → ℂ, ∑ m ∈ range (2 ^ (j + 1)), f m
      = ∑ m ∈ range (2 ^ j), f m + ∑ m ∈ range (2 ^ j), f (2 ^ j + m) := by
    intro f; rw [pow_succ, mul_two, sum_range_add]
  have hpow : ∀ m : ℕ, stdAddChar (-((m : ZMod (2 ^ (j + 1))) * k)) = stdAddChar (-k) ^ m := by
    intro m
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]; ring_nf
  rw [dft_apply, sum_zmod_eq_sum_range, hsum]
  have h1 : ∀ m ∈ range (2 ^ j), stdAddChar (-((m : ZMod (2 ^ (j + 1))) * k))
      • sqWave j (m : ZMod (2 ^ (j + 1))) = -(1 / 2) * stdAddChar (-k) ^ m := by
    intro m hm
    have hm' := mem_range.1 hm
    have hv : (m : ZMod (2 ^ (j + 1))).val = m :=
      ZMod.val_natCast_of_lt (by rw [pow_succ]; omega)
    rw [smul_eq_mul, sqWave, hv, hpow]
    simp only [show ¬ (2 ^ j ≤ m) by omega, ↓reduceIte]; ring
  have h2 : ∀ m ∈ range (2 ^ j), stdAddChar (-(((2 ^ j + m : ℕ) : ZMod (2 ^ (j + 1))) * k))
      • sqWave j ((2 ^ j + m : ℕ) : ZMod (2 ^ (j + 1)))
      = 1 / 2 * (stdAddChar (-k) ^ 2 ^ j * stdAddChar (-k) ^ m) := by
    intro m hm
    have hm' := mem_range.1 hm
    have hv : ((2 ^ j + m : ℕ) : ZMod (2 ^ (j + 1))).val = 2 ^ j + m :=
      ZMod.val_natCast_of_lt (by rw [pow_succ]; omega)
    rw [smul_eq_mul, sqWave, hv, hpow, pow_add]
    simp only [show 2 ^ j ≤ 2 ^ j + m by omega, ↓reduceIte]; ring
  rw [sum_congr rfl h1, sum_congr rfl h2, stdAddChar_neg_pow, ← mul_sum, ← mul_sum, ← mul_sum]
  ring

theorem ghat_eq_zero_of_even (j : ℕ) {k : ZMod (2 ^ (j + 1))} (hk : Even k.val) :
    ghat j k = 0 := by
  rw [ghat, dft_sqWave, hk.neg_one_pow]; ring

theorem norm_ghat_of_odd (j : ℕ) {k : ZMod (2 ^ (j + 1))} (hk : Odd k.val) :
    ‖ghat j k‖ = 1 / (2 ^ (j + 1) * Real.sin (π * k.val / 2 ^ (j + 1))) := by
  set ω := stdAddChar (-k)
  have hpow : ω ^ 2 ^ j = -1 := by rw [stdAddChar_neg_pow, hk.neg_one_pow]
  have hω : ω ≠ 1 := by
    intro h; rw [h, one_pow] at hpow; norm_num at hpow
  have hk0 : 0 < k.val := hk.pos
  have hkN : k.val < 2 ^ (j + 1) := ZMod.val_lt k
  -- `ω = exp(i x)` with `x = -2π k / N`
  have hωx : ω = Complex.exp (Complex.I * ((-(2 * π * k.val / 2 ^ (j + 1)) : ℝ) : ℂ)) := by
    have : -k = (((-(k.val : ℤ)) : ℤ) : ZMod (2 ^ (j + 1))) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    simp only [ω]
    rw [this, stdAddChar_coe]; congr 1; push_cast; ring
  have hsin : 0 < Real.sin (π * k.val / 2 ^ (j + 1)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ (by positivity)]
      have : (k.val : ℝ) < 2 ^ (j + 1) := by exact_mod_cast hkN
      nlinarith [Real.pi_pos]
  have hnorm : ‖ω - 1‖ = 2 * Real.sin (π * k.val / 2 ^ (j + 1)) := by
    rw [hωx, Complex.norm_exp_I_mul_ofReal_sub_one,
      show -(2 * π * k.val / 2 ^ (j + 1)) / 2 = -(π * k.val / 2 ^ (j + 1)) by ring,
      Real.sin_neg, mul_neg, norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hsin]
    norm_num
  have hF : 𝓕 (sqWave j) k = 2 / (ω - 1) := by
    rw [dft_sqWave, hk.neg_one_pow, geom_sum_eq hω, hpow]
    have : ω - 1 ≠ 0 := sub_ne_zero.2 hω
    field_simp; ring
  rw [ghat, hF, norm_mul, norm_div, hnorm, norm_inv]
  push_cast
  rw [Complex.norm_pow, Complex.norm_ofNat]
  field_simp

/-- Jordan's inequality on both halves: `sin(π m/N) ≥ 2 min(m, N-m)/N`. -/
theorem sin_ge_min (N m : ℕ) (hm : m < N) :
    2 * ((min m (N - m) : ℕ) : ℝ) / N ≤ Real.sin (π * m / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rcases le_total m (N - m) with h | h
  · rw [min_eq_left h]
    have h2 : (2 * m : ℝ) ≤ N := by exact_mod_cast (show 2 * m ≤ N by omega)
    have := Real.mul_le_sin (x := π * m / N) (by positivity)
      (by rw [div_le_iff₀ hN]; nlinarith [Real.pi_pos])
    calc 2 * (m : ℝ) / N = 2 / π * (π * m / N) := by field_simp
      _ ≤ _ := this
  · rw [min_eq_right h, Nat.cast_sub hm.le]
    have hle : ((N - m : ℕ) : ℝ) ≤ m := by exact_mod_cast h
    rw [Nat.cast_sub hm.le] at hle
    have hmN : (m : ℝ) < N := by exact_mod_cast hm
    have := Real.mul_le_sin (x := π * (N - m) / N) (by
      have : (0 : ℝ) ≤ N - m := by linarith
      positivity) (by rw [div_le_iff₀ hN]; nlinarith [Real.pi_pos])
    rw [show π * (m : ℝ) / N = π - π * (N - m) / N by field_simp; ring, Real.sin_pi_sub]
    calc 2 * ((N : ℝ) - m) / N = 2 / π * (π * (N - m) / N) := by field_simp
      _ ≤ _ := this

/-- `pm k = min(k, N - k)`, the size of the frequency `k`. -/
def pm (j : ℕ) (k : ZMod (2 ^ (j + 1))) : ℕ := min k.val (2 ^ (j + 1) - k.val)

theorem one_le_pm_of_odd (j : ℕ) {k : ZMod (2 ^ (j + 1))} (hk : Odd k.val) : 1 ≤ pm j k := by
  have h0 : 0 < k.val := hk.pos
  have h1 : k.val < 2 ^ (j + 1) := ZMod.val_lt k
  unfold pm; omega

/-- **Square-wave coefficients.** `|ĝ(k)| ≤ 1/(2 min(k, N-k))` for odd `k`. -/
@[category API, AMS 42, group "evgq17_p1"]
theorem norm_ghat_le (j : ℕ) {k : ZMod (2 ^ (j + 1))} (hk : Odd k.val) :
    ‖ghat j k‖ ≤ 1 / (2 * (pm j k : ℝ)) := by
  rw [norm_ghat_of_odd j hk]
  have hp : (1 : ℝ) ≤ pm j k := by exact_mod_cast one_le_pm_of_odd j hk
  have hs := sin_ge_min (2 ^ (j + 1)) k.val (ZMod.val_lt k)
  push_cast at hs
  apply one_div_le_one_div_of_le (by positivity)
  have hN : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  calc 2 * (pm j k : ℝ) = 2 ^ (j + 1) * (2 * (pm j k : ℝ) / 2 ^ (j + 1)) := by field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hN.le
      simpa [pm] using hs

/-! ## Uniform chain decay -/

/-- Odd frequencies stay odd under multiplication by the unit `3^(-j)`. -/
theorem odd_val_mul_u3_pow (j : ℕ) {k : ZMod (2 ^ (j + 1))} (hk : Odd k.val) :
    Odd (k * u3 j ^ j).val := by
  have h2 : 2 ∣ 2 ^ (j + 1) := dvd_pow_self 2 (Nat.succ_ne_zero j)
  set φ := ZMod.castHom h2 (ZMod 2)
  have hval : ∀ x : ZMod (2 ^ (j + 1)), ((x.val : ℕ) : ZMod 2) = φ x := by
    intro x; rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hu : φ (u3 j) = 1 := by
    have h := congrArg φ (three_mul_u3 j)
    rw [map_mul, map_one, map_ofNat] at h
    have h3 : (3 : ZMod 2) = 1 := by decide
    rwa [h3, one_mul] at h
  rw [← ZMod.natCast_eq_one_iff_odd, hval, map_mul, map_pow, hu, one_pow, mul_one, ← hval]
  exact ZMod.natCast_eq_one_iff_odd.2 hk

theorem norm_one_add_exp (x : ℝ) :
    ‖1 + Complex.exp (Complex.I * x)‖ = 2 * |Real.cos (x / 2)| := by
  have h : 1 + Complex.exp (Complex.I * x)
      = -(Complex.exp (Complex.I * ((x + π : ℝ) : ℂ)) - 1) := by
    push_cast
    rw [mul_add, Complex.exp_add, mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I]; ring
  rw [h, norm_neg, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (x + π) / 2 = x / 2 + π / 2 by ring, Real.sin_add_pi_div_two, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs]
  norm_num

/-- `m_j = ⌊log₃((j+4)/4)⌋`, the guaranteed number of bad steps on a chain of length `j`. -/
def mj (j : ℕ) : ℕ := Nat.log 3 ((j + 4) / 4)

/-- **Uniform chain decay.** For every odd frequency `k`,
`|∏_{t<j} (1 + ψ(k x_t))| ≤ 2^j cos(π/5)^(m_j)`.  The factors are `2|cos π θ_s|` along the chain
`θ_s = y·3^(s-2)/2^s`, `2 ≤ s ≤ j+1`, of the odd integer `y = k·3^(-j)`, i.e. along the real
orbit `y (3/2)^s / 9`; Theorem A′ (`prod_abs_cos_le`, `add_two_le_mul_three_pow_bad`) applies. -/
@[category research solved, AMS 11 42, group "evgq17_p1"]
theorem norm_prod_le (j : ℕ) {k : ZMod (2 ^ (j + 1))} (hk : Odd k.val) :
    ‖∏ t ∈ range j, (1 + stdAddChar (k * xt j t))‖ ≤ 2 ^ j * Real.cos (π / 5) ^ mj j := by
  set y : ℕ := (k * u3 j ^ j).val with hydef
  have hy : Odd y := odd_val_mul_u3_pow j hk
  -- the chain
  set a : ℕ → ℤ := fun s => (y : ℤ) * 3 ^ (s - 2) with hadef
  have hodd : ∀ s, Odd (a s) := fun s => (Int.odd_coe_nat _ |>.2 hy).mul (Odd.pow (by decide))
  have hrel : ∀ s, (2 : ℤ) ^ s ∣ a (s + 1) - 3 * a s := by
    intro s
    rcases s with _ | _ | s
    · simp
    · exact ⟨-(y : ℤ), by simp only [hadef]; norm_num; ring⟩
    · refine ⟨0, ?_⟩
      simp only [hadef]
      rw [show s + 1 + 1 + 1 - 2 = (s + 1 + 1 - 2) + 1 by omega, pow_succ]; ring
  set θ : ℕ → ℝ := fun s => (a s : ℝ) / 2 ^ s with hθ
  set e : ℕ → ℝ := fun s => θ s - round (θ s) with he
  have hch : ∀ s, 1 ≤ s → (∃ z : ℤ, 2 * e (s + 1) - 3 * e s = z) ∧ (1 / 2 : ℝ) ^ s ≤ |e s| ∧
      |e s| ≤ 1 / 2 ∧ |Real.cos (π * e s)| = |Real.cos (π * θ s)| :=
    fun s hs => dyadic_chain a hodd hrel s hs
  have hrel' : ∀ u, ∃ z : ℤ, 2 * e (u + 1) - 3 * e u = z := fun u => dyadic_chain_rel a hrel u
  have hlow : ∀ s, 1 ≤ s → (1 / 2 : ℝ) ^ s ≤ |e s| := fun s hs => (hch s hs).2.1
  have hhalf : ∀ s, |e s| ≤ 1 / 2 := fun s => abs_sub_round _
  -- each factor
  have hfac : ∀ t ∈ range j,
      ‖1 + stdAddChar (k * xt j t)‖ = 2 * |Real.cos (π * e (2 + (j - 1 - t)))| := by
    intro t ht
    have ht' := mem_range.1 ht
    have hx : k * xt j t = ((y * 3 ^ (j - 1 - t) * 2 ^ t : ℕ) : ZMod (2 ^ (j + 1))) := by
      simp only [xt, hydef]; push_cast; rw [ZMod.natCast_zmod_val]; ring
    have harg : 2 * π * Complex.I * ((y * 3 ^ (j - 1 - t) * 2 ^ t : ℕ) : ℂ)
        / ((2 ^ (j + 1) : ℕ) : ℂ) = Complex.I * ((2 * (π * θ (2 + (j - 1 - t))) : ℝ) : ℂ) := by
      simp only [hθ, hadef]
      rw [show 2 + (j - 1 - t) - 2 = j - 1 - t by omega]
      have hp : (2 : ℂ) ^ (j + 1) = 2 ^ t * 2 ^ (2 + (j - 1 - t)) := by
        rw [← pow_add]; congr 1; omega
      push_cast
      rw [hp]
      field_simp
    rw [hx, stdAddChar_natCast, harg, norm_one_add_exp,
      show 2 * (π * θ (2 + (j - 1 - t))) / 2 = π * θ (2 + (j - 1 - t)) by ring,
      (hch _ (by omega)).2.2.2]
  -- the product
  have hprod : ‖∏ t ∈ range j, (1 + stdAddChar (k * xt j t))‖
      = 2 ^ j * ∏ s ∈ Ico 2 (j + 2), |Real.cos (π * e s)| := by
    rw [norm_prod, prod_congr rfl hfac, prod_mul_distrib, prod_const, card_range]
    congr 1
    rw [prod_Ico_eq_prod_range, show j + 2 - 2 = j by omega]
    exact prod_range_reflect (fun r => |Real.cos (π * e (2 + r))|) j
  rw [hprod]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (prod_abs_cos_le hhalf 2 (j + 2)).trans ?_
  -- at least `m_j` bad steps
  have hbad : 1 / 5 ≤ |e 2| := le_trans (by norm_num) (hlow 2 (by norm_num))
  have hB := add_two_le_mul_three_pow_bad hrel' hlow hbad (j + 2) (by omega)
  have hm : mj j ≤ badCount e 2 (j + 2) := by
    have h1 : 3 ^ mj j ≤ (j + 4) / 4 := Nat.pow_log_le_self 3 (by omega)
    have h2 : 4 * 3 ^ mj j ≤ j + 4 := by
      have := Nat.mul_le_mul_left 4 h1
      exact this.trans (Nat.mul_div_le (j + 4) 4)
    have h3 : 3 ^ mj j ≤ 3 ^ badCount e 2 (j + 2) := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have hc5 : 0 ≤ Real.cos (π / 5) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  exact pow_le_pow_of_le_one hc5 (Real.cos_le_one _) hm

/-! ## Theorem B -/

theorem norm_SW_le (j N₀ : ℕ) {k : ZMod (2 ^ (j + 1))} (hk : Odd k.val) :
    ‖SW j N₀ k‖ ≤ 2 ^ j * Real.cos (π / 5) ^ mj j := by
  rw [SW_eq, norm_mul, AddChar.norm_apply, one_mul]; exact norm_prod_le j hk

/-- Telescoping: `Σ_{K < m < M} 1/m² ≤ 1/K`. -/
theorem sum_inv_sq_tail (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ m ∈ range M, (if K < m then 1 / (m : ℝ) ^ 2 else 0) ≤ 1 / (K : ℝ) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have key : ∀ n : ℕ, ∑ m ∈ range (K + 1 + n), (if K < m then 1 / (m : ℝ) ^ 2 else 0)
      ≤ 1 / (K : ℝ) - 1 / ((K : ℝ) + n) := by
    intro n
    induction n with
    | zero =>
      rw [add_zero, sum_eq_zero (fun m hm => by
        have := mem_range.1 hm; simp only [show ¬ K < m by omega, ↓reduceIte])]
      simp
    | succ n ih =>
      rw [show K + 1 + (n + 1) = (K + 1 + n) + 1 by ring, sum_range_succ]
      simp only [show K < K + 1 + n by omega, ↓reduceIte]
      have ha : (1 : ℝ) ≤ K + n := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
      have hstep : 1 / ((K + 1 + n : ℕ) : ℝ) ^ 2
          ≤ 1 / ((K : ℝ) + n) - 1 / ((K : ℝ) + ((n + 1 : ℕ) : ℝ)) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at hstep ⊢
      linarith
  calc _ ≤ ∑ m ∈ range (K + 1 + M), (if K < m then 1 / (m : ℝ) ^ 2 else 0) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          (fun m _ _ => by split_ifs <;> positivity)
    _ ≤ 1 / (K : ℝ) - 1 / ((K : ℝ) + M) := key M
    _ ≤ 1 / (K : ℝ) := by
      have : (0 : ℝ) ≤ 1 / ((K : ℝ) + M) := by positivity
      linarith

/-- The square-wave tail: `Σ_{min(k, N-k) > K} 1/(4 min(k, N-k)²) ≤ 1/(2K)`. -/
theorem tail_sum (j K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ univ.filter (fun k : ZMod (2 ^ (j + 1)) => ¬ pm j k ≤ K), 1 / (4 * (pm j k : ℝ) ^ 2)
      ≤ 1 / (2 * (K : ℝ)) := by
  set N := 2 ^ (j + 1) with hN
  set G : ℕ → ℝ := fun m => (if K < m then 1 / (m : ℝ) ^ 2 else 0)
    + (if K < N - m then 1 / ((N - m : ℕ) : ℝ) ^ 2 else 0) with hG
  have hG0 : ∀ m, 0 ≤ G m := fun m => by
    simp only [hG]; split_ifs <;> positivity
  have hpt : ∀ k ∈ univ.filter (fun k : ZMod N => ¬ pm j k ≤ K),
      1 / (4 * (pm j k : ℝ) ^ 2) ≤ 1 / 4 * G k.val := by
    intro k hk
    have hk' := (mem_filter.1 hk).2
    unfold pm at hk'
    have h1 : K < k.val := by omega
    have h2 : K < N - k.val := by omega
    simp only [hG, h1, h2, ↓reduceIte]
    have e1 : (0 : ℝ) ≤ 1 / (k.val : ℝ) ^ 2 := by positivity
    have e2 : (0 : ℝ) ≤ 1 / ((N - k.val : ℕ) : ℝ) ^ 2 := by positivity
    unfold pm
    rcases le_total k.val (N - k.val) with h | h
    · rw [min_eq_left h]
      have : 1 / (4 * (k.val : ℝ) ^ 2) = 1 / 4 * (1 / (k.val : ℝ) ^ 2) := by ring
      rw [this]; nlinarith
    · rw [min_eq_right h]
      have : 1 / (4 * ((N - k.val : ℕ) : ℝ) ^ 2) = 1 / 4 * (1 / ((N - k.val : ℕ) : ℝ) ^ 2) := by
        ring
      rw [this]; nlinarith
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  have hall : ∑ k ∈ univ.filter (fun k : ZMod N => ¬ pm j k ≤ K), G k.val
      ≤ ∑ m ∈ range N, G m := by
    refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => hG0 _)).trans
      (le_of_eq ?_)
    rw [sum_zmod_eq_sum_range (fun k : ZMod N => G k.val)]
    exact sum_congr rfl fun m hm => by rw [ZMod.val_natCast_of_lt (mem_range.1 hm)]
  have hfirst := sum_inv_sq_tail K hK N
  have hsecond : ∑ m ∈ range N, (if K < N - m then 1 / ((N - m : ℕ) : ℝ) ^ 2 else 0)
      ≤ 1 / (K : ℝ) := by
    rw [← sum_range_reflect]
    have : ∀ m ∈ range N, (if K < N - (N - 1 - m) then 1 / ((N - (N - 1 - m) : ℕ) : ℝ) ^ 2 else 0)
        = (fun i : ℕ => if K < i then 1 / (i : ℝ) ^ 2 else 0) (m + 1) := by
      intro m hm
      have := mem_range.1 hm
      rw [show N - (N - 1 - m) = m + 1 by omega]
    rw [sum_congr rfl this]
    refine le_trans ?_ (sum_inv_sq_tail K hK (N + 1))
    rw [sum_range_succ' (fun i : ℕ => if K < i then 1 / (i : ℝ) ^ 2 else 0) N]
    simp only [show ¬ K < 0 by omega, ↓reduceIte, add_zero, le_refl]
  have hsplit : ∑ m ∈ range N, G m = ∑ m ∈ range N, (if K < m then 1 / (m : ℝ) ^ 2 else 0)
      + ∑ m ∈ range N, (if K < N - m then 1 / ((N - m : ℕ) : ℝ) ^ 2 else 0) := sum_add_distrib
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  calc 1 / 4 * ∑ k ∈ univ.filter (fun k : ZMod N => ¬ pm j k ≤ K), G k.val
      ≤ 1 / 4 * (1 / (K : ℝ) + 1 / (K : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    _ = 1 / (2 * (K : ℝ)) := by field_simp; ring

/-- The tail of the Fourier form: Cauchy–Schwarz and Parseval give
`Σ_{min(k, N-k) > K} |ĝ(k)| |S(k)| ≤ 2^j/√K`. -/
theorem tail_le (j N₀ K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ univ.filter (fun k : ZMod (2 ^ (j + 1)) => ¬ pm j k ≤ K), ‖ghat j k‖ * ‖SW j N₀ k‖
      ≤ 2 ^ j / Real.sqrt K := by
  set T := univ.filter (fun k : ZMod (2 ^ (j + 1)) => ¬ pm j k ≤ K) with hT
  have hcs := sum_mul_sq_le_sq_mul_sq T (fun k => ‖ghat j k‖) (fun k => ‖SW j N₀ k‖)
  have hg2 : ∑ k ∈ T, ‖ghat j k‖ ^ 2 ≤ 1 / (2 * (K : ℝ)) := by
    refine le_trans (sum_le_sum fun k hk => ?_) (tail_sum j K hK)
    rcases Nat.even_or_odd k.val with h | h
    · rw [ghat_eq_zero_of_even j h, norm_zero, zero_pow two_ne_zero]; positivity
    · have hp : (1 : ℝ) ≤ pm j k := by exact_mod_cast one_le_pm_of_odd j h
      calc ‖ghat j k‖ ^ 2 ≤ (1 / (2 * (pm j k : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_ghat_le j h) 2
        _ = 1 / (4 * (pm j k : ℝ) ^ 2) := by ring
  have hS2 : ∑ k ∈ T, ‖SW j N₀ k‖ ^ 2 ≤ 2 ^ (j + 1) * 2 ^ j :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)).trans
      (sum_norm_sq_SW j N₀).le
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hsq : (∑ k ∈ T, ‖ghat j k‖ * ‖SW j N₀ k‖) ^ 2 ≤ (2 ^ j / Real.sqrt K) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hKr.le]
    calc (∑ k ∈ T, ‖ghat j k‖ * ‖SW j N₀ k‖) ^ 2
        ≤ (∑ k ∈ T, ‖ghat j k‖ ^ 2) * ∑ k ∈ T, ‖SW j N₀ k‖ ^ 2 := hcs
      _ ≤ 1 / (2 * (K : ℝ)) * (2 ^ (j + 1) * 2 ^ j) :=
          mul_le_mul hg2 hS2 (sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = (2 ^ j) ^ 2 / K := by rw [pow_succ]; field_simp
  exact (pow_le_pow_iff_left₀ (sum_nonneg fun k _ => by positivity) (by positivity)
    (by norm_num)).1 hsq

/-- **Theorem B (Lean form).** For all `j`, `N₀` and `K ≥ 1`,
`|β_j(N₀)| ≤ 2^j ((K+1) cos(π/5)^(m_j) + 1/√K)`, `m_j = ⌊log₃((j+4)/4)⌋`.  Split the Fourier form
at `min(k, N-k) = K`: the head is bounded by the uniform chain decay, the tail by Cauchy–Schwarz
and Parseval. -/
@[category research solved, AMS 11 37 42, group "evgq17_p1"]
theorem abs_beta_le (j N₀ K : ℕ) (hK : 1 ≤ K) :
    |beta j N₀| ≤ 2 ^ j * ((K + 1) * Real.cos (π / 5) ^ mj j + 1 / Real.sqrt K) := by
  set δ := Real.cos (π / 5) ^ mj j with hδ
  have hδ0 : 0 ≤ δ := pow_nonneg (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])) _
  set F : ZMod (2 ^ (j + 1)) → ℝ := fun k => ‖ghat j k‖ * ‖SW j N₀ k‖ with hF
  have hstart : |beta j N₀| ≤ ∑ k, F k := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, beta_eq_sum_ghat_mul_SW]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [hF, norm_mul]
  rw [← sum_filter_add_sum_filter_not univ (fun k => pm j k ≤ K)] at hstart
  -- the head
  have hhead : ∑ k ∈ univ.filter (fun k => pm j k ≤ K), F k ≤ (K + 1) * (2 ^ j * δ) := by
    have hpt : ∀ k ∈ univ.filter (fun k => pm j k ≤ K), F k ≤ 1 / 2 * (2 ^ j * δ) := by
      intro k _
      rcases Nat.even_or_odd k.val with h | h
      · simp only [hF, ghat_eq_zero_of_even j h, norm_zero, zero_mul]; positivity
      · have hp : (1 : ℝ) ≤ pm j k := by exact_mod_cast one_le_pm_of_odd j h
        have h1 : ‖ghat j k‖ ≤ 1 / 2 := (norm_ghat_le j h).trans
          (one_div_le_one_div_of_le (by norm_num) (by linarith))
        exact mul_le_mul h1 (norm_SW_le j N₀ h) (norm_nonneg _) (by norm_num)
    have hcard : (univ.filter (fun k : ZMod (2 ^ (j + 1)) => pm j k ≤ K)).card ≤ 2 * K + 1 := by
      calc _ ≤ (range (K + 1) ∪ Ico (2 ^ (j + 1) - K) (2 ^ (j + 1))).card := by
            apply card_le_card_of_injOn (fun k => k.val)
            · intro k hk
              have h1 := (mem_filter.1 hk).2
              have hl := ZMod.val_lt k
              unfold pm at h1
              refine Finset.mem_coe.2 ?_
              simp only [mem_union, mem_range, mem_Ico]
              omega
            · intro k _ k' _ h; exact ZMod.val_injective _ h
        _ ≤ (range (K + 1)).card + (Ico (2 ^ (j + 1) - K) (2 ^ (j + 1))).card := card_union_le _ _
        _ ≤ 2 * K + 1 := by rw [card_range, Nat.card_Ico]; omega
    have hcard' : ((univ.filter (fun k : ZMod (2 ^ (j + 1)) => pm j k ≤ K)).card : ℝ)
        ≤ 2 * K + 1 := by exact_mod_cast hcard
    calc _ ≤ ∑ k ∈ univ.filter (fun k => pm j k ≤ K), 1 / 2 * (2 ^ j * δ) := sum_le_sum hpt
      _ = ((univ.filter (fun k : ZMod (2 ^ (j + 1)) => pm j k ≤ K)).card : ℝ)
          * (1 / 2 * (2 ^ j * δ)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * K + 1) * (1 / 2 * (2 ^ j * δ)) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ ≤ (K + 1) * (2 ^ j * δ) := by
          have : (0 : ℝ) ≤ 2 ^ j * δ := by positivity
          nlinarith
  have htail : ∑ k ∈ univ.filter (fun k => ¬ pm j k ≤ K), F k ≤ 2 ^ j / Real.sqrt K :=
    tail_le j N₀ K hK
  calc |beta j N₀| ≤ _ := hstart
    _ ≤ (K + 1) * (2 ^ j * δ) + 2 ^ j / Real.sqrt K := add_le_add hhead htail
    _ = _ := by ring

/-- **The first letter past the horizon is balanced.** `β_j(N₀) = o(2^j)` uniformly in `N₀`: in
every window of `2^j` consecutive seeds the proportion with `U^j(n)` odd tends to `1/2`. -/
@[category research solved, AMS 11 37, group "evgq17_p1"]
theorem beta_balance {ε : ℝ} (hε : 0 < ε) :
    ∃ J, ∀ j ≥ J, ∀ N₀, |beta j N₀| ≤ ε * 2 ^ j := by
  set K : ℕ := ⌈4 / ε ^ 2⌉₊ + 1 with hKdef
  have hK : 1 ≤ K := by omega
  have hKr : 4 / ε ^ 2 ≤ K := by
    have := Nat.le_ceil (4 / ε ^ 2)
    rw [hKdef]; push_cast; linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hsq : 1 / Real.sqrt K ≤ ε / 2 := by
    have h2 : (2 : ℝ) ≤ ε * Real.sqrt K := by
      rw [← Real.sqrt_sq hε.le, ← Real.sqrt_mul (by positivity),
        show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      have := mul_le_mul_of_nonneg_left hKr (sq_nonneg ε)
      rwa [mul_div_cancel₀ _ (by positivity)] at this
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 hK0) (by norm_num)]
    linarith
  have hρ0 : 0 ≤ Real.cos (π / 5) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have hρ1 : Real.cos (π / 5) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) (by positivity)
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (2 * (K + 1)) by positivity) hρ1
  refine ⟨4 * 3 ^ M, fun j hj N₀ => ?_⟩
  have hmj : M ≤ mj j := by
    unfold mj
    apply Nat.le_log_of_pow_le (by norm_num)
    rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
  have hδ : Real.cos (π / 5) ^ mj j ≤ ε / (2 * (K + 1)) :=
    (pow_le_pow_of_le_one hρ0 hρ1.le hmj).trans hM.le
  calc |beta j N₀| ≤ 2 ^ j * ((K + 1) * Real.cos (π / 5) ^ mj j + 1 / Real.sqrt K) :=
        abs_beta_le j N₀ K hK
    _ ≤ 2 ^ j * ((K + 1) * (ε / (2 * (K + 1))) + ε / 2) := by gcongr
    _ = ε * 2 ^ j := by field_simp; ring

end EVG25.P1
