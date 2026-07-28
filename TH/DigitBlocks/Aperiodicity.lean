/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.DigitBlocks.GapPrinciples
import Mathlib.Data.Nat.Log

/-!
# Theorem B2: the binary period-`p` breaks of `3^m` grow

Milestone **M-5 = Theorem B2** of the digit-block plan ([A4+] §3.2), the "novel
core": no window of the binary expansion of `3^m` deeper than `polylog` is
`p`-periodic, for every fixed period `p`.  With `breakCount p n` the number of
positions `i < M := ⌊log₂ n⌋` at which `bitᵢ ≠ bitᵢ₊ₚ`,

  `∀ p ≥ 1, ∃ C_p > 0, ∀ m ≥ 2 :
      log m/(log log m + C_p) − 2 ≤ breakCount p (3^m)`

(`breakCount_three_pow_lower`).  The `p = 1` case is B1's transition count
(sharper); larger `p` detects the failure of every fixed periodicity.

## Proof

The engine is **gap principle P** (`TH/DigitBlocks/GapPrinciples.lean`), the
four-log Baker–Wüstholz lemma: a `p`-periodic window `[x, y)` (trimmed to a
multiple of `p`) collapses `3^m` to `(2^p − 1)·3^m = A₁'·2^{y'} + E` with `E`
**odd** — the parity nondegeneracy again — giving a small four-log form.  Each
depth window `[M − θ^{j+1}, M − θ^j)` above a `θ ≍ p²·log(2m+p)` threshold is
therefore *not* `p`-periodic (`window_break`); the `k = ⌊log_θ M⌋` disjoint
windows inject into the break set (`log_le_breakCount`), and the generalized
pigeonhole endgame `windowCount_lower_bound_gen` (with coefficient
`κ_p ≍ p²·log p`) converts this to the headline bound.  Footprint
std3 + `BakerWustholz.linearForms_logs` ([BW93]).

## Contents

* `breakCount` — the period-`p` break count (`category API`).
* `breakCount_three_pow_lower` — **Theorem B2**.
* `breakCount_three_pow_tendsto_atTop` — corollary: `breakCount p (3^m) → ∞`.

## References

* [A4+] `plan-A4+.html` (this repository, 2026-07): §2 (gap principle P), §3.2
  (B2), §5.2 (this file).
* [BW93] Baker, Wüstholz, *Logarithmic forms and group varieties*, J. reine
  angew. Math. **442** (1993).  (Via `CITED/BakerWustholz.lean`.)
* [Ste80] Stewart, *On the representation of an integer in two different bases*,
  J. reine angew. Math. **319** (1980).  (The `p = 1` digit-change template.)
-/

namespace TH


private noncomputable def Bp (p : ℕ) : ℝ := 2 + (Real.log (2 + p) + 1) / Real.log 2
private noncomputable def kappa (p : ℕ) : ℝ :=
  BakerWustholz.C 4 1 * Real.log 3 * p * (1 + 2 * p) * Bp p + (p + 1) + 2 * p

private lemma hmaxbound {m p : ℕ} (hm : 2 ≤ m) :
    max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 ≤ Bp p * Real.log m := by
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2R
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  have hlog2pos : (0 : ℝ) < Real.log 2 := log_two_pos'
  have hlog2p_pos : (0 : ℝ) ≤ Real.log (2 + (p : ℝ)) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) p])
  refine max_le ?_ ?_
  · have h2mp : ((2 * m + p : ℕ) : ℝ) ≤ (2 + (p : ℝ)) * m := by
      have : (2 * m + p : ℕ) ≤ (2 + p) * m := by nlinarith [hm]
      calc ((2 * m + p : ℕ) : ℝ) ≤ (((2 + p) * m : ℕ) : ℝ) := by exact_mod_cast this
        _ = (2 + (p : ℝ)) * m := by push_cast; ring
    have hstep : Real.log ((2 * m + p : ℕ) : ℝ) ≤ Real.log (2 + (p : ℝ)) + Real.log m := by
      calc Real.log ((2 * m + p : ℕ) : ℝ)
          ≤ Real.log ((2 + (p : ℝ)) * m) := Real.log_le_log (by positivity) h2mp
        _ = Real.log (2 + (p : ℝ)) + Real.log m := by
            rw [Real.log_mul (by positivity) (by positivity)]
    have hbig : Real.log (2 + (p : ℝ)) + Real.log m ≤ Bp p * Real.log m := by
      rw [Bp]
      have hlp : Real.log (2 + (p : ℝ)) ≤ (Real.log (2 + p) + 1) * Real.log m / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]; nlinarith [hlogm, hlog2p_pos]
      have hexp : (2 + (Real.log (2 + p) + 1) / Real.log 2) * Real.log m
          = 2 * Real.log m + (Real.log (2 + p) + 1) * Real.log m / Real.log 2 := by ring
      rw [hexp]; linarith
    linarith
  · rw [Bp]
    have : (2 : ℝ) * Real.log m ≤ (2 + (Real.log (2 + p) + 1) / Real.log 2) * Real.log m := by
      have hnn : (0 : ℝ) ≤ (Real.log (2 + p) + 1) / Real.log 2 := by positivity
      nlinarith [hlogm_pos, hnn]
    nlinarith [Real.log_two_gt_d9, hlogm]

private lemma window_break {m p θ j : ℕ} (hm : 2 ≤ m) (hp : 1 ≤ p) (hθ2 : 2 ≤ θ)
    (hthr : kappa p * Real.log m < (θ : ℝ) * Real.log 2)
    (hj : θ ^ (j + 1) < Nat.log 2 (3 ^ m)) :
    ∃ i, Nat.log 2 (3 ^ m) - θ ^ (j + 1) ≤ i ∧ i + p < Nat.log 2 (3 ^ m) - θ ^ j
      ∧ (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + p) := by
  set M : ℕ := Nat.log 2 (3 ^ m) with hMdef
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2R
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  have hlog2pos : (0 : ℝ) < Real.log 2 := log_two_pos'
  -- θ ≥ 2p+1 from the threshold (κ ≥ 2p, m ≥ 2)
  have hBpnn : (0 : ℝ) ≤ Bp p := by
    rw [Bp]
    have hln : (0 : ℝ) ≤ Real.log (2 + (p : ℝ)) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) p])
    have : (0 : ℝ) ≤ (Real.log (2 + (p : ℝ)) + 1) / Real.log 2 :=
      div_nonneg (by linarith) log_two_pos'.le
    linarith
  have hκ2p : (2 * p : ℝ) ≤ kappa p := by
    rw [kappa]
    have h1 : (0 : ℝ) ≤ BakerWustholz.C 4 1 * Real.log 3 * p * (1 + 2 * p) * Bp p :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (C_one_nonneg 4) log_three_pos'.le)
        (Nat.cast_nonneg p)) (by positivity)) hBpnn
    have h2 : (0 : ℝ) ≤ (p : ℝ) + 1 := by positivity
    linarith
  have hθ2p : (2 * p : ℝ) < (θ : ℝ) := by
    have h1 : kappa p ≤ kappa p * (Real.log m / Real.log 2) := by
      have : (1 : ℝ) ≤ Real.log m / Real.log 2 := by rw [le_div_iff₀ hlog2pos]; linarith
      nlinarith [le_trans (by positivity : (0:ℝ) ≤ 2*(p:ℝ)) hκ2p]
    have h2 : kappa p * Real.log m / Real.log 2 < θ := by
      rw [div_lt_iff₀ hlog2pos]; linarith [hthr]
    have h3 : kappa p * (Real.log m / Real.log 2) = kappa p * Real.log m / Real.log 2 := by ring
    rw [h3] at h1
    calc (2 * p : ℝ) ≤ kappa p := hκ2p
      _ ≤ kappa p * Real.log m / Real.log 2 := h1
      _ < θ := h2
  have hθ2pN : 2 * p + 1 ≤ θ := by
    have : (2 * p : ℝ) < (θ : ℝ) := hθ2p
    have : (2 * p : ℕ) < θ := by exact_mod_cast this
    omega
  -- window geometry
  have hpowlt : θ ^ j < θ ^ (j + 1) := by
    have h1 : θ ^ (j + 1) = θ ^ j * θ := pow_succ θ j
    have h2 : 1 ≤ θ ^ j := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hjM : θ ^ j ≤ M := by omega
  have hx1 : 1 ≤ M - θ ^ (j + 1) := by omega
  have hxy : M - θ ^ (j + 1) < M - θ ^ j := by omega
  have h2pwin : 2 * p ≤ (M - θ ^ j) - (M - θ ^ (j + 1)) := by
    have h1 : θ ^ (j + 1) = θ ^ j * θ := pow_succ θ j
    have h2 : 1 ≤ θ ^ j := Nat.one_le_pow _ _ (by omega)
    have h4 : 2 * p + θ ^ j ≤ θ ^ (j + 1) := by
      nlinarith [Nat.mul_le_mul (le_refl (θ ^ j)) (show 2 * p + 1 ≤ θ from by omega), h1, h2]
    omega
  by_contra hc
  push Not at hc
  have hper : ∀ i, M - θ ^ (j + 1) ≤ i → i + p < M - θ ^ j →
      (3 ^ m).testBit i = (3 ^ m).testBit (i + p) := by
    intro i hi1 hi2
    have := hc i hi1 hi2
    simpa using this
  have hgp := gap_principle (by omega : 1 ≤ m) hp hx1 hxy (Nat.sub_le _ _) h2pwin hper
  rw [← hMdef] at hgp
  -- cast the window endpoints
  have hXc : (M : ℝ) - ((M - θ ^ (j + 1) : ℕ) : ℝ) = (θ : ℝ) ^ (j + 1) := by
    rw [Nat.cast_sub hj.le]; push_cast; ring
  have hYc : (M : ℝ) + 2 * p - ((M - θ ^ j : ℕ) : ℝ) = (θ : ℝ) ^ j + 2 * p := by
    rw [Nat.cast_sub hjM]; push_cast; ring
  rw [hXc, hYc] at hgp
  -- contradiction
  have hθj1 : (1 : ℝ) ≤ (θ : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ θ))
  have hθjpos : (0 : ℝ) < (θ : ℝ) ^ j := by positivity
  have hLb : max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 ≤ Bp p * Real.log m := hmaxbound hm
  have hCPnn : (0 : ℝ) ≤ BakerWustholz.C 4 1 * Real.log 3 * p :=
    mul_nonneg (mul_nonneg (C_one_nonneg 4) log_three_pos'.le) (Nat.cast_nonneg p)
  have hpoweq : (θ : ℝ) ^ (j + 1) = θ * (θ : ℝ) ^ j := by rw [pow_succ]; ring
  -- RHS of hgp ≤ θ^j · (κ log m)
  have hLnn : (0 : ℝ) ≤ max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 := le_trans zero_le_one (le_max_right _ _)
  have hbound : (θ : ℝ) ^ (j + 1) * Real.log 2 ≤ (θ : ℝ) ^ j * (kappa p * Real.log m) := by
    have hstep1 : BakerWustholz.C 4 1 * (p : ℝ) * Real.log 3 * ((θ : ℝ) ^ j + 2 * p)
          * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 + (p + 1) * Real.log 2
        ≤ (θ : ℝ) ^ j * (kappa p * Real.log m) := by
      rw [kappa]
      set L : ℝ := max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 with hLdef
      set Cp : ℝ := BakerWustholz.C 4 1 * (p : ℝ) * Real.log 3 with hCpdef
      have hCp : (0 : ℝ) ≤ Cp := by
        rw [hCpdef]
        exact mul_nonneg (mul_nonneg (C_one_nonneg 4) (Nat.cast_nonneg p)) log_three_pos'.le
      have hlogmnn : (0 : ℝ) ≤ Real.log m := hlogm_pos.le
      have hA : ((θ : ℝ) ^ j + 2 * p) ≤ (θ : ℝ) ^ j * (1 + 2 * p) := by
        nlinarith [hθj1, Nat.cast_nonneg (α := ℝ) p]
      have hT1 : 0 ≤ Cp * ((θ : ℝ) ^ j + 2 * p) * (Bp p * Real.log m - L) :=
        mul_nonneg (mul_nonneg hCp (by positivity)) (by linarith [hLb])
      have hT2 : 0 ≤ Cp * Bp p * Real.log m * ((θ : ℝ) ^ j * (1 + 2 * p) - ((θ : ℝ) ^ j + 2 * p)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hCp hBpnn) hlogmnn) (by linarith [hA])
      have hT3 : 0 ≤ ((θ : ℝ) ^ j - 1) * (((p : ℝ) + 1) + 2 * p) * Real.log m :=
        mul_nonneg (mul_nonneg (by linarith [hθj1]) (by positivity)) hlogmnn
      have hT4 : 0 ≤ ((p : ℝ) + 1) * (Real.log m - Real.log 2) :=
        mul_nonneg (by positivity) (by linarith [hlogm])
      nlinarith [hT1, hT2, hT3, hT4]
    linarith [hgp, hstep1]
  rw [hpoweq] at hbound
  have hfin : (θ : ℝ) * Real.log 2 ≤ kappa p * Real.log m := by
    have h := hbound
    rw [show (θ : ℝ) * (θ : ℝ) ^ j * Real.log 2 = (θ : ℝ) ^ j * ((θ : ℝ) * Real.log 2) by ring] at h
    exact le_of_mul_le_mul_left h hθjpos
  linarith [hthr, hfin]

private lemma kappa_pos (p : ℕ) (hp : 1 ≤ p) : 0 < kappa p := by
  rw [kappa]
  have hBpnn : (0 : ℝ) ≤ Bp p := by
    rw [Bp]
    have hln : (0 : ℝ) ≤ Real.log (2 + (p : ℝ)) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) p])
    have : (0 : ℝ) ≤ (Real.log (2 + (p : ℝ)) + 1) / Real.log 2 :=
      div_nonneg (by linarith) log_two_pos'.le
    linarith
  have h1 : (0 : ℝ) ≤ BakerWustholz.C 4 1 * Real.log 3 * p * (1 + 2 * p) * Bp p :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (C_one_nonneg 4) log_three_pos'.le)
      (Nat.cast_nonneg p)) (by positivity)) hBpnn
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2 : (0 : ℝ) ≤ 2 * (p : ℝ) := by positivity
  linarith

/-- The number of **period-`p` breaks** of `n`: positions `i < ⌊log₂ n⌋` with
`bitᵢ(n) ≠ bitᵢ₊ₚ(n)`.  For `p = 1` this is `transitionCount`. -/
@[category API, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
def breakCount (p n : ℕ) : ℕ :=
  ((Finset.range (Nat.log 2 n)).filter (fun i => n.testBit i ≠ n.testBit (i + p))).card

private lemma log_le_breakCount {p m θ : ℕ} (hm : 2 ≤ m) (hp : 1 ≤ p) (hθ2 : 2 ≤ θ)
    (hthr : kappa p * Real.log m < (θ : ℝ) * Real.log 2) :
    Nat.log θ (Nat.log 2 (3 ^ m)) ≤ breakCount p (3 ^ m) + 1 := by
  set M : ℕ := Nat.log 2 (3 ^ m) with hMdef
  set k : ℕ := Nat.log θ M with hkdef
  have hMpos : 1 ≤ M := by
    rw [hMdef]
    have h2 : (2 : ℕ) ^ 1 ≤ 3 ^ m := by
      calc (2 : ℕ) ^ 1 ≤ 3 ^ 1 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 1 = Nat.log 2 (2 ^ 1) := (Nat.log_pow (by norm_num) 1).symm
      _ ≤ Nat.log 2 (3 ^ m) := Nat.log_mono_right h2
  have hwin : ∀ j : ℕ, ∃ i : ℕ, j < k - 1 →
      (M - θ ^ (j + 1) ≤ i ∧ i + p < M - θ ^ j
        ∧ (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + p)) := by
    intro j
    by_cases hj : j < k - 1
    · have hpow : θ ^ (j + 1) < M := by
        have hk1 : j + 1 ≤ k - 1 := by omega
        have h1 : θ ^ (j + 1) ≤ θ ^ (k - 1) := Nat.pow_le_pow_right (by omega) hk1
        have hpk : θ ^ ((k - 1) + 1) = θ ^ (k - 1) * θ := pow_succ θ (k - 1)
        rw [show (k - 1) + 1 = k by omega] at hpk
        have hone : 1 ≤ θ ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
        have h3 : θ ^ k ≤ M := by rw [hkdef]; exact Nat.pow_log_le_self θ (by omega)
        nlinarith [h1, h3, hpk, hone, hθ2]
      obtain ⟨i, h1, h2, h3⟩ := window_break hm hp hθ2 hthr hpow
      rw [← hMdef] at h1 h2
      exact ⟨i, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose f hf using hwin
  have hfmem : ∀ j ∈ Finset.range (k - 1), f j ∈ (Finset.range M).filter
      (fun i => (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + p)) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hf j (Finset.mem_range.mp hj)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h3⟩
  have hmono : ∀ a b : ℕ, a < b → b < k - 1 → f b < f a := by
    intro a b hab hbk
    obtain ⟨ha1, _, _⟩ := hf a (by omega)
    obtain ⟨_, hb2, _⟩ := hf b hbk
    have hpow : θ ^ (a + 1) ≤ θ ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hinj : Set.InjOn f (Finset.range (k - 1)) := by
    intro a ha b hb heq
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · have := hmono a b h hb; omega
    · exact h
    · have := hmono b a h ha; omega
  have hcard : k - 1 ≤ ((Finset.range M).filter
      (fun i => (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + p))).card := by
    calc k - 1 = (Finset.range (k - 1)).card := (Finset.card_range (k - 1)).symm
      _ ≤ _ := Finset.card_le_card_of_injOn f hfmem hinj
  have hBC : breakCount p (3 ^ m) = ((Finset.range M).filter
      (fun i => (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + p))).card := rfl
  rw [hBC]; omega

/-- **Theorem B2** ([A4+] §3.2, the novel core): for every fixed period `p ≥ 1`,
the number of binary period-`p` breaks of `3^m` grows,
`log m/(log log m + C_p) − 2 ≤ breakCount p (3^m)` for all `m ≥ 2`, with an
effective `C_p > 0` (growing like `C(1 + log p)`).  A window deeper than
`polylog` cannot be `p`-periodic — the `p = 1` case sharpens B1.  Footprint
std3 + [BW93].  (The `−2` offset: one window is dropped to keep the base
position `≥ 1` for gap principle P.) -/
@[category research solved, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
theorem breakCount_three_pow_lower (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      Real.log m / (Real.log (Real.log m) + C) - 2 ≤ (breakCount p (3 ^ m) : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := windowCount_lower_bound_gen (fun m => breakCount p (3 ^ m) + 1)
    (kappa p) (kappa_pos p hp) (fun m θ hm hθ2 hthr => log_le_breakCount hm hp hθ2 hthr)
  refine ⟨C, hC, fun m hm => ?_⟩
  have h := hbound m hm
  push_cast at h
  linarith

/-- **Corollary**: for each fixed `p ≥ 1`, the number of binary period-`p`
breaks of `3^m` tends to infinity.  Footprint std3 + [BW93]. -/
@[category research solved, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
theorem breakCount_three_pow_tendsto_atTop (p : ℕ) (hp : 1 ≤ p) :
    Filter.Tendsto (fun m : ℕ => breakCount p (3 ^ m)) Filter.atTop Filter.atTop := by
  have h := tendsto_atTop_of_lower_bound (fun m => breakCount p (3 ^ m) + 1)
    (windowCount_lower_bound_gen (fun m => breakCount p (3 ^ m) + 1) (kappa p) (kappa_pos p hp)
      (fun m θ hm hθ2 hthr => log_le_breakCount hm hp hθ2 hthr))
  rw [Filter.tendsto_atTop_atTop] at h ⊢
  intro N
  obtain ⟨M, hM⟩ := h (N + 1)
  exact ⟨M, fun m hmM => by have := hM m hmM; omega⟩

end TH
