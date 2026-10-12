/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import EVG25.P1.Balance

/-!
# Theorem D: what a power saving needs (P1 paper, §5)

Plan EVGQ17-M0, §7.4.

As `N₀` runs over `ℤ/2^(j+1)`, the shift `c = c₀ - N₀` of the window formula runs over all
residues, so `β_j(N₀) = Σ_k a_k ψ(-k N₀)` is a Fourier series in `N₀` with coefficients
`a_k = ĝ(k) S(k)` (`beta_eq_sum_acoef`).

* `mean_sq_beta` — **mean square**:
  `2^-(j+1) Σ_{N₀ mod 2^(j+1)} β_j(N₀)² = Σ_k |ĝ(k)|² |S(k)|²` (only odd `k` contribute).
* `norm_SW_le_of_abs_beta_le` — **lower bound**: if `|β_j(N₀)| ≤ B` for all `N₀`, then
  `|S(k)| ≤ π min(k, N-k) B` for every odd `k`; so a power saving for `β` forces one for every
  single chain.
* `abs_beta_le_of_norm_SW_le` — **converse**: `|S(k)| ≤ D` for all odd `k` with
  `min(k, N-k) ≤ K` gives `|β_j(N₀)| ≤ D (1 + log K) + 2^j/√K`;
  `abs_beta_le_of_norm_SW_le_pow` is the form with `K = 2^m`, `D = 2^j η`.
-/

open Finset Real CC CC.Base3div2 ZMod
open scoped ComplexConjugate

namespace EVG25.P1

/-! ## The Fourier series in `N₀` -/

theorem cst_eq (j N₀ : ℕ) : cst j N₀ = cst j 0 - N₀ := by simp [cst]

/-- `|S(k)|` does not depend on the window. -/
theorem norm_SW_eq (j N₀ M : ℕ) (k : ZMod (2 ^ (j + 1))) : ‖SW j N₀ k‖ = ‖SW j M k‖ := by
  rw [SW_eq, SW_eq, norm_mul, norm_mul, AddChar.norm_apply, AddChar.norm_apply]

/-- The Fourier coefficients `a_k = ĝ(k) S(k)` of `N₀ ↦ β_j(N₀)`. -/
noncomputable def acoef (j : ℕ) (k : ZMod (2 ^ (j + 1))) : ℂ := ghat j k * SW j 0 k

theorem beta_eq_sum_acoef (j N₀ : ℕ) :
    (beta j N₀ : ℂ) = ∑ k, acoef j k * stdAddChar (-(k * (N₀ : ZMod (2 ^ (j + 1))))) := by
  rw [beta_eq_sum_ghat_mul_SW]
  refine sum_congr rfl fun k _ => ?_
  rw [acoef, SW_eq, SW_eq, cst_eq j N₀, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

/-- Orthogonality in `N₀`. -/
theorem sum_range_stdAddChar (j : ℕ) (m : ZMod (2 ^ (j + 1))) :
    ∑ N₀ ∈ range (2 ^ (j + 1)), stdAddChar ((N₀ : ZMod (2 ^ (j + 1))) * m)
      = if m = 0 then ((2 ^ (j + 1) : ℕ) : ℂ) else 0 := by
  rw [← sum_zmod_eq_sum_range (fun x : ZMod (2 ^ (j + 1)) => stdAddChar (x * m)),
    AddChar.sum_mulShift _ (isPrimitive_stdAddChar _)]
  simp [ZMod.card]

/-- Extraction of a coefficient: `Σ_{N₀} β_j(N₀) ψ(k N₀) = 2^(j+1) a_k`. -/
theorem sum_beta_mul_stdAddChar (j : ℕ) (k : ZMod (2 ^ (j + 1))) :
    ∑ N₀ ∈ range (2 ^ (j + 1)), (beta j N₀ : ℂ) * stdAddChar (k * (N₀ : ZMod (2 ^ (j + 1))))
      = ((2 ^ (j + 1) : ℕ) : ℂ) * acoef j k := by
  simp_rw [beta_eq_sum_acoef, sum_mul]
  rw [sum_comm]
  have h : ∀ k' : ZMod (2 ^ (j + 1)), ∑ N₀ ∈ range (2 ^ (j + 1)),
      acoef j k' * stdAddChar (-(k' * (N₀ : ZMod (2 ^ (j + 1)))))
        * stdAddChar (k * (N₀ : ZMod (2 ^ (j + 1))))
      = acoef j k' * (if k - k' = 0 then ((2 ^ (j + 1) : ℕ) : ℂ) else 0) := by
    intro k'
    rw [← sum_range_stdAddChar, mul_sum]
    refine sum_congr rfl fun N₀ _ => ?_
    rw [mul_assoc, ← AddChar.map_add_eq_mul]; ring_nf
  rw [sum_congr rfl fun k' _ => h k', sum_eq_single k]
  · simp [mul_comm]
  · intro k' _ hne; simp [sub_eq_zero, Ne.symm hne]
  · intro h; exact absurd (mem_univ k) h

/-! ## The mean square -/

/-- **Theorem D, mean square.** `2^-(j+1) Σ_{N₀ mod 2^(j+1)} β_j(N₀)² = Σ_k |ĝ(k)|² |S(k)|²`. -/
@[category research solved, AMS 11 37 42, group "evgq17_p1"]
theorem mean_sq_beta (j M : ℕ) :
    1 / 2 ^ (j + 1) * ∑ N₀ ∈ range (2 ^ (j + 1)), beta j N₀ ^ 2
      = ∑ k, ‖ghat j k‖ ^ 2 * ‖SW j M k‖ ^ 2 := by
  have hconj : ∀ N₀ : ℕ, (beta j N₀ : ℂ) = ∑ k, conj (acoef j k) * stdAddChar (k * (N₀ : ZMod (2 ^ (j + 1)))) := by
    intro N₀
    rw [← Complex.conj_ofReal, beta_eq_sum_acoef, map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [map_mul, ← AddChar.map_neg_eq_conj, neg_neg]
  have hsum : ∑ N₀ ∈ range (2 ^ (j + 1)), ((beta j N₀ ^ 2 : ℝ) : ℂ)
      = ((2 ^ (j + 1) : ℕ) : ℂ) * ∑ k, ((‖acoef j k‖ ^ 2 : ℝ) : ℂ) := by
    calc ∑ N₀ ∈ range (2 ^ (j + 1)), ((beta j N₀ ^ 2 : ℝ) : ℂ)
        = ∑ N₀ ∈ range (2 ^ (j + 1)),
            ∑ k, conj (acoef j k) * ((beta j N₀ : ℂ) * stdAddChar (k * (N₀ : ZMod (2 ^ (j + 1))))) := by
          refine sum_congr rfl fun N₀ _ => ?_
          rw [Complex.ofReal_pow, sq]
          nth_rewrite 2 [hconj N₀]
          rw [mul_sum]
          exact sum_congr rfl fun k _ => by ring
      _ = ∑ k, conj (acoef j k) * (((2 ^ (j + 1) : ℕ) : ℂ) * acoef j k) := by
          rw [sum_comm]
          exact sum_congr rfl fun k _ => by rw [← mul_sum, sum_beta_mul_stdAddChar]
      _ = _ := by
          rw [mul_sum]
          refine sum_congr rfl fun k _ => ?_
          rw [Complex.ofReal_pow, ← Complex.mul_conj']; ring
  have hR : ∑ N₀ ∈ range (2 ^ (j + 1)), beta j N₀ ^ 2
      = 2 ^ (j + 1) * ∑ k, ‖acoef j k‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, hsum]; push_cast; rfl
  rw [hR]
  have hN : (2 : ℝ) ^ (j + 1) ≠ 0 := by positivity
  rw [← mul_assoc, one_div_mul_cancel hN, one_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [acoef, norm_mul, mul_pow, norm_SW_eq j 0 M]

/-! ## The lower bound -/

/-- `|ĝ(k)| ≥ 1/(π min(k, N-k))` for odd `k`, from `sin x ≤ x`. -/
theorem one_le_pi_mul_pm_mul_norm_ghat (j : ℕ) {k : ZMod (2 ^ (j + 1))} (hk : Odd k.val) :
    1 ≤ π * pm j k * ‖ghat j k‖ := by
  rw [norm_ghat_of_odd j hk]
  have hk0 : 0 < k.val := hk.pos
  have hkN : k.val < 2 ^ (j + 1) := ZMod.val_lt k
  have hN : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  have hkN' : (k.val : ℝ) < 2 ^ (j + 1) := by exact_mod_cast hkN
  have hsin : 0 < Real.sin (π * k.val / 2 ^ (j + 1)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < k.val := by exact_mod_cast hk0
      positivity
    · rw [div_lt_iff₀ hN]; nlinarith [Real.pi_pos]
  have hle : 2 ^ (j + 1) * Real.sin (π * k.val / 2 ^ (j + 1)) ≤ π * pm j k := by
    unfold pm
    rcases le_total k.val (2 ^ (j + 1) - k.val) with h | h
    · rw [min_eq_left h]
      have := Real.sin_le (x := π * k.val / 2 ^ (j + 1)) (by positivity)
      calc _ ≤ 2 ^ (j + 1) * (π * k.val / 2 ^ (j + 1)) := mul_le_mul_of_nonneg_left this hN.le
        _ = _ := by field_simp
    · rw [min_eq_right h, Nat.cast_sub hkN.le]
      push_cast
      rw [show π * (k.val : ℝ) / 2 ^ (j + 1) = π - π * (2 ^ (j + 1) - k.val) / 2 ^ (j + 1) by
        field_simp; ring, Real.sin_pi_sub]
      have := Real.sin_le (x := π * (2 ^ (j + 1) - k.val) / 2 ^ (j + 1)) (by
        have : (0 : ℝ) ≤ 2 ^ (j + 1) - k.val := by linarith
        positivity)
      calc _ ≤ 2 ^ (j + 1) * (π * (2 ^ (j + 1) - k.val) / 2 ^ (j + 1)) :=
            mul_le_mul_of_nonneg_left this hN.le
        _ = _ := by field_simp
  rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
  exact hle

/-- **Theorem D, lower bound.** If `|β_j(N₀)| ≤ B` for every `N₀ mod 2^(j+1)`, then
`|S(k)| ≤ π min(k, N-k) B` for every odd `k`.  Equivalently
`sup_{N₀} |β_j(N₀)| ≥ |S(k)| / (π min(k, N-k))`. -/
@[category research solved, AMS 11 37 42, group "evgq17_p1"]
theorem norm_SW_le_of_abs_beta_le (j M : ℕ) {B : ℝ}
    (hB : ∀ N₀ < 2 ^ (j + 1), |beta j N₀| ≤ B) {k : ZMod (2 ^ (j + 1))} (hk : Odd k.val) :
    ‖SW j M k‖ ≤ π * pm j k * B := by
  have hN : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  -- `2^(j+1) |a_k| ≤ 2^(j+1) B`
  have ha : ‖acoef j k‖ ≤ B := by
    have h1 := congrArg norm (sum_beta_mul_stdAddChar j k)
    rw [norm_mul, Complex.norm_natCast] at h1
    have h2 : ‖∑ N₀ ∈ range (2 ^ (j + 1)), (beta j N₀ : ℂ) * stdAddChar (k * (N₀ : ZMod (2 ^ (j + 1))))‖
        ≤ 2 ^ (j + 1) * B := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ N₀ ∈ range (2 ^ (j + 1)), ‖(beta j N₀ : ℂ) * stdAddChar (k * (N₀ : ZMod (2 ^ (j + 1))))‖
          ≤ ∑ N₀ ∈ range (2 ^ (j + 1)), B := by
            refine sum_le_sum fun N₀ hN₀ => ?_
            rw [norm_mul, AddChar.norm_apply, mul_one, Complex.norm_real, Real.norm_eq_abs]
            exact hB N₀ (mem_range.1 hN₀)
        _ = 2 ^ (j + 1) * B := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    rw [h1] at h2
    push_cast at h2
    exact le_of_mul_le_mul_left h2 hN
  rw [acoef, norm_mul, norm_SW_eq j 0 M] at ha
  have hg := one_le_pi_mul_pm_mul_norm_ghat j hk
  have hp : (0 : ℝ) ≤ π * pm j k := by positivity
  calc ‖SW j M k‖ ≤ (π * pm j k * ‖ghat j k‖) * ‖SW j M k‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hg
    _ = π * pm j k * (‖ghat j k‖ * ‖SW j M k‖) := by ring
    _ ≤ π * pm j k * B := mul_le_mul_of_nonneg_left ha hp

/-- The mean-square form of the lower bound: `|ĝ(k)|² |S(k)|²` is at most the mean square. -/
theorem sq_le_mean_sq_beta (j M : ℕ) (k : ZMod (2 ^ (j + 1))) :
    ‖ghat j k‖ ^ 2 * ‖SW j M k‖ ^ 2
      ≤ 1 / 2 ^ (j + 1) * ∑ N₀ ∈ range (2 ^ (j + 1)), beta j N₀ ^ 2 := by
  rw [mean_sq_beta j M]
  exact single_le_sum (f := fun k => ‖ghat j k‖ ^ 2 * ‖SW j M k‖ ^ 2)
    (fun _ _ => by positivity) (mem_univ k)

/-! ## The converse -/

/-- The truncated harmonic weight `g(m) = 1/m` for `1 ≤ m ≤ K`, else `0`. -/
noncomputable def hw (K m : ℕ) : ℝ := if 1 ≤ m ∧ m ≤ K then 1 / (m : ℝ) else 0

theorem hw_eq {K m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ K) : hw K m = 1 / (m : ℝ) := by
  simp [hw, h1, h2]

theorem hw_nonneg (K m : ℕ) : 0 ≤ hw K m := by unfold hw; split_ifs <;> positivity

theorem sum_hw_le (K M : ℕ) : ∑ m ∈ range M, hw K m ≤ 1 + Real.log K := by
  calc ∑ m ∈ range M, hw K m ≤ ∑ m ∈ range (K + 1 + M), hw K m :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          (fun _ _ _ => hw_nonneg _ _)
    _ = ∑ m ∈ range (K + 1), hw K m := by
        rw [← sum_range_add_sum_Ico _ (show K + 1 ≤ K + 1 + M by omega)]
        rw [sum_eq_zero (s := Ico _ _) fun m hm => by
          have := (mem_Ico.1 hm).1
          simp only [hw, show ¬ (1 ≤ m ∧ m ≤ K) by omega, ↓reduceIte], add_zero]
    _ = (harmonic K : ℝ) := by
        rw [sum_range_succ', harmonic, show hw K 0 = 0 by simp [hw], add_zero]
        push_cast
        refine sum_congr rfl fun i hi => ?_
        have := mem_range.1 hi
        rw [hw_eq (by omega) (by omega)]
        push_cast; ring
    _ ≤ 1 + Real.log K := harmonic_le_one_add_log K

/-- The head of the square-wave coefficients: `Σ_{min(k, N-k) ≤ K} |ĝ(k)| ≤ 1 + log K`. -/
theorem head_sum (j K : ℕ) :
    ∑ k ∈ univ.filter (fun k : ZMod (2 ^ (j + 1)) => pm j k ≤ K), ‖ghat j k‖
      ≤ 1 + Real.log K := by
  set N := 2 ^ (j + 1) with hN
  have hpt : ∀ k : ZMod N, pm j k ≤ K →
      ‖ghat j k‖ ≤ 1 / 2 * (hw K k.val + hw K (N - k.val)) := by
    intro k hk
    have e1 := hw_nonneg K k.val
    have e2 := hw_nonneg K (N - k.val)
    rcases Nat.even_or_odd k.val with h | h
    · rw [ghat_eq_zero_of_even j h, norm_zero]; positivity
    · refine (norm_ghat_le j h).trans ?_
      have h1 := one_le_pm_of_odd j h
      have hkN : k.val < N := ZMod.val_lt k
      unfold pm at hk h1 ⊢
      rcases le_total k.val (N - k.val) with h' | h'
      · rw [min_eq_left h'] at hk h1 ⊢
        rw [hw_eq h1 hk]
        have : 1 / (2 * (k.val : ℝ)) = 1 / 2 * (1 / (k.val : ℝ)) := by ring
        rw [this]; nlinarith
      · rw [min_eq_right h'] at hk h1 ⊢
        rw [hw_eq h1 hk]
        have : 1 / (2 * ((N - k.val : ℕ) : ℝ)) = 1 / 2 * (1 / ((N - k.val : ℕ) : ℝ)) := by
          ring
        rw [this]; nlinarith
  refine (sum_le_sum fun k hk => hpt k (mem_filter.1 hk).2).trans ?_
  rw [← mul_sum]
  refine (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ _)
    (fun k _ _ => add_nonneg (hw_nonneg _ _) (hw_nonneg _ _))) (by norm_num)).trans ?_
  rw [sum_add_distrib]
  have h1 : ∑ k : ZMod N, hw K k.val ≤ 1 + Real.log K := by
    rw [sum_zmod_eq_sum_range (fun k : ZMod N => hw K k.val)]
    refine le_trans (le_of_eq (sum_congr rfl fun m hm => ?_)) (sum_hw_le K N)
    rw [ZMod.val_natCast_of_lt (mem_range.1 hm)]
  have h2 : ∑ k : ZMod N, hw K (N - k.val) ≤ 1 + Real.log K := by
    rw [sum_zmod_eq_sum_range (fun k : ZMod N => hw K (N - k.val))]
    have : ∀ m ∈ range N, hw K (N - (m : ZMod N).val) = hw K (N - m) := fun m hm => by
      rw [ZMod.val_natCast_of_lt (mem_range.1 hm)]
    rw [sum_congr rfl this, ← sum_range_reflect]
    have : ∀ m ∈ range N, hw K (N - (N - 1 - m)) = hw K (m + 1) := fun m hm => by
      have := mem_range.1 hm
      rw [show N - (N - 1 - m) = m + 1 by omega]
    rw [sum_congr rfl this]
    refine le_trans (le_of_eq ?_) (sum_hw_le K (N + 1))
    rw [sum_range_succ' (fun m => hw K m) N]
    simp [hw]
  linarith

/-- With `K ≥ 1`, a bound `|S(k)| ≤ D` on the odd frequencies `min(k, N-k) ≤ K` forces `D ≥ 0`. -/
theorem nonneg_of_norm_SW_le (j N₀ K : ℕ) (hK : 1 ≤ K) {D : ℝ}
    (hD : ∀ k : ZMod (2 ^ (j + 1)), Odd k.val → pm j k ≤ K → ‖SW j N₀ k‖ ≤ D) : 0 ≤ D := by
  have h1 : (1 : ZMod (2 ^ (j + 1))).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  have hp : pm j 1 ≤ K := by
    unfold pm; rw [h1]; omega
  exact (norm_nonneg _).trans (hD 1 (by rw [h1]; exact odd_one) hp)

/-- **Theorem D, converse.** If `|S(k)| ≤ D` for every odd `k` with `min(k, N-k) ≤ K`, then
`|β_j(N₀)| ≤ D (1 + log K) + 2^j/√K`. -/
@[category research solved, AMS 11 37 42, group "evgq17_p1"]
theorem abs_beta_le_of_norm_SW_le (j N₀ K : ℕ) (hK : 1 ≤ K) {D : ℝ}
    (hD : ∀ k : ZMod (2 ^ (j + 1)), Odd k.val → pm j k ≤ K → ‖SW j N₀ k‖ ≤ D) :
    |beta j N₀| ≤ D * (1 + Real.log K) + 2 ^ j / Real.sqrt K := by
  have hD0 := nonneg_of_norm_SW_le j N₀ K hK hD
  set F : ZMod (2 ^ (j + 1)) → ℝ := fun k => ‖ghat j k‖ * ‖SW j N₀ k‖ with hF
  have hstart : |beta j N₀| ≤ ∑ k, F k := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, beta_eq_sum_ghat_mul_SW]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [hF, norm_mul]
  rw [← sum_filter_add_sum_filter_not univ (fun k => pm j k ≤ K)] at hstart
  have hhead : ∑ k ∈ univ.filter (fun k => pm j k ≤ K), F k ≤ D * (1 + Real.log K) := by
    calc _ ≤ ∑ k ∈ univ.filter (fun k : ZMod (2 ^ (j + 1)) => pm j k ≤ K), ‖ghat j k‖ * D := by
          refine sum_le_sum fun k hk => ?_
          rcases Nat.even_or_odd k.val with h | h
          · simp only [hF, ghat_eq_zero_of_even j h, norm_zero, zero_mul, le_refl]
          · exact mul_le_mul_of_nonneg_left (hD k h (mem_filter.1 hk).2) (norm_nonneg _)
      _ = D * ∑ k ∈ univ.filter (fun k : ZMod (2 ^ (j + 1)) => pm j k ≤ K), ‖ghat j k‖ := by
          rw [mul_sum]; exact sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ D * (1 + Real.log K) := mul_le_mul_of_nonneg_left (head_sum j K) hD0
  have htail : ∑ k ∈ univ.filter (fun k => ¬ pm j k ≤ K), F k ≤ 2 ^ j / Real.sqrt K :=
    tail_le j N₀ K hK
  linarith

/-- **Theorem D, converse, exponential form.** If `|S(k)| ≤ 2^j η` for every odd `k` with
`min(k, N-k) ≤ 2^m`, then `|β_j(N₀)| ≤ 2^j ((1 + m) η + 1/√(2^m))`.  With `m = εj` and
`η = 2^(-δj)` this is `2^j ((1 + εj) 2^(-δj) + 2^(-εj/2))`. -/
@[category research solved, AMS 11 37 42, group "evgq17_p1"]
theorem abs_beta_le_of_norm_SW_le_pow (j N₀ m : ℕ) {η : ℝ}
    (hη : ∀ k : ZMod (2 ^ (j + 1)), Odd k.val → pm j k ≤ 2 ^ m → ‖SW j N₀ k‖ ≤ 2 ^ j * η) :
    |beta j N₀| ≤ 2 ^ j * ((1 + m) * η + 1 / Real.sqrt (2 ^ m)) := by
  have hK : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h := abs_beta_le_of_norm_SW_le j N₀ (2 ^ m) hK hη
  have hD0 := nonneg_of_norm_SW_le j N₀ (2 ^ m) hK hη
  have hη0 : 0 ≤ η := nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 2 ^ j)
  have hlog : Real.log ((2 ^ m : ℕ) : ℝ) ≤ m := by
    push_cast
    rw [Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    nlinarith
  push_cast at h hlog
  calc |beta j N₀| ≤ 2 ^ j * η * (1 + Real.log (2 ^ m)) + 2 ^ j / Real.sqrt (2 ^ m) := h
    _ ≤ 2 ^ j * η * (1 + m) + 2 ^ j / Real.sqrt (2 ^ m) := by gcongr
    _ = _ := by ring

end EVG25.P1
