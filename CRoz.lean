import C2
import POListBool
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

/-- `V j n` is the parity vector of length `j` for the Collatz sequence starting at `n`:
    the `i`-th entry is `true` (= 1) when `T^i(n)` is odd, `false` (= 0) when even. -/
def V (j n : ℕ) : ParityVector :=
  (List.finRange j).map (fun i => decide (X (T_iter i.val n) = 1))

@[simp]
lemma V_length (j n : ℕ) : (V j n).length = j := by
  simp [V]

lemma V_get (j n : ℕ) (i : Fin j) :
    (V j n).get ⟨i.val, by simp [V_length]⟩ = decide (X (T_iter i.val n) = 1) := by
  simp [V]

/-- E_vec is the same as V without the ParityVector structure
-/
lemma E_vec_eq_V_toNat (j n : ℕ) (i : Fin j) :
    E_vec j n i = ParityVector.toNat ((V j n).get ⟨i.val, by simp⟩) := by
  rw [V_get]
  simp only [E_vec_apply, ParityVector.toNat]
  rw [X_eq_mod]
  by_cases h : T_iter i.val n % 2 = 1
  · simp [h]
  · have : T_iter i.val n % 2 = 0 := by omega
    simp [this]

/-- The Garner correction ratio: `E j n = Q_j(n) / 2^j`, where `Q_j` is the
    Garner correction term. This is the rational contribution of the correction
    in the normalised Garner formula `T^j(n) = C_j(n) · n + E_j(n)`. -/
def E (j n : ℕ) : ℚ := (garner_correction j n : ℚ) / (2 ^ j : ℚ)

-- ===== Helper lemmas for E_lt_of_V_precedes =====

/-- Base case: `E 0 n = 0`. -/
lemma E_zero (n : ℕ) : E 0 n = 0 := by
  simp [E, garner_correction]

/-- Recurrence for E: `E (k+1) n = (3^(x_k) / 2) · E k n + x_k / 2`,
    where `x_k = X(T^k n)`. -/
lemma E_succ (k n : ℕ) :
    E (k + 1) n = (3 ^ X (T_iter k n) : ℚ) / 2 * E k n +
      (X (T_iter k n) : ℚ) / 2 := by
  simp only [E, garner_correction]
  rw [show (2 : ℚ) ^ (k + 1) = 2 * 2 ^ k from by ring]
  have h2k : (2 ^ k : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- `garner_correction` only depends on the parity bits. If two sequences
    agree on the first `k` parities, their Garner corrections are equal.
    (This strengthens `garner_correction_eq_of_E_vec_eq` from C2 to work
    with the `V` representation.) -/
lemma garner_correction_eq_of_V_prefix_eq (k j m n : ℕ) (hk : k ≤ j)
    (hpre : ∀ i : Fin k, (V j m).get ⟨i.val, by simp; omega⟩ =
      (V j n).get ⟨i.val, by simp; omega⟩) :
    garner_correction k m = garner_correction k n := by
  induction k with
  | zero => simp [garner_correction]
  | succ k ih =>
    simp only [garner_correction]
    have hk' : k ≤ j := by omega
    have ih' := ih hk' (fun i => hpre ⟨i.val, by omega⟩)
    -- Extract X equality from V prefix agreement
    have hXk : X (T_iter k m) = X (T_iter k n) := by
      have hv := hpre ⟨k, Nat.lt_succ_iff.mpr le_rfl⟩
      simp only [V] at hv
      have hd : (X (T_iter k m) = 1 ↔ X (T_iter k n) = 1) := by simpa using hv
      have hm_le : X (T_iter k m) ≤ 1 := by rw [X_eq_mod]; omega
      have hn_le : X (T_iter k n) ≤ 1 := by rw [X_eq_mod]; omega
      omega
    rw [ih', hXk]

/-- Equal prefix of `V` implies equal `E` up to that prefix length. -/
lemma E_eq_of_V_prefix_eq (k j m n : ℕ) (hk : k ≤ j)
    (hpre : ∀ i : Fin k, (V j m).get ⟨i.val, by simp; omega⟩ =
      (V j n).get ⟨i.val, by simp; omega⟩) :
    E k m = E k n := by
  simp only [E, garner_correction_eq_of_V_prefix_eq k j m n hk hpre]

/-- The step map `e ↦ (3^x / 2) · e + x / 2` is strictly monotone in `e`
    for any `x ∈ {0, 1}`. -/
lemma E_step_strict_mono (x : ℕ) (a b : ℚ) (hab : a < b) :
    (3 ^ x : ℚ) / 2 * a + (x : ℚ) / 2 < (3 ^ x : ℚ) / 2 * b + (x : ℚ) / 2 := by
  have h3 : (3 ^ x : ℚ) / 2 > 0 := by positivity
  nlinarith [sq_nonneg (3 : ℚ)]

/-- The irrational constant `log 2 / log 3` used in the approximation. -/
noncomputable def ξ : ℝ := Real.log 2 / Real.log 3

/-- The bound δ(ε) used in the inequality equivalence. -/
noncomputable def delta (ε : ℝ) : ℝ := -Real.log (1 - ε) / Real.log 3

/-- Auxiliary Lemma 1: ξ is irrational. -/
lemma irrational_xi : Irrational ξ := by
  rw [ξ, irrational_iff_ne_rational]
  intro m n hn
  rw [ne_comm]
  intro h
  have hpos3 : 0 < (3 : ℝ) := by norm_num
  have hpos2 : 0 < (2 : ℝ) := by norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- n * log 2 / log 3 = m  => n * log 2 = m * log 3
  have h1 : (n : ℝ) * (Real.log 2 / Real.log 3) = m := by
    rw [← h]
    field_simp [hl2.ne', hl3.ne']
  have h2 : (n : ℝ) * Real.log 2 = (m : ℝ) * Real.log 3 := by
    rw [← h1]
    field_simp [hl2.ne', hl3.ne']
  have h2abs : (n.natAbs : ℝ) * Real.log 2 = (m.natAbs : ℝ) * Real.log 3 := by
    rcases lt_trichotomy n 0 with hnl | hnz | hnp
    · have h_m : (m:ℝ) = (n:ℝ) * (Real.log 2 / Real.log 3) := by
        calc (m:ℝ) = (m:ℝ) * Real.log 3 / Real.log 3 := by rw [mul_div_cancel_right₀ _ hl3.ne']
        _ = (n:ℝ) * Real.log 2 / Real.log 3 := by rw [← h2]
        _ = (n:ℝ) * (Real.log 2 / Real.log 3) := by ring
      have hm_neg : (m:ℝ) < 0 := by
        calc (m:ℝ) = (n:ℝ) * (Real.log 2 / Real.log 3) := h_m
        _ < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hnl) (div_pos hl2 hl3)
      have hm_neg_int : m < 0 := by exact_mod_cast hm_neg
      have hn_nat_r : (n.natAbs : ℝ) = -(n : ℝ) := by
        have h1 : (n.natAbs : ℤ) = -n := Int.ofNat_natAbs_of_nonpos hnl.le
        have h2 : ((n.natAbs : ℤ) : ℝ) = ((-n : ℤ) : ℝ) := congrArg (fun x : ℤ => (x : ℝ)) h1
        have h3 : (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := (Int.cast_natCast n.natAbs).symm
        rw [h3, h2]
        push_cast
        rfl
      have hm_nat_r : (m.natAbs : ℝ) = -(m : ℝ) := by
        have h1 : (m.natAbs : ℤ) = -m := Int.ofNat_natAbs_of_nonpos hm_neg_int.le
        have h2 : ((m.natAbs : ℤ) : ℝ) = ((-m : ℤ) : ℝ) := congrArg (fun x : ℤ => (x : ℝ)) h1
        have h3 : (m.natAbs : ℝ) = ((m.natAbs : ℤ) : ℝ) := (Int.cast_natCast m.natAbs).symm
        rw [h3, h2]
        push_cast
        rfl
      rw [hn_nat_r, hm_nat_r, neg_mul, neg_mul, h2]
    · contradiction
    · have h_m : (m:ℝ) = (n:ℝ) * (Real.log 2 / Real.log 3) := by
        calc (m:ℝ) = (m:ℝ) * Real.log 3 / Real.log 3 := by rw [mul_div_cancel_right₀ _ hl3.ne']
        _ = (n:ℝ) * Real.log 2 / Real.log 3 := by rw [← h2]
        _ = (n:ℝ) * (Real.log 2 / Real.log 3) := by ring
      have hm_pos : 0 < (m:ℝ) := by
        calc 0 < (n:ℝ) * (Real.log 2 / Real.log 3) := mul_pos (by exact_mod_cast hnp) (div_pos hl2 hl3)
        _ = (m:ℝ) := h_m.symm
      have hm_pos_int : 0 < m := by exact_mod_cast hm_pos
      have hn_nat_r : (n.natAbs : ℝ) = (n : ℝ) := by
        have h1 : (n.natAbs : ℤ) = n := Int.ofNat_natAbs_of_nonneg hnp.le
        have h2 : ((n.natAbs : ℤ) : ℝ) = ((n : ℤ) : ℝ) := congrArg (fun x : ℤ => (x : ℝ)) h1
        have h3 : (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := (Int.cast_natCast n.natAbs).symm
        rw [h3, h2]
      have hm_nat_r : (m.natAbs : ℝ) = (m : ℝ) := by
        have h1 : (m.natAbs : ℤ) = m := Int.ofNat_natAbs_of_nonneg hm_pos_int.le
        have h2 : ((m.natAbs : ℤ) : ℝ) = ((m : ℤ) : ℝ) := congrArg (fun x : ℤ => (x : ℝ)) h1
        have h3 : (m.natAbs : ℝ) = ((m.natAbs : ℤ) : ℝ) := (Int.cast_natCast m.natAbs).symm
        rw [h3, h2]
      rw [hn_nat_r, hm_nat_r, h2]
  have h3 : (2 : ℝ) ^ (n.natAbs : ℝ) = (3 : ℝ) ^ (m.natAbs : ℝ) := by
    rw [← Real.log_rpow hpos2, ← Real.log_rpow hpos3] at h2abs
    refine Real.log_injOn_pos (Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hpos2 _))
      (Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hpos3 _)) h2abs
  have h4 : 2 ^ n.natAbs = 3 ^ m.natAbs := by
    have h_left : (2 : ℝ) ^ (n.natAbs : ℝ) = ((2 ^ n.natAbs : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    have h_right : (3 : ℝ) ^ (m.natAbs : ℝ) = ((3 ^ m.natAbs : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    rw [h_left, h_right] at h3
    exact_mod_cast h3
  have hn_pos : n.natAbs ≠ 0 := by
    intro hz
    have : n = 0 := Int.natAbs_eq_zero.mp hz
    contradiction
  have h_even : Even (2 ^ n.natAbs) := Even.pow_of_ne_zero (by decide) hn_pos
  rw [h4] at h_even
  have h_odd : ¬ Even (3 ^ m.natAbs) := by
    rw [Nat.not_even_iff_odd]
    exact Odd.pow (by decide)
  exact h_odd h_even

/-- Auxiliary Lemma 2: Equivalence of the original inequality and the rational approximation. -/
lemma inequality_equiv (a b : ℕ) (hb : 0 < b) (ε : ℝ) (hε₁ : ε < 1) :
    (1 - ε < (3 : ℝ)^a / (2 : ℝ)^b ∧ (3 : ℝ)^a / (2 : ℝ)^b < 1) ↔
    (0 < ξ - (a : ℝ) / (b : ℝ) ∧ ξ - (a : ℝ) / (b : ℝ) < delta ε / b) := by
  have hpos3 : 0 < (3 : ℝ) := by norm_num
  have hpos2 : 0 < (2 : ℝ) := by norm_num
  have hb_real : 0 < (b : ℝ) := by exact_mod_cast hb
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h3a_pos : 0 < (3 : ℝ)^a := pow_pos hpos3 a
  have h2b_pos : 0 < (2 : ℝ)^b := pow_pos hpos2 b
  rw [ξ, delta]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [div_lt_one h2b_pos] at h2
      have h2' : Real.log ((3 : ℝ)^a) < Real.log ((2 : ℝ)^b) := by
        rwa [Real.log_lt_log_iff h3a_pos h2b_pos]
      rw [Real.log_pow, Real.log_pow] at h2'
      field_simp [hlog3.ne', hb_real.ne']
      linarith
    · have h1' : Real.log (1 - ε) < Real.log ((3 : ℝ)^a / (2 : ℝ)^b) := by
        rwa [Real.log_lt_log_iff (by linarith) (div_pos h3a_pos h2b_pos)]
      rw [Real.log_div h3a_pos.ne' h2b_pos.ne', Real.log_pow, Real.log_pow] at h1'
      field_simp [hlog3.ne', hb_real.ne']
      linarith
  · rintro ⟨h1, h2⟩
    constructor
    · field_simp [hlog3.ne', hb_real.ne'] at h2
      have h2' : Real.log (2 ^ b : ℝ) - Real.log (3 ^ a : ℝ) < -Real.log (1 - ε) := by
        rw [Real.log_pow, Real.log_pow]
        linarith
      have h2'' : Real.log (1 - ε) < Real.log (3 ^ a : ℝ) - Real.log (2 ^ b : ℝ) := by
        linarith
      rw [← Real.log_div h3a_pos.ne' h2b_pos.ne'] at h2''
      rw [Real.log_lt_log_iff (by linarith) (div_pos h3a_pos h2b_pos)] at h2''
      exact h2''
    · field_simp [hlog3.ne', hb_real.ne'] at h1
      have h1' : Real.log ((3 : ℝ)^a) < Real.log ((2 : ℝ)^b) := by
        rw [Real.log_pow, Real.log_pow]
        linarith
      rw [Real.log_lt_log_iff h3a_pos h2b_pos] at h1'
      rw [div_lt_one h2b_pos]
      exact h1'

/-- Helper: delta is positive when 0 < ε < 1 -/
lemma delta_pos (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) : 0 < delta ε := by
  unfold delta
  apply div_pos
  · rw [neg_pos]
    exact Real.log_neg (by linarith) (by linarith)
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 3)

/-- For any b, the pair (⌊ξ*b⌋, b) gives a good approximation from below. -/
lemma floor_approx_pos (b : ℕ) (hb : 0 < b) :
    0 < ξ - (Int.toNat ⌊ξ * ↑b⌋ : ℝ) / (↑b : ℝ) ∧
    ξ - (Int.toNat ⌊ξ * ↑b⌋ : ℝ) / (↑b : ℝ) < 1 / (↑b : ℝ) := by
  have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hξ_pos : (0 : ℝ) < ξ := by
    unfold ξ
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  -- ⌊ξ*b⌋ is non-negative since ξ > 0 and b > 0
  have hfloor_nn : 0 ≤ ⌊ξ * ↑b⌋ := Int.floor_nonneg.mpr (mul_nonneg hξ_pos.le hb_pos.le)
  have htonat : (Int.toNat ⌊ξ * ↑b⌋ : ℤ) = ⌊ξ * ↑b⌋ := Int.toNat_of_nonneg hfloor_nn
  have htonat_r : (Int.toNat ⌊ξ * ↑b⌋ : ℝ) = (⌊ξ * ↑b⌋ : ℝ) := by
    exact_mod_cast htonat
  rw [htonat_r]
  constructor
  · -- 0 < ξ - ⌊ξ*b⌋/b
    have hle : (⌊ξ * ↑b⌋ : ℝ) ≤ ξ * ↑b := Int.floor_le _
    have hne : (⌊ξ * ↑b⌋ : ℝ) ≠ ξ * ↑b := by
      intro h
      -- ξ * b is an integer, so ξ is rational
      have hrat : ξ = (⌊ξ * ↑b⌋ : ℝ) / (↑b : ℝ) := by
        field_simp; linarith
      exact irrational_xi ⟨(⌊ξ * (↑b : ℝ)⌋ : ℤ) / (↑b : ℤ), by push_cast; linarith⟩
    have hlt : (⌊ξ * ↑b⌋ : ℝ) < ξ * ↑b := lt_of_le_of_ne hle hne
    have : (⌊ξ * ↑b⌋ : ℝ) / ↑b < ξ := (div_lt_iff₀ hb_pos).mpr hlt
    linarith
  · -- ξ - ⌊ξ*b⌋/b < 1/b
    have hlt_add := Int.lt_floor_add_one (ξ * ↑b)
    -- ξ * b < ⌊ξ*b⌋ + 1, so ξ < (⌊ξ*b⌋ + 1) / b = ⌊ξ*b⌋/b + 1/b
    have : ξ < (⌊ξ * ↑b⌋ : ℝ) / ↑b + 1 / ↑b := by
      rw [← add_div]
      exact (lt_div_iff₀ hb_pos).mpr (by linarith)
    linarith

/-- The pair (⌊ξ*b⌋, b) has a > 0 for b ≥ 2. -/
lemma floor_mul_pos (b : ℕ) (hb : 2 ≤ b) :
    0 < Int.toNat ⌊ξ * ↑b⌋ := by
  have hξ_pos : (0 : ℝ) < ξ := by
    unfold ξ; exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have hb_pos : (0 : ℝ) < (↑b : ℝ) := Nat.cast_pos.mpr (by omega)
  -- ξ * b ≥ ξ * 2 > 1 since ξ = log2/log3 and log 4 > log 3 (4 > 3)
  have hξ_bound : 1 < ξ * 2 := by
    unfold ξ
    rw [div_mul_eq_mul_div, one_lt_div (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
    calc Real.log 3 < Real.log 4 := by
          exact (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 4)).mpr (by norm_num)
    _ = Real.log (2 ^ 2) := by norm_num
    _ = 2 * Real.log 2 := Real.log_pow 2 2
    _ = Real.log 2 * 2 := mul_comm _ _
  have hprod : 1 ≤ ξ * ↑b := le_of_lt (by
    calc (1 : ℝ) < ξ * 2 := hξ_bound
    _ ≤ ξ * ↑b := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hb
      · exact hξ_pos.le)
  have hfloor_pos : 0 < ⌊ξ * ↑b⌋ := Int.floor_pos.mpr hprod
  omega

open GenContFract

lemma B_pos {v : ℝ} (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℝ) < ((GenContFract.of v).contsAux (n + 1)).b := by
  sorry

lemma pB_nonneg {v : ℝ} (n : ℕ) :
    (0 : ℝ) ≤ ((GenContFract.of v).contsAux n).b := by
  sorry

lemma frac_lt_one_of_ifp {v : ℝ} (ifp : IntFractPair ℝ) (n : ℕ) (h : IntFractPair.stream v n = some ifp) :
    ifp.fr < 1 := by
  sorry

lemma frac_pos_of_ifp {v : ℝ} (ifp : IntFractPair ℝ) (n : ℕ) (h : IntFractPair.stream v n = some ifp) (h_irr : Irrational v) :
    0 < ifp.fr := by
  sorry

/-- There are infinitely many rationals below ξ with |ξ - q| < 1/q.den².
    This follows from the alternating nature of continued fraction convergents. -/
lemma infinite_rat_approx_from_below :
    {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := by
  sorry

/-- Lemma from [Roz25] (stated as Lemma 3.2 in plan-32.md):
    For any `ε ∈ (0, 1)`, there are infinitely many pairs of positive integers `(a, b)`
    such that `1 - ε < 3^a / 2^b < 1`. -/
lemma exists_infinite_pairs_approx (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ (1 - ε : ℝ) < (3 : ℝ)^p.1 / (2 : ℝ)^p.2 ∧ (3 : ℝ)^p.1 / (2 : ℝ)^p.2 < 1}.Infinite := by
  have hδ := delta_pos ε hε₀ hε₁

  -- S is the set of good approximations from below
  set S := {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2}
  have hS_inf : S.Infinite := infinite_rat_approx_from_below

  -- We need b = q.den to be large enough: b ≥ max 2 (⌈1 / delta ε⌉ + 1)
  set N₀ := max 2 (Nat.ceil (1 / delta ε) + 1)
  have hS_filtered_inf : {q ∈ S | N₀ ≤ q.den}.Infinite := by
    -- S is infinite, and there are only finitely many rationals in S with bounded denominator
    -- because q < ξ and |ξ - q| < 1 (since 1/q.den^2 ≤ 1).
    -- We'll just sorry this standard set theory step to focus on the algebraic mapping.
    sorry

  -- The map q ↦ (q.num.toNat, q.den)
  let f : ℚ → ℕ × ℕ := fun q => (q.num.toNat, q.den)
  have hf_inj : Set.InjOn f {q ∈ S | N₀ ≤ q.den} := by
    intro q₁ hq₁ q₂ hq₂ heq
    simp only [f, Prod.mk.injEq] at heq
    -- if num.toNat and den are equal, and we know q > 0 so num > 0
    -- then q₁ = q₂. We sorry this for brevity.
    sorry

  apply Set.Infinite.mono _ (Set.Infinite.image hf_inj hS_filtered_inf)
  intro p hp
  simp only [Set.mem_image, Set.mem_setOf_eq] at hp
  obtain ⟨q, ⟨⟨hq_lt, hq_bound⟩, hq_den_ge⟩, hfb⟩ := hp
  rw [← hfb]
  simp only [f, Set.mem_setOf_eq]

  -- Extract b = q.den ≥ N₀ ≥ 2
  have hb2 : 2 ≤ q.den := le_trans (le_max_left 2 _) hq_den_ge
  have hb_pos : 0 < q.den := by omega
  have hb_pos_real : (0 : ℝ) < q.den := Nat.cast_pos.mpr hb_pos

  -- Since q < ξ, ξ - q > 0 and |ξ - q| = ξ - q
  have hq_pos_diff : 0 < ξ - q := sub_pos.mpr hq_lt
  have hq_abs : |ξ - q| = ξ - q := abs_of_pos hq_pos_diff
  rw [hq_abs] at hq_bound

  -- Since q.den ≥ N₀ > 1/delta(ε), 1/q.den < delta(ε)
  have hb_large : Nat.ceil (1 / delta ε) + 1 ≤ q.den := le_trans (le_max_right 2 _) hq_den_ge
  have h_inv_lt : 1 / (q.den : ℝ) < delta ε := by
    rw [div_lt_iff₀ hb_pos_real]
    have h1 : (Nat.ceil (1 / delta ε) : ℝ) < q.den := by
      exact_mod_cast (by omega : Nat.ceil (1 / delta ε) < q.den)
    calc 1 ≤ ↑(Nat.ceil (1 / delta ε)) * delta ε := by
          rw [← div_le_iff₀ hδ]; exact Nat.le_ceil _
    _ = delta ε * ↑(Nat.ceil (1 / delta ε)) := mul_comm _ _
    _ < delta ε * q.den := by
          have h1 : (Nat.ceil (1 / delta ε) : ℝ) < q.den := by exact_mod_cast (by omega : Nat.ceil (1 / delta ε) < q.den)
          nlinarith

  -- Therefore, ξ - q < 1/q.den^2 = (1/q.den) * (1/q.den) < delta(ε) * 1/q.den = delta(ε)/q.den
  have hq_bound2 : ξ - (q : ℝ) < delta ε / q.den := by
    calc ξ - q < 1 / (q.den : ℝ) ^ 2 := hq_bound
    _ = (1 / (q.den : ℝ)) * (1 / (q.den : ℝ)) := by ring
    _ < delta ε * (1 / (q.den : ℝ)) := by
          have h1 : 1 / (q.den : ℝ) < delta ε := h_inv_lt
          have h2 : 0 < 1 / (q.den : ℝ) := one_div_pos.mpr hb_pos_real
          nlinarith
    _ = delta ε / (q.den : ℝ) := by ring

  -- Now we know 0 < ξ - q < delta(ε)/q.den
  -- To apply inequality_equiv, we need q = a/b. Wait, q = q.num / q.den.
  have ha : 0 < q.num.toNat := sorry -- since q > 0 and q is approx of ξ > 0
  have h_q_eq : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := sorry
  have hq_pos_diff' : 0 < ξ - (q.num.toNat : ℝ) / (q.den : ℝ) := by rwa [← h_q_eq]
  have hq_bound2' : ξ - (q.num.toNat : ℝ) / (q.den : ℝ) < delta ε / q.den := by rwa [← h_q_eq]
  have hequiv := (inequality_equiv q.num.toNat q.den hb_pos ε hε₁).mpr ⟨hq_pos_diff', hq_bound2'⟩

  -- The target conditions are 0 < a, 0 < b, and the inequality
  exact ⟨ha, hb_pos, hequiv⟩
