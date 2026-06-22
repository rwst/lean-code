import CollatzMapBasics.Decomposition
import CollatzMapBasics.Approximation
import CollatzMapBasics.RozierTerracol.CRozLemma32
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

open CollatzMapBasics

namespace CollatzMapBasics

lemma isParadoxical_bound {j n : ℕ} (hn : n > 0) (h : IsParadoxical j n) :
    0 < 1 - C j n ∧ 1 - C j n ≤ E j n / n :=
  ⟨by linarith [h.2], by
    have hnq : (n : ℚ) > 0 := by positivity
    rw [le_div_iff₀ hnq]
    have hd := linear_decomposition' j n
    have ht : (n : ℚ) ≤ T_iter j n := by exact_mod_cast h.1
    nlinarith⟩

lemma odd_step_bound (x m : ℕ) (hm : m > 0) (hx : x ≥ m) (hodd : x % 2 = 1) :
    (T x : ℚ) ≤ (x : ℚ) * (3 + (1 : ℚ) / (m : ℚ)) / 2 := by
  have hm_pos : (m : ℚ) > 0 := by exact_mod_cast hm
  have hx_pos : (x : ℚ) > 0 := by exact_mod_cast (by omega : x > 0)
  have hT : T x = (3 * x + 1) / 2 := T_odd hodd
  have hTq : (T x : ℚ) = (3 * (x : ℚ) + 1) / 2 := by
    rw [hT]
    have hd : 2 ∣ 3 * x + 1 := by omega
    have hz : (2 : ℚ) ≠ 0 := by norm_num
    exact Nat.cast_div hd hz |>.trans (by push_cast; rfl)
  rw [hTq]
  have h1 : (1 : ℚ) ≤ (x : ℚ) / (m : ℚ) := by
    rw [one_le_div hm_pos]
    exact_mod_cast hx
  have h2 : 3 * (x : ℚ) + 1 ≤ (x : ℚ) * (3 + 1 / (m : ℚ)) := by
    calc 3 * (x : ℚ) + 1 ≤ 3 * (x : ℚ) + (x : ℚ) / (m : ℚ) := by linarith
         _ = (x : ℚ) * (3 + 1 / (m : ℚ)) := by ring
  linarith

lemma even_step_bound (x : ℕ) (heven : x % 2 = 0) :
    (T x : ℚ) = (x : ℚ) / 2 := by
  have hT : T x = x / 2 := T_even heven
  rw [hT]
  have hd : 2 ∣ x := by omega
  have hz : (2 : ℚ) ≠ 0 := by norm_num
  exact Nat.cast_div hd hz |>.trans (by push_cast; rfl)

lemma odd_iter_bound_theorem_4_1 (j n m : ℕ) (hm_pos : m > 0)
    (h_odd_bounded : ∀ (k : ℕ), k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m) :
    (T_iter j n : ℚ) ≤ n * ((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j := by
  induction j with
  | zero =>
    simp [T_iter, num_odd_steps]
  | succ j ih =>
    have hp2 : (2 : ℚ) ^ (j + 1) = 2 ^ j * 2 := by ring
    rw [hp2]
    have h_odd_bounded_prev : ∀ (k : ℕ), k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m := by
      intro k hk; exact h_odd_bounded k (Nat.lt_trans hk (Nat.lt_succ_self j))
    have ih2 := ih h_odd_bounded_prev
    by_cases hodd : T_iter j n % 2 = 1
    · have X_val : X (T_iter j n) = 1 := by exact X_odd hodd
      have step_eq : (T_iter (j + 1) n : ℚ) = (T (T_iter j n) : ℚ) := rfl
      rw [step_eq, num_odd_steps_succ, X_val, pow_add, pow_one]
      have h1 := odd_step_bound (T_iter j n) m hm_pos (h_odd_bounded j (Nat.lt_succ_self j) hodd) hodd
      have h2 : (T (T_iter j n) : ℚ) ≤ ((n : ℚ) * (3 + 1 / (m : ℚ)) ^ num_odd_steps j n / 2 ^ j) * (3 + 1 / (m : ℚ)) / 2 := by
        calc (T (T_iter j n) : ℚ) ≤ (T_iter j n : ℚ) * (3 + (1 : ℚ) / (m : ℚ)) / 2 := h1
             _ ≤ ((n : ℚ) * (3 + (1 : ℚ) / m) ^ num_odd_steps j n / 2 ^ j) * (3 + (1 : ℚ) / (m : ℚ)) / 2 := by
               have hp3 : 3 + (1 : ℚ) / (m : ℚ) ≥ 0 := by positivity
               nlinarith
      have hr : ((n : ℚ) * (3 + 1 / (m : ℚ)) ^ num_odd_steps j n / 2 ^ j) * (3 + 1 / (m : ℚ)) / 2 =
                (n : ℚ) * ((3 + 1 / (m : ℚ)) ^ num_odd_steps j n * (3 + 1 / (m : ℚ))) / (2 ^ j * 2) := by ring
      rw [hr] at h2
      exact h2
    · have heven : T_iter j n % 2 = 0 := by omega
      have X_val : X (T_iter j n) = 0 := by exact X_even heven
      have step_eq : (T_iter (j + 1) n : ℚ) = (T (T_iter j n) : ℚ) := rfl
      rw [step_eq, num_odd_steps_succ, X_val, add_zero]
      have h1 := even_step_bound (T_iter j n) heven
      have h2 : (T (T_iter j n) : ℚ) ≤ ((n : ℚ) * (3 + 1 / (m : ℚ)) ^ num_odd_steps j n / 2 ^ j) / 2 := by
        calc (T (T_iter j n) : ℚ) = (T_iter j n : ℚ) / 2 := h1
             _ ≤ ((n : ℚ) * (3 + (1 : ℚ) / m) ^ num_odd_steps j n / 2 ^ j) / 2 := by
               exact div_le_div_of_nonneg_right ih2 (by positivity)
      have hr : ((n : ℚ) * (3 + 1 / (m : ℚ)) ^ num_odd_steps j n / 2 ^ j) / 2 =
                (n : ℚ) * (3 + 1 / (m : ℚ)) ^ num_odd_steps j n / (2 ^ j * 2) := by ring
      rw [hr] at h2
      exact h2

/-- A generic bound strictly on the correction ratio `E(j,n)/n`, relaxing the paradoxical requirement. -/
lemma correction_ratio_bound_theorem_4_1 (j n m : ℕ) (hn : n > 0) (hm_pos : m > 0)
    (h_odd_bounded : ∀ (k : ℕ), k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m) :
    E j n / n ≤ ((3 + (1 : ℚ) / m) ^ num_odd_steps j n - 3 ^ num_odd_steps j n) / 2 ^ j := by
  have hbound := odd_iter_bound_theorem_4_1 j n m hm_pos h_odd_bounded
  have hn_pos : (n : ℚ) > 0 := by exact_mod_cast hn
  have h_dec := linear_decomposition' j n
  have hp : (T_iter j n : ℚ) = C j n * n + E j n := by exact_mod_cast h_dec
  have hC : C j n = (3 ^ num_odd_steps j n : ℚ) / 2 ^ j := rfl
  rw [hp] at hbound

  -- Divide by n
  have hbound2 : (C j n * n + E j n) / n ≤ (n * ((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j) / n :=
    div_le_div_of_nonneg_right hbound (by positivity)

  -- Simplify LHS
  have hLHS : (C j n * n + E j n) / n = C j n + E j n / n := by
    calc (C j n * n + E j n) / n = C j n * n / n + E j n / n := by ring
         _ = C j n + E j n / n := by rw [mul_div_cancel_right₀ (C j n) (by positivity)]
  rw [hLHS] at hbound2

  -- Simplify RHS
  have hRHS : (n * ((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j) / n = ((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j := by
    calc (n * ((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j) / n
      _ = (n / n) * (((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j) := by ring
      _ = 1 * (((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j) := by rw [div_self (by positivity)]
      _ = ((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j := by ring
  rw [hRHS] at hbound2

  -- E / n <= ... - C
  have hbound3 : E j n / n ≤ ((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j - C j n := by linarith
  rw [hC] at hbound3
  have hRHS2 : ((3 + (1 : ℚ) / m) ^ num_odd_steps j n) / 2 ^ j - (3 ^ num_odd_steps j n : ℚ) / 2 ^ j =
               (((3 + (1 : ℚ) / m) ^ num_odd_steps j n) - (3 ^ num_odd_steps j n : ℚ)) / 2 ^ j := by ring
  rw [hRHS2] at hbound3
  exact hbound3

lemma paradoxical_ratio_real (j q m : ℕ) (hj_pos : j > 0) (hm_pos : m > 0)
    (h_para : (1 : ℝ) - (3 : ℝ)^q / (2 : ℝ)^j > 0)
    (h_E : (1 : ℝ) - (3 : ℝ)^q / (2 : ℝ)^j ≤ ((3 + 1 / (m : ℝ))^q - (3 : ℝ)^q) / (2 : ℝ)^j) :
    Real.log 2 / Real.log (3 + 1 / (m : ℝ)) ≤ (q : ℝ) / (j : ℝ) ∧
    (q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3 := by
  have hjR_pos : (j : ℝ) > 0 := by exact_mod_cast hj_pos
  have hmR_pos : (m : ℝ) > 0 := by exact_mod_cast hm_pos
  have h2j_pos : (0 : ℝ) < 2^j := by positivity

  -- Upper bound
  have h_upper1 : (3 : ℝ)^q / (2 : ℝ)^j < 1 := by linarith
  have h_upper2 : (3 : ℝ)^q < (2 : ℝ)^j := by
    exact (div_lt_one (by positivity)).mp h_upper1
  have h_upper3 : Real.log ((3 : ℝ)^q) < Real.log ((2 : ℝ)^j) := by
    exact Real.log_lt_log (by positivity) h_upper2
  rw [Real.log_pow, Real.log_pow] at h_upper3
  have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h_upper_final : (q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3 := by
    rw [div_lt_div_iff₀ hjR_pos hlog3_pos]
    linarith

  -- Lower bound
  have h_lower1 : (2 : ℝ)^j - (3 : ℝ)^q ≤ (3 + 1 / (m : ℝ))^q - (3 : ℝ)^q := by
    have h_times : ((1 : ℝ) - (3 : ℝ)^q / (2 : ℝ)^j) * (2 : ℝ)^j ≤ (((3 + 1 / (m : ℝ))^q - (3 : ℝ)^q) / (2 : ℝ)^j) * (2 : ℝ)^j := by
      exact mul_le_mul_of_nonneg_right h_E (by positivity)
    have hr1 : ((1 : ℝ) - (3 : ℝ)^q / (2 : ℝ)^j) * (2 : ℝ)^j = (2 : ℝ)^j - (3 : ℝ)^q := by
      calc ((1 : ℝ) - (3 : ℝ)^q / (2 : ℝ)^j) * (2 : ℝ)^j
        _ = 1 * (2 : ℝ)^j - ((3 : ℝ)^q / (2 : ℝ)^j) * (2 : ℝ)^j := by ring
        _ = (2 : ℝ)^j - (3 : ℝ)^q := by rw [one_mul, div_mul_cancel₀ _ (by positivity)]
    have hr2 : (((3 + 1 / (m : ℝ))^q - (3 : ℝ)^q) / (2 : ℝ)^j) * (2 : ℝ)^j = (3 + 1 / (m : ℝ))^q - (3 : ℝ)^q := by
      exact div_mul_cancel₀ _ (by positivity)
    linarith

  have h_lower2 : (2 : ℝ)^j ≤ (3 + 1 / (m : ℝ))^q := by linarith
  have h_lower3 : Real.log ((2 : ℝ)^j) ≤ Real.log ((3 + 1 / (m : ℝ))^q) := by
    have h2j_pos' : (0 : ℝ) < (2 : ℝ)^j := by positivity
    exact Real.log_le_log h2j_pos' h_lower2
  rw [Real.log_pow, Real.log_pow] at h_lower3
  have hlog3m_pos : (0 : ℝ) < Real.log (3 + 1 / (m : ℝ)) := by
    apply Real.log_pos
    have : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith
  have h_lower_final : Real.log 2 / Real.log (3 + 1 / (m : ℝ)) ≤ (q : ℝ) / (j : ℝ) := by
    rw [le_div_iff₀ hjR_pos, div_mul_eq_mul_div, div_le_iff₀ hlog3m_pos]
    linarith

  exact ⟨h_lower_final, h_upper_final⟩

/-- A necessary condition for (j,n) to be paradoxical
    is that the ratio of odd steps q/j satisfies the given logarithmic bounds. -/
lemma paradoxical_ratio_bounds (j n m : ℕ) (hn : n > 0) (hm_pos : m > 0)
    (h_odd_bounded : ∀ (k : ℕ), k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m)
    (h_para : IsParadoxical j n) :
    let q := num_odd_steps j n
    (Real.log 2 / Real.log (3 + 1 / (m : ℝ)) ≤ (q : ℝ) / (j : ℝ)) ∧
    ((q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3) := by
  have h_bound1 := isParadoxical_bound hn h_para
  have h_bound2 := correction_ratio_bound_theorem_4_1 j n m hn hm_pos h_odd_bounded
  have hj_pos : j > 0 := by
    by_contra h0
    have : j = 0 := by omega
    subst this
    have : C 0 n = 1 := by simp [C, num_odd_steps]
    linarith [h_para.2]
  have h_E_le : 1 - C j n ≤ ((3 + (1 : ℚ) / m) ^ num_odd_steps j n - 3 ^ num_odd_steps j n) / 2 ^ j := by
    linarith
  have h_para_real : (1 : ℝ) - (3 : ℝ)^(num_odd_steps j n) / (2 : ℝ)^j > 0 := by
    have hC : C j n = (3 ^ num_odd_steps j n : ℚ) / 2 ^ j := rfl
    have hl : (0 : ℚ) < 1 - C j n := h_bound1.1
    rw [hC] at hl
    have h_cast : (((0 : ℚ) : ℝ) < (((1 : ℚ) - (3 ^ num_odd_steps j n : ℚ) / 2 ^ j : ℚ) : ℝ)) := by
      exact_mod_cast hl
    push_cast at h_cast
    exact h_cast
  have h_E_real : (1 : ℝ) - (3 : ℝ)^(num_odd_steps j n) / (2 : ℝ)^j ≤
      ((3 + 1 / (m : ℝ))^(num_odd_steps j n) - (3 : ℝ)^(num_odd_steps j n)) / (2 : ℝ)^j := by
    have hC : C j n = (3 ^ num_odd_steps j n : ℚ) / 2 ^ j := rfl
    have hl := h_E_le
    rw [hC] at hl
    have h_cast : (((1 : ℚ) - (3 ^ num_odd_steps j n : ℚ) / 2 ^ j : ℚ) : ℝ) ≤
        ((((3 + (1 : ℚ) / m) ^ num_odd_steps j n - 3 ^ num_odd_steps j n) / 2 ^ j : ℚ) : ℝ) := by
      exact_mod_cast hl
    push_cast at h_cast
    exact h_cast

  exact paradoxical_ratio_real j (num_odd_steps j n) m hj_pos hm_pos h_para_real h_E_real

lemma log_ratio_not_int (j k : ℕ) (hj_ge_2 : j ≥ 2) :
    (j : ℝ) * Real.log 2 / Real.log 3 ≠ (k : ℝ) := by
  intro h
  have h1 : ξ = (k : ℝ) / (j : ℝ) := by
    calc ξ = Real.log 2 / Real.log 3 := rfl
         _ = ((j : ℝ) * Real.log 2 / Real.log 3) / (j : ℝ) := by
           rw [mul_div_assoc]
           exact (mul_div_cancel_left₀ _ (by exact_mod_cast (by omega : j ≠ 0))).symm
         _ = (k : ℝ) / (j : ℝ) := by rw [h]
  have h2 : (k : ℝ) / (j : ℝ) = (((k : ℚ) / (j : ℚ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h2] at h1
  exact irrational_xi ⟨(k : ℚ) / (j : ℚ), h1.symm⟩

lemma strict_floor_log_ratio (j : ℕ) (hj_ge_2 : j ≥ 2) :
    ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ) < (j : ℝ) * Real.log 2 / Real.log 3 := by
  have h_le := Int.floor_le ((j : ℝ) * Real.log 2 / Real.log 3)
  have h_ne : ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ) ≠ (j : ℝ) * Real.log 2 / Real.log 3 := by
    set k_int := ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋
    by_cases hpos : k_int < 0
    · have h_j_pos : (0 : ℝ) < j := by exact_mod_cast (by omega : j > 0)
      have h1 : (0 : ℝ) < (j : ℝ) * Real.log 2 / Real.log 3 := by positivity
      have h2 : ((k_int : ℤ) : ℝ) < 0 := by exact_mod_cast hpos
      linarith
    · push Not at hpos
      have h_nat : ∃ k : ℕ, (k : ℤ) = k_int := ⟨k_int.toNat, Int.toNat_of_nonneg hpos⟩
      obtain ⟨k, hk⟩ := h_nat
      rw [← hk]
      push_cast
      exact (log_ratio_not_int j k hj_ge_2).symm
  exact lt_of_le_of_ne h_le h_ne

lemma paradoxical_m_bound_q_real (j q m : ℕ) (hj_pos : j > 0) (hq_pos : q > 0) (hm_pos : m > 0)
    (h_ratio_lower : Real.log 2 / Real.log (3 + 1 / (m : ℝ)) ≤ (q : ℝ) / (j : ℝ))
    (h_ratio_upper : (q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3) :
    (2 : ℝ)^((j : ℝ) / (q : ℝ)) - 3 > 0 ∧
    (m : ℝ) ≤ 1 / ((2 : ℝ)^((j : ℝ) / (q : ℝ)) - 3) := by
  have hj : (j : ℝ) > 0 := by exact_mod_cast hj_pos
  have hq : (q : ℝ) > 0 := by exact_mod_cast hq_pos
  have hm : (m : ℝ) > 0 := by exact_mod_cast hm_pos
  have hlogm : Real.log (3 + 1 / (m : ℝ)) > 0 := by
    apply Real.log_pos
    have : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith
  have hlog3 : Real.log 3 > 0 := Real.log_pos (by norm_num)

  -- First prove the denominator is positive: 2^(j/q) > 3
  have h_denom_pos : (2 : ℝ)^((j : ℝ) / (q : ℝ)) > 3 := by
    have h1 : (q : ℝ) * Real.log 3 < (j : ℝ) * Real.log 2 := by
      have htemp : (q : ℝ) * Real.log 3 < Real.log 2 * (j : ℝ) := (div_lt_div_iff₀ hj hlog3).mp h_ratio_upper
      rwa [mul_comm (Real.log 2) _] at htemp
    have h2 : Real.log 3 < ((j : ℝ) / (q : ℝ)) * Real.log 2 := by
      have htemp : Real.log 3 < (j : ℝ) * Real.log 2 / (q : ℝ) := (lt_div_iff₀' hq).mpr h1
      rwa [mul_comm, ← mul_div_assoc, mul_comm]
    have h3 : Real.log 3 < Real.log ((2 : ℝ)^((j : ℝ) / (q : ℝ))) := by
      have h_pow' : Real.log ((2 : ℝ)^((j : ℝ) / (q : ℝ))) = ((j : ℝ) / (q : ℝ)) * Real.log 2 := by
        exact Real.log_rpow (by norm_num) _
      rwa [← h_pow'] at h2
    have h2pow_pos : (0 : ℝ) < (2 : ℝ)^((j : ℝ) / (q : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h3_pos : (0 : ℝ) < 3 := by norm_num
    exact (Real.log_lt_log_iff h3_pos h2pow_pos).mp h3

  have h_denom_gt_0 : (2 : ℝ)^((j : ℝ) / (q : ℝ)) - 3 > 0 := by linarith

  -- Now show the bound
  have h3m : ((j : ℝ) / (q : ℝ)) * Real.log 2 ≤ Real.log (3 + 1 / (m : ℝ)) := by
    have h1 := (div_le_div_iff₀ hlogm hj).mp h_ratio_lower
    -- h1 : Real.log 2 * j ≤ q * Real.log (3 + 1 / m)
    rw [show ((j : ℝ) / (q : ℝ)) * Real.log 2 = Real.log 2 * (j : ℝ) / (q : ℝ) from by ring]
    exact (div_le_iff₀ hq).mpr (by nlinarith)

  have h4m : Real.log ((2 : ℝ)^((j : ℝ) / (q : ℝ))) ≤ Real.log (3 + 1 / (m : ℝ)) := by
    have h_pow' : Real.log ((2 : ℝ)^((j : ℝ) / (q : ℝ))) = ((j : ℝ) / (q : ℝ)) * Real.log 2 := by
      exact Real.log_rpow (by norm_num) _
    rw [h_pow']
    exact h3m

  have h5m : (2 : ℝ)^((j : ℝ) / (q : ℝ)) ≤ 3 + 1 / (m : ℝ) := by
    have h2pow_pos : (0 : ℝ) < (2 : ℝ)^((j : ℝ) / (q : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h3M_pos : (0 : ℝ) < 3 + 1 / (m : ℝ) := by positivity
    exact (Real.log_le_log_iff h2pow_pos h3M_pos).mp h4m

  have h6m : (2 : ℝ)^((j : ℝ) / (q : ℝ)) - 3 ≤ 1 / (m : ℝ) := by linarith

  have h_bound : (m : ℝ) ≤ 1 / ((2 : ℝ)^((j : ℝ) / (q : ℝ)) - 3) := by
    rw [le_div_iff₀ h_denom_gt_0]
    have h7 := mul_le_mul_of_nonneg_left h6m (le_of_lt hm)
    have h8 : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
    linarith

  exact ⟨h_denom_gt_0, h_bound⟩

lemma paradoxical_m_bound_floor_real (j q m : ℕ) (hj_ge_2 : j ≥ 2) (hm_pos : m > 0)
    (h_q_bounds : (Real.log 2 / Real.log (3 + 1 / (m : ℝ)) ≤ (q : ℝ) / (j : ℝ)) ∧
                  ((q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3)) :
    let r := (j : ℝ) / ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋
    (2 : ℝ)^r - 3 > 0 ∧ (m : ℝ) ≤ 1 / ((2 : ℝ)^r - 3) := by
  have hj_pos : j > 0 := by omega
  have hj : (j : ℝ) > 0 := by exact_mod_cast hj_pos
  have hm : (m : ℝ) > 0 := by exact_mod_cast hm_pos

  -- q > 0 follows from the lower bound
  have hq_pos : q > 0 := by
    by_contra h0
    have : q = 0 := by omega
    subst this
    have hc : Real.log 2 / Real.log (3 + 1 / (m : ℝ)) ≤ 0 := by
      have : (0 : ℝ) / (j : ℝ) = 0 := zero_div _
      linarith [h_q_bounds.1]
    have hc2 : Real.log 2 / Real.log (3 + 1 / (m : ℝ)) > 0 := by
      have h2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
      have h_logm : (0 : ℝ) < Real.log (3 + 1 / (m : ℝ)) := by
        apply Real.log_pos
        have : (0 : ℝ) < 1 / (m : ℝ) := by positivity
        linarith
      positivity
    linarith

  have h_q_real := paradoxical_m_bound_q_real j q m hj_pos hq_pos hm_pos h_q_bounds.1 h_q_bounds.2

  -- Show q <= floor(j log 2 / log 3)
  have ht : (q : ℝ) < (j : ℝ) * Real.log 2 / Real.log 3 := by
    have hlog3_pos := Real.log_pos (show (1:ℝ) < 3 by norm_num)
    have h := (div_lt_div_iff₀ hj hlog3_pos).mp h_q_bounds.2
    exact (lt_div_iff₀ hlog3_pos).mpr (by nlinarith)

  have h_q_int : (q : ℝ) = ((q : ℤ) : ℝ) := rfl
  have ht_z : ((q : ℤ) : ℝ) ≤ (j : ℝ) * Real.log 2 / Real.log 3 := le_of_lt (by rwa [← h_q_int])

  have h_floor : (q : ℤ) ≤ ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ := Int.le_floor.mpr ht_z
  have hq_le : (q : ℝ) ≤ ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ := by exact_mod_cast h_floor

  -- show the denominator is positive
  set r := (j : ℝ) / ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋

  have hf_strict := strict_floor_log_ratio j hj_ge_2
  have h_floor_pos : (0 : ℝ) < ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ := by
    have hq_real_pos : (0 : ℝ) < q := by exact_mod_cast hq_pos
    calc (0 : ℝ) < (q : ℝ) := hq_real_pos
         _ ≤ ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ := hq_le

  have hq_real_pos : (q : ℝ) > 0 := by exact_mod_cast hq_pos
  have h_r_ge : r ≤ (j : ℝ) / (q : ℝ) := by
    exact div_le_div_of_nonneg_left (le_of_lt hj) hq_real_pos hq_le

  have h_denom : (2 : ℝ)^r ≤ (2 : ℝ)^((j : ℝ) / (q : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h_r_ge

  have h_r_gt_log : r > Real.log 3 / Real.log 2 := by
    have h2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
    have h3 : Real.log 3 > 0 := Real.log_pos (by norm_num)

    have hd1 : 1 / ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ) > 1 / ((j : ℝ) * (Real.log 2 / Real.log 3)) := by
      apply one_div_lt_one_div_of_lt
      · exact h_floor_pos
      · have : (j : ℝ) * Real.log 2 / Real.log 3 = (j : ℝ) * (Real.log 2 / Real.log 3) := by ring
        linarith

    have hd2 : (j : ℝ) * (1 / ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ)) > (j : ℝ) * (1 / ((j : ℝ) * (Real.log 2 / Real.log 3))) := by
      have := hd1
      have hr : (1 : ℝ) / ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ) > 1 / ((j : ℝ) * (Real.log 2 / Real.log 3)) := this
      nlinarith

    calc r = (j : ℝ) * (1 / ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ)) := by ring
         _ > (j : ℝ) * (1 / ((j : ℝ) * (Real.log 2 / Real.log 3))) := hd2
         _ = (j : ℝ) / ((j : ℝ) * (Real.log 2 / Real.log 3)) := by ring
         _ = 1 / (Real.log 2 / Real.log 3) := by rw [div_mul_eq_div_div, div_self (ne_of_gt hj), one_div]
         _ = Real.log 3 / Real.log 2 := by rw [one_div, inv_div]

  have h_2r : (2 : ℝ)^r > 3 := by
    have h2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
    have h3 : Real.log 3 > 0 := Real.log_pos (by norm_num)
    have h_r_log : r * Real.log 2 > Real.log 3 := (div_lt_iff₀ h2).mp h_r_gt_log
    have h_exp : Real.log ((2 : ℝ)^r) > Real.log 3 := by
      have : Real.log ((2 : ℝ)^r) = r * Real.log 2 := Real.log_rpow (by norm_num) r
      rwa [this]
    exact (Real.log_lt_log_iff (by norm_num) (Real.rpow_pos_of_pos (by norm_num) r)).mp h_exp

  have h_pos : (2 : ℝ)^r - 3 > 0 := by linarith
  have h_bound : (m : ℝ) ≤ 1 / ((2 : ℝ)^r - 3) := by
    calc (m : ℝ) ≤ 1 / ((2 : ℝ)^((j : ℝ) / (q : ℝ)) - 3) := h_q_real.2
         _ ≤ 1 / ((2 : ℝ)^r - 3) := by
           apply one_div_le_one_div_of_le (by linarith)
           linarith
  exact ⟨h_pos, h_bound⟩

/-- **Corollary 4.2** A necessary condition for (j,n) to be paradoxical involving the minimum odd
step scalar is m <= 1 / (2^r - 3). -/
lemma paradoxical_m_bound (j n m : ℕ) (hj_ge_2 : j ≥ 2) (hn : n > 0) (hm_pos : m > 0)
    (h_odd_bounded : ∀ (k : ℕ), k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m)
    (h_para : IsParadoxical j n) :
    let r := (j : ℝ) / ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋
    (2 : ℝ)^r - 3 > 0 ∧ (m : ℝ) ≤ 1 / ((2 : ℝ)^r - 3) := by
  have hl := paradoxical_ratio_bounds j n m hn hm_pos h_odd_bounded h_para
  exact paradoxical_m_bound_floor_real j (num_odd_steps j n) m hj_ge_2 hm_pos hl
