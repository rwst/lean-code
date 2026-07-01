import CC.Decomposition
import RT.Approximation
import RT.CRozLemma32
import RT.ProductIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Corollary 4.2 and the min-term forms of Theorem 4.2 / Corollaries 4.3, 4.4

The upper bound on `E/n` and the resulting constraints on the ones-ratio `q/j` and the smallest
odd term `m` are the **min-term** forms `4.2'`, `4.3'`, `4.4'` of [Roz25].  They are obtained here
from the exact product identity `RT.correction_exact_product` (Theorem 4.2★) by bounding each
odd-term factor `1 + 1/(3 mₖ)` by its worst case `1 + 1/(3 m)` (`Finset.prod_le_pow_card`), where
`m` is any lower bound on the odd terms.  The log/floor real-analytic cores are shared with the
harmonic-mean forms and live in `RT.ProductIdentity`.

* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

open CC

namespace RT

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
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

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma even_step_bound (x : ℕ) (heven : x % 2 = 0) :
    (T x : ℚ) = (x : ℚ) / 2 := by
  have hT : T x = x / 2 := T_even heven
  rw [hT]
  have hd : 2 ∣ x := by omega
  have hz : (2 : ℚ) ≠ 0 := by norm_num
  exact Nat.cast_div hd hz |>.trans (by push_cast; rfl)

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
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

/-- **Theorem 4.2′** (min-term form). A generic upper bound on the correction ratio `E(j,n)/n`,
    for `m` any lower bound on the odd terms.  Re-based on the exact product identity
    `RT.correction_exact_product` (Theorem 4.2★): each odd-term factor `1 + 1/(3 mₖ)` is bounded by
    its worst case `1 + 1/(3 m)`, so the product is bounded by `(1 + 1/(3m))^q`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma correction_ratio_bound_theorem_4_1 (j n m : ℕ) (hn : n > 0) (hm_pos : m > 0)
    (h_odd_bounded : ∀ (k : ℕ), k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m) :
    E j n / n ≤ ((3 + (1 : ℚ) / m) ^ num_odd_steps j n - 3 ^ num_odd_steps j n) / 2 ^ j := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm_pos
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hCpos : (0 : ℚ) < C j n := by unfold C; positivity
  -- Bound the exact product by the worst-case factor to the `q`-th power.
  have hbound : ∏ k ∈ Finset.range j, oddFactor (T_iter k n)
      ≤ (1 + 1 / (3 * (m : ℚ))) ^ num_odd_steps j n := by
    rw [prod_range_oddFactor_eq_oddIdx, ← oddIdx_card, ← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro k _; exact (oddFactor_pos _).le
    · intro k hk
      simp only [oddIdx, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hk_lt, hk_odd⟩ := hk
      rw [oddFactor_odd hk_odd]
      have hge : (m : ℚ) ≤ T_iter k n := by exact_mod_cast h_odd_bounded k hk_lt hk_odd
      have hle : 1 / (3 * (T_iter k n : ℚ)) ≤ 1 / (3 * (m : ℚ)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
  -- Combine with 4.2★ and rearrange, exactly as in the harmonic-mean case.
  have hCEP := correction_exact_product j n hn
  have hEC : E j n / (C j n * n) ≤ (1 + 1 / (3 * (m : ℚ))) ^ num_odd_steps j n - 1 := by
    have hstep : 1 + E j n / (C j n * n) ≤ (1 + 1 / (3 * (m : ℚ))) ^ num_odd_steps j n := by
      rw [hCEP]; exact hbound
    linarith
  have hEn : E j n / (n : ℚ) = C j n * (E j n / (C j n * n)) := by field_simp
  rw [hEn]
  calc C j n * (E j n / (C j n * n))
      ≤ C j n * ((1 + 1 / (3 * (m : ℚ))) ^ num_odd_steps j n - 1) :=
        mul_le_mul_of_nonneg_left hEC (le_of_lt hCpos)
    _ = ((3 + (1 : ℚ) / m) ^ num_odd_steps j n - 3 ^ num_odd_steps j n) / 2 ^ j := by
        have hCval : C j n = (3 : ℚ) ^ num_odd_steps j n / (2 : ℚ) ^ j := rfl
        have hpow : (3 : ℚ) ^ num_odd_steps j n * (1 + 1 / (3 * (m : ℚ))) ^ num_odd_steps j n
            = (3 + 1 / (m : ℚ)) ^ num_odd_steps j n := by
          rw [← mul_pow]; congr 1; field_simp
        rw [hCval, mul_sub, mul_one, div_mul_eq_mul_div, hpow, ← sub_div]

/-- **Corollary 4.3′** (min-term form). A necessary condition for `(j,n)` to be paradoxical is that
    the ones-ratio `q/j` satisfies the given logarithmic bounds, with `m` any lower bound on the
    odd terms. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_cor_43"]
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
  exact paradoxical_ratio_real j (num_odd_steps j n) (m : ℝ) hj_pos
    (by exact_mod_cast hm_pos) h_para_real h_E_real

/-- **Corollary 4.4′** (min-term form). A necessary condition for `(j,n)` to be paradoxical
    involving the minimum odd-step scalar is `m ≤ 1 / (2^r - 3)`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_cor_44"]
lemma paradoxical_m_bound (j n m : ℕ) (hj_ge_2 : j ≥ 2) (hn : n > 0) (hm_pos : m > 0)
    (h_odd_bounded : ∀ (k : ℕ), k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m)
    (h_para : IsParadoxical j n) :
    let r := (j : ℝ) / ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋
    (2 : ℝ)^r - 3 > 0 ∧ (m : ℝ) ≤ 1 / ((2 : ℝ)^r - 3) := by
  have hl := paradoxical_ratio_bounds j n m hn hm_pos h_odd_bounded h_para
  exact paradoxical_m_bound_floor_real j (num_odd_steps j n) (m : ℝ) hj_ge_2
    (by exact_mod_cast hm_pos) hl

end RT
