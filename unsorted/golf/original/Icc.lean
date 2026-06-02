import Mathlib

lemma prod_Icc_succ_div (n : ℕ) (hn : 2 ≤ n) : (∏ x in Icc 1 n, ((x + 1) : ℝ) / x) = n + 1 := by
  induction n with
  | zero => linarith
  | succ n ih =>
    have hnpos : 1 ≤ n := by linarith
    have hall (hn': n ≥ 1) : ∏ x in Finset.Icc 1 n, ((x + 1) : ℝ) / x = n + 1 := by
      cases lt_or_eq_of_le hn'
      case inr heq =>
        rw [heq.symm]
        simp only [Finset.Icc_self, prod_div_distrib, Finset.prod_singleton, Nat.cast_one, div_one]
      case inl hlt => exact ih hlt
    rw [← mul_prod_Ico_eq_prod_Icc, Nat.cast_succ]
    rw [add_assoc, one_add_one_eq_two, prod_Ico_succ_top]
    nth_rewrite 1 [mul_comm]
    rw [prod_Ico_mul_eq_prod_Icc, hall, mul_div ((n : ℝ) + 1) ((n : ℝ) + 2) ((n : ℝ) + 1)]
    rw [mul_comm, mul_div_cancel_of_imp]
    assumption'
    . intro hl
      have : ¬((n : ℝ) + 1 = 0) := by linarith
      contradiction
    . exact Nat.one_le_of_lt hn

