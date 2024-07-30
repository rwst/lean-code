import Mathlib

lemma prod_Icc_succ_div (n : ℕ) (hn : 2 ≤ n) : (∏ x in Icc 1 n, ((x + 1) : ℝ) / x) = n + 1 := by
  rw [← Nat.Ico_succ_right]
  induction' n with n h
  · simp
  · rw [Finset.prod_Ico_succ_top <| Nat.le_add_left 1 n]
    norm_num
    cases' lt_or_ge n 2 with _ h2
    · interval_cases n
      · tauto
      · norm_num
    specialize h h2
    field_simp [Finset.prod_eq_zero_iff] at h ⊢
    rw [h]
    ring
