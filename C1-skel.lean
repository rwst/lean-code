import Mathlib

/-- do a single collatz-step. `collatz_step n` returns 1 if `n < 2`, otherwise `n/2` if `n` is even, otherwise `3 * n + 1`-/
def collatz_step (n : ℕ) : ℕ :=
  if n % 2 == 0 then
    (n / 2)
  else
    (3 * n + 1)

/-- `collatz_iter k n` does `k` collatz-steps on `n` -/
def collatz_iter : ℕ → ℕ → ℕ
| 0, n     => n
| (k + 1), n => collatz_iter k (collatz_step n)

#eval collatz_iter 986 670617279 -- this number gets to 1 only after 986 steps

lemma collatz_step_pow_two (k : ℕ) (hk : k ≥ 1) : collatz_step (2^k) = 2^(k-1) := by
  sorry

lemma collatz_iter_pow_two (l : ℕ) : collatz_iter l (2^l) = 1 := by
  sorry

lemma collatz_iter_pow_two_ne_one (l k : ℕ) (hk : k < l) : collatz_iter k (2^l) ≠ 1 := by
  sorry

lemma exists_collatz_reverse_strict (l : ℕ) :
  ∃ n : ℕ, collatz_iter l n = 1 ∧ ∀ k, k < l → collatz_iter k n ≠ 1 := by
  sorry

/--
Relation asserting that `n` reaches 1 with exactly `m` steps of the form `3n+1`.
Any number of `n/2` steps are allowed and do not contribute to the count `m`.
-/
inductive CollatzOddSteps : ℕ → ℕ → Prop where
  -- Base case: We are at 1. We have used 0 odd steps.
  | base : CollatzOddSteps 1 0

  -- Even step: If n is even, divide by 2.
  -- The count 'm' passes through unchanged.
  | even {n m : ℕ} :
      n % 2 = 0 →
      n ≠ 0 →            -- safety to prevent 0 loop
      CollatzOddSteps (n / 2) m →
      CollatzOddSteps n m

  -- Odd step: If n is odd (and not 1), do 3n+1.
  -- The count increases to 'm + 1'.
  | odd {n m : ℕ} :
      n % 2 = 1 →
      n > 1 →            -- prevent stepping away from 1
      CollatzOddSteps (3 * n + 1) m →
      CollatzOddSteps n (m + 1)

-- 2^k mod 3 is 1 if k is even (and k > 0), 2 if k is odd
lemma pow_two_mod_three (k : ℕ) (hk : k ≥ 1) : 2^k % 3 = if k % 2 = 0 then 1 else 2 := by
  sorry

lemma exists_predecessor_of_odd (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) :
  ∃ x k : ℕ, x % 2 = 1 ∧ (3 * x + 1) = 2^k * y := by
  sorry

/--
If `y` is a multiple of 3, it implies there is no number `n`
(and shift `k`) such that performing a `3n+1` step and `k` divisions reaches `y`.
-/
lemma no_odd_predecessor_for_div3 (y : ℕ) (h_div3 : y % 3 = 0) :
  ∀ n k : ℕ, 3 * n + 1 ≠ y * 2^k := by
  sorry

/-- CollatzOddSteps is preserved under multiplication by powers of 2 -/
lemma CollatzOddSteps_mul_pow_two (y m k : ℕ) (hy : CollatzOddSteps y m) (hk : k ≥ 1) :
    CollatzOddSteps (2^k * y) m := by
  sorry

/-- Numbers reachable via CollatzOddSteps are positive -/
lemma CollatzOddSteps_pos (n m : ℕ) (h : CollatzOddSteps n m) : n ≥ 1 := by
  cases h with
  | base => simp
  | even _ hn _ => omega
  | odd _ hgt1 _ => omega

/-- For y ≡ 1 (mod 6), there exists x > 1 odd such that 3x+1 = 4y -/
lemma exists_predecessor_gt_one_mod1 (y : ℕ) (hy_mod6 : y % 6 = 1) (hy_gt : y > 1) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^2 * y := by
  sorry

/-- For y ≡ 5 (mod 6), there exists x > 1 odd such that 3x+1 = 2y -/
lemma exists_predecessor_gt_one_mod5 (y : ℕ) (hy_mod6 : y % 6 = 5) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^1 * y := by
  sorry

/-- Main helper: for odd y not div by 3 and y > 1, exists x > 1 odd with 3x+1 = 2^k * y -/
lemma exists_predecessor_of_odd_gt_one (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) (h_gt : y > 1) :
    ∃ x k : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^k * y := by
  sorry

/-- For odd y > 1 with y % 3 ≠ 0, exists x > 1 odd with x % 3 ≠ 0 and 3x+1 = 2^k * y -/
lemma exists_predecessor_not_div3 (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) (h_gt : y > 1) :
    ∃ x k : ℕ, x % 2 = 1 ∧ x > 1 ∧ x % 3 ≠ 0 ∧ (3 * x + 1) = 2^k * y := by
  sorry

/-- Strengthened Main Lemma: exists n with CollatzOddSteps n m AND n % 3 ≠ 0 AND (m > 0 → n is
odd and n > 1) -/
lemma exists_n_with_m_odd_steps_not_div3 (m : ℕ) :
    ∃ n : ℕ, CollatzOddSteps n m ∧ n % 3 ≠ 0 ∧ (m > 0 → n % 2 = 1 ∧ n > 1) := by
  sorry

/-- Main Lemma -/
lemma exists_n_with_m_odd_steps (m : ℕ) : ∃ n : ℕ, CollatzOddSteps n m := by
  obtain ⟨n, hn, _⟩ := exists_n_with_m_odd_steps_not_div3 m
  exact ⟨n, hn⟩

/-- Thanks to Edward van de Meent. -/
theorem collatz_conjecture : ∀ (n : ℕ), n = 0 ∨ ∃ k, collatz_iter k n = 1 :=
  sorry
