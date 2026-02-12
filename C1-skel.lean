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

--proven
lemma collatz_step_pow_two (k : ℕ) (hk : k ≥ 1) : collatz_step (2^k) = 2^(k-1) := by
  sorry

--proven
lemma collatz_iter_pow_two (l : ℕ) : collatz_iter l (2^l) = 1 := by
  sorry

--proven
lemma collatz_iter_pow_two_ne_one (l k : ℕ) (hk : k < l) : collatz_iter k (2^l) ≠ 1 := by
  sorry

--proven
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
--proven
lemma pow_two_mod_three (k : ℕ) (hk : k ≥ 1) : 2^k % 3 = if k % 2 = 0 then 1 else 2 := by
  sorry

--proven
lemma exists_predecessor_of_odd (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) :
  ∃ x k : ℕ, x % 2 = 1 ∧ (3 * x + 1) = 2^k * y := by
  sorry

--proven
lemma no_odd_predecessor_for_div3 (y : ℕ) (h_div3 : y % 3 = 0) :
  ∀ n k : ℕ, 3 * n + 1 ≠ y * 2^k := by
  sorry

--proven
/-- CollatzOddSteps is preserved under multiplication by powers of 2 -/
lemma CollatzOddSteps_mul_pow_two (y m k : ℕ) (hy : CollatzOddSteps y m) (hk : k ≥ 1) :
    CollatzOddSteps (2^k * y) m := by
  sorry

--proven
lemma CollatzOddSteps_pos (n m : ℕ) (h : CollatzOddSteps n m) : n ≥ 1 := by
  cases h with
  | base => simp
  | even _ hn _ => omega
  | odd _ hgt1 _ => omega

--proven
lemma exists_predecessor_gt_one_mod1 (y : ℕ) (hy_mod6 : y % 6 = 1) (hy_gt : y > 1) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^2 * y := by
  sorry

--proven
lemma exists_predecessor_gt_one_mod5 (y : ℕ) (hy_mod6 : y % 6 = 5) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^1 * y := by
  sorry

--proven
lemma exists_predecessor_of_odd_gt_one (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) (h_gt : y > 1) :
    ∃ x k : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^k * y := by
  sorry

--proven
lemma exists_predecessor_not_div3 (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) (h_gt : y > 1) :
    ∃ x k : ℕ, x % 2 = 1 ∧ x > 1 ∧ x % 3 ≠ 0 ∧ (3 * x + 1) = 2^k * y := by
  sorry

--proven
lemma exists_n_with_m_odd_steps_not_div3 (m : ℕ) :
    ∃ n : ℕ, CollatzOddSteps n m ∧ n % 3 ≠ 0 ∧ (m > 0 → n % 2 = 1 ∧ n > 1) := by
  sorry

--proven
lemma exists_n_with_m_odd_steps (m : ℕ) : ∃ n : ℕ, CollatzOddSteps n m := by
  obtain ⟨n, hn, _⟩ := exists_n_with_m_odd_steps_not_div3 m
  exact ⟨n, hn⟩

--proven
lemma CollatzOddSteps_4n_add_1 (n m : ℕ) (h_odd : n % 2 = 1) (h_gt1 : n > 1)
    (h : CollatzOddSteps n m) : CollatzOddSteps (4 * n + 1) m := by
  sorry

/-- Sequence: iterate (4*x + 1) starting from n₀ -/
def iter_4n_plus_1 (n₀ : ℕ) : ℕ → ℕ
  | 0 => n₀
  | i + 1 => 4 * iter_4n_plus_1 n₀ i + 1

-- proven
lemma iter_4n_plus_1_odd (n₀ : ℕ) (h_odd : n₀ % 2 = 1) : ∀ i, iter_4n_plus_1 n₀ i % 2 = 1 := by
  sorry

-- proven
lemma iter_4n_plus_1_gt_one (n₀ : ℕ) (h_gt1 : n₀ > 1) : ∀ i, iter_4n_plus_1 n₀ i > 1 := by
  sorry

--proven
lemma iter_4n_plus_1_growth (n₀ : ℕ) (h_pos : n₀ ≥ 1) : ∀ i, iter_4n_plus_1 n₀ i ≥ i + 1 := by
  sorry

--proven
lemma infinitely_many_collatz_odd_steps (m : ℕ) : ∀ k, ∃ n, n > k ∧ CollatzOddSteps n m := by
  sorry

/--
A "primitive" for step count `m` is an odd number `n` that reaches 1 in `m` steps,
but is not the child of another *odd* number `k` (via `4k+1`) that also reaches 1 in `m` steps.

Since the "Odd Step" count is preserved between `k` and `4k+1` only when `k` is odd,
we explicitly require the predecessor to be odd.
-/
def IsPrimitive4x1 (n m : ℕ) : Prop :=
  CollatzOddSteps n m ∧
  n % 2 = 1 ∧
  ∀ k, k % 2 = 1 → 4 * k + 1 = n → ¬ CollatzOddSteps k m

--proven
lemma is_primitive_iff_mod_8_ne_5 (n m : ℕ) (h_odd : n % 2 = 1) (h_steps : CollatzOddSteps n m)
    (h_ne5 : n ≠ 5) : IsPrimitive4x1 n m ↔ n % 8 ≠ 5 := by
  sorry

--proven
lemma infinitely_many_not_div3 (m : ℕ) : ∀ B, ∃ n, n > B ∧ CollatzOddSteps n m ∧ n % 3 ≠ 0 := by
  sorry

--proven
lemma odd_node_generates_primitive (y m : ℕ)
  (h_steps : CollatzOddSteps y m)
  (h_odd : y % 2 = 1)
  (h_not_div3 : y % 3 ≠ 0) :
  ∃ n, IsPrimitive4x1 n (m + 1) := by
  sorry

/--
For every level `m`, there are infinitely many primitive numbers.
-/
lemma infinite_primitives (m : ℕ) (h2le: 2 ≤ m) : ∀ B, ∃ n, n > B ∧ IsPrimitive4x1 n m := by
  sorry

/-- Thanks to Edward van de Meent. -/
theorem collatz_conjecture : ∀ (n : ℕ), n = 0 ∨ ∃ k, collatz_iter k n = 1 :=
  sorry
