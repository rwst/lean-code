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
  simp only [collatz_step]
  have h : 2^k % 2 = 0 := by
    have : 2 ∣ 2^k := dvd_pow_self 2 (by omega : k ≠ 0)
    exact Nat.dvd_iff_mod_eq_zero.mp this
  simp only [h, beq_self_eq_true, ↓reduceIte]
  have hk' : k = k - 1 + 1 := by omega
  conv_lhs => rw [hk', Nat.pow_succ]
  simp

lemma collatz_iter_pow_two (l : ℕ) : collatz_iter l (2^l) = 1 := by
  induction l with
  | zero => simp [collatz_iter]
  | succ l ih =>
    simp only [collatz_iter]
    have h : collatz_step (2^(l+1)) = 2^l := by
      rw [collatz_step_pow_two (l+1) (by omega)]
      simp
    rw [h]
    exact ih

lemma collatz_iter_pow_two_ne_one (l k : ℕ) (hk : k < l) : collatz_iter k (2^l) ≠ 1 := by
  induction k generalizing l with
  | zero =>
    simp only [collatz_iter]
    have : 2^l ≥ 2 := by
      have : l ≥ 1 := by omega
      calc 2^l ≥ 2^1 := Nat.pow_le_pow_right (by norm_num) this
           _ = 2 := by norm_num
    omega
  | succ k ih =>
    simp only [collatz_iter]
    have hl : l ≥ 1 := by omega
    have hstep : collatz_step (2^l) = 2^(l-1) := collatz_step_pow_two l hl
    rw [hstep]
    apply ih
    omega

lemma exists_collatz_reverse_strict (l : ℕ) :
  ∃ n : ℕ, collatz_iter l n = 1 ∧ ∀ k, k < l → collatz_iter k n ≠ 1 := by
  use 2^l
  constructor
  · exact collatz_iter_pow_two l
  · exact collatz_iter_pow_two_ne_one l

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
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      simp only [Nat.pow_succ]
      rw [Nat.mul_mod, ih hn']
      by_cases hparity : n % 2 = 0
      · simp only [hparity, ↓reduceIte]
        have : (n + 1) % 2 = 1 := by omega
        simp [this]
      · have hnodd : n % 2 = 1 := by omega
        simp only [hnodd]
        have : (n + 1) % 2 = 0 := by omega
        simp [this]

lemma exists_predecessor_of_odd (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) :
  ∃ x k : ℕ, x % 2 = 1 ∧ (3 * x + 1) = 2^k * y := by
  have hy_mod3 : y % 3 = 1 ∨ y % 3 = 2 := by omega
  have hy_pos : y ≥ 1 := by omega
  rcases hy_mod3 with hy1 | hy2
  · use (2^2 * y - 1) / 3, 2
    constructor
    · have hy6 : y % 6 = 1 := by omega
      have hmod6 : (4 * y - 1) % 6 = 3 := by omega
      have hform : ∃ q, 4 * y - 1 = 6 * q + 3 := by
        use (4 * y - 1) / 6
        have := Nat.div_add_mod (4 * y - 1) 6
        omega
      obtain ⟨q, hq⟩ := hform
      have hdiv_eq : (4 * y - 1) / 3 = 2 * q + 1 := by
        rw [hq, show 6 * q + 3 = 3 * (2 * q + 1) by ring]
        exact Nat.mul_div_cancel_left (2 * q + 1) (by norm_num : 0 < 3)
      show (2^2 * y - 1) / 3 % 2 = 1
      have h4 : 2^2 * y = 4 * y := by ring
      rw [h4, hdiv_eq]
      omega
    · have hdiv : 3 ∣ (2^2 * y - 1) := by
        have h1 : 2^2 * y % 3 = 1 := by
          rw [Nat.mul_mod, Nat.pow_mod]; simp [hy1]
        omega
      have hge : 2^2 * y ≥ 1 := by omega
      have : 3 * ((2^2 * y - 1) / 3) + 1 = 2^2 * y := by
        have := Nat.div_add_mod (2^2 * y - 1) 3
        have hmod : (2^2 * y - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
        omega
      exact this
  · use (2^1 * y - 1) / 3, 1
    constructor
    · have hy6 : y % 6 = 5 := by omega
      have hge2y : 2 * y ≥ 1 := by omega
      have hmod6 : (2 * y - 1) % 6 = 3 := by omega
      have hform : ∃ q, 2 * y - 1 = 6 * q + 3 := by
        use (2 * y - 1) / 6
        have := Nat.div_add_mod (2 * y - 1) 6
        omega
      obtain ⟨q, hq⟩ := hform
      have hdiv_eq : (2 * y - 1) / 3 = 2 * q + 1 := by
        rw [hq, show 6 * q + 3 = 3 * (2 * q + 1) by ring]
        exact Nat.mul_div_cancel_left (2 * q + 1) (by norm_num : 0 < 3)
      rw [show 2^1 * y = 2 * y by ring, hdiv_eq]
      omega
    · have hdiv : 3 ∣ (2 * y - 1) := by
        have h1 : 2 * y % 3 = 1 := by rw [Nat.mul_mod]; omega
        omega
      have hge : 2 * y ≥ 1 := by omega
      have : 3 * ((2 * y - 1) / 3) + 1 = 2 * y := by
        have := Nat.div_add_mod (2 * y - 1) 3
        have hmod : (2 * y - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
        omega
      simp only [pow_one]
      exact this

/--
If `y` is a multiple of 3, it implies there is no number `n`
(and shift `k`) such that performing a `3n+1` step and `k` divisions reaches `y`.
-/
lemma no_odd_predecessor_for_div3 (y : ℕ) (h_div3 : y % 3 = 0) :
  ∀ n k : ℕ, 3 * n + 1 ≠ y * 2^k := by
  intro n k h_eq
  have lhs_mod : (3 * n + 1) % 3 = 1 := by
    simp [Nat.add_mod]
  have rhs_mod : (y * 2^k) % 3 = 0 := by
    rw [Nat.mul_mod, h_div3]
    simp
  rw [h_eq] at lhs_mod
  rw [rhs_mod] at lhs_mod
  contradiction

/-- CollatzOddSteps is preserved under multiplication by powers of 2 -/
lemma CollatzOddSteps_mul_pow_two (y m k : ℕ) (hy : CollatzOddSteps y m) (hk : k ≥ 1) :
    CollatzOddSteps (2^k * y) m := by
  have hy_pos : y ≥ 1 := by
    cases hy with
    | base => simp
    | even _ hn _ => omega
    | odd _ hn _ => omega
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases hk' : k' = 0
    · simp only [hk', zero_add, pow_one]
      apply CollatzOddSteps.even
      · simp only [Nat.mul_mod_right]
      · omega
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]; exact hy
    · have hk'' : k' ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk'
      have ih' := ih hk''
      apply CollatzOddSteps.even
      · have : 2^(k' + 1) * y = 2 * (2^k' * y) := by ring
        rw [this]; simp
      · -- 2^(k'+1) * y ≠ 0
        have hpow : 2^k' ≥ 1 := Nat.one_le_pow k' 2 (by omega)
        have : 2^(k' + 1) * y ≥ 2 := by
          calc 2^(k' + 1) * y = 2 * 2^k' * y := by ring
            _ ≥ 2 * 1 * 1 := by nlinarith
            _ = 2 := by ring
        omega
      · have hdiv : 2^(k' + 1) * y / 2 = 2^k' * y := by
          have : 2^(k' + 1) * y = 2 * (2^k' * y) := by ring
          rw [this]
          exact Nat.mul_div_cancel_left _ (by omega)
        rw [hdiv]
        exact ih'

/-- Numbers reachable via CollatzOddSteps are positive -/
lemma CollatzOddSteps_pos (n m : ℕ) (h : CollatzOddSteps n m) : n ≥ 1 := by
  cases h with
  | base => simp
  | even _ hn _ => omega
  | odd _ hgt1 _ => omega

/-- For y ≡ 1 (mod 6), there exists x > 1 odd such that 3x+1 = 4y -/
lemma exists_predecessor_gt_one_mod1 (y : ℕ) (hy_mod6 : y % 6 = 1) (hy_gt : y > 1) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^2 * y := by
  use (4 * y - 1) / 3
  have hy_pos : y ≥ 1 := by omega
  have h4y_ge : 4 * y ≥ 4 := by omega
  have hdiv3 : 3 ∣ (4 * y - 1) := by
    have : (4 * y) % 3 = 1 := by
      have hy_mod3 : y % 3 = 1 := by omega
      simp [Nat.mul_mod, hy_mod3]
    omega
  -- Show it's odd
  have hmod6 : (4 * y - 1) % 6 = 3 := by omega
  have hform : ∃ q, 4 * y - 1 = 6 * q + 3 := by
    use (4 * y - 1) / 6
    have := Nat.div_add_mod (4 * y - 1) 6
    omega
  obtain ⟨q, hq⟩ := hform
  have hdiv_eq : (4 * y - 1) / 3 = 2 * q + 1 := by
    rw [hq, show 6 * q + 3 = 3 * (2 * q + 1) by ring]
    exact Nat.mul_div_cancel_left (2 * q + 1) (by norm_num : 0 < 3)
  constructor
  · -- odd
    rw [hdiv_eq]; omega
  constructor
  · -- > 1
    rw [hdiv_eq]
    have hq_pos : q ≥ 1 := by
      have : 4 * y - 1 ≥ 7 := by omega
      rw [hq] at this
      omega
    omega
  · -- 3x + 1 = 4y
    have : 3 * ((4 * y - 1) / 3) + 1 = 4 * y := by
      have := Nat.div_add_mod (4 * y - 1) 3
      have hmod : (4 * y - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv3
      omega
    simp only [show (2:ℕ)^2 = 4 from by norm_num]; exact this

/-- For y ≡ 5 (mod 6), there exists x > 1 odd such that 3x+1 = 2y -/
lemma exists_predecessor_gt_one_mod5 (y : ℕ) (hy_mod6 : y % 6 = 5) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^1 * y := by
  use (2 * y - 1) / 3
  have hy_pos : y ≥ 5 := by omega
  have h2y_ge : 2 * y ≥ 10 := by omega
  have hdiv3 : 3 ∣ (2 * y - 1) := by
    have : (2 * y) % 3 = 1 := by
      have hy_mod3 : y % 3 = 2 := by omega
      simp [Nat.mul_mod, hy_mod3]
    omega
  -- Show it's odd
  have hmod6 : (2 * y - 1) % 6 = 3 := by omega
  have hform : ∃ q, 2 * y - 1 = 6 * q + 3 := by
    use (2 * y - 1) / 6
    have := Nat.div_add_mod (2 * y - 1) 6
    omega
  obtain ⟨q, hq⟩ := hform
  have hdiv_eq : (2 * y - 1) / 3 = 2 * q + 1 := by
    rw [hq, show 6 * q + 3 = 3 * (2 * q + 1) by ring]
    exact Nat.mul_div_cancel_left (2 * q + 1) (by norm_num : 0 < 3)
  constructor
  · -- odd
    rw [hdiv_eq]; omega
  constructor
  · -- > 1
    rw [hdiv_eq]
    have hq_pos : q ≥ 1 := by
      have : 2 * y - 1 ≥ 9 := by omega
      rw [hq] at this
      omega
    omega
  · -- 3x + 1 = 2y
    have : 3 * ((2 * y - 1) / 3) + 1 = 2 * y := by
      have := Nat.div_add_mod (2 * y - 1) 3
      have hmod : (2 * y - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv3
      omega
    simpa only [pow_one]

/-- Main helper: for odd y not div by 3 and y > 1, exists x > 1 odd with 3x+1 = 2^k * y -/
lemma exists_predecessor_of_odd_gt_one (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) (h_gt : y > 1) :
    ∃ x k : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^k * y := by
  have hy_mod6 : y % 6 = 1 ∨ y % 6 = 5 := by omega
  rcases hy_mod6 with h1 | h5
  · obtain ⟨x, hx_odd, hx_gt, hx_eq⟩ := exists_predecessor_gt_one_mod1 y h1 h_gt
    exact ⟨x, 2, hx_odd, hx_gt, hx_eq⟩
  · obtain ⟨x, hx_odd, hx_gt, hx_eq⟩ := exists_predecessor_gt_one_mod5 y h5
    exact ⟨x, 1, hx_odd, hx_gt, hx_eq⟩

/-- For odd y > 1 with y % 3 ≠ 0, exists x > 1 odd with x % 3 ≠ 0 and 3x+1 = 2^k * y -/
lemma exists_predecessor_not_div3 (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) (h_gt : y > 1) :
    ∃ x k : ℕ, x % 2 = 1 ∧ x > 1 ∧ x % 3 ≠ 0 ∧ (3 * x + 1) = 2^k * y := by
  -- The idea: try k values until we find one where x % 3 ≠ 0
  -- Since 2^k mod 9 cycles with period 6, we will find a valid k
  have hy_mod6 : y % 6 = 1 ∨ y % 6 = 5 := by omega
  rcases hy_mod6 with h1 | h5
  · -- y ≡ 1 (mod 6), so y ≡ 1 (mod 3)
    -- Try k = 2, 4, 6 (even k so that 2^k ≡ 1 mod 3)
    -- For k = 2: x = (4y - 1)/3
    -- For k = 4: x = (16y - 1)/3
    -- For k = 6: x = (64y - 1)/3
    -- x mod 3 depends on (2^k * y) mod 9
    -- 2^2 = 4, 2^4 = 16 ≡ 7, 2^6 = 64 ≡ 1 (mod 9)
    -- If y ≡ 1 (mod 9): 4y ≡ 4, 16y ≡ 7, 64y ≡ 1 (mod 9)
    --   k=2: (4-1)/3 mod 3 = 1 ✓
    -- If y ≡ 4 (mod 9): 4y ≡ 7, 16y ≡ 1, 64y ≡ 4 (mod 9)
    --   k=2: (7-1)/3 = 2 mod 3 ✓
    -- If y ≡ 7 (mod 9): 4y ≡ 1, 16y ≡ 4, 64y ≡ 7 (mod 9)
    --   k=4: (4-1)/3 = 1 mod 3 ✓
    -- So k = 2 or k = 4 always works for y ≡ 1 (mod 6)
    by_cases hy9 : y % 9 = 7
    · -- Use k = 4
      use (16 * y - 1) / 3, 4
      have hdiv3 : 3 ∣ (16 * y - 1) := by
        have : (16 * y) % 3 = 1 := by omega
        omega
      have hmod6_val : (16 * y - 1) % 6 = 3 := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- odd: (16y-1) % 6 = 3 means (16y-1)/3 is odd
        have : ∃ q, 16 * y - 1 = 6 * q + 3 := ⟨(16 * y - 1) / 6, by omega⟩
        obtain ⟨q, hq⟩ := this
        have heq : (16 * y - 1) / 3 = 2 * q + 1 := by
          rw [hq, show 6 * q + 3 = 3 * (2 * q + 1) by ring]
          exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)
        omega
      · -- > 1
        have : 16 * y - 1 ≥ 15 := by omega
        omega
      · -- % 3 ≠ 0: 16y ≡ 16*7 = 112 ≡ 4 (mod 9), so (16y-1)/3 ≡ 1 (mod 3)
        have h16y_mod9 : (16 * y) % 9 = 4 := by omega
        have h16ym1_mod9 : (16 * y - 1) % 9 = 3 := by omega
        omega
      · -- 3x + 1 = 16y
        have := Nat.div_add_mod (16 * y - 1) 3
        have hmod : (16 * y - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv3
        simp only [pow_succ, pow_zero, one_mul]; omega
    · -- Use k = 2
      use (4 * y - 1) / 3, 2
      have hdiv3 : 3 ∣ (4 * y - 1) := by
        have : (4 * y) % 3 = 1 := by omega
        omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- odd
        have hmod6_val : (4 * y - 1) % 6 = 3 := by omega
        have : ∃ q, 4 * y - 1 = 6 * q + 3 := ⟨(4 * y - 1) / 6, by omega⟩
        obtain ⟨q, hq⟩ := this
        have heq : (4 * y - 1) / 3 = 2 * q + 1 := by
          rw [hq, show 6 * q + 3 = 3 * (2 * q + 1) by ring]
          exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)
        omega
      · -- > 1
        have : 4 * y - 1 ≥ 7 := by omega
        omega
      · -- % 3 ≠ 0
        have hy_mod9 : y % 9 = 1 ∨ y % 9 = 4 := by omega
        rcases hy_mod9 with h1' | h4'
        · have : (4 * y - 1) % 9 = 3 := by omega
          omega
        · have : (4 * y - 1) % 9 = 6 := by omega
          omega
      · -- 3x + 1 = 4y
        have := Nat.div_add_mod (4 * y - 1) 3
        have hmod : (4 * y - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv3
        simp only [pow_succ, pow_zero, one_mul]; omega
  · -- y ≡ 5 (mod 6), so y ≡ 2 (mod 3)
    -- Try k = 1, 3, 5 (odd k so that 2^k ≡ 2 mod 3)
    -- 2^1 = 2, 2^3 = 8 ≡ 8, 2^5 = 32 ≡ 5 (mod 9)
    -- If y ≡ 2 (mod 9): 2y ≡ 4, 8y ≡ 7, 32y ≡ 1 (mod 9)
    --   k=1: (4-1)/3 = 1 mod 3 ✓
    -- If y ≡ 5 (mod 9): 2y ≡ 1, 8y ≡ 4, 32y ≡ 7 (mod 9)
    --   k=3: (4-1)/3 = 1 mod 3 ✓
    -- If y ≡ 8 (mod 9): 2y ≡ 7, 8y ≡ 1, 32y ≡ 4 (mod 9)
    --   k=1: (7-1)/3 = 2 mod 3 ✓
    by_cases hy9 : y % 9 = 5
    · -- Use k = 3
      use (8 * y - 1) / 3, 3
      have hdiv3 : 3 ∣ (8 * y - 1) := by
        have : (8 * y) % 3 = 1 := by omega
        omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- odd
        have hmod6_val : (8 * y - 1) % 6 = 3 := by omega
        have : ∃ q, 8 * y - 1 = 6 * q + 3 := ⟨(8 * y - 1) / 6, by omega⟩
        obtain ⟨q, hq⟩ := this
        have heq : (8 * y - 1) / 3 = 2 * q + 1 := by
          rw [hq, show 6 * q + 3 = 3 * (2 * q + 1) by ring]
          exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)
        omega
      · -- > 1
        have : 8 * y - 1 ≥ 39 := by omega
        omega
      · -- % 3 ≠ 0: 8y ≡ 8*5 = 40 ≡ 4 (mod 9)
        have h8y_mod9 : (8 * y) % 9 = 4 := by omega
        have h8ym1_mod9 : (8 * y - 1) % 9 = 3 := by omega
        omega
      · -- 3x + 1 = 8y
        have := Nat.div_add_mod (8 * y - 1) 3
        have hmod : (8 * y - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv3
        simp only [pow_succ, pow_zero, one_mul]; omega
    · -- Use k = 1
      use (2 * y - 1) / 3, 1
      have hdiv3 : 3 ∣ (2 * y - 1) := by
        have : (2 * y) % 3 = 1 := by omega
        omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- odd
        have hmod6_val : (2 * y - 1) % 6 = 3 := by omega
        have : ∃ q, 2 * y - 1 = 6 * q + 3 := ⟨(2 * y - 1) / 6, by omega⟩
        obtain ⟨q, hq⟩ := this
        have heq : (2 * y - 1) / 3 = 2 * q + 1 := by
          rw [hq, show 6 * q + 3 = 3 * (2 * q + 1) by ring]
          exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)
        omega
      · -- > 1
        have : 2 * y - 1 ≥ 9 := by omega
        omega
      · -- % 3 ≠ 0
        have hy_mod9 : y % 9 = 2 ∨ y % 9 = 8 := by omega
        rcases hy_mod9 with h2' | h8'
        · have : (2 * y - 1) % 9 = 3 := by omega
          omega
        · have : (2 * y - 1) % 9 = 6 := by omega
          omega
      · -- 3x + 1 = 2y
        have := Nat.div_add_mod (2 * y - 1) 3
        have hmod : (2 * y - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv3
        simp only [pow_one]; omega

/-- Strengthened Main Lemma: exists n with CollatzOddSteps n m AND n % 3 ≠ 0 AND (m > 0 → n is odd and n > 1) -/
lemma exists_n_with_m_odd_steps_not_div3 (m : ℕ) :
    ∃ n : ℕ, CollatzOddSteps n m ∧ n % 3 ≠ 0 ∧ (m > 0 → n % 2 = 1 ∧ n > 1) := by
  induction m with
  | zero =>
    -- Case 0: n=1 works, 1 % 3 = 1 ≠ 0
    use 1
    refine ⟨CollatzOddSteps.base, by simp, by simp⟩
  | succ m_prev ih =>
    obtain ⟨y, hy, hy_not_div3, hy_odd_gt1⟩ := ih
    by_cases hm_prev : m_prev = 0
    · -- m_prev = 0: use n = 5
      -- 5 % 3 = 2 ≠ 0, 5 is odd, 5 > 1, and CollatzOddSteps 5 1
      use 5
      refine ⟨?_, by simp, by simp⟩
      apply CollatzOddSteps.odd (by simp) (by omega)
      have h16 : CollatzOddSteps 16 0 := by
        apply CollatzOddSteps.even; simp; omega
        apply CollatzOddSteps.even; simp; omega
        apply CollatzOddSteps.even; simp; omega
        apply CollatzOddSteps.even; simp; omega
        exact CollatzOddSteps.base
      rw [hm_prev]; exact h16
    · -- m_prev > 0, so y is odd and y > 1 (from our strengthened IH)
      have hm_prev_pos : m_prev > 0 := Nat.pos_of_ne_zero hm_prev
      have ⟨hy_odd, hy_gt1⟩ := hy_odd_gt1 hm_prev_pos
      -- Find predecessor with x % 3 ≠ 0
      obtain ⟨x, k, hx_odd, hx_gt1, hx_not_div3, hx_eq⟩ :=
        exists_predecessor_not_div3 y hy_odd hy_not_div3 hy_gt1
      use x
      refine ⟨?_, hx_not_div3, fun _ => ⟨hx_odd, hx_gt1⟩⟩
      apply CollatzOddSteps.odd hx_odd hx_gt1
      rw [hx_eq]
      by_cases hk : k = 0
      · simp [hk]; exact hy
      · have hk_pos : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
        exact CollatzOddSteps_mul_pow_two y m_prev k hy hk_pos

/-- Main Lemma -/
lemma exists_n_with_m_odd_steps (m : ℕ) : ∃ n : ℕ, CollatzOddSteps n m := by
  obtain ⟨n, hn, _⟩ := exists_n_with_m_odd_steps_not_div3 m
  exact ⟨n, hn⟩

/--
If `n` is odd and greater than 1, then `4n + 1` requires the same number of odd steps `m` as `n`.
This is because `4n + 1` reaches `3n + 1` (the successor of `n`) using exactly 1 odd step,
just like `n` reaches `3n + 1` using exactly 1 odd step.
-/
lemma CollatzOddSteps_4n_add_1 (n m : ℕ) (h_odd : n % 2 = 1) (h_gt1 : n > 1)
    (h : CollatzOddSteps n m) : CollatzOddSteps (4 * n + 1) m := by
  -- Since n is odd and > 1, h must use the `odd` constructor
  -- So m = m_prev + 1 for some m_prev, and CollatzOddSteps (3n+1) m_prev
  cases h with
  | base =>
    -- Contradiction: n > 1 but base case has n = 1
    contradiction
  | even h_even _ _ =>
    -- Contradiction: n is odd but even constructor requires n even
    rw [h_odd] at h_even; contradiction
  | @odd n' m_prev _ _ h_next =>
    -- h_next : CollatzOddSteps (3 * n + 1) m_prev
    -- Goal: CollatzOddSteps (4 * n + 1) (m_prev + 1)

    -- Apply odd constructor to 4n+1
    apply CollatzOddSteps.odd
    · -- 4n+1 is odd
      omega
    · -- 4n+1 > 1
      omega

    -- Goal: CollatzOddSteps (3 * (4*n+1) + 1) m_prev = CollatzOddSteps (12n+4) m_prev
    -- 12n + 4 is even
    apply CollatzOddSteps.even
    · omega
    · omega

    -- Goal: CollatzOddSteps ((12n+4)/2) m_prev = CollatzOddSteps (6n+2) m_prev
    -- 6n + 2 is even
    apply CollatzOddSteps.even
    · omega
    · omega

    -- Goal: CollatzOddSteps ((6n+2)/2) m_prev = CollatzOddSteps (3n+1) m_prev
    -- This is exactly h_next
    convert h_next using 1
    omega

/-- Sequence: iterate (4*x + 1) starting from n₀ -/
def iter_4n_plus_1 (n₀ : ℕ) : ℕ → ℕ
  | 0 => n₀
  | i + 1 => 4 * iter_4n_plus_1 n₀ i + 1

lemma iter_4n_plus_1_odd (n₀ : ℕ) (h_odd : n₀ % 2 = 1) : ∀ i, iter_4n_plus_1 n₀ i % 2 = 1 := by
  intro i
  induction i with
  | zero => exact h_odd
  | succ i ih => simp [iter_4n_plus_1]; omega

lemma iter_4n_plus_1_gt_one (n₀ : ℕ) (h_gt1 : n₀ > 1) : ∀ i, iter_4n_plus_1 n₀ i > 1 := by
  intro i
  induction i with
  | zero => exact h_gt1
  | succ i ih => simp [iter_4n_plus_1]; omega

lemma iter_4n_plus_1_growth (n₀ : ℕ) (h_pos : n₀ ≥ 1) : ∀ i, iter_4n_plus_1 n₀ i ≥ i + 1 := by
  intro i
  induction i with
  | zero => simp [iter_4n_plus_1]; omega
  | succ i ih =>
    simp [iter_4n_plus_1]
    have h1 : 4 * iter_4n_plus_1 n₀ i + 1 ≥ 4 * (i + 1) + 1 := by omega
    omega

/--
For every step count `m`, there are infinitely many `n` (forall k, exists n > k)
that reach 1 using exactly `m` odd steps.
-/
lemma infinitely_many_collatz_odd_steps (m : ℕ) : ∀ k, ∃ n, n > k ∧ CollatzOddSteps n m := by
  intro k
  cases m with
  | zero =>
    -- Case m = 0: Powers of 2.
    use 2^(k+1)
    exact ⟨by have := Nat.lt_two_pow_self (n := k + 1); omega,
      by simpa using CollatzOddSteps_mul_pow_two 1 0 (k+1) CollatzOddSteps.base (by omega)⟩

  | succ m_prev =>
    -- Case m > 0.
    obtain ⟨n₀, h_steps, _, h_cond⟩ := exists_n_with_m_odd_steps_not_div3 (m_prev + 1)
    have ⟨h_odd, h_gt1⟩ := h_cond (by omega : m_prev + 1 > 0)

    use iter_4n_plus_1 n₀ k
    constructor
    · -- Growth: iter_4n_plus_1 n₀ k > k
      have := iter_4n_plus_1_growth n₀ (by omega : n₀ ≥ 1) k
      omega
    · -- CollatzOddSteps (iter_4n_plus_1 n₀ k) (m_prev + 1)
      induction k with
      | zero => simp [iter_4n_plus_1]; exact h_steps
      | succ i ih =>
        simp [iter_4n_plus_1]
        apply CollatzOddSteps_4n_add_1
        · exact iter_4n_plus_1_odd n₀ h_odd i
        · exact iter_4n_plus_1_gt_one n₀ h_gt1 i
        · exact ih

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

/--
Lemma: The definition of a primitive simplifies to a modular arithmetic check.
If `n` is odd and has step count `m`, it is primitive if and only if `n % 8 ≠ 5` or `n = 5`.
-/
lemma is_primitive_iff_mod_8_ne_5 (n m : ℕ) (h_odd : n % 2 = 1) (h_steps : CollatzOddSteps n m)
    (h_ne5 : n ≠ 5) : IsPrimitive4x1 n m ↔ n % 8 ≠ 5 := by
  constructor
  · intro h_prim h_mod5
    unfold IsPrimitive4x1 at h_prim
    have ⟨k, hk⟩ : ∃ k, n = 8 * k + 5 := by
      use n / 8
      have := Nat.div_add_mod n 8
      omega
    let x := 2 * k + 1
    have hx_odd : x % 2 = 1 := by simp [x]
    have hk_pos : k ≥ 1 := by omega
    have hx_gt1 : x > 1 := by simp [x]; omega
    have h_map : 4 * x + 1 = n := by
      rw [hk]; simp [x]; ring
    have h_x_steps : CollatzOddSteps x m := by
      cases h_steps with
      | base => omega
      | even h_even _ _ => omega
      | odd h_odd' h_gt1' h_next =>
        have h_strip : ∀ v m', CollatzOddSteps v m' → v % 2 = 0 → v ≠ 0 →
            CollatzOddSteps (v / 2) m' := fun v m' hv heven hne => by
          cases hv with
          | base => omega
          | even _ _ h => exact h
          | odd hodd _ _ => omega
        have h1 := h_strip (3 * n + 1) _ h_next (by omega) (by omega)
        have h2 := h_strip ((3 * n + 1) / 2) _ h1 (by omega) (by omega)
        apply CollatzOddSteps.odd hx_odd hx_gt1
        have h_eq : 3 * x + 1 = (3 * n + 1) / 4 := by simp only [x]; omega
        rw [h_eq]
        rwa [Nat.div_div_eq_div_mul] at h2
    exact h_prim.2.2 x hx_odd h_map h_x_steps
  · intro h_mod8_ne_5
    refine ⟨h_steps, h_odd, fun k hk_odd h_map => absurd ?_ h_mod8_ne_5⟩
    have := (Nat.div_add_mod k 2).symm; rw [hk_odd] at this; omega

/--
For every level `m`, there are infinitely many members not divisible by 3.
-/
lemma infinitely_many_not_div3 (m : ℕ) : ∀ B, ∃ n, n > B ∧ CollatzOddSteps n m ∧ n % 3 ≠ 0 := by
  intro B
  obtain ⟨n₀, h_steps, h_mod3, _⟩ := exists_n_with_m_odd_steps_not_div3 m
  have h_pos := CollatzOddSteps_pos n₀ m h_steps
  use 2 ^ (B + 1) * n₀
  refine ⟨?_, CollatzOddSteps_mul_pow_two n₀ m (B + 1) h_steps (by omega), ?_⟩
  · -- 2^(B+1) * n₀ > B
    have h_2pow : 2 ^ (B + 1) ≥ B + 1 := by
      have := Nat.lt_two_pow_self (n := B + 1)
      omega
    nlinarith
  · -- (2^(B+1) * n₀) % 3 ≠ 0
    rw [Nat.mul_mod]
    have h2k : 2 ^ (B + 1) % 3 = 1 ∨ 2 ^ (B + 1) % 3 = 2 := by
      have := pow_two_mod_three (B + 1) (by omega)
      split_ifs at this <;> omega
    have hn0 : n₀ % 3 = 1 ∨ n₀ % 3 = 2 := by
      have := Nat.mod_lt n₀ (show (0 : ℕ) < 3 by omega)
      omega
    rcases h2k with h1 | h1 <;> rcases hn0 with h2 | h2 <;> simp [h1, h2]

/--
Every odd number `y` (not div 3) at level `m` generates a Primitive at level `m+1`.
-/
lemma odd_node_generates_primitive (y m : ℕ)
  (h_steps : CollatzOddSteps y m)
  (h_odd : y % 2 = 1)
  (h_not_div3 : y % 3 ≠ 0) :
  ∃ n, IsPrimitive4x1 n (m + 1) := by
  by_cases hy1 : y = 1
  · -- y = 1: must have m = 0; use n = 5
    subst hy1
    cases h_steps with
    | base =>
      use 5
      refine ⟨?_, by norm_num, ?_⟩
      · -- CollatzOddSteps 5 1
        apply CollatzOddSteps.odd (by norm_num) (by omega)
        apply CollatzOddSteps.even (by norm_num) (by omega)
        apply CollatzOddSteps.even (by norm_num) (by omega)
        apply CollatzOddSteps.even (by norm_num) (by omega)
        apply CollatzOddSteps.even (by norm_num) (by omega)
        exact CollatzOddSteps.base
      · -- Primitivity: only predecessor is k=1, which lacks CollatzOddSteps 1 1
        intro k _ hk_eq
        have : k = 1 := by omega
        subst this
        intro h; cases h with
        | even h_ev _ _ => omega
        | odd _ h_gt _ => omega
    | even h_ev _ _ => omega
    | odd _ h_gt _ => omega
  · -- y > 1
    have hy_gt1 : y > 1 := by have := CollatzOddSteps_pos y m h_steps; omega
    have hy_mod6 : y % 6 = 1 ∨ y % 6 = 5 := by omega
    rcases hy_mod6 with h6 | h6
    · -- y ≡ 1 (mod 6): predecessor via shift k = 2
      obtain ⟨x, hx_odd, hx_gt1, hx_eq⟩ := exists_predecessor_gt_one_mod1 y h6 hy_gt1
      use x
      have hx_steps : CollatzOddSteps x (m + 1) := by
        apply CollatzOddSteps.odd hx_odd hx_gt1; rw [hx_eq]
        exact CollatzOddSteps_mul_pow_two y m 2 h_steps (by omega)
      obtain ⟨q, hq⟩ : ∃ q, y = 6 * q + 1 := ⟨y / 6, by omega⟩
      have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h4] at hx_eq
      have hx_val : x = 8 * q + 1 := by omega
      exact (is_primitive_iff_mod_8_ne_5 x (m + 1) hx_odd hx_steps (by omega)).mpr (by omega)
    · -- y ≡ 5 (mod 6): predecessor via shift k = 1
      obtain ⟨x, hx_odd, hx_gt1, hx_eq⟩ := exists_predecessor_gt_one_mod5 y h6
      use x
      have hx_steps : CollatzOddSteps x (m + 1) := by
        apply CollatzOddSteps.odd hx_odd hx_gt1; rw [hx_eq]
        exact CollatzOddSteps_mul_pow_two y m 1 h_steps (by omega)
      obtain ⟨q, hq⟩ : ∃ q, y = 6 * q + 5 := ⟨y / 6, by omega⟩
      have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
      rw [h2] at hx_eq
      have hx_val : x = 4 * q + 3 := by omega
      exact (is_primitive_iff_mod_8_ne_5 x (m + 1) hx_odd hx_steps (by omega)).mpr (by omega)

/-- Primitives at level m+1 generated by different odd numbers at level m are distinct.
    The generation relationship is 3*p+1 = 2^k * y: p does an odd step then k halvings to reach y.
    Since 3p+1 has a unique odd part, different generators y produce different primitives p. -/
lemma primitives_from_distinct_generators_ne
    (y₁ y₂ p₁ p₂ k₁ k₂ m : ℕ)
    (hy₁_odd : y₁ % 2 = 1) (hy₂_odd : y₂ % 2 = 1)
    (hp₂_prim : IsPrimitive4x1 p₂ (m + 1))
    (hgen₁ : 3 * p₁ + 1 = 2 ^ k₁ * y₁)
    (hgen₂ : 3 * p₂ + 1 = 2 ^ k₂ * y₂)
    (hy_ne : y₁ ≠ y₂) : p₁ ≠ p₂ := by
  intro heq
  subst heq
  apply hy_ne
  have h := hgen₁.symm.trans hgen₂
  -- h : 2 ^ k₁ * y₁ = 2 ^ k₂ * y₂
  have hk : k₁ = k₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- k₁ < k₂ implies 2 ∣ y₁, contradicting oddness
      have : 2 ^ k₂ = 2 ^ k₁ * 2 ^ (k₂ - k₁) := by
        rw [← pow_add]; congr 1; omega
      rw [this, mul_assoc] at h
      have h1 := Nat.eq_of_mul_eq_mul_left (by positivity) h
      obtain ⟨c, hc⟩ : 2 ∣ y₁ := by
        rw [h1]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) y₂
      omega
    · -- k₂ < k₁ implies 2 ∣ y₂, contradicting oddness
      have : 2 ^ k₁ = 2 ^ k₂ * 2 ^ (k₁ - k₂) := by
        rw [← pow_add]; congr 1; omega
      rw [this, mul_assoc] at h
      have h1 := (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm
      obtain ⟨c, hc⟩ : 2 ∣ y₂ := by
        rw [h1]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) y₁
      omega
  subst hk
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

lemma iter_4n_plus_1_mod3 (n₀ i : ℕ) : iter_4n_plus_1 n₀ i % 3 = (n₀ + i) % 3 := by
  induction i with
  | zero => simp [iter_4n_plus_1]
  | succ i ih => simp [iter_4n_plus_1, Nat.add_mod, Nat.mul_mod, ih]; omega

/--
For every level `m`, there are infinitely many primitive numbers.
-/
lemma infinite_primitives (m : ℕ) (h2le: 2 ≤ m) : ∀ B, ∃ n, n > B ∧ IsPrimitive4x1 n m := by
  intro B
  have hm : m - 1 + 1 = m := by omega
  -- Get seed at level m-1: odd, > 1, % 3 ≠ 0
  obtain ⟨n₀, hn₀_steps, hn₀_mod3, hn₀_cond⟩ := exists_n_with_m_odd_steps_not_div3 (m - 1)
  have ⟨hn₀_odd, hn₀_gt1⟩ := hn₀_cond (by omega : m - 1 > 0)
  -- Build large odd y at level m-1
  set y := iter_4n_plus_1 n₀ (3 * (B + 1)) with hy_def
  have hy_odd : y % 2 = 1 := iter_4n_plus_1_odd n₀ hn₀_odd _
  have hy_gt1 : y > 1 := iter_4n_plus_1_gt_one n₀ hn₀_gt1 _
  have hy_mod3 : y % 3 ≠ 0 := by
    rw [hy_def, iter_4n_plus_1_mod3]
    have : (n₀ + 3 * (B + 1)) % 3 = n₀ % 3 := by omega
    rw [this]; exact hn₀_mod3
  have hy_large : y ≥ 3 * B + 4 := by
    have := iter_4n_plus_1_growth n₀ (by omega : n₀ ≥ 1) (3 * (B + 1))
    omega
  -- y has CollatzOddSteps at level m-1 (by iterating CollatzOddSteps_4n_add_1)
  have hy_steps : CollatzOddSteps y (m - 1) := by
    rw [hy_def]
    induction (3 * (B + 1)) with
    | zero => simp [iter_4n_plus_1]; exact hn₀_steps
    | succ i ih =>
      simp [iter_4n_plus_1]
      exact CollatzOddSteps_4n_add_1 _ _ (iter_4n_plus_1_odd n₀ hn₀_odd i)
        (iter_4n_plus_1_gt_one n₀ hn₀_gt1 i) ih
  -- Construct primitive at level m from y (inline from odd_node_generates_primitive)
  have hy_mod6 : y % 6 = 1 ∨ y % 6 = 5 := by omega
  rcases hy_mod6 with h6 | h6
  · -- y ≡ 1 (mod 6): primitive x with 3x+1 = 4y
    obtain ⟨x, hx_odd, hx_gt1, hx_eq⟩ := exists_predecessor_gt_one_mod1 y h6 (by omega)
    use x
    have hx_steps : CollatzOddSteps x (m - 1 + 1) := by
      apply CollatzOddSteps.odd hx_odd hx_gt1; rw [hx_eq]
      exact CollatzOddSteps_mul_pow_two y (m - 1) 2 hy_steps (by omega)
    rw [hm] at hx_steps
    obtain ⟨q, hq⟩ : ∃ q, y = 6 * q + 1 := ⟨y / 6, by omega⟩
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4] at hx_eq
    have hx_val : x = 8 * q + 1 := by omega
    constructor
    · -- x > B: from 3x+1 = 4y and y ≥ 3B+4
      omega
    · exact (is_primitive_iff_mod_8_ne_5 x m hx_odd hx_steps (by omega)).mpr (by omega)
  · -- y ≡ 5 (mod 6): primitive x with 3x+1 = 2y
    obtain ⟨x, hx_odd, hx_gt1, hx_eq⟩ := exists_predecessor_gt_one_mod5 y h6
    use x
    have hx_steps : CollatzOddSteps x (m - 1 + 1) := by
      apply CollatzOddSteps.odd hx_odd hx_gt1; rw [hx_eq]
      exact CollatzOddSteps_mul_pow_two y (m - 1) 1 hy_steps (by omega)
    rw [hm] at hx_steps
    obtain ⟨q, hq⟩ : ∃ q, y = 6 * q + 5 := ⟨y / 6, by omega⟩
    have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [h2] at hx_eq
    have hx_val : x = 4 * q + 3 := by omega
    constructor
    · -- x > B: from 3x+1 = 2y and y ≥ 3B+4
      omega
    · exact (is_primitive_iff_mod_8_ne_5 x m hx_odd hx_steps (by omega)).mpr (by omega)

/-- The odd Collatz successor of an odd number n is the odd part of 3n+1,
    i.e., (3n+1) / 2^v₂(3n+1). This exceeds n only when n ≡ 3 (mod 4). -/
lemma odd_collatz_successor_gt_iff_mod4 (n : ℕ) (h_mod4 : n % 4 = 3)
    (k : ℕ) (hk : k ≥ 1) (hk_val : (3 * n + 1) = 2 ^ k * ((3 * n + 1) / 2 ^ k))
    (hk_odd : (3 * n + 1) / 2 ^ k % 2 = 1) :
    ((3 * n + 1) / 2 ^ k > n ↔ n % 4 = 3) := by
  refine ⟨fun _ => h_mod4, fun _ => ?_⟩
  have hk_eq : k = 1 := by
    by_contra hne
    have : (4 : ℕ) ∣ (3 * n + 1) :=
      hk_val ▸ dvd_mul_of_dvd_left (by simpa using Nat.pow_dvd_pow 2 (show k ≥ 2 by omega)) _
    omega
  subst hk_eq; simp only [pow_one] at hk_val ⊢; omega

theorem collatz_conjecture : ∀ (n : ℕ), n = 0 ∨ ∃ k, collatz_iter k n = 1 :=
  sorry
