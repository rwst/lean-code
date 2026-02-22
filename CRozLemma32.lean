import C2
import CRoz
import CRozLemma22
import CRozLemma23

/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

-- ===== Helper lemmas for T_iter and Garner formula shifts =====

lemma T_iter_add_shift (k j n : ℕ) :
    T_iter (k + j) n = T_iter j (T_iter k n) := by
  rw [add_comm, T_iter_add]

lemma T_iter_pow_two_mul (k n : ℕ) : T_iter k (2 ^ k * n) = n := by
  induction k with
  | zero => simp [T_iter]
  | succ k ih =>
    have h_even : (2 ^ (k + 1) * n) % 2 = 0 := by
      rw [pow_succ]
      have : 2 * (2 ^ k * n) % 2 = 0 := Nat.mul_mod_right 2 _
      convert this using 1
      ring_nf
    have h_T : T (2 ^ (k + 1) * n) = 2 ^ k * n := by
      rw [T_even h_even, pow_succ]
      have : 2 * (2 ^ k * n) / 2 = 2 ^ k * n := Nat.mul_div_cancel_left _ (by omega)
      convert this using 1
      ring_nf
    have : T_iter (k + 1) (2 ^ (k + 1) * n) = T_iter k (T (2 ^ (k + 1) * n)) := by
      rw [add_comm k 1, T_iter_add_shift]
      rfl
    rw [this, h_T]
    exact ih

lemma num_odd_steps_pow_two_mul (k n : ℕ) : num_odd_steps k (2 ^ k * n) = 0 := by
  induction k generalizing n with
  | zero => simp [num_odd_steps]
  | succ k ih =>
    have h1 : 2 ^ (k + 1) * n = 2 ^ k * (2 * n) := by rw [pow_succ]; ring
    rw [h1, num_odd_steps_succ, ih (2 * n)]
    have h_T : T_iter k (2 ^ k * (2 * n)) = 2 * n := T_iter_pow_two_mul k (2 * n)
    rw [h_T, X_even (by omega)]

lemma num_odd_steps_add (k j n : ℕ) :
    num_odd_steps (k + j) n = num_odd_steps k n + num_odd_steps j (T_iter k n) := by
  induction j with
  | zero => simp [num_odd_steps]
  | succ j ih =>
    rw [← add_assoc, num_odd_steps_succ, ih, num_odd_steps_succ, T_iter_add_shift]
    ring

lemma num_odd_steps_shift (k j n : ℕ) :
    num_odd_steps (k + j) (2 ^ k * n) = num_odd_steps j n := by
  rw [num_odd_steps_add, num_odd_steps_pow_two_mul, T_iter_pow_two_mul, zero_add]

lemma garner_correction_pow_two_mul (k n : ℕ) :
    garner_correction k (2 ^ k * n) = 0 := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [garner_correction]
    have ih' : garner_correction k (2 ^ (k + 1) * n) = 0 := by
      have : 2 ^ (k + 1) * n = 2 ^ k * (2 * n) := by rw [pow_succ]; ring
      rw [this]
      exact ih (2 * n)
    rw [ih']
    have h_T : T_iter k (2 ^ (k + 1) * n) = 2 * n := by
      have : 2 ^ (k + 1) * n = 2 ^ k * (2 * n) := by rw [pow_succ]; ring
      rw [this]
      exact T_iter_pow_two_mul k (2 * n)
    rw [h_T, X_even (by omega)]
    ring

lemma garner_correction_add (k j n : ℕ) :
    garner_correction (k + j) n =
      3 ^ num_odd_steps j (T_iter k n) * garner_correction k n +
      2 ^ k * garner_correction j (T_iter k n) := by
  induction j with
  | zero => simp [garner_correction, num_odd_steps]
  | succ j ih =>
    rw [← add_assoc, garner_correction, ih]
    rw [num_odd_steps_succ]
    have ht : T_iter (k + j) n = T_iter j (T_iter k n) := T_iter_add_shift k j n
    rw [ht, garner_correction]
    have hpow : 3 ^ (num_odd_steps j (T_iter k n) + X (T_iter j (T_iter k n))) = 3 ^ X (T_iter j (T_iter k n)) * 3 ^ num_odd_steps j (T_iter k n) := by
      rw [pow_add, mul_comm]
    have hexp : 2 ^ (k + j) = 2 ^ j * 2 ^ k := by rw [pow_add, mul_comm]
    rw [hpow, hexp]
    ring

lemma garner_correction_shift (k j n : ℕ) :
    garner_correction (k + j) (2 ^ k * n) = 2 ^ k * garner_correction j n := by
  rw [garner_correction_add, T_iter_pow_two_mul, garner_correction_pow_two_mul, mul_zero, zero_add]

lemma E_shift_mul (k j n : ℕ) : E (k + j) (2 ^ k * n) = E j n := by
  unfold E
  have h1 : garner_correction (k + j) (2 ^ k * n) = 2 ^ k * garner_correction j n :=
    garner_correction_shift k j n
  rw [h1]
  have h2 : (2 ^ (k + j) : ℚ) = (2 ^ k : ℚ) * (2 ^ j : ℚ) := by rw [pow_add]
  rw [h2]
  push_cast
  have h_ne : (2 ^ k : ℚ) ≠ 0 := by positivity
  exact mul_div_mul_left _ _ h_ne

-- ===== Lemma 3.2 Proof Parts =====

lemma lemma32_case_1 (n a b j : ℕ) (hn : stopping_time n = ⊤)
    (h_S : 1 - (1 : ℚ) / (4 * n) < (3 : ℚ) ^ a / 2 ^ b ∧ (3 : ℚ) ^ a / 2 ^ b < 1)
    (h_j : num_odd_steps j n = a)
    (h_j_ge_b : j ≥ b) :
    IsParadoxical j n := by
  have hj_pos : j ≥ 1 := by
    by_contra h0; push_neg at h0
    have : j = 0 := by omega
    subst this
    have hb0 : b = 0 := by omega
    subst hb0
    have ha0 : a = 0 := by rw [← h_j]; rfl
    subst ha0
    have := h_S.2
    norm_num at this
  constructor
  · have h_not_drop : ¬ ∃ k, k ≥ 1 ∧ T_iter k n < n := by
      rw [← stopping_time_ne_top_iff n]
      exact hn ▸ by simp
    push_neg at h_not_drop
    exact h_not_drop j hj_pos
  · unfold C
    rw [h_j]
    calc (3 : ℚ) ^ a / 2 ^ j ≤ (3 : ℚ) ^ a / 2 ^ b := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          have : (2 : ℚ) ^ b ≤ (2 : ℚ) ^ j := by gcongr; norm_num
          exact this
      _ < 1 := h_S.2

-- Key arithmetic lemma: from 3^a/2^b being close to 1 from below,
-- derive the inequality needed for T_iter ≥ m
private lemma case2_arith (n a b : ℕ) (hn : n ≥ 1) (hba : b ≥ a + 1)
    (h_lower : 1 - (1 : ℚ) / (4 * n) < (3 : ℚ) ^ a / 2 ^ b) :
    (↑n + 1) * (3 : ℚ) ^ a > ↑n * (2 : ℚ) ^ b + (2 : ℚ) ^ a := by
  have hN : (n : ℚ) ≥ 1 := by exact_mod_cast hn
  have h3pos : (0 : ℚ) < (3 : ℚ) ^ a := by positivity
  have h2pos : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have h2apos : (0 : ℚ) < (2 : ℚ) ^ a := by positivity
  -- Step 1: Cross-multiply h_lower to clear fractions
  -- h_lower: 1 - 1/(4n) < 3^a/2^b, multiply both sides by 4n * 2^b
  have h1 : (4 * ↑n - 1) * (2 : ℚ) ^ b < 4 * ↑n * (3 : ℚ) ^ a := by
    have h4n_ne : (4 : ℚ) * ↑n ≠ 0 := by positivity
    have h2b_ne : (2 : ℚ) ^ b ≠ 0 := by positivity
    have hAB : (1 - 1 / (4 * ↑n)) * (2 : ℚ) ^ b < (3 : ℚ) ^ a := by
      rwa [lt_div_iff₀ h2pos] at h_lower
    calc (4 * ↑n - 1) * (2 : ℚ) ^ b
        = 4 * ↑n * ((1 - 1 / (4 * ↑n)) * (2 : ℚ) ^ b) := by field_simp
      _ < 4 * ↑n * (3 : ℚ) ^ a := by nlinarith
  -- Step 2: 4 * 3^a > 3 * 2^b (from h1 and n ≥ 1)
  have h2 : 4 * (3 : ℚ) ^ a > 3 * (2 : ℚ) ^ b := by nlinarith
  -- Step 3: 2^b ≥ 2 * 2^a (from b ≥ a + 1)
  have h3 : (2 : ℚ) ^ b ≥ 2 * (2 : ℚ) ^ a := by
    have : (2 : ℕ) ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hba
    calc (2 : ℚ) ^ b ≥ (2 : ℚ) ^ (a + 1) := by exact_mod_cast this
         _ = 2 * (2 : ℚ) ^ a := by ring
  -- Step 4: Combine everything
  nlinarith

lemma lemma32_case_2 (n a b j : ℕ) (hn : stopping_time n = ⊤)
    (h_S : 1 - (1 : ℚ) / (4 * n) < (3 : ℚ) ^ a / 2 ^ b ∧ (3 : ℚ) ^ a / 2 ^ b < 1)
    (h_j : num_odd_steps j n = a)
    (h_j_lt_b : j < b) :
    IsParadoxical b (2 ^ (b - j) * n) := by
  set k := b - j with hk_def
  have hbkj : b = k + j := by omega
  have hk_pos : k ≥ 1 := by omega
  have hn_pos : n ≥ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h_S; linarith [h_S.1, h_S.2]
    · exact h
  have ha_pos : a ≥ 1 := by
    by_contra h0; push_neg at h0; interval_cases a
    simp only [pow_zero] at h_S
    have h2b : (1 : ℚ) / 2 ^ b ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left one_pos.le (by positivity : (0:ℚ) < 2)
      exact_mod_cast Nat.pow_le_pow_right (show 1 ≤ 2 from by omega) (show 1 ≤ b from by omega)
    have h_lb : (1 : ℚ) - 1 / (4 * ↑n) ≥ 3 / 4 := by
      have : (1 : ℚ) / (4 * ↑n) ≤ 1 / 4 := by
        apply div_le_div_of_nonneg_left one_pos.le (by positivity : (0:ℚ) < 4)
        exact_mod_cast (show 4 ≤ 4 * n from by omega)
      linarith
    linarith [h_S.1]
  have hj_pos : j ≥ 1 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [num_odd_steps] at h_j; omega
    · exact hj
  have hb_ge_a1 : b ≥ a + 1 := by
    by_contra h0; push_neg at h0
    have : (1 : ℚ) ≤ (3 : ℚ) ^ a / 2 ^ b := by
      rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ b)]
      calc 1 * (2 : ℚ) ^ b = (2 : ℚ) ^ b := one_mul _
           _ ≤ (3 : ℚ) ^ b := by exact_mod_cast Nat.pow_le_pow_left (by omega : 2 ≤ 3) b
           _ ≤ (3 : ℚ) ^ a := by exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 3) (by omega : b ≤ a)
    linarith [h_S.2]
  have h_arith := case2_arith n a b hn_pos hb_ge_a1 h_S.1
  constructor
  · -- T_iter b (2^k * n) ≥ 2^k * n
    have hT_eq : T_iter b (2 ^ k * n) = T_iter j n := by
      conv_lhs => rw [hbkj]; rw [T_iter_add_shift, T_iter_pow_two_mul]
    rw [hT_eq]
    have hgf := garner_formula j n
    rw [h_j] at hgf
    have hE := (E_bounds j n hj_pos).1
    rw [h_j] at hE
    -- gc_j(n) ≥ (3^a - 2^a) in ℚ
    have hgc_Q : (garner_correction j n : ℚ) ≥ (3 : ℚ) ^ a - (2 : ℚ) ^ a := by
      unfold L E at hE
      exact (div_le_div_iff_of_pos_right (by positivity : (0:ℚ) < 2 ^ j)).mp hE
    -- Work in ℚ: cast garner_formula and combine with h_arith
    rw [ge_iff_le, ← Nat.cast_le (α := ℚ)]
    push_cast
    have hgf_Q : (2 : ℚ) ^ j * ↑(T_iter j n) = (3 : ℚ) ^ a * ↑n + ↑(garner_correction j n) := by
      exact_mod_cast hgf
    -- Goal: 2^k * n ≤ T_iter j n (in ℚ)
    suffices h : (2 ^ k * n : ℚ) ≤ (T_iter j n : ℚ) by exact_mod_cast h
    have h_eq : (T_iter j n : ℚ) = ((3 : ℚ) ^ a * ↑n + ↑(garner_correction j n)) / (2 : ℚ) ^ j := by
      field_simp; linarith [hgf_Q]
    rw [h_eq, le_div_iff₀ (show (0:ℚ) < 2 ^ j from by positivity)]
    rw [show (2 : ℚ) ^ k * ↑n * (2 : ℚ) ^ j = (2 : ℚ) ^ b * ↑n from by
      rw [hbkj]; ring]
    nlinarith [hgc_Q, h_arith]
  · -- C b (2^k * n) < 1
    unfold C; rw [hbkj, num_odd_steps_shift, h_j, ← hbkj]; exact h_S.2

-- ===== Helpers for CRoz_lemma_32 =====

/-- If T_iter j n is even for all j in [J, J+k), then 2^k divides T_iter J n
    and T_iter (J+k) n = T_iter J n / 2^k. -/
private lemma even_run_exact (J n : ℕ) :
    ∀ k, (∀ i, i < k → T_iter (J + i) n % 2 = 0) →
      2 ^ k ∣ T_iter J n ∧ T_iter (J + k) n = T_iter J n / 2 ^ k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨one_dvd _, by simp⟩
  | succ k ih =>
    intro h_even
    have ih' := ih (fun i hi => h_even i (by omega))
    obtain ⟨hdvd, heq⟩ := ih'
    have h_ek : T_iter (J + k) n % 2 = 0 := h_even k (by omega)
    constructor
    · obtain ⟨q, hq⟩ := hdvd
      rw [heq, hq, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ k)] at h_ek
      obtain ⟨r, hr⟩ := Nat.dvd_of_mod_eq_zero h_ek
      exact ⟨r, by rw [hq, hr, pow_succ]; ring⟩
    · have hsucc : T_iter (J + (k + 1)) n = T (T_iter (J + k) n) := by
        rw [show J + (k + 1) = (J + k) + 1 from by omega]
        simp [T_iter]
      rw [hsucc, T_even h_ek, heq, pow_succ, Nat.div_div_eq_div_mul]

/-- If n has infinite stopping time and n ≥ 1, then num_odd_steps is unbounded. -/
private lemma num_odd_steps_unbounded (n : ℕ) (hn : stopping_time n = ⊤) (hn1 : n ≥ 1) :
    ∀ M, ∃ j, num_odd_steps j n ≥ M := by
  by_contra h
  push_neg at h
  obtain ⟨M, hM⟩ := h
  -- num_odd_steps bounded by M-1, non-decreasing, step ≤ 1
  -- So eventually constant → eventually all even → contradiction
  -- Find J where num_odd_steps stabilizes
  -- Key: num_odd_steps can increase at most M-1 times total
  -- After M-1 increases, it's stuck. Each increase needs X = 1.
  -- Construct J by finding the last index where X = 1 (if any), + 1.
  -- Since num_odd_steps j n < M and num_odd_steps 0 n = 0,
  -- and each increase is by 1, there are < M increases total.
  -- The set {i | X(T_iter i n) = 1} has < M elements.
  -- So ∃ J, ∀ j ≥ J, X(T_iter j n) = 0.
  have h_stable : ∃ J, ∀ j ≥ J, X (T_iter j n) = 0 := by
    -- The set of indices where X = 1 is bounded in size by M
    -- because each such index increases num_odd_steps by 1
    -- Use: if X(T_iter i n) = 1 for i₁ < i₂ < ... < i_M, then
    -- num_odd_steps (i_M + 1) ≥ M, contradicting hM.
    -- So there are < M such indices. Let J = max of them + 1.
    by_contra h_no_stable
    push_neg at h_no_stable
    -- For each J, ∃ j ≥ J with X(T_iter j n) ≠ 0
    -- Build M indices where X = 1
    have : ∀ k ≤ M, ∃ j, num_odd_steps j n ≥ k := by
      intro k hk
      induction k with
      | zero => exact ⟨0, by omega⟩
      | succ k ih =>
        obtain ⟨j₀, hj₀⟩ := ih (by omega)
        -- Find j > j₀ with X(T_iter j n) ≠ 0 (i.e., = 1)
        obtain ⟨j, hj_ge, hj_ne⟩ := h_no_stable (j₀ + 1)
        have hj_gt : j ≥ j₀ + 1 := hj_ge
        have hX1 : X (T_iter j n) = 1 := by
          have := X_eq_mod (T_iter j n); omega
        have h_succ : num_odd_steps (j + 1) n = num_odd_steps j n + 1 := by
          have := num_odd_steps_succ j n; rw [hX1] at this; omega
        have h_mono : num_odd_steps j n ≥ num_odd_steps j₀ n := num_odd_steps_mono (by omega) n
        exact ⟨j + 1, by omega⟩
    obtain ⟨j, hj⟩ := this M (le_refl M)
    linarith [hM j]
  obtain ⟨J, hJ⟩ := h_stable
  have h_all_even : ∀ j, j ≥ J → T_iter j n % 2 = 0 := by
    intro j hj; have := hJ j hj; rw [X_eq_mod] at this; omega
  have h_dvd : ∀ k, 2 ^ k ∣ T_iter J n := by
    intro k
    exact (even_run_exact J n k (fun i hi => h_all_even (J + i) (by omega))).1
  have h_pos : T_iter J n ≥ 1 := by
    rcases Nat.eq_zero_or_pos J with rfl | hJ_pos
    · simp [T_iter]; exact hn1
    · have h_not_drop : ¬ ∃ k, k ≥ 1 ∧ T_iter k n < n := by
        rw [← stopping_time_ne_top_iff n]; exact hn ▸ by simp
      push_neg at h_not_drop
      linarith [h_not_drop J hJ_pos]
  -- No positive natural is divisible by all powers of 2
  have h2 := h_dvd (T_iter J n + 1)
  have h3 : 2 ^ (T_iter J n + 1) ≤ T_iter J n := Nat.le_of_dvd (by omega) h2
  have h4 : T_iter J n < 2 ^ (T_iter J n + 1) := by
    have : T_iter J n < 2 ^ (T_iter J n) := by
      induction (T_iter J n) with
      | zero => simp
      | succ m ih => calc m + 1 ≤ 2 * m + 1 := by omega
          _ < 2 * 2 ^ m := by omega
          _ = 2 ^ (m + 1) := by ring
    calc T_iter J n < 2 ^ (T_iter J n) := this
      _ ≤ 2 ^ (T_iter J n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- If n has infinite stopping time and n ≥ 1, num_odd_steps hits every natural number. -/
private lemma num_odd_steps_hits_all (n : ℕ) (hn : stopping_time n = ⊤) (hn1 : n ≥ 1) :
    ∀ a, ∃ j, num_odd_steps j n = a := by
  -- Follows from: step size ≤ 1, starts at 0, unbounded
  suffices hub : ∀ M, ∃ j, num_odd_steps j n ≥ M from by
    intro a
    induction a with
    | zero => exact ⟨0, by simp [num_odd_steps]⟩
    | succ a ih =>
      obtain ⟨j₀, hj₀⟩ := ih
      obtain ⟨j₁, hj₁⟩ := hub (a + 1)
      have hlt : j₀ < j₁ := by
        by_contra hle; push_neg at hle
        have := num_odd_steps_mono hle n; omega
      -- Find first index after j₀ where num_odd_steps ≥ a + 1
      have hex : ∃ d, num_odd_steps (j₀ + 1 + d) n ≥ a + 1 :=
        ⟨j₁ - j₀ - 1, by rwa [show j₀ + 1 + (j₁ - j₀ - 1) = j₁ from by omega]⟩
      set d := Nat.find hex
      have hd_spec : num_odd_steps (j₀ + 1 + d) n ≥ a + 1 := Nat.find_spec hex
      -- Previous index has num_odd_steps ≤ a
      have h_prev : num_odd_steps (j₀ + d) n ≤ a := by
        rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
        · rw [hd0]; simp; omega
        · have := Nat.find_min hex (show d - 1 < d from by omega)
          push_neg at this
          rw [show j₀ + 1 + (d - 1) = j₀ + d from by omega] at this
          omega
      -- Also ≥ a by monotonicity
      have h_ge : num_odd_steps (j₀ + d) n ≥ a := by
        have := num_odd_steps_mono (show j₀ ≤ j₀ + d from by omega) n; omega
      -- Step adds X which is 0 or 1, so the step from (j₀+d) to (j₀+d+1) is exactly +1
      have h_eq : num_odd_steps (j₀ + d) n = a := by omega
      have h_step : num_odd_steps (j₀ + 1 + d) n = a + 1 := by
        have hs := num_odd_steps_succ (j₀ + d) n
        have hX : X (T_iter (j₀ + d) n) ≤ 1 := by rw [X_eq_mod]; omega
        rw [show j₀ + d + 1 = j₀ + 1 + d from by omega] at hs
        omega
      exact ⟨j₀ + 1 + d, h_step⟩
  exact num_odd_steps_unbounded n hn hn1

/-- Cast helper: ℝ inequality for 3^a/2^b implies ℚ inequality. -/
private lemma real_to_rat_approx (a b n : ℕ)
    (h_lower : (1 - 1 / (4 * (n : ℝ))) < (3 : ℝ) ^ a / (2 : ℝ) ^ b)
    (h_upper : (3 : ℝ) ^ a / (2 : ℝ) ^ b < 1) :
    1 - (1 : ℚ) / (4 * n) < (3 : ℚ) ^ a / 2 ^ b ∧ (3 : ℚ) ^ a / 2 ^ b < 1 := by
  constructor
  · have : ((1 - (1 : ℚ) / (4 * ↑n) : ℚ) : ℝ) < (((3 : ℚ) ^ a / (2 : ℚ) ^ b : ℚ) : ℝ) := by
      push_cast; convert h_lower using 1
    exact_mod_cast this
  · have : (((3 : ℚ) ^ a / (2 : ℚ) ^ b : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by
      push_cast; convert h_upper using 1
    exact_mod_cast this

/-- For each a, there is at most one b with 3^a/2^b ∈ (1-1/(4n), 1) when n ≥ 1. -/
private lemma unique_b_for_a (a b₁ b₂ n : ℕ) (hn : n ≥ 1)
    (h1 : (1 - 1 / (4 * (n : ℝ))) < (3 : ℝ) ^ a / (2 : ℝ) ^ b₁)
    (h1' : (3 : ℝ) ^ a / (2 : ℝ) ^ b₁ < 1)
    (h2 : (1 - 1 / (4 * (n : ℝ))) < (3 : ℝ) ^ a / (2 : ℝ) ^ b₂)
    (h2' : (3 : ℝ) ^ a / (2 : ℝ) ^ b₂ < 1) :
    b₁ = b₂ := by
  by_contra hne
  wlog h_lt : b₁ < b₂ with H
  · exact H a b₂ b₁ n hn h2 h2' h1 h1' (Ne.symm hne) (by omega)
  -- 3^a/2^b₂ ≤ 3^a/2^(b₁+1) = (3^a/2^b₁)/2 < 1/2
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have h2b1 : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
  have h2b2 : (0 : ℝ) < (2 : ℝ) ^ b₂ := by positivity
  have hb2_ge : b₁ + 1 ≤ b₂ := by omega
  have : (3 : ℝ) ^ a / (2 : ℝ) ^ b₂ ≤ (3 : ℝ) ^ a / (2 : ℝ) ^ (b₁ + 1) := by
    apply div_le_div_of_nonneg_left (le_of_lt h3pos) (by positivity : (0:ℝ) < 2 ^ (b₁ + 1))
    exact_mod_cast Nat.pow_le_pow_right (show 1 ≤ 2 from by omega) hb2_ge
  have : (3 : ℝ) ^ a / (2 : ℝ) ^ (b₁ + 1) = ((3 : ℝ) ^ a / (2 : ℝ) ^ b₁) / 2 := by
    rw [pow_succ]; field_simp
  have h_half : (3 : ℝ) ^ a / (2 : ℝ) ^ b₂ < 1 / 2 := by linarith
  -- But lower bound: 1 - 1/(4n) ≥ 3/4 > 1/2
  have h_lb : (1 : ℝ) - 1 / (4 * ↑n) ≥ 3 / 4 := by
    have : (4 : ℝ) * ↑n ≥ 4 := by exact_mod_cast (show 4 ≤ 4 * n from by omega)
    have : 1 / (4 * (↑n : ℝ)) ≤ 1 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity) this
    linarith
  linarith

/-- **Theorem 3.2** (Rozier–Terracol). If the integer `n` has an infinite stopping time,
    then there exist infinitely many paradoxical sequences starting from integers of the form
    `2^k n` with `k` a non-negative integer. -/
lemma CRoz_lemma_32 (n : ℕ) (hn : stopping_time n = ⊤) :
    {p : ℕ × ℕ | IsParadoxical p.1 (2 ^ p.2 * n)}.Infinite := by
  -- Handle n = 0 separately
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · -- n = 0: T_iter j 0 = 0 ≥ 0 and C j 0 = 1/2^j < 1 for j ≥ 1
    have hT0 : ∀ j, T_iter j 0 = 0 := by
      intro j; induction j with
      | zero => rfl
      | succ j ih => simp [T_iter, ih, T, X_even (by omega : 0 % 2 = 0)]
    have hN0 : ∀ j, num_odd_steps j 0 = 0 := by
      intro j; induction j with
      | zero => rfl
      | succ j ih => rw [num_odd_steps_succ, ih, hT0, X_even (by omega : 0 % 2 = 0)]
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k + 1, 0))
    · intro a b h; simp only [Prod.mk.injEq] at h; omega
    · intro k
      simp only [Set.mem_setOf_eq, pow_zero, one_mul]
      refine ⟨Nat.zero_le _, ?_⟩
      show C (k + 1) 0 < 1
      unfold C; rw [hN0]; simp
      rw [inv_lt_comm₀ (by positivity : (0:ℚ) < 2 ^ (k + 1)) one_pos, inv_one]
      exact lt_of_lt_of_le (by norm_num) (le_self_pow₀ (by norm_num : (1:ℚ) ≤ 2) (by omega))
  · -- n ≥ 1
    have hn1 : n ≥ 1 := hn_pos
    have hε_pos : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by positivity
    have hε_lt : 1 / (4 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity : (0:ℝ) < 4 * n)]; exact_mod_cast (show 1 < 4 * n from by omega)
    set S := {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧
        (1 - 1 / (4 * (n : ℝ))) < (3 : ℝ) ^ p.1 / (2 : ℝ) ^ p.2 ∧
        (3 : ℝ) ^ p.1 / (2 : ℝ) ^ p.2 < 1}
    have S_inf : S.Infinite := exists_infinite_pairs_approx (1 / (4 * n)) hε_pos hε_lt
    have h_hits := num_odd_steps_hits_all n hn hn1
    let j_of : ℕ → ℕ := fun a => Nat.find (h_hits a)
    have hj_spec : ∀ a, num_odd_steps (j_of a) n = a := fun a => Nat.find_spec (h_hits a)
    -- j_of is strictly monotone (hence injective)
    have hj_inj : Function.Injective j_of := by
      intro a₁ a₂ h
      have h1 := hj_spec a₁; have h2 := hj_spec a₂
      rw [h] at h1; linarith
    -- Map each (a,b) ∈ S to a paradoxical pair
    let f : ℕ × ℕ → ℕ × ℕ := fun ⟨a, b⟩ =>
      if j_of a < b then (b, b - j_of a) else (j_of a, 0)
    -- f maps S into the paradoxical set
    have hf_mem : ∀ p ∈ S, f p ∈ {p : ℕ × ℕ | IsParadoxical p.1 (2 ^ p.2 * n)} := by
      intro ⟨a, b⟩ ⟨ha_pos, hb_pos, h_lo, h_hi⟩
      dsimp only at ha_pos hb_pos h_lo h_hi
      have h_Q := real_to_rat_approx a b n h_lo h_hi
      simp only [Set.mem_setOf_eq, f]
      split
      · exact lemma32_case_2 n a b (j_of a) hn h_Q (hj_spec a) ‹_›
      · push_neg at *
        have h_para := lemma32_case_1 n a b (j_of a) hn h_Q (hj_spec a) ‹_›
        simp only [pow_zero, one_mul]; exact h_para
    -- f is injective on S
    have hf_inj : Set.InjOn f S := by
      intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 hfeq
      simp only [f] at hfeq
      obtain ⟨h1a, h1b, h1lo, h1hi⟩ := h1
      obtain ⟨h2a, h2b, h2lo, h2hi⟩ := h2
      split at hfeq <;> split at hfeq
      · -- Both case 2
        simp only [Prod.mk.injEq] at hfeq
        obtain ⟨hb_eq, hk_eq⟩ := hfeq
        subst hb_eq
        have : j_of a₁ = j_of a₂ := by omega
        exact Prod.ext (hj_inj this) rfl
      · -- Case 2 vs case 1: b₁ - j₁ > 0 vs 0
        simp only [Prod.mk.injEq] at hfeq; omega
      · -- Case 1 vs case 2
        simp only [Prod.mk.injEq] at hfeq; omega
      · -- Both case 1
        simp only [Prod.mk.injEq] at hfeq
        have ha_eq : a₁ = a₂ := hj_inj hfeq.1
        subst ha_eq
        have := unique_b_for_a a₁ b₁ b₂ n hn1 h1lo h1hi h2lo h2hi
        exact Prod.ext rfl this
    -- Conclude: image of infinite set under injective map is infinite, subset of target
    apply (S_inf.image hf_inj).mono
    intro p hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hf_mem q hq
