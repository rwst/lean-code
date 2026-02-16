import C1
import C2
--import ParityVector

/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

/-- The Garner coefficient: `C k n = 3^(num_odd_steps k n) / 2^k` as a rational number. -/
def C (k n : ℕ) : ℚ := (3 ^ num_odd_steps k n : ℚ) / (2 ^ k : ℚ)

/-- The coefficient stopping time `τ(n)` is the least `j ≥ 1` such that `C j n < 1`,
    or `⊤` if no such `j` exists. -/
noncomputable def coeff_stopping_time (n : ℕ) : ℕ∞ :=
  if h : ∃ j : ℕ, j ≥ 1 ∧ C j n < 1 then
    (Nat.find h : ℕ∞)
  else
    ⊤

/-- The stopping time is at least the coefficient stopping time. -/
lemma stopping_time_ge_coeff_stopping_time (n : ℕ) :
    stopping_time n ≥ coeff_stopping_time n := by
  unfold stopping_time coeff_stopping_time
  by_cases hs : ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n
  · -- Case: stopping_time is finite (= Nat.find hs)
    rw [dif_pos hs]
    have hfind := Nat.find_spec hs
    have hk1 := hfind.1
    have hlt := hfind.2
    -- n must be >= 1, since T_iter k 0 = 0 for all k, contradicting T_iter k n < n
    have hn : n ≥ 1 := by
      by_contra h; push_neg at h; interval_cases n; simp at hlt
    set k := Nat.find hs
    -- From garner_formula: 2^k * T_iter k n = 3^S * n + Q (where Q >= 0)
    have hg := garner_formula k n
    -- So 3^S * n <= 2^k * T_iter k n < 2^k * n, giving 3^S < 2^k
    have h1 : 3 ^ num_odd_steps k n * n ≤ 2 ^ k * T_iter k n := by omega
    have h2 : 2 ^ k * T_iter k n < 2 ^ k * n :=
      Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    have h3 : 3 ^ num_odd_steps k n * n < 2 ^ k * n := by omega
    have h4 : 3 ^ num_odd_steps k n < 2 ^ k := Nat.lt_of_mul_lt_mul_right h3
    -- Therefore C k n = 3^S / 2^k < 1
    have hC : C k n < 1 := by
      unfold C; rw [div_lt_one (by positivity : (2 ^ k : ℚ) > 0)]; exact_mod_cast h4
    -- This witnesses the coeff existential, so coeff_stopping_time is finite
    have hcoeff : ∃ j : ℕ, j ≥ 1 ∧ C j n < 1 := ⟨k, hk1, hC⟩
    rw [dif_pos hcoeff]
    -- Nat.find for coeff <= k = Nat.find for stopping, via Nat.find_le
    simp only [ge_iff_le, ENat.coe_le_coe]
    exact Nat.find_le ⟨hk1, hC⟩
  · -- Case: stopping_time = top, so top >= coeff_stopping_time trivially
    rw [dif_neg hs]; exact le_top

/-- **Terras' CST conjecture.** For every `n ≥ 2`, the stopping time equals the
    coefficient stopping time: `σ(n) = τ(n)`. -/
theorem terras_CST_conjecture :
    ∀ n : ℕ, n ≥ 2 → stopping_time n = coeff_stopping_time n := by
  sorry

/-- The CST conjecture implies there are no non-trivial cycles under `T`. -/
-- Helper: T preserves positivity (reproved since T_pos is private in C2)
private lemma T_pos' {n : ℕ} (hn : n ≥ 1) : T n ≥ 1 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega)]; omega
  · rw [T_odd (by omega)]; omega

-- Helper: T_iter preserves positivity
private lemma T_iter_pos' {n : ℕ} (hn : n ≥ 1) (k : ℕ) : T_iter k n ≥ 1 := by
  induction k with
  | zero => exact hn
  | succ k ih => exact T_pos' ih

-- Helper: T_iter on values ≤ 2 stays ≤ 2
private lemma T_iter_le_two {n : ℕ} (hn : n ≤ 2) (k : ℕ) : T_iter k n ≤ 2 := by
  induction k with
  | zero => simpa [T_iter]
  | succ k ih =>
    simp only [T_iter]
    have hle : T_iter k n ≤ 2 := ih
    interval_cases (T_iter k n) <;> simp [T, X_eq_mod]

-- Helper: if T_iter k n = n and n > 4, then all cycle elements are > 4
-- Actually we just need: T_iter i n > 2 for all i when n > 4 and periodic
-- This is because if any cycle element ≤ 2, then by T_iter_le_two all elements ≤ 2, contradicting n > 4

lemma CST_implies_no_cycles
    (hCST : ∀ n : ℕ, n ≥ 2 → stopping_time n = coeff_stopping_time n)
    (n : ℕ) (k : ℕ) (hn : n > 4) (hk : k ≥ 1) : T_iter k n ≠ n := by
  intro hcycle
  -- Step 1: Find the minimum element of the cycle {T_iter 0 n, ..., T_iter (k-1) n}
  have hne : (Finset.range k).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  obtain ⟨i₀, hi₀_mem, hi₀_min⟩ :=
    Finset.exists_min_image (Finset.range k) (fun i => T_iter i n) hne
  set x := T_iter i₀ n with hx_def
  -- Step 2: x has period k: T_iter k x = x
  have hx_cycle : T_iter k x = x := by
    rw [hx_def, ← T_iter_add k i₀ n, Nat.add_comm, T_iter_add i₀ k n, hcycle]
  -- Step 3: All iterates of x are ≥ x
  -- For any m, T_iter m x = T_iter ((m + i₀) % k) n (up to periodicity)
  -- Since the cycle values are {T_iter i n | i < k}, and x is the minimum...
  -- Helper: T_iter (q * k) n = n for any q
  have hqk : ∀ q, T_iter (q * k) n = n := by
    intro q; induction q with
    | zero => simp [T_iter]
    | succ q' ih =>
      rw [show (q' + 1) * k = k + q' * k by ring,
          T_iter_add k (q' * k) n, ih, hcycle]
  -- Helper: T_iter j n only depends on j mod k
  have hmod_eq : ∀ j, T_iter j n = T_iter (j % k) n := by
    intro j
    conv_lhs => rw [← Nat.mod_add_div j k]
    rw [show j % k + k * (j / k) = j % k + (j / k) * k by ring]
    rw [T_iter_add (j % k) ((j / k) * k) n, hqk]
  have hx_min_all : ∀ m : ℕ, x ≤ T_iter m x := by
    intro m
    have h1 : T_iter m x = T_iter (m + i₀) n := by
      rw [hx_def, ← T_iter_add m i₀ n]
    have h2 : T_iter (m + i₀) n = T_iter ((m + i₀) % k) n := hmod_eq (m + i₀)
    rw [h1, h2]
    have hr : (m + i₀) % k < k := Nat.mod_lt _ (by omega)
    exact hi₀_min _ (Finset.mem_range.mpr hr)
  -- Step 4: x ≥ 1 (since n ≥ 1 and T_iter preserves positivity)
  have hx_pos : x ≥ 1 := T_iter_pos' (by omega : n ≥ 1) i₀
  -- Step 5: x ≥ 2. If x ≤ 1, then x = 1, and by T_iter_le_two all iterates ≤ 2,
  -- but n = T_iter (k - i₀) (T_iter i₀ n) would be ≤ 2, contradicting n > 4.
  -- Actually: if x ≤ 2, then T_iter_le_two gives all iterates ≤ 2.
  -- n is in the cycle, so n = T_iter (some amount) x, hence n ≤ 2, contradiction.
  have hx_ge2 : x ≥ 2 := by
    by_contra h
    push_neg at h
    -- x ≤ 1, so x = 0 or x = 1
    have hx_le1 : x ≤ 1 := by omega
    -- n is reachable from x: n = T_iter (k - i₀ if i₀ > 0, or 0 if i₀ = 0) x
    -- Actually T_iter 0 n = n, and 0 ∈ range k, so x ≤ T_iter 0 n = n
    -- But we need n ≤ 2 from x ≤ 2
    -- n = T_iter (k * 1) n. We need to express n as T_iter j x for some j.
    -- T_iter (k - i₀) x = T_iter (k - i₀) (T_iter i₀ n) = T_iter k n = n
    have hn_from_x : n = T_iter (k - i₀) x := by
      have hi₀_lt : i₀ < k := Finset.mem_range.mp hi₀_mem
      have : k - i₀ + i₀ = k := Nat.sub_add_cancel (le_of_lt hi₀_lt)
      rw [hx_def, ← T_iter_add (k - i₀) i₀ n, this, hcycle]
    have hle := T_iter_le_two (by omega : x ≤ 2) (k - i₀)
    omega
  -- Step 6: x ≥ 2, so CST applies. Prove C k x < 1 (from the cycle).
  -- From garner_formula: 2^k * x = 3^S * x + Q where Q ≥ 0
  -- Since T_iter k x = x: 2^k * x = 3^S * x + Q, so 3^S * x ≤ 2^k * x, so 3^S ≤ 2^k
  -- Strict: 3^S is odd, 2^k is even (k ≥ 1), so 3^S ≠ 2^k, hence 3^S < 2^k
  have hC_lt : C k x < 1 := by
    unfold C
    set S := num_odd_steps k x
    have hg := garner_formula k x
    rw [hx_cycle] at hg
    have h_ge : 2 ^ k * x ≥ 3 ^ S * x := le_of_add_le_left (le_of_eq hg.symm)
    have h_ge' : 2 ^ k ≥ 3 ^ S := Nat.le_of_mul_le_mul_right h_ge (by omega)
    have h3_odd : ¬ 2 ∣ 3 ^ S := by simp [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
    have h2_even : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
    have h_ne : 3 ^ S ≠ 2 ^ k := fun heq => by rw [heq] at h3_odd; exact h3_odd h2_even
    have h_lt : 3 ^ S < 2 ^ k := by omega
    rw [div_lt_one (by positivity : (2 ^ k : ℚ) > 0)]
    exact_mod_cast h_lt
  -- Step 7: coeff_stopping_time x is finite (witnessed by k)
  have hcoeff_finite : coeff_stopping_time x ≠ ⊤ := by
    unfold coeff_stopping_time
    rw [dif_pos ⟨k, hk, hC_lt⟩]
    exact WithTop.natCast_ne_top _
  -- Step 8: By CST, stopping_time x is also finite
  have hst_eq := hCST x (by omega)
  have hst_finite : stopping_time x ≠ ⊤ := by rw [hst_eq]; exact hcoeff_finite
  -- Step 9: stopping_time x being finite means ∃ m ≥ 1, T_iter m x < x
  -- But hx_min_all says all iterates ≥ x. Contradiction.
  have hno_drop : ¬ ∃ m : ℕ, m ≥ 1 ∧ T_iter m x < x := by
    push_neg
    intro m _
    exact hx_min_all m
  have : stopping_time x = ⊤ := by
    unfold stopping_time
    rw [dif_neg hno_drop]
  exact hst_finite this

/-- `Ω j n` is the sequence of consecutive `T` iterations of `n`:
    `n, T(n), T²(n), …, Tʲ(n)`, as a function `Fin (j + 1) → ℕ`. -/
def Ω (j n : ℕ) : Fin (j + 1) → ℕ := fun i => T_iter i.val n

/-- `Ω_j(n)` is paradoxical if `T^j(n) ≥ n` and `C_j(n) < 1`. -/
def IsParadoxical (j n : ℕ) : Prop := T_iter j n ≥ n ∧ C j n < 1

/-- If `C j n ≥ 1` then `T^j(n) ≥ n`. -/
lemma T_iter_ge_of_C_ge_one (j n : ℕ) (hC : C j n ≥ 1) :
    T_iter j n ≥ n := by
  -- From hC: (3^S : ℚ) / (2^j : ℚ) ≥ 1, derive 3^S ≥ 2^j as naturals
  unfold C at hC
  have h2pos : (2 ^ j : ℚ) > 0 := by positivity
  rw [ge_iff_le, le_div_iff₀ h2pos] at hC
  simp at hC
  -- hC : (2 : ℚ) ^ j ≤ (3 : ℚ) ^ num_odd_steps j n
  have h3S_ge_2j : 3 ^ num_odd_steps j n ≥ 2 ^ j := by
    exact_mod_cast hC
  -- From garner_formula: 2^j * T_iter j n = 3^S * n + garner_correction j n
  have hg := garner_formula j n
  -- So 2^j * T_iter j n ≥ 3^S * n ≥ 2^j * n
  have h1 : 2 ^ j * T_iter j n ≥ 3 ^ num_odd_steps j n * n := by omega
  have h2 : 3 ^ num_odd_steps j n * n ≥ 2 ^ j * n :=
    Nat.mul_le_mul_right n h3S_ge_2j
  have h3 : 2 ^ j * T_iter j n ≥ 2 ^ j * n := by omega
  exact Nat.le_of_mul_le_mul_left h3 (by positivity)

/-- Any Collatz sequence starting and ending at the same integer is necessarily paradoxical. -/
lemma cycle_is_paradoxical (j n : ℕ) (hn : n ≥ 1) (hj : j ≥ 1) (hcycle : T_iter j n = n) :
    IsParadoxical j n := by
  constructor
  · -- Part A: T_iter j n ≥ n
    rw [hcycle]
  · -- Part B: C j n < 1
    unfold C
    -- Let S = num_odd_steps j n
    set S := num_odd_steps j n with hS_def
    -- From garner_formula: 2^j * T_iter j n = 3^S * n + garner_correction j n
    have hg := garner_formula j n
    -- Substitute hcycle: 2^j * n = 3^S * n + garner_correction j n
    rw [hcycle] at hg
    -- So 2^j * n ≥ 3^S * n
    have h_ge : 2 ^ j * n ≥ 3 ^ S * n := le_of_add_le_left (le_of_eq hg.symm)
    -- Since n ≥ 1, we get 2^j ≥ 3^S
    have h_ge' : 2 ^ j ≥ 3 ^ S := Nat.le_of_mul_le_mul_right h_ge (by omega)
    -- Now show strict inequality: 3^S ≠ 2^j
    -- 3^S is odd, 2^j is even (j ≥ 1), so they can't be equal
    have h3_odd : ¬ 2 ∣ 3 ^ S := by
      simp [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
    have h2_even : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega : j ≠ 0)
    have h_ne : 3 ^ S ≠ 2 ^ j := by
      intro heq; rw [heq] at h3_odd; exact h3_odd h2_even
    -- Combined: 3^S < 2^j
    have h_lt : 3 ^ S < 2 ^ j := by omega
    -- Convert to rational: (3^S : ℚ) / (2^j : ℚ) < 1
    have h2pos : (2 ^ j : ℚ) > 0 := by positivity
    rw [div_lt_one h2pos]
    exact_mod_cast h_lt

/-- From the CST conjecture: a paradoxical sequence whose first term `n` is also the
    smallest element of `Ω j n` does not exist, unless `n = 1`. -/
lemma CST_no_paradoxical_at_min
    (hCST : ∀ n : ℕ, n ≥ 2 → stopping_time n = coeff_stopping_time n)
    (j n : ℕ) (hn : n ≥ 1) (hj : j ≥ 1)
    (hpar : IsParadoxical j n)
    (hmin : ∀ i : Fin (j + 1), n ≤ T_iter i.val n) :
    n = 1 := by
  sorry
