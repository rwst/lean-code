import C1

/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical


/-- `X n` is `(1 - (-1)^n) / 2`, i.e., 0 when `n` is even and 1 when `n` is odd. -/
def X (n : ℕ) : ℕ := ((1 - (-1 : ℤ)^n) / 2).toNat

lemma X_even {n : ℕ} (h : n % 2 = 0) : X n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  simp [X, pow_mul]

lemma X_odd {n : ℕ} (h : n % 2 = 1) : X n = 1 := by
  obtain ⟨k, hk⟩ := Nat.odd_iff.mpr h
  subst hk
  simp [X, pow_succ, pow_mul]

lemma X_eq_mod (n : ℕ) : X n = n % 2 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [X_even (by omega)]; omega
  · rw [X_odd (by omega)]; omega

/-- `T n` is one step of the Collatz map in the compact form `(n * 3^X(n) + X(n)) / 2`,
    where `X(n) = n % 2`. When `n` is even this gives `n / 2`; when `n` is odd, `(3n + 1) / 2`. -/
def T (n : ℕ) : ℕ := (n * 3 ^ X n + X n) / 2

lemma T_even {n : ℕ} (h : n % 2 = 0) : T n = n / 2 := by
  simp [T, X_even h]

lemma T_odd {n : ℕ} (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by
  simp [T, X_odd h]; ring_nf

/-- `T_iter k n` applies `T` to `n` a total of `k` times: `T^0 = id`, `T^(k+1) = T ∘ T^k`. -/
def T_iter : ℕ → ℕ → ℕ
  | 0, n     => n
  | k + 1, n => T (T_iter k n)

/-- The stopping time of `n` under `T` is the smallest positive `k` such that `T_iter k n < n`,
    or `⊤` if no such `k` exists. [Ter76] -/
noncomputable def stopping_time (n : ℕ) : ℕ∞ :=
  if h : ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n then
    (Nat.find h : ℕ∞)
  else
    ⊤

/-- The total stopping time of `n` under `T` is the least positive `k` such that `T_iter k n = 1`,
    or `⊤` if no such `k` exists. -/
noncomputable def total_stopping_time (n : ℕ) : ℕ∞ :=
  if h : ∃ k : ℕ, k ≥ 1 ∧ T_iter k n = 1 then
    (Nat.find h : ℕ∞)
  else
    ⊤

private lemma T_pos {n : ℕ} (hn : n ≥ 1) : T n ≥ 1 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega)]; omega
  · rw [T_odd (by omega)]; omega

private lemma T_iter_pos {n : ℕ} (hn : n ≥ 1) (k : ℕ) : T_iter k n ≥ 1 := by
  induction k with
  | zero => exact hn
  | succ k ih => exact T_pos ih

lemma T_iter_add (a b n : ℕ) : T_iter (a + b) n = T_iter a (T_iter b n) := by
  induction a with
  | zero => simp only [Nat.zero_add, T_iter]
  | succ a ih =>
    simp only [Nat.succ_add, T_iter, ih]

private lemma collatz_step_even' {n : ℕ} (h : n % 2 = 0) : collatz_step n = n / 2 := by
  simp [collatz_step, h]

private lemma collatz_step_odd' {n : ℕ} (h : n % 2 = 1) : collatz_step n = 3 * n + 1 := by
  simp [collatz_step]; omega

/-- One T step equals one or two collatz_steps. -/
private lemma T_step_collatz (n : ℕ) :
    ∃ j, j ≥ 1 ∧ collatz_iter j n = T n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨1, le_refl _, by simp only [collatz_iter, collatz_step_even' (by omega : (k+k)%2=0),
      T_even (by omega : (k+k)%2=0)]⟩
  · exact ⟨2, by omega, by simp only [collatz_iter, collatz_step_odd' (by omega : (2*k+1)%2=1),
      collatz_step_even' (by omega : (3*(2*k+1)+1)%2=0), T_odd (by omega : (2*k+1)%2=1)]⟩

/-- For any k, T_iter k n can be simulated by some number of collatz_iter steps. -/
lemma T_iter_to_collatz_iter (k n : ℕ) :
    ∃ j, collatz_iter j n = T_iter k n := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨j₀, hj₀⟩ := ih
    obtain ⟨j₁, _, hj₁⟩ := T_step_collatz (T_iter k n)
    exact ⟨j₁ + j₀, by rw [collatz_iter_add, hj₀, hj₁]; rfl⟩

/-- If collatz_iter reaches 1, then T_iter also reaches 1. -/
lemma collatz_iter_to_T_iter (j n : ℕ) (hn : n ≥ 1) (hj : collatz_iter j n = 1) :
    ∃ k, T_iter k n = 1 := by
  induction j generalizing n with
  | zero => exact ⟨0, hj⟩
  | succ j ih =>
    simp only [collatz_iter] at hj
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- even case
      have he : (m + m) % 2 = 0 := by omega
      have hdiv : (m + m) / 2 = m := by omega
      rw [collatz_step_even' he, hdiv] at hj
      obtain ⟨k', hk'⟩ := ih m (by omega) hj
      exact ⟨k' + 1, by rw [T_iter_add k' 1]; simp only [T_iter]; rw [T_even he, hdiv]; exact hk'⟩
    · -- odd case
      have hodd : (2 * m + 1) % 2 = 1 := by omega
      rw [collatz_step_odd' hodd] at hj
      obtain ⟨k', hk'⟩ := ih (3 * (2 * m + 1) + 1) (by omega) hj
      have hk'_pos : k' ≥ 1 := by
        by_contra h0; push_neg at h0; interval_cases k'; simp [T_iter] at hk'
      refine ⟨k', ?_⟩
      have hsplit : k' = (k' - 1) + 1 := by omega
      rw [hsplit, T_iter_add _ 1]; simp only [T_iter]; rw [T_odd hodd]
      rw [hsplit, T_iter_add _ 1] at hk'; simp only [T_iter] at hk'
      rwa [T_even (by omega)] at hk'

private lemma stopping_time_ne_top_iff (n : ℕ) :
    stopping_time n ≠ ⊤ ↔ ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n := by
  simp only [stopping_time]; constructor
  · intro h; split at h
    · assumption
    · exact absurd rfl h
  · intro ⟨k, hk1, hklt⟩; split
    · exact WithTop.natCast_ne_top _
    · rename_i h; exact absurd ⟨k, hk1, hklt⟩ h

private lemma finite_stopping_descent
    (h : ∀ n ≥ 2, stopping_time n ≠ ⊤) (n : ℕ) (hn : n ≥ 1) :
    ∃ k, T_iter k n = 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn1 : n = 1
    · exact ⟨0, hn1⟩
    · have hn2 : n ≥ 2 := by omega
      obtain ⟨k, _, hklt⟩ := (stopping_time_ne_top_iff n).mp (h n hn2)
      have hpos : T_iter k n ≥ 1 := T_iter_pos hn k
      obtain ⟨k', hk'⟩ := ih (T_iter k n) hklt hpos
      exact ⟨k' + k, by rw [T_iter_add, hk']⟩

/-- The stopping time of every `n ≥ 2` is finite iff the Collatz conjecture holds. -/
lemma finite_stopping_time_iff_collatz :
    (∀ n ≥ 2, stopping_time n ≠ ⊤) ↔
    (∀ m, m = 0 ∨ ∃ j, collatz_iter j m = 1) := by
  constructor
  · intro h m
    rcases eq_or_ne m 0 with rfl | hm
    · exact Or.inl rfl
    · obtain ⟨k, hk⟩ := finite_stopping_descent h m (Nat.pos_of_ne_zero hm)
      obtain ⟨j, hj⟩ := T_iter_to_collatz_iter k m
      exact Or.inr ⟨j, by rw [hj, hk]⟩
  · intro h n hn
    rw [stopping_time_ne_top_iff]
    rcases h n with rfl | ⟨j, hj⟩
    · omega
    · obtain ⟨k, hk⟩ := collatz_iter_to_T_iter j n (by omega) hj
      have : k ≥ 1 := by
        by_contra h0; push_neg at h0; interval_cases k; simp [T_iter] at hk; omega
      exact ⟨k, this, by omega⟩


/-- Theorem A (Terras). The set `Sₖ = {n : σ(n) ≤ k}` has limiting asymptotic density `F(k)`,
    i.e., `F(k) = lim_{x→∞} (1/x) · #{n ≤ x : σ(n) ≤ k}` exists.
    In addition, `F(k) → 1` as `k → ∞`, so that almost all integers have a finite
    stopping time. Proved in Terras, Riho. "On the existence of a density."
    Acta Arithmetica 35.1 (1979): 101-102. -/

theorem terras_theorem_A :
    ∃ F : ℕ → ℝ,
      (∀ k : ℕ, Filter.Tendsto
        (fun x : ℕ => ((Finset.filter
          (fun n => stopping_time n ≤ ↑k) (Finset.range x)).card : ℝ) / x)
        Filter.atTop (nhds (F k))) ∧
      Filter.Tendsto F Filter.atTop (nhds 1) := by
  sorry


/-- `X_vec k n` is the `BitVec` of length `k` whose `i`-th bit (from the LSB) is `X(T^i(n))`,
    i.e., the parity of the `i`-th iterate. -/
def X_vec (k : ℕ) (n : ℕ) : BitVec k :=
  BitVec.ofFnLE (fun i : Fin k => X (T_iter i.val n) == 1)

@[simp]
lemma X_vec_getElem (k n : ℕ) (i : ℕ) (hi : i < k) :
    (X_vec k n)[i] = (X (T_iter i n) == 1) := by
  simp [X_vec]

/-- The number of odd iterates among the first `k` steps starting from `n`. -/
def num_odd_steps (k n : ℕ) : ℕ :=
  (Finset.range k).sum (fun i => X (T_iter i n))

/-- The Garner correction term: `Q(0) = 0`, `Q(k+1) = 3^{x_k} · Q(k) + 2^k · x_k`,
    where `x_k = X(T^k(n))`. -/
def garner_correction : ℕ → ℕ → ℕ
  | 0, _     => 0
  | k + 1, n => 3 ^ X (T_iter k n) * garner_correction k n + 2 ^ k * X (T_iter k n)

private lemma T_expand (m : ℕ) : 2 * T m = 3 ^ X m * m + X m := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega), X_even (by omega)]; omega
  · rw [T_odd (by omega), X_odd (by omega)]; omega

/-- **Garner's formula** [Gar81]. After `k` steps of the Collatz map `T`,
    `2^k · T^k(n) = 3^{S_k} · n + Q_k`
    where `S_k` is the number of odd iterates and `Q_k` is the accumulated correction. -/
lemma garner_formula (k n : ℕ) :
    2 ^ k * T_iter k n = 3 ^ num_odd_steps k n * n + garner_correction k n := by
  induction k with
  | zero => simp [T_iter, num_odd_steps, garner_correction]
  | succ k ih =>
    simp only [T_iter, num_odd_steps, garner_correction, Finset.sum_range_succ]
    have hexp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hexp]
    have hT := T_expand (T_iter k n)
    calc 2 * 2 ^ k * T (T_iter k n)
        = 2 ^ k * (2 * T (T_iter k n)) := by ring
      _ = 2 ^ k * (3 ^ X (T_iter k n) * T_iter k n + X (T_iter k n)) := by rw [hT]
      _ = 3 ^ X (T_iter k n) * (2 ^ k * T_iter k n) + 2 ^ k * X (T_iter k n) := by ring
      _ = 3 ^ X (T_iter k n) * (3 ^ num_odd_steps k n * n + garner_correction k n)
          + 2 ^ k * X (T_iter k n) := by rw [ih]
      _ = 3 ^ (num_odd_steps k n + X (T_iter k n)) * n
          + (3 ^ X (T_iter k n) * garner_correction k n + 2 ^ k * X (T_iter k n)) := by
        rw [pow_add]; ring

private lemma X_eq_beq_toNat (m : ℕ) : X m = (X m == 1).toNat := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [X_even (by omega)]; simp
  · rw [X_odd (by omega)]; simp

/-- The popcount of a `BitVec` (sum of its bits). -/
def bv_popcount (v : BitVec k) : ℕ :=
  (Finset.range k).sum (fun i => if h : i < k then (v[i]).toNat else 0)

lemma num_odd_steps_eq_bv_popcount (k n : ℕ) :
    num_odd_steps k n = bv_popcount (X_vec k n) := by
  unfold num_odd_steps bv_popcount
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos hi, X_vec_getElem _ _ _ hi]
  exact X_eq_beq_toNat (T_iter i n)

private lemma num_odd_steps_mono {j k : ℕ} (hjk : j ≤ k) (n : ℕ) :
    num_odd_steps j n ≤ num_odd_steps k n := by
  unfold num_odd_steps
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hjk)

private lemma num_odd_steps_succ (k n : ℕ) :
    num_odd_steps (k + 1) n = num_odd_steps k n + X (T_iter k n) := by
  simp [num_odd_steps, Finset.sum_range_succ]

/-- Closed-form expression for `garner_correction`:
    `Q(k) = ∑_{j<k} X(T^j n) · 2^j · 3^{S_k - S_{j+1}}`,
    where `S_m = num_odd_steps m n`. -/
def garner_correction_sum (k n : ℕ) : ℕ :=
  (Finset.range k).sum (fun j =>
    X (T_iter j n) * 2 ^ j * 3 ^ (num_odd_steps k n - num_odd_steps (j + 1) n))

lemma garner_correction_eq_sum (k n : ℕ) :
    garner_correction k n = garner_correction_sum k n := by
  induction k with
  | zero => simp [garner_correction, garner_correction_sum]
  | succ k ih =>
    simp only [garner_correction, garner_correction_sum, Finset.sum_range_succ]
    -- last term: 3^(S_{k+1} - S_{k+1}) = 3^0 = 1
    have hlast : num_odd_steps (k + 1) n - num_odd_steps (k + 1) n = 0 := Nat.sub_self _
    rw [hlast, pow_zero, mul_one, mul_comm (2 ^ k)]
    -- prefix sum: factor out 3^{x_k}
    congr 1
    rw [ih, garner_correction_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hle : num_odd_steps (j + 1) n ≤ num_odd_steps k n :=
      num_odd_steps_mono (by omega) n
    have : num_odd_steps (k + 1) n - num_odd_steps (j + 1) n =
        X (T_iter k n) + (num_odd_steps k n - num_odd_steps (j + 1) n) := by
      rw [num_odd_steps_succ]; omega
    rw [this, pow_add]
    ring

/-- **Garner's formula** (BitVec form). `2^k · T^k(n) = 3^{popcount(X_vec k n)} · n + Q_k`. -/
lemma garner_formula' (k n : ℕ) :
    2 ^ k * T_iter k n =
      3 ^ bv_popcount (X_vec k n) * n + garner_correction k n := by
  rw [← num_odd_steps_eq_bv_popcount]; exact garner_formula k n

/-- **Garner's formula** (fully expanded). `2^k · T^k(n) = 3^{S_k} · n +
    ∑_{j<k} x_j · 2^j · 3^{S_k - S_{j+1}}`,
    where `S_m = num_odd_steps m n` and `x_j = X(T^j n)`. -/
lemma garner_formula_sum (k n : ℕ) :
    2 ^ k * T_iter k n =
      3 ^ num_odd_steps k n * n +
      (Finset.range k).sum (fun j =>
        X (T_iter j n) * 2 ^ j * 3 ^ (num_odd_steps k n - num_odd_steps (j + 1) n)) := by
  rw [garner_formula, garner_correction_eq_sum]; rfl

/-- `E_vec k n` is the parity vector `(X(n), X(T n), …, X(T^{k-1} n))` as a function `Fin k → ℕ`,
    where each entry is 0 or 1. -/
def E_vec (k : ℕ) (n : ℕ) : Fin k → ℕ :=
  fun i => X (T_iter i.val n)

@[simp]
lemma E_vec_apply (k n : ℕ) (i : Fin k) : E_vec k n i = X (T_iter i.val n) := rfl

lemma E_vec_le_one (k n : ℕ) (i : Fin k) : E_vec k n i ≤ 1 := by
  simp only [E_vec_apply, X_eq_mod]; omega

lemma num_odd_steps_eq_E_vec_sum (k n : ℕ) :
    num_odd_steps k n = Finset.univ.sum (E_vec k n) := by
  simp [num_odd_steps, E_vec]; exact Finset.sum_range _

/-- **Garner's formula** (E_vec form). `2^k · T^k(n) = 3^{∑ E_k} · n +
    ∑_j E_k(j) · 2^j · 3^{S_k - S_{j+1}}`. -/
lemma garner_formula_E (k n : ℕ) :
    2 ^ k * T_iter k n =
      3 ^ Finset.univ.sum (E_vec k n) * n +
      Finset.univ.sum (fun j : Fin k =>
        E_vec k n j * 2 ^ j.val *
          3 ^ (num_odd_steps k n - num_odd_steps (j.val + 1) n)) := by
  rw [← num_odd_steps_eq_E_vec_sum, garner_formula, garner_correction_eq_sum,
      garner_correction_sum]
  congr 1
  simp only [E_vec_apply]
  exact Finset.sum_range (fun j : ℕ => X (T_iter j n) * 2 ^ j *
    3 ^ (num_odd_steps k n - num_odd_steps (j + 1) n))

private lemma num_odd_steps_eq_Iic_sum (k n : ℕ) (j : Fin k) :
    num_odd_steps (j.val + 1) n = (Finset.Iic j).sum (E_vec k n) := by
  simp only [num_odd_steps, E_vec]
  apply (Finset.sum_nbij (fun i => i.val) _ _ _ _).symm
  · intro i hi; simp at hi; simp [Finset.mem_range]; omega
  · intro a _ b _ h; exact Fin.val_injective h
  · intro i hi; simp at hi
    exact ⟨⟨i, by omega⟩, by simp; omega, rfl⟩
  · intros; rfl

/-- **Garner's formula** (pure E_vec form).
    `2^k · T^k(n) = 3^{∑ E_k} · n + ∑_j E_k(j) · 2^j · 3^{∑_{i>j} E_k(i)}`. -/
lemma garner_formula_E' (k n : ℕ) :
    2 ^ k * T_iter k n =
      3 ^ Finset.univ.sum (E_vec k n) * n +
      Finset.univ.sum (fun j : Fin k =>
        E_vec k n j * 2 ^ j.val *
          3 ^ (Finset.univ.sum (E_vec k n) - (Finset.Iic j).sum (E_vec k n))) := by
  rw [garner_formula_E]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← num_odd_steps_eq_E_vec_sum, ← num_odd_steps_eq_Iic_sum]

-- ===== Helper lemmas for terras_periodicity =====

private lemma T_iter_succ_right (i n : ℕ) : T_iter (i + 1) n = T_iter i (T n) := by
  rw [T_iter_add i 1 n]; rfl

private lemma E_vec_head (k n : ℕ) :
    E_vec (k + 1) n ⟨0, Nat.zero_lt_succ k⟩ = X n := by
  simp [E_vec_apply, T_iter]

private lemma E_vec_tail (k n : ℕ) (i : Fin k) :
    E_vec (k + 1) n ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = E_vec k (T n) i := by
  simp only [E_vec_apply, T_iter_succ_right]

private lemma X_congr {m n : ℕ} (h : m % 2 = n % 2) : X m = X n := by
  rw [X_eq_mod, X_eq_mod, h]

private lemma int_dvd_sub_of_mod_eq {a b c : ℕ} (h : a % c = b % c) :
    (c : ℤ) ∣ ((a : ℤ) - (b : ℤ)) :=
  Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (by exact_mod_cast h))

private lemma nat_mod_eq_of_int_dvd_sub {a b c : ℕ} (h : (c : ℤ) ∣ ((a : ℤ) - (b : ℤ))) :
    a % c = b % c := by
  exact_mod_cast Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp h)

private lemma parity_of_mod_pow_succ {k m n : ℕ} (h : m % 2 ^ (k + 1) = n % 2 ^ (k + 1)) :
    m % 2 = n % 2 := by
  have h1 : m % 2 ^ (k + 1) % 2 = m % 2 :=
    Nat.mod_mod_of_dvd m (dvd_pow_self 2 (Nat.succ_ne_zero k))
  have h2 : n % 2 ^ (k + 1) % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (dvd_pow_self 2 (Nat.succ_ne_zero k))
  omega

private lemma T_congr (k m n : ℕ) (h : m % 2 ^ (k + 1) = n % 2 ^ (k + 1)) :
    T m % 2 ^ k = T n % 2 ^ k := by
  have hparity := parity_of_mod_pow_succ h
  have hX : X m = X n := X_congr hparity
  have hTm := T_expand m
  have hTn := T_expand n
  rw [← hX] at hTn
  -- In ℤ: 2*(Tm - Tn) = 3^(Xm)*(m - n), and 2^(k+1) | (m - n)
  have h_dvd_mn : (2 ^ (k + 1) : ℤ) ∣ ((m : ℤ) - (n : ℤ)) := int_dvd_sub_of_mod_eq h
  have h_eq : (2 : ℤ) * ((T m : ℤ) - (T n : ℤ)) =
      (3 ^ X m : ℤ) * ((m : ℤ) - (n : ℤ)) := by
    have hTm' : (2 * T m : ℤ) = (3 ^ X m : ℤ) * m + (X m : ℤ) := by exact_mod_cast hTm
    have hTn' : (2 * T n : ℤ) = (3 ^ X m : ℤ) * n + (X m : ℤ) := by exact_mod_cast hTn
    linarith
  have h_dvd_final : (2 ^ k : ℤ) ∣ ((T m : ℤ) - (T n : ℤ)) := by
    have h2 : (2 ^ (k + 1) : ℤ) ∣ ((2 : ℤ) * ((T m : ℤ) - (T n : ℤ))) := h_eq ▸ dvd_mul_of_dvd_right h_dvd_mn _
    rwa [show (2 ^ (k + 1) : ℤ) = 2 * 2 ^ k from by ring,
         mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)] at h2
  exact nat_mod_eq_of_int_dvd_sub h_dvd_final

-- Backward direction: m % 2^k = n % 2^k → E_vec k m = E_vec k n
private lemma terras_backward (k : ℕ) : ∀ m n : ℕ, m % 2 ^ k = n % 2 ^ k →
    E_vec k m = E_vec k n := by
  induction k with
  | zero => intro m n _; ext i; exact i.elim0
  | succ k ih =>
    intro m n h
    have hparity := parity_of_mod_pow_succ h
    have ih_applied := ih (T m) (T n) (T_congr k m n h)
    ext ⟨i, hi⟩
    cases i with
    | zero =>
      simp only [E_vec_apply, T_iter]
      exact X_congr hparity
    | succ i =>
      simp only [E_vec_apply, T_iter_succ_right]
      have hi' : i < k := by omega
      have := congr_fun ih_applied ⟨i, hi'⟩
      simpa [E_vec_apply] using this

-- E_vec restriction: equal on k+1 implies equal on k
private lemma E_vec_restrict (k m n : ℕ) (h : E_vec (k + 1) m = E_vec (k + 1) n) :
    E_vec k m = E_vec k n := by
  ext ⟨i, hi⟩
  have := congr_fun h ⟨i, by omega⟩
  simpa [E_vec_apply] using this

private lemma num_odd_steps_eq_of_E_vec_eq (k m n : ℕ) (h : E_vec k m = E_vec k n) :
    num_odd_steps k m = num_odd_steps k n := by
  simp only [num_odd_steps]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have := congr_fun h ⟨i, hi⟩
  simpa [E_vec_apply] using this

private lemma garner_correction_eq_of_E_vec_eq (k m n : ℕ) (h : E_vec k m = E_vec k n) :
    garner_correction k m = garner_correction k n := by
  induction k with
  | zero => simp [garner_correction]
  | succ k ih =>
    simp only [garner_correction]
    have hk : E_vec k m = E_vec k n := E_vec_restrict k m n h
    have hXk : X (T_iter k m) = X (T_iter k n) := by
      have := congr_fun h ⟨k, lt_add_one k⟩
      simpa [E_vec_apply] using this
    rw [hXk, ih hk]

private lemma coprime_pow_three_pow_two (s k : ℕ) : Nat.Coprime (3 ^ s) (2 ^ k) := by
  apply Nat.Coprime.pow; decide

-- Forward direction: E_vec k m = E_vec k n → m % 2^k = n % 2^k
private lemma terras_forward (k m n : ℕ) (_hm : m ≥ 1) (_hn : n ≥ 1)
    (h : E_vec k m = E_vec k n) : m % 2 ^ k = n % 2 ^ k := by
  have hS := num_odd_steps_eq_of_E_vec_eq k m n h
  have hQ := garner_correction_eq_of_E_vec_eq k m n h
  have gm := garner_formula k m
  have gn := garner_formula k n
  rw [← hS, ← hQ] at gn
  -- gm: 2^k * T_iter k m = 3^S * m + Q
  -- gn: 2^k * T_iter k n = 3^S * n + Q  (same S, same Q)
  set S := num_odd_steps k m
  set Q := garner_correction k m
  -- In ℤ: 3^S * (m - n) = 2^k * (T_iter k m - T_iter k n)
  have h_eq : (3 ^ S : ℤ) * ((m : ℤ) - (n : ℤ)) =
      (2 ^ k : ℤ) * ((T_iter k m : ℤ) - (T_iter k n : ℤ)) := by
    have gm' : (2 ^ k * T_iter k m : ℤ) = (3 ^ S * m + Q : ℤ) := by exact_mod_cast gm
    have gn' : (2 ^ k * T_iter k n : ℤ) = (3 ^ S * n + Q : ℤ) := by exact_mod_cast gn
    linarith
  have h_dvd : (2 ^ k : ℤ) ∣ ((3 ^ S : ℤ) * ((m : ℤ) - (n : ℤ))) :=
    h_eq ▸ dvd_mul_of_dvd_left dvd_rfl _
  have h_dvd_mn : (2 ^ k : ℤ) ∣ ((m : ℤ) - (n : ℤ)) :=
    ((coprime_pow_three_pow_two S k).isCoprime.symm).dvd_of_dvd_mul_left h_dvd
  exact nat_mod_eq_of_int_dvd_sub h_dvd_mn

/-- **Terras periodicity theorem** [Ter76]. Two positive integers have the same parity vector
    `E_k` if and only if they are congruent modulo `2^k`. -/
theorem terras_periodicity (k : ℕ) (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    E_vec k m = E_vec k n ↔ m % 2 ^ k = n % 2 ^ k :=
  ⟨terras_forward k m n hm hn, terras_backward k m n⟩

