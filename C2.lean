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
  simp [X, pow_mul, Int.one_pow]

lemma X_odd {n : ℕ} (h : n % 2 = 1) : X n = 1 := by
  obtain ⟨k, hk⟩ := Nat.odd_iff.mpr h
  subst hk
  simp [X, pow_succ, pow_mul, Int.one_pow]

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

lemma T_pos {n : ℕ} (hn : n ≥ 1) : T n ≥ 1 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega)]; omega
  · rw [T_odd (by omega)]; omega

lemma T_iter_pos {n : ℕ} (hn : n ≥ 1) (k : ℕ) : T_iter k n ≥ 1 := by
  induction k with
  | zero => exact hn
  | succ k ih => exact T_pos ih

lemma T_iter_add (a b n : ℕ) : T_iter (a + b) n = T_iter a (T_iter b n) := by
  induction a with
  | zero => simp only [Nat.zero_add, T_iter]
  | succ a ih =>
    simp only [Nat.succ_add, T_iter, ih]

lemma collatz_step_even' {n : ℕ} (h : n % 2 = 0) : collatz_step n = n / 2 := by
  simp [collatz_step, h]

lemma collatz_step_odd' {n : ℕ} (h : n % 2 = 1) : collatz_step n = 3 * n + 1 := by
  simp [collatz_step]; omega

/-- One T step equals one or two collatz_steps. -/
lemma T_step_collatz (n : ℕ) :
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

lemma stopping_time_ne_top_iff (n : ℕ) :
    stopping_time n ≠ ⊤ ↔ ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n := by
  simp only [stopping_time]; constructor
  · intro h; split at h
    · assumption
    · exact absurd rfl h
  · intro ⟨k, hk1, hklt⟩; split
    · exact WithTop.natCast_ne_top _
    · rename_i h; exact absurd ⟨k, hk1, hklt⟩ h

lemma finite_stopping_descent
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

lemma T_expand (m : ℕ) : 2 * T m = 3 ^ X m * m + X m := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega), X_even (by omega)]; omega
  · rw [T_odd (by omega), X_odd (by omega)]; omega

/-- **Gar(k : ℕ) ner's formula** [Gar81]. After `k` steps of the Collatz map `T`,
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

lemma X_eq_beq_toNat (m : ℕ) : X m = (X m == 1).toNat := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [X_even (by omega)]; simp
  · rw [X_odd (by omega)]; simp

/-- The popcount of a `BitVec` (sum of its bits). -/
def bv_popcount (k : ℕ) (v : BitVec k) : ℕ :=
  (Finset.range k).sum (fun i => if h : i < k then (v[i]).toNat else 0)

lemma num_odd_steps_eq_bv_popcount (k n : ℕ) :
    num_odd_steps k n = bv_popcount k (X_vec k n) := by
  unfold num_odd_steps bv_popcount
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos hi, X_vec_getElem _ _ _ hi]
  exact X_eq_beq_toNat (T_iter i n)

lemma num_odd_steps_mono {j k : ℕ} (hjk : j ≤ k) (n : ℕ) :
    num_odd_steps j n ≤ num_odd_steps k n := by
  unfold num_odd_steps
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hjk)

lemma num_odd_steps_succ (k n : ℕ) :
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
      3 ^ bv_popcount k (X_vec k n) * n + garner_correction k n := by
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

lemma num_odd_steps_eq_Iic_sum (k n : ℕ) (j : Fin k) :
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

lemma T_iter_succ_right (i n : ℕ) : T_iter (i + 1) n = T_iter i (T n) := by
  rw [T_iter_add i 1 n]; rfl

lemma E_vec_head (k n : ℕ) :
    E_vec (k + 1) n ⟨0, Nat.zero_lt_succ k⟩ = X n := by
  simp [E_vec_apply, T_iter]

lemma E_vec_tail (k n : ℕ) (i : Fin k) :
    E_vec (k + 1) n ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = E_vec k (T n) i := by
  simp only [E_vec_apply, T_iter_succ_right]

lemma X_congr {m n : ℕ} (h : m % 2 = n % 2) : X m = X n := by
  rw [X_eq_mod, X_eq_mod, h]

lemma int_dvd_sub_of_mod_eq {a b c : ℕ} (h : a % c = b % c) :
    (c : ℤ) ∣ ((a : ℤ) - (b : ℤ)) :=
  Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (by exact_mod_cast h))

lemma nat_mod_eq_of_int_dvd_sub {a b c : ℕ} (h : (c : ℤ) ∣ ((a : ℤ) - (b : ℤ))) :
    a % c = b % c := by
  exact_mod_cast Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp h)

lemma parity_of_mod_pow_succ {k m n : ℕ} (h : m % 2 ^ (k + 1) = n % 2 ^ (k + 1)) :
    m % 2 = n % 2 := by
  have h1 : m % 2 ^ (k + 1) % 2 = m % 2 :=
    Nat.mod_mod_of_dvd m (dvd_pow_self 2 (Nat.succ_ne_zero k))
  have h2 : n % 2 ^ (k + 1) % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (dvd_pow_self 2 (Nat.succ_ne_zero k))
  omega

lemma T_congr (k m n : ℕ) (h : m % 2 ^ (k + 1) = n % 2 ^ (k + 1)) :
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
lemma terras_backward (k : ℕ) : ∀ m n : ℕ, m % 2 ^ k = n % 2 ^ k →
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
lemma E_vec_restrict (k m n : ℕ) (h : E_vec (k + 1) m = E_vec (k + 1) n) :
    E_vec k m = E_vec k n := by
  ext ⟨i, hi⟩
  have := congr_fun h ⟨i, by omega⟩
  simpa [E_vec_apply] using this

lemma num_odd_steps_eq_of_E_vec_eq (k m n : ℕ) (h : E_vec k m = E_vec k n) :
    num_odd_steps k m = num_odd_steps k n := by
  simp only [num_odd_steps]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have := congr_fun h ⟨i, hi⟩
  simpa [E_vec_apply] using this

lemma garner_correction_eq_of_E_vec_eq (k m n : ℕ) (h : E_vec k m = E_vec k n) :
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

lemma coprime_pow_three_pow_two (s k : ℕ) : Nat.Coprime (3 ^ s) (2 ^ k) := by
  apply Nat.Coprime.pow; decide

-- Forward direction: E_vec k m = E_vec k n → m % 2^k = n % 2^k
lemma terras_forward (k m n : ℕ) (_hm : m ≥ 1) (_hn : n ≥ 1)
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
lemma T_pos' {n : ℕ} (hn : n ≥ 1) : T n ≥ 1 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega)]; omega
  · rw [T_odd (by omega)]; omega

-- Helper: T_iter preserves positivity
lemma T_iter_pos' {n : ℕ} (hn : n ≥ 1) (k : ℕ) : T_iter k n ≥ 1 := by
  induction k with
  | zero => exact hn
  | succ k ih => exact T_pos' ih

-- Helper: T_iter on values ≤ 2 stays ≤ 2
lemma T_iter_le_two {n : ℕ} (hn : n ≤ 2) (k : ℕ) : T_iter k n ≤ 2 := by
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
  by_contra h_ne
  have hn2 : n ≥ 2 := by omega
  -- From hpar: C j n < 1
  obtain ⟨_, hC_lt⟩ := hpar
  -- j witnesses the coeff_stopping_time existential
  have hcoeff_wit : ∃ m : ℕ, m ≥ 1 ∧ C m n < 1 := ⟨j, hj, hC_lt⟩
  -- By CST: stopping_time n = coeff_stopping_time n, which is finite
  have hCST_n := hCST n hn2
  -- coeff_stopping_time n is finite and ≤ j
  have hcoeff_val : coeff_stopping_time n ≤ j := by
    unfold coeff_stopping_time; rw [dif_pos hcoeff_wit]
    exact ENat.coe_le_coe.mpr (Nat.find_le ⟨hj, hC_lt⟩)
  -- stopping_time n ≤ j (via CST equality)
  have hstop_le_j : stopping_time n ≤ j := hCST_n ▸ hcoeff_val
  -- stopping_time n is finite, so the existential holds
  have hstop_exists : ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n := by
    by_contra h_neg
    have htop : stopping_time n = ⊤ := by unfold stopping_time; rw [dif_neg h_neg]
    rw [htop] at hstop_le_j; exact absurd hstop_le_j (by simp)
  -- Extract the stopping time σ via Nat.find
  unfold stopping_time at hstop_le_j
  rw [dif_pos hstop_exists] at hstop_le_j
  have hσ_le_j : Nat.find hstop_exists ≤ j := ENat.coe_le_coe.mp hstop_le_j
  obtain ⟨hσ1, hσ_lt⟩ := Nat.find_spec hstop_exists
  -- hmin at index σ gives n ≤ T_iter σ n, but hσ_lt gives T_iter σ n < n
  have hmin_σ := hmin ⟨Nat.find hstop_exists, by omega⟩
  simp at hmin_σ
  omega
