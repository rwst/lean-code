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

private lemma T_iter_add (a b n : ℕ) : T_iter (a + b) n = T_iter a (T_iter b n) := by
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
-- proven
private lemma T_iter_to_collatz_iter (k n : ℕ) :
    ∃ j, collatz_iter j n = T_iter k n := by
  sorry

/-- If collatz_iter reaches 1, then T_iter also reaches 1. -/
-- proven
private lemma collatz_iter_to_T_iter (j n : ℕ) (hn : n ≥ 1) (hj : collatz_iter j n = 1) :
    ∃ k, T_iter k n = 1 := by
  sorry

-- proven
private lemma stopping_time_ne_top_iff (n : ℕ) :
    stopping_time n ≠ ⊤ ↔ ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n := by
  sorry

-- proven
private lemma finite_stopping_descent
    (h : ∀ n ≥ 2, stopping_time n ≠ ⊤) (n : ℕ) (hn : n ≥ 1) :
    ∃ k, T_iter k n = 1 := by
  sorry

/-- The stopping time of every `n ≥ 2` is finite iff the Collatz conjecture holds. -/
-- proven
-- proven
lemma finite_stopping_time_iff_collatz :
    (∀ n ≥ 2, stopping_time n ≠ ⊤) ↔
    (∀ m, m = 0 ∨ ∃ j, collatz_iter j m = 1) := by
  sorry


/-- Theorem A (Terras). The set `Sₖ = {n : σ(n) ≤ k}` has limiting asymptotic density `F(k)`,
    i.e., `F(k) = lim_{x→∞} (1/x) · #{n ≤ x : σ(n) ≤ k}` exists.
    In addition, `F(k) → 1` as `k → ∞`, so that almost all integers have a finite
    stopping time. Terras, Riho. "On the existence of a density."
    Acta Arithmetica 35.1 (1979): 101-102. -/

theorem terras_theorem_A :
    ∃ F : ℕ → ℝ,
      (∀ k : ℕ, Filter.Tendsto
        (fun x : ℕ => ((Finset.filter
          (fun n => stopping_time n ≤ ↑k) (Finset.range x)).card : ℝ) / x)
        Filter.atTop (nhds (F k))) ∧
      Filter.Tendsto F Filter.atTop (nhds 1) := by
  sorry
