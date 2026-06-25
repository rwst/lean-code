import CC.Parity

namespace CC

open Classical

/-- The correction term: `Q(0) = 0`, `Q(k+1) = 3^{x_k} · Q(k) + 2^k · x_k`,
    where `x_k = X(T^k(n))`. -/
def decomposition_correction : ℕ → ℕ → ℕ
  | 0, _     => 0
  | k + 1, n => 3 ^ X (T_iter k n) * decomposition_correction k n + 2 ^ k * X (T_iter k n)

lemma decomposition_correction_eq_of_E_vec_eq (k m n : ℕ) (h : E_vec k m = E_vec k n) :
    decomposition_correction k m = decomposition_correction k n := by
  induction k with
  | zero => simp [decomposition_correction]
  | succ k ih =>
    simp only [decomposition_correction]
    have hk : E_vec k m = E_vec k n := E_vec_restrict k m n h
    have hXk : X (T_iter k m) = X (T_iter k n) := by
      have := congr_fun h ⟨k, lt_add_one k⟩
      simpa [E_vec_apply] using this
    rw [hXk, ih hk]

/-- After `k` steps of the Collatz map `T`,
    `2^k · T^k(n) = 3^{S_k} · n + Q_k`
    where `S_k` is the number of odd iterates and `Q_k` is the accumulated correction. -/
lemma linear_decomposition (k n : ℕ) :
    2 ^ k * T_iter k n = 3 ^ num_odd_steps k n * n + decomposition_correction k n := by
  induction k with
  | zero => simp [T_iter, num_odd_steps, decomposition_correction]
  | succ k ih =>
    simp only [T_iter, num_odd_steps, decomposition_correction, Finset.sum_range_succ]
    have hexp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hexp]
    have hT := T_expand (T_iter k n)
    calc 2 * 2 ^ k * T (T_iter k n)
        = 2 ^ k * (2 * T (T_iter k n)) := by ring
      _ = 2 ^ k * (3 ^ X (T_iter k n) * T_iter k n + X (T_iter k n)) := by rw [hT]
      _ = 3 ^ X (T_iter k n) * (2 ^ k * T_iter k n) + 2 ^ k * X (T_iter k n) := by ring
      _ = 3 ^ X (T_iter k n) * (3 ^ num_odd_steps k n * n + decomposition_correction k n)
          + 2 ^ k * X (T_iter k n) := by rw [ih]
      _ = 3 ^ (num_odd_steps k n + X (T_iter k n)) * n
          + (3 ^ X (T_iter k n) * decomposition_correction k n + 2 ^ k * X (T_iter k n)) := by
        rw [pow_add]; ring

lemma num_odd_steps_mono {j k : ℕ} (hjk : j ≤ k) (n : ℕ) :
    num_odd_steps j n ≤ num_odd_steps k n := by
  unfold num_odd_steps
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hjk)

lemma num_odd_steps_succ (k n : ℕ) :
    num_odd_steps (k + 1) n = num_odd_steps k n + X (T_iter k n) := by
  simp [num_odd_steps, Finset.sum_range_succ]

/-- Closed-form expression for `decomposition_correction`:
    `Q(k) = ∑_{j<k} X(T^j n) · 2^j · 3^{S_k - S_{j+1}}`,
    where `S_m = num_odd_steps m n`. -/
def decomposition_correction_sum (k n : ℕ) : ℕ :=
  (Finset.range k).sum (fun j =>
    X (T_iter j n) * 2 ^ j * 3 ^ (num_odd_steps k n - num_odd_steps (j + 1) n))

lemma decomposition_correction_eq_sum (k n : ℕ) :
    decomposition_correction k n = decomposition_correction_sum k n := by
  induction k with
  | zero => simp [decomposition_correction, decomposition_correction_sum]
  | succ k ih =>
    simp only [decomposition_correction, decomposition_correction_sum, Finset.sum_range_succ]
    -- last term: 3^(S_{k+1} - S_{k+1}) = 3^0 = 1
    have hlast : num_odd_steps (k + 1) n - num_odd_steps (k + 1) n = 0 := Nat.sub_self _
    rw [hlast, pow_zero, mul_one, mul_comm (2 ^ k)]
    -- prefix sum: factor out 3^{x_k}
    congr 1
    rw [ih, decomposition_correction_sum, Finset.mul_sum]
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

/-- The decomposition coefficient: `C k n = 3^(num_odd_steps k n) / 2^k` as a rational number. -/
def C (k n : ℕ) : ℚ := (3 ^ num_odd_steps k n : ℚ) / (2 ^ k : ℚ)

/-- The coefficient stopping time `τ(n)` is the least `j ≥ 1` such that `C j n < 1`,
    or `⊤` if no such `j` exists. -/
noncomputable def coeff_stopping_time (n : ℕ) : ℕ∞ :=
  if h : ∃ j : ℕ, j ≥ 1 ∧ C j n < 1 then
    (Nat.find h : ℕ∞)
  else
    ⊤

/-- The correction ratio: `E j n = Q_j(n) / 2^j`. -/
def E (j n : ℕ) : ℚ := (decomposition_correction j n : ℚ) / (2 ^ j : ℚ)

lemma E_zero (n : ℕ) : E 0 n = 0 := by
  simp [E, decomposition_correction]

lemma E_succ (k n : ℕ) :
    E (k + 1) n = (3 ^ X (T_iter k n) : ℚ) / 2 * E k n +
      (X (T_iter k n) : ℚ) / 2 := by
  simp only [E, decomposition_correction]
  rw [show (2 : ℚ) ^ (k + 1) = 2 * 2 ^ k from by ring]
  have h2k : (2 ^ k : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

lemma E_step_strict_mono (x : ℕ) (a b : ℚ) (hab : a < b) :
    (3 ^ x : ℚ) / 2 * a + (x : ℚ) / 2 < (3 ^ x : ℚ) / 2 * b + (x : ℚ) / 2 := by
  have h3 : (3 ^ x : ℚ) / 2 > 0 := by positivity
  nlinarith

lemma linear_decomposition' (j n : ℕ) : T_iter j n = C j n * n + E j n := by
  rw [C, E]
  field_simp
  norm_cast
  rw [mul_comm]
  exact linear_decomposition j n

end CC
