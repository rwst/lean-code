import CC.Terras
import CC.Decomposition

namespace CollatzMapBasics

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

-- Forward direction: E_vec k m = E_vec k n → m % 2^k = n % 2^k
lemma terras_forward (k m n : ℕ) (_hm : m ≥ 1) (_hn : n ≥ 1)
    (h : E_vec k m = E_vec k n) : m % 2 ^ k = n % 2 ^ k := by
  have hS := num_odd_steps_eq_of_E_vec_eq k m n h
  have hQ := decomposition_correction_eq_of_E_vec_eq k m n h
  have gm := linear_decomposition k m
  have gn := linear_decomposition k n
  rw [← hS, ← hQ] at gn
  set S := num_odd_steps k m
  set Q := decomposition_correction k m
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
