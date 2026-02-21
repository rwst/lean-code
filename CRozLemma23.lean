import C2
import CRoz
import CRozLemma22

/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

/-- Shift lemma: T^j(m + 2^j) and T^j(m) are related, which implies they have opposite parity. -/
lemma X_T_iter_shift (j m : ℕ) : X (T_iter j m) + X (T_iter j (m + 2 ^ j)) = 1 := by
  have hE : E_vec j (m + 2 ^ j) = E_vec j m := by
    apply terras_backward
    exact Nat.add_mod_right m (2 ^ j)
  have hS : num_odd_steps j (m + 2 ^ j) = num_odd_steps j m := by
    exact num_odd_steps_eq_of_E_vec_eq _ _ _ hE
  have hQ : garner_correction j (m + 2 ^ j) = garner_correction j m := by
    exact garner_correction_eq_of_E_vec_eq _ _ _ hE
  have g1 := garner_formula j m
  have g2 := garner_formula j (m + 2 ^ j)
  rw [hS, hQ] at g2
  have eq1 : 2 ^ j * T_iter j (m + 2 ^ j) = 2 ^ j * (T_iter j m + 3 ^ (num_odd_steps j m)) := by
    calc 2 ^ j * T_iter j (m + 2 ^ j)
      _ = 3 ^ num_odd_steps j m * (m + 2 ^ j) + garner_correction j m := g2
      _ = 3 ^ num_odd_steps j m * m + 3 ^ num_odd_steps j m * 2 ^ j + garner_correction j m := by ring
      _ = (3 ^ num_odd_steps j m * m + garner_correction j m) + 2 ^ j * 3 ^ num_odd_steps j m := by ring
      _ = 2 ^ j * T_iter j m + 2 ^ j * 3 ^ num_odd_steps j m := by rw [← g1]
      _ = 2 ^ j * (T_iter j m + 3 ^ (num_odd_steps j m)) := by ring
  have h2pos : 2 ^ j > 0 := by positivity
  have eq2 : T_iter j (m + 2 ^ j) = T_iter j m + 3 ^ (num_odd_steps j m) := by
    exact Nat.eq_of_mul_eq_mul_left h2pos eq1
  have hX : X (T_iter j (m + 2 ^ j)) = X (T_iter j m + 3 ^ num_odd_steps j m) := by rw [eq2]
  rw [hX]
  repeat rw [X_eq_mod]
  have h3 : 3 ^ num_odd_steps j m % 2 = 1 := by
    rw [Nat.pow_mod]
    simp
  omega

/-- Periodicity of the parity vector implies E_j(m + 2^j) = E_j(m) -/
lemma E_shift (j m : ℕ) : E j (m + 2 ^ j) = E j m := by
  apply E_eq_of_V_prefix_eq j j (m + 2 ^ j) m (by rfl)
  intro i
  have h1 : E_vec j (m + 2 ^ j) = E_vec j m := by
    apply terras_backward
    exact Nat.add_mod_right m (2 ^ j)
  have h2 : (V j (m + 2 ^ j)).get ⟨i.val, by simp⟩ = decide (E_vec j (m + 2 ^ j) i = 1) := by
    simp [V, E_vec]
  have h3 : (V j m).get ⟨i.val, by simp⟩ = decide (E_vec j m i = 1) := by
    simp [V, E_vec]
  rw [h2, h3, h1]

/-- Pairwise sum of E_{j+1} for m and m+2^j -/
lemma E_succ_pair_sum (j m : ℕ) :
    E (j + 1) m + E (j + 1) (m + 2 ^ j) = 2 * E j m + 1 / 2 := by
  rw [E_succ, E_succ, E_shift]
  have hX : X (T_iter j m) + X (T_iter j (m + 2 ^ j)) = 1 := X_T_iter_shift j m
  have hX1 : X (T_iter j m) = 0 ∨ X (T_iter j m) = 1 := by
    have : X (T_iter j m) ≤ 1 := by rw [X_eq_mod]; omega
    omega
  rcases hX1 with h1 | h1
  · have h2 : X (T_iter j (m + 2 ^ j)) = 1 := by omega
    rw [h1, h2]
    norm_num
    ring
  · have h2 : X (T_iter j (m + 2 ^ j)) = 0 := by omega
    rw [h1, h2]
    norm_num
    ring

/-- **Lemma 2.3** (Rozier–Terracol). For every positive integer `j`, the arithmetic
    mean of `{E_j(n)}_{n=1}^{2^j}` is equal to `j/4`. -/
lemma CRoz_lemma_23 (j : ℕ) (hj : 0 < j) :
    ((Finset.Icc 1 (2 ^ j)).sum (fun n => E j n)) / (2 ^ j : ℚ) = (j : ℚ) / 4 := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst hj0
      -- Base case: j = 1
      simp only [Nat.zero_add, pow_one]
      have h1 : E 1 1 = 1 / 2 := by
        simp only [E_succ, E_zero, mul_zero, zero_add]
        simp only [T_iter, X_odd (show 1 % 2 = 1 from rfl)]
        norm_num
      have h2 : E 1 2 = 0 := by
        simp only [E_succ, E_zero, mul_zero, zero_add]
        simp only [T_iter, X_even (show 2 % 2 = 0 from rfl)]
        norm_num
      have : Finset.Icc 1 2 = {1, 2} := by decide
      rw [this, Finset.sum_insert (by decide), Finset.sum_singleton, h1, h2, add_zero]
      norm_num
    · -- Inductive step
      have hih := ih (by omega)
      -- Convert Icc to Ico for splitting
      have hIcc_Ico : ∀ n, Finset.Icc 1 (2 ^ n) = Finset.Ico 1 (2 ^ n + 1) := by
        intro n; ext x; simp [Finset.mem_Icc, Finset.mem_Ico]
      rw [hIcc_Ico]
      -- Split: Ico 1 (2^(j+1)+1) = Ico 1 (2^j+1) ∪ Ico (2^j+1) (2^(j+1)+1)
      have hle1 : (1 : ℕ) ≤ 2 ^ j + 1 := by linarith [Nat.one_le_two_pow (n := j)]
      have hle2 : 2 ^ j + 1 ≤ 2 ^ (j + 1) + 1 := by
        have : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      rw [← Finset.sum_Ico_consecutive _ hle1 hle2]
      -- Shift the second sum
      have h_shift : (Finset.Ico (2 ^ j + 1) (2 ^ (j + 1) + 1)).sum (fun n => E (j + 1) n) =
          (Finset.Ico 1 (2 ^ j + 1)).sum (fun n => E (j + 1) (n + 2 ^ j)) := by
        have heq : Finset.Ico (2 ^ j + 1) (2 ^ (j + 1) + 1) =
            Finset.Ico (1 + 2 ^ j) (2 ^ j + 1 + 2 ^ j) := by
          ext x; simp [Finset.mem_Ico, pow_succ]; omega
        rw [heq, ← Finset.sum_Ico_add']
      rw [h_shift, ← Finset.sum_add_distrib]
      -- Apply pair sum lemma
      have h_pair : (Finset.Ico 1 (2 ^ j + 1)).sum (fun n => E (j + 1) n + E (j + 1) (n + 2 ^ j)) =
          (Finset.Ico 1 (2 ^ j + 1)).sum (fun n => 2 * E j n + 1 / 2) :=
        Finset.sum_congr rfl (fun n _ => E_succ_pair_sum j n)
      rw [h_pair, Finset.sum_add_distrib]
      -- First part: sum of 2 * E j n
      have h_sum1 : (Finset.Ico 1 (2 ^ j + 1)).sum (fun n => 2 * E j n) =
          2 * (Finset.Icc 1 (2 ^ j)).sum (fun n => E j n) := by
        rw [← hIcc_Ico, ← Finset.mul_sum]
      -- Second part: sum of constants
      have h_sum2 : (Finset.Ico 1 (2 ^ j + 1)).sum (fun _ => (1 / 2 : ℚ)) = (2 ^ j : ℚ) / 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hcard : (Finset.Ico 1 (2 ^ j + 1)).card = 2 ^ j := by
          rw [Nat.card_Ico]; omega
        rw [hcard]
        push_cast; ring
      rw [h_sum1, h_sum2]
      -- Use induction hypothesis
      have h_ih_sum : (Finset.Icc 1 (2 ^ j)).sum (fun n => E j n) = (j : ℚ) * 2 ^ j / 4 := by
        have h_pos : (2 ^ j : ℚ) ≠ 0 := by positivity
        field_simp at hih
        linarith
      rw [h_ih_sum]
      push_cast
      field_simp
      ring
