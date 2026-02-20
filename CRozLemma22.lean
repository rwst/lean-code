import C2
import CRoz
import POListBool


/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

/-- The lower bound sequence: `L_j(q) = (3^q - 2^q) / 2^j`. -/
def L (j q : ℕ) : ℚ := ((3 : ℚ) ^ q - 2 ^ q) / 2 ^ j

/-- The upper bound: `R(q) = (3^q - 2^q) / 2^q`. -/
def R (q : ℕ) : ℚ := ((3 : ℚ) ^ q - 2 ^ q) / 2 ^ q

lemma num_odd_steps_le (j n : ℕ) : num_odd_steps j n ≤ j := by
  unfold num_odd_steps
  have h (i : ℕ) : X (T_iter i n) ≤ 1 := by rw [X_eq_mod]; omega
  refine (Finset.sum_le_card_nsmul (Finset.range j) (fun i => X (T_iter i n)) 1 (fun i _ => h i)).trans_eq (by simp)

lemma L_nonneg (j q : ℕ) : L j q ≥ 0 := by
  unfold L
  apply div_nonneg
  · rw [sub_nonneg]
    gcongr; norm_num
  · positivity

lemma R_nonneg (q : ℕ) : R q ≥ 0 := by
  unfold R
  apply div_nonneg
  · rw [sub_nonneg]
    gcongr; norm_num
  · positivity

lemma L_succ_even (j q : ℕ) : L (j + 1) q = L j q / 2 := by
  unfold L; rw [pow_succ]; ring

lemma L_succ_odd (j q : ℕ) : L (j + 1) (q + 1) = (3 * L j q + (2 : ℚ) ^ q / 2 ^ j) / 2 := by
  unfold L; rw [pow_succ, pow_succ, pow_succ]
  field_simp; ring

lemma R_succ_even (q : ℕ) : R q / 2 ≤ R q := by
  have : R q ≥ 0 := R_nonneg q
  linarith

lemma R_succ_odd (q : ℕ) : R (q + 1) = (3 * R q + 1) / 2 := by
  unfold R; rw [pow_succ, pow_succ]
  field_simp; ring

/-- **Theorem 2.2** (Rozier–Terracol), inequality (3).
    For every positive integers `j` and `n`, writing `q = num_odd_steps j n`,
    we have `(3^q - 2^q) / 2^j ≤ E_j(n) ≤ (3^q - 2^q) / 2^q`. -/
theorem E_bounds (j n : ℕ) (hj : 0 < j) :
    let q := num_odd_steps j n
    L j q ≤ E j n ∧ E j n ≤ R q := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst hj0
      rcases Nat.even_or_odd n with h | h
      · have hX : X n = 0 := by rw [X_eq_mod, Nat.even_iff.mp h]
        simp [num_odd_steps, L, R, T_iter, E_zero, hX, E_succ]
      · have hX : X n = 1 := by rw [X_eq_mod, Nat.odd_iff.mp h]
        simp [num_odd_steps, L, R, T_iter, E_zero, hX, E_succ]; norm_num
    · have hih := ih (by omega)
      set q := num_odd_steps j n with hq_def
      set v := X (T_iter j n) with hv_def
      have hqp : num_odd_steps (j + 1) n = q + v := by
        simp [num_odd_steps, Finset.sum_range_succ, hq_def, hv_def]
      rw [hqp]
      constructor
      · rcases Nat.even_or_odd (T_iter j n) with h | h
        · have hX : X (T_iter j n) = 0 := by rw [X_eq_mod, Nat.even_iff.mp h]
          have hv0 : v = 0 := by rw [hv_def]; exact hX
          rw [hv0, add_zero, L_succ_even, E_succ, hX]
          have hE := hih.1; field_simp at *; nlinarith
        · have hX : X (T_iter j n) = 1 := by rw [X_eq_mod, Nat.odd_iff.mp h]
          have hv1 : v = 1 := by rw [hv_def]; exact hX
          have hE := hih.1
          have h2qj : (2 : ℚ) ^ q ≤ 2 ^ j := by
            gcongr; norm_num; rw [hq_def]; exact num_odd_steps_le j n
          have hqj_ratio : (2 : ℚ) ^ q / 2 ^ j ≤ 1 :=
            (div_le_one (by positivity)).mpr h2qj
          rw [hv1]
          calc L (j + 1) (q + 1) = (3 * L j q + (2 : ℚ) ^ q / 2 ^ j) / 2 := by
                rw [L_succ_odd]
              _ ≤ (3 * E j n + 1) / 2 := by
                gcongr
              _ = E (j + 1) n := by rw [E_succ, hX]; ring
      · rcases Nat.even_or_odd (T_iter j n) with h | h
        · have hX : X (T_iter j n) = 0 := by rw [X_eq_mod, Nat.even_iff.mp h]
          have hv0 : v = 0 := by rw [hv_def]; exact hX
          rw [hv0, add_zero, E_succ, hX]
          have hE := hih.2; have hR := R_nonneg q
          field_simp at *; nlinarith
        · have hX : X (T_iter j n) = 1 := by rw [X_eq_mod, Nat.odd_iff.mp h]
          have hv1 : v = 1 := by rw [hv_def]; exact hX
          have hE := hih.2
          rw [hv1]
          calc E (j + 1) n = (3 * E j n + 1) / 2 := by rw [E_succ, hX]; ring
            _ ≤ (3 * R q + 1) / 2 := by gcongr
            _ = R (q + 1) := by rw [R_succ_odd]

lemma V_succ (j n : ℕ) : (V (j + 1) n : List Bool) = List.append (V j n : List Bool) [decide (X (T_iter j n) = 1)] := by
  sorry

lemma R_eq_zero_iff (q : ℕ) : R q = 0 ↔ q = 0 := by
  sorry

lemma L_eq_zero_iff (j q : ℕ) : L j q = 0 ↔ q = 0 := by
  sorry

/-- The upper bound in Theorem 2.2 is reached iff `V_j(n) = ⟨0^{j-q} 1^q⟩`,
    i.e. `n ≡ -2^{j-q} (mod 2^j)`. -/
theorem E_upper_bound_iff (j n : ℕ) (hj : 0 < j) :
    let q := num_odd_steps j n
    E j n = R q ↔
      (V j n : List Bool) = List.replicate (j - q) false ++ List.replicate q true := by
  sorry

/-- The lower bound in Theorem 2.2 is reached iff `V_j(n) = ⟨1^q 0^{j-q}⟩`,
    i.e. `n ≡ (2/3)^q - 1 (mod 2^j)`. -/
theorem E_lower_bound_iff (j n : ℕ) (hj : 0 < j) :
    let q := num_odd_steps j n
    E j n = L j q ↔
      (V j n : List Bool) = List.replicate q true ++ List.replicate (j - q) false := by
  sorry
