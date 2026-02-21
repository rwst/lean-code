import C2
import CRoz


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
  simp only [V, List.finRange_succ_last, List.map_append, List.map_map, Function.comp_def,
    Fin.castSucc, Fin.last, List.map_cons, List.map_nil, Fin.val_castAdd]
  rfl

lemma R_eq_zero_iff (q : ℕ) : R q = 0 ↔ q = 0 := by
  constructor
  · intro h
    unfold R at h
    have h2 : (2 : ℚ) ^ q > 0 := by positivity
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · rw [sub_eq_zero] at h
      by_contra hq
      have hq0 : 0 < q := Nat.pos_of_ne_zero hq
      have : (3 : ℚ) ^ q > (2 : ℚ) ^ q := by
        exact pow_lt_pow_left₀ (by norm_num : (2:ℚ) < 3) (by positivity) hq0.ne'
      linarith
    · linarith
  · rintro rfl; simp [R]

lemma L_eq_zero_iff (j q : ℕ) : L j q = 0 ↔ q = 0 := by
  constructor
  · intro h
    unfold L at h
    have h2 : (2 : ℚ) ^ j > 0 := by positivity
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · rw [sub_eq_zero] at h
      by_contra hq
      have hq0 : 0 < q := Nat.pos_of_ne_zero hq
      have : (3 : ℚ) ^ q > (2 : ℚ) ^ q := by
        exact pow_lt_pow_left₀ (by norm_num : (2:ℚ) < 3) (by positivity) hq0.ne'
      linarith
    · linarith
  · rintro rfl; simp [L]

/-- The upper bound in Theorem 2.2 is reached iff `V_j(n) = ⟨0^{j-q} 1^q⟩`,
    i.e. `n ≡ -2^{j-q} (mod 2^j)`. -/
theorem E_upper_bound_iff (j n : ℕ) (hj : 0 < j) :
    let q := num_odd_steps j n
    E j n = R q ↔
      (V j n : List Bool) = List.replicate (j - q) false ++ List.replicate q true := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst hj0
      rcases Nat.even_or_odd n with h | h
      · have hX : X n = 0 := by rw [X_eq_mod, Nat.even_iff.mp h]
        simp [num_odd_steps, V, R, T_iter, E_zero, hX, E_succ, List.finRange]
      · have hX : X n = 1 := by rw [X_eq_mod, Nat.odd_iff.mp h]
        simp [num_odd_steps, V, R, T_iter, E_zero, hX, E_succ, List.finRange]; norm_num
    · have hih := ih (by omega)
      set q := num_odd_steps j n with hq_def
      set v := X (T_iter j n) with hv_def
      have hqj : q ≤ j := hq_def ▸ num_odd_steps_le j n
      have hqp : num_odd_steps (j + 1) n = q + v := by
        simp [num_odd_steps, Finset.sum_range_succ, hq_def, hv_def]
      rw [hqp]
      rcases Nat.even_or_odd (T_iter j n) with h | h
      · -- Even case: v = 0
        have hX : X (T_iter j n) = 0 := by rw [X_eq_mod, Nat.even_iff.mp h]
        have hv0 : v = 0 := by rw [hv_def]; exact hX
        rw [hv0, add_zero]
        have hVsucc : (V (j + 1) n : List Bool) =
            List.append (V j n : List Bool) [false] := by
          have h := V_succ j n; rw [hX] at h; exact h
        -- In the even case, equality E = R forces q = 0
        -- and V = all-false forces q = 0 as well.
        -- So both sides ↔ q = 0.
        have hq0_of_E : E j n / 2 = R q → q = 0 := by
          intro hE; exact (R_eq_zero_iff q).mp (by
            have := R_nonneg q; have := (E_bounds j n (by omega)).2; nlinarith)
        have hq0_of_V : List.append (V j n : List Bool) [false] =
            List.replicate (j + 1 - q) false ++ List.replicate q true → q = 0 := by
          intro hV; by_contra hq_ne
          obtain ⟨q', hq'⟩ := Nat.exists_eq_succ_of_ne_zero hq_ne
          rw [hq', show j + 1 - (q' + 1) = j - q' from by omega,
              List.replicate_succ' (n := q'), ← List.append_assoc] at hV
          exact absurd (List.append_inj hV (by simp; omega)).2 (by decide)
        -- Both sides of the iff are equivalent to q = 0.
        have hUb : E j n ≤ R q := (E_bounds j n (by omega)).2
        have hLb : L j q ≤ E j n := (E_bounds j n (by omega)).1
        -- Helper: q = 0 implies E j n = 0
        have hEj0_of_q0 : q = 0 → E j n = 0 := by
          intro hq0; rw [hq0] at hUb hLb; simp [R] at hUb; linarith [L_nonneg j 0]
        constructor
        · -- Forward: E (j+1) n = R q → vector condition
          intro hE
          rw [E_succ, hX] at hE
          have hRq0 : R q = 0 := by
            have := R_nonneg q; nlinarith
          have hq0 : q = 0 := (R_eq_zero_iff q).mp hRq0
          have hEj0 := hEj0_of_q0 hq0
          have hVj := hih.mp (by rw [hq0]; simp [R]; linarith)
          rw [hq0] at hVj; simp at hVj
          rw [hq0]; simp only [Nat.sub_zero, List.replicate_zero, List.append_nil]
          rw [hVsucc, hVj]; simp [List.replicate_succ']
        · -- Backward: vector condition → E (j+1) n = R q
          intro hV
          rw [hVsucc] at hV
          have hq0 := hq0_of_V hV
          have hEj0 := hEj0_of_q0 hq0
          rw [hq0, E_succ, hX]; simp [R]; nlinarith
      · -- Odd case: v = 1
        have hX : X (T_iter j n) = 1 := by rw [X_eq_mod, Nat.odd_iff.mp h]
        have hv1 : v = 1 := by rw [hv_def]; exact hX
        rw [hv1]
        have hVsucc : (V (j + 1) n : List Bool) =
            List.append (V j n : List Bool) [true] := by
          have h := V_succ j n; rw [hX] at h; exact h
        have hsub : j + 1 - (q + 1) = j - q := by omega
        constructor
        · intro hE
          rw [E_succ, hX, R_succ_odd] at hE
          have hEq : E j n = R q := by linarith
          have hVj := hih.mp hEq
          rw [hVsucc, hsub, List.replicate_succ' (n := q), ← List.append_assoc]
          exact congrArg (· ++ [true]) hVj
        · intro hV
          rw [hVsucc, hsub, List.replicate_succ' (n := q), ← List.append_assoc] at hV
          have hVj : (V j n : List Bool) = List.replicate (j - q) false ++ List.replicate q true :=
            List.append_cancel_right hV
          have hEq := hih.mpr hVj
          rw [E_succ, hX, hEq]; simp [R_succ_odd]; ring

/-- The lower bound in Theorem 2.2 is reached iff `V_j(n) = ⟨1^q 0^{j-q}⟩`,
    i.e. `n ≡ (2/3)^q - 1 (mod 2^j)`. -/
theorem E_lower_bound_iff (j n : ℕ) (hj : 0 < j) :
    let q := num_odd_steps j n
    E j n = L j q ↔
      (V j n : List Bool) = List.replicate q true ++ List.replicate (j - q) false := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst hj0
      rcases Nat.even_or_odd n with h | h
      · have hX : X n = 0 := by rw [X_eq_mod, Nat.even_iff.mp h]
        simp [num_odd_steps, V, L, T_iter, E_zero, hX, E_succ, List.finRange]
      · have hX : X n = 1 := by rw [X_eq_mod, Nat.odd_iff.mp h]
        simp [num_odd_steps, V, L, T_iter, E_zero, hX, E_succ, List.finRange]; norm_num
    · have hih := ih (by omega)
      set q := num_odd_steps j n with hq_def
      set v := X (T_iter j n) with hv_def
      have hqj : q ≤ j := hq_def ▸ num_odd_steps_le j n
      have hqp : num_odd_steps (j + 1) n = q + v := by
        simp [num_odd_steps, Finset.sum_range_succ, hq_def, hv_def]
      rw [hqp]
      rcases Nat.even_or_odd (T_iter j n) with h | h
      · -- Even case: v = 0, reduces directly to IH via L_succ_even
        have hX : X (T_iter j n) = 0 := by rw [X_eq_mod, Nat.even_iff.mp h]
        have hv0 : v = 0 := by rw [hv_def]; exact hX
        rw [hv0, add_zero]
        have hVsucc : (V (j + 1) n : List Bool) =
            List.append (V j n : List Bool) [false] := by
          have h := V_succ j n; rw [hX] at h; exact h
        constructor
        · intro hE
          rw [E_succ, hX, L_succ_even] at hE
          have hEq : E j n = L j q := by linarith
          have hVj := hih.mp hEq
          rw [hVsucc, hVj]
          simp [show j + 1 - q = (j - q) + 1 from by omega, List.replicate_succ',
                List.append_assoc]
        · intro hV
          rw [hVsucc] at hV
          simp only [show j + 1 - q = (j - q) + 1 from by omega,
              List.replicate_succ' (n := j - q), ← List.append_assoc] at hV
          have hVj := List.append_cancel_right hV
          have hEq := hih.mpr hVj
          rw [E_succ, hX, L_succ_even]; linarith
      · -- Odd case: v = 1, forces q = j
        have hX : X (T_iter j n) = 1 := by rw [X_eq_mod, Nat.odd_iff.mp h]
        have hv1 : v = 1 := by rw [hv_def]; exact hX
        rw [hv1]
        have hVsucc : (V (j + 1) n : List Bool) =
            List.append (V j n : List Bool) [true] := by
          have h := V_succ j n; rw [hX] at h; exact h
        have hLb : L j q ≤ E j n := (E_bounds j n (by omega)).1
        have h2qj : (2 : ℚ) ^ q / 2 ^ j ≤ 1 :=
          (div_le_one (by positivity)).mpr (by gcongr; norm_num)
        -- Helper: vector condition forces q = j (last element argument)
        have hqj_of_V : List.append (V j n : List Bool) [true] =
            List.replicate (q + 1) true ++ List.replicate (j + 1 - (q + 1)) false → q = j := by
          intro hV
          by_contra hne
          have hlt : q < j := lt_of_le_of_ne hqj hne
          rw [show j + 1 - (q + 1) = (j - q - 1) + 1 from by omega,
              List.replicate_succ' (n := j - q - 1), ← List.append_assoc] at hV
          exact absurd (List.append_inj hV (by simp; omega)).2 (by decide)
        constructor
        · intro hE
          rw [E_succ, hX, L_succ_odd] at hE
          -- (3 * E j n + 1) / 2 = (3 * L j q + 2^q / 2^j) / 2
          -- → 3 * (E j n - L j q) = 2^q / 2^j - 1
          have hEq : E j n = L j q := by nlinarith
          have h2eq : (2 : ℚ) ^ q / 2 ^ j = 1 := by nlinarith
          have hqeqj : q = j := by
            by_contra hne
            have hlt : q < j := lt_of_le_of_ne hqj hne
            have : (2 : ℚ) ^ q < 2 ^ j := by gcongr; norm_num
            have : (2 : ℚ) ^ q / 2 ^ j < 1 := by
              rwa [div_lt_one (by positivity)]
            linarith
          have hVj := hih.mp hEq
          rw [hVsucc, hVj, hqeqj]; simp [List.replicate_succ']
        · intro hV
          rw [hVsucc] at hV
          have hqeqj := hqj_of_V hV
          rw [hqeqj] at hV
          simp only [show j + 1 - (j + 1) = 0 from by omega,
              List.replicate_zero, List.append_nil] at hV
          rw [List.replicate_succ' (n := j)] at hV
          have hVj : (V j n : List Bool) = List.replicate j true :=
            List.append_cancel_right hV
          have hEq := hih.mpr (by rw [hqeqj]; simp; exact hVj)
          rw [E_succ, hX, hEq, L_succ_odd, hqeqj]; norm_num; ring
