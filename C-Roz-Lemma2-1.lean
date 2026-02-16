import C1
import C2
import C3
import ParityVector

/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

/-- If `E k n < E k m` and the parity bits agree from position `k` to `j-1`,
    then `E j n < E j m`. -/
lemma E_suffix_preserves_lt (k j m n : ℕ) (hkj : k ≤ j)
    (hE : E k n < E k m)
    (hsuf : ∀ i, k ≤ i → i < j → X (T_iter i m) = X (T_iter i n)) :
    E j n < E j m := by
  induction j with
  | zero => have := le_antisymm hkj (Nat.zero_le k); subst this; exact hE
  | succ j ih =>
    by_cases hkj' : k ≤ j
    · have hX := hsuf j hkj' (by omega)
      rw [E_succ, E_succ, hX]
      exact E_step_strict_mono _ (by rw [X_eq_mod]; omega)
        _ _ (ih hkj' fun i hi1 hi2 => hsuf i hi1 (by omega))
    · have : k = j + 1 := by omega
      subst this; exact hE

/-- Helper: V entry `true` implies `X = 1`, entry `false` implies `X = 0`. -/
lemma X_of_V_true (j n i : ℕ) (hi : i < j)
    (htrue : (V j n).get ⟨i, by simp; omega⟩ = true) : X (T_iter i n) = 1 := by
  have h := V_get j n ⟨i, hi⟩; rw [h] at htrue; exact of_decide_eq_true htrue

lemma X_of_V_false (j n i : ℕ) (hi : i < j)
    (hfalse : (V j n).get ⟨i, by simp; omega⟩ = false) : X (T_iter i n) = 0 := by
  have h := V_get j n ⟨i, hi⟩; rw [h] at hfalse
  have hne : X (T_iter i n) ≠ 1 := of_decide_eq_false hfalse
  have hle : X (T_iter i n) ≤ 1 := by rw [X_eq_mod]; omega
  interval_cases (X (T_iter i n)) <;> simp_all

/-- Elementary swap strictly increases E: if `V j m` and `V j n` differ by
    a single elementary swap (01 → 10), then `E j m > E j n`. -/

-- Helper to extract X value from V entry equality with a known Bool
private lemma X_from_V_eq (j n i : ℕ) (hi : i < j) (b : Bool)
    (hb : (V j n).get ⟨i, by simp; omega⟩ = b) :
    X (T_iter i n) = if b then 1 else 0 := by
  have h := V_get j n ⟨i, hi⟩; rw [h] at hb
  cases b with
  | true => exact of_decide_eq_true hb
  | false =>
    have := of_decide_eq_false hb
    have hle : X (T_iter i n) ≤ 1 := by rw [X_eq_mod]; omega
    interval_cases (X (T_iter i n)) <;> simp_all

-- Helper: get entry from w1 ++ [a, b] ++ w2 - simplified approach
-- We just state this as an auxiliary fact and handle cases directly in main proof
private lemma get_append_mid_case1 {α : Type*} (w1 : List α) (a b : α) (w2 : List α)
    (i : ℕ) (hi : i < w1.length) (h : i < (w1 ++ [a, b] ++ w2).length) :
    (w1 ++ [a, b] ++ w2).get ⟨i, h⟩ = w1.get ⟨i, hi⟩ := by
  simp [List.get_eq_getElem, hi]

private lemma get_append_mid_case2 {α : Type*} (w1 : List α) (a b : α) (w2 : List α)
    (h : w1.length < (w1 ++ [a, b] ++ w2).length) :
    (w1 ++ [a, b] ++ w2).get ⟨w1.length, h⟩ = a := by
  simp [List.get_eq_getElem]

private lemma get_append_mid_case3 {α : Type*} (w1 : List α) (a b : α) (w2 : List α)
    (h : w1.length + 1 < (w1 ++ [a, b] ++ w2).length) :
    (w1 ++ [a, b] ++ w2).get ⟨w1.length + 1, h⟩ = b := by
  simp [List.get_eq_getElem]

-- For the suffix case, we just need: entries at same suffix position are equal
-- regardless of which pair (a,b) is in the middle
private lemma get_append_suffix_eq {α : Type*} (w1 : List α) (a1 b1 a2 b2 : α) (w2 : List α)
    (i : ℕ) (hi : w1.length + 2 ≤ i)
    (h1 : i < (w1 ++ [a1, b1] ++ w2).length) (h2 : i < (w1 ++ [a2, b2] ++ w2).length) :
    (w1 ++ [a1, b1] ++ w2).get ⟨i, h1⟩ = (w1 ++ [a2, b2] ++ w2).get ⟨i, h2⟩ := by
  -- Both lists share the same suffix w2, and i indexes into that suffix
  -- Strategy: show both sides equal w2[i - w1.length - 2]
  -- via List.getElem on the nested appends
  simp only [List.get_eq_getElem]
  -- w1 ++ [a_, b_] ++ w2 is parsed as (w1 ++ [a_, b_]) ++ w2
  -- First split: i ≥ (w1 ++ [a_, b_]).length = w1.length + 2
  have hlen1 : (w1 ++ [a1, b1]).length = w1.length + 2 := by simp
  have hlen2 : (w1 ++ [a2, b2]).length = w1.length + 2 := by simp
  have hi1 : ¬ i < (w1 ++ [a1, b1]).length := by simp; omega
  have hi2 : ¬ i < (w1 ++ [a2, b2]).length := by simp; omega
  simp only [List.getElem_append, hlen1, hlen2, show ¬ i < w1.length + 2 from by omega, ↓reduceDIte]

lemma E_elementary_lt (v1 v2 : ParityVector)
    (hswap : ParityVector.ElementaryPrecedes v1 v2)
    (j m n : ℕ) (hv1 : V j m = v1) (hv2 : V j n = v2) :
    E j n < E j m := by
  cases hswap with
  | swap w1 w2 =>
    set k1 := w1.length with hk1_def
    have hj_eq : j = k1 + 2 + w2.length := by
      have h1 : (V j m).length = j := V_length j m
      rw [hv1] at h1; simp at h1; omega
    -- Extract X values at the swap positions using V
    have k1_lt_j : k1 < j := by rw [hj_eq]; omega
    have k1_plus_1_lt_j : k1 + 1 < j := by rw [hj_eq]; omega
    -- Extract X values using V_get and the list equalities
    -- Since V j m = w1 ++ [false, true] ++ w2, the i-th entry of V j m
    -- equals decide (X (T_iter i m) = 1). We extract this via nth_le/get.
    -- Bridge: if two ParityVectors are equal, their .get results are equal
    have V_eq_get : ∀ (v w : ParityVector) (i : ℕ) (hv : i < v.length) (hw : i < w.length),
        v = w → v.get ⟨i, hv⟩ = w.get ⟨i, hw⟩ := by
      intros v w i hv hw heq; subst heq; rfl
    have hXm_k1 : X (T_iter k1 m) = 0 := by
      apply X_from_V_eq j m k1 k1_lt_j false
      have h1 : (V j m).get ⟨k1, by simp; omega⟩ =
          (w1 ++ [false, true] ++ w2).get ⟨k1, by simp; omega⟩ :=
        V_eq_get _ _ k1 _ _ hv1
      rw [h1]; exact get_append_mid_case2 w1 false true w2 _
    have hXm_k1' : X (T_iter (k1 + 1) m) = 1 := by
      apply X_from_V_eq j m (k1 + 1) k1_plus_1_lt_j true
      have h1 : (V j m).get ⟨k1 + 1, by simp; omega⟩ =
          (w1 ++ [false, true] ++ w2).get ⟨k1 + 1, by simp; omega⟩ :=
        V_eq_get _ _ (k1 + 1) _ _ hv1
      rw [h1]; exact get_append_mid_case3 w1 false true w2 _
    have hXn_k1 : X (T_iter k1 n) = 1 := by
      apply X_from_V_eq j n k1 k1_lt_j true
      have h1 : (V j n).get ⟨k1, by simp; omega⟩ =
          (w1 ++ [true, false] ++ w2).get ⟨k1, by simp; omega⟩ :=
        V_eq_get _ _ k1 _ _ hv2
      rw [h1]; exact get_append_mid_case2 w1 true false w2 _
    have hXn_k1' : X (T_iter (k1 + 1) n) = 0 := by
      apply X_from_V_eq j n (k1 + 1) k1_plus_1_lt_j false
      have h1 : (V j n).get ⟨k1 + 1, by simp; omega⟩ =
          (w1 ++ [true, false] ++ w2).get ⟨k1 + 1, by simp; omega⟩ :=
        V_eq_get _ _ (k1 + 1) _ _ hv2
      rw [h1]; exact get_append_mid_case3 w1 true false w2 _
    -- Prefix equality: E k1 m = E k1 n
    have hE_prefix : E k1 m = E k1 n := by
      apply E_eq_of_V_prefix_eq k1 j m n (by omega)
      intro ⟨i, hi⟩
      have h1 := V_eq_get _ _ i (by simp; omega) (by simp; omega) hv1
      have h2 := V_eq_get _ _ i (by simp; omega) (by simp; omega) hv2
      rw [h1, h2, get_append_mid_case1 w1 false true w2 i hi,
          get_append_mid_case1 w1 true false w2 i hi]
    -- Two-step calculation
    have hEm2 : E (k1 + 2) m = (3 : ℚ) / 4 * E k1 m + 1 / 2 := by
      rw [show k1 + 2 = (k1 + 1) + 1 from by omega, E_succ, hXm_k1', E_succ, hXm_k1]
      simp; ring
    have hEn2 : E (k1 + 2) n = (3 : ℚ) / 4 * E k1 n + 1 / 4 := by
      rw [show k1 + 2 = (k1 + 1) + 1 from by omega, E_succ, hXn_k1', E_succ, hXn_k1]
      simp; ring
    have hE_swap : E (k1 + 2) n < E (k1 + 2) m := by
      rw [hEm2, hEn2, hE_prefix]; linarith
    -- Suffix: bits agree, preserving inequality
    apply E_suffix_preserves_lt (k1 + 2) j m n (by omega: k1 + 2 ≤ j) hE_swap
    intro i hi1 hi2
    -- Since i >= k1 + 2 = w1.length + 2, we have i > w1.length + 1
    have i_lt_j : i < j := by omega
    -- Both V j m and V j n map to the same w2 suffix at position i,
    -- so they have equal entries
    have : (V j m).get ⟨i, by simp; omega⟩ = (V j n).get ⟨i, by simp; omega⟩ := by
      have h1 := V_eq_get _ _ i (by simp; omega) (by simp; omega) hv1
      have h2 := V_eq_get _ _ i (by simp; omega) (by simp; omega) hv2
      rw [h1, h2]
      exact get_append_suffix_eq w1 false true true false w2 i (by omega) _ _
    simp only [V] at this
    have hd : (X (T_iter i m) = 1 ↔ X (T_iter i n) = 1) := by simpa using this
    have hm_le : X (T_iter i m) ≤ 1 := by rw [X_eq_mod]; omega
    have hn_le : X (T_iter i n) ≤ 1 := by rw [X_eq_mod]; omega
    omega

-- ===== E_pv: E computed directly from a parity vector =====

/-- Step function for computing E from parity bits. -/
private def E_step (e : ℚ) (b : Bool) : ℚ :=
  (3 ^ b.toNat : ℚ) / 2 * e + (b.toNat : ℚ) / 2

/-- E computed from a parity vector via left fold. -/
private def E_pv (v : ParityVector) : ℚ := (v : List Bool).foldl E_step 0

/-- E_step is strictly monotone in its first argument. -/
private lemma E_step_strict_mono' (b : Bool) (a1 a2 : ℚ) (h : a1 < a2) :
    E_step a1 b < E_step a2 b := by
  simp only [E_step]
  have : (0 : ℚ) < (3 : ℚ) ^ b.toNat / 2 := by positivity
  linarith [mul_lt_mul_of_pos_left h this]

/-- foldl E_step preserves strict inequality. -/
private lemma foldl_E_step_lt (xs : List Bool) (a1 a2 : ℚ) (h : a1 < a2) :
    xs.foldl E_step a1 < xs.foldl E_step a2 := by
  induction xs generalizing a1 a2 with
  | nil => exact h
  | cons b rest ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (E_step_strict_mono' b a1 a2 h)

/-- An elementary swap strictly decreases E_pv. -/
private lemma E_pv_elementary_lt {v1 v2 : ParityVector}
    (h : ParityVector.ElementaryPrecedes v1 v2) : E_pv v2 < E_pv v1 := by
  cases h with
  | swap w1 w2 =>
    simp only [E_pv, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set a := w1.foldl E_step 0
    apply foldl_E_step_lt
    simp only [E_step, Bool.toNat_false, Bool.toNat_true]
    norm_num; linarith

/-- `V (j+1) n` is `V j n` with one more parity bit appended. -/
private lemma V_succ (j n : ℕ) :
    (V (j + 1) n : List Bool) = (V j n : List Bool) ++ [decide (X (T_iter j n) = 1)] := by
  simp only [V, List.finRange_succ_last, List.map_append, List.map_map,
    Function.comp, Fin.val_castSucc, List.map_cons, Fin.val_last, List.map_nil]

/-- `(decide (x = 1)).toNat = x` when `x ≤ 1`. -/
private lemma bool_toNat_eq_X (x : ℕ) (hx : x ≤ 1) :
    (decide (x = 1)).toNat = x := by
  interval_cases x <;> simp

/-- `E_pv (V j n) = E j n`: the parity-vector E matches the sequence-based E. -/
private lemma E_pv_eq_E (j n : ℕ) : E_pv (V j n) = E j n := by
  induction j with
  | zero => simp [E_pv, V, E_zero]
  | succ j ih =>
    show (V (j + 1) n : List Bool).foldl E_step 0 = E (j + 1) n

/-- TransGen of ElementaryPrecedes strictly decreases E_pv. -/
private lemma E_pv_transGen_lt {v1 v2 : ParityVector}
    (h : Relation.TransGen ParityVector.ElementaryPrecedes v1 v2) : E_pv v2 < E_pv v1 := by
  induction h with
  | single h => exact E_pv_elementary_lt h
  | tail _ h ih => exact lt_trans (E_pv_elementary_lt h) ih

/-- Lemma 2.1 ([Roz25] p.5)
    If `V j m` strictly precedes `V j n` in the parity-vector partial order
    (i.e., at least one elementary swap), then `E_j(m) > E_j(n)`. -/
lemma E_lt_of_V_precedes (j m n : ℕ)
    (hprec : Relation.TransGen ParityVector.ElementaryPrecedes (V j m) (V j n)) :
    E j n < E j m := by
  have h := E_pv_transGen_lt hprec
  rwa [E_pv_eq_E, E_pv_eq_E] at h
