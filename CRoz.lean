import C2
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

/-- `V j n` is the parity vector of length `j` for the Collatz sequence starting at `n`:
    the `i`-th entry is `true` (= 1) when `T^i(n)` is odd, `false` (= 0) when even. -/
def V (j n : ℕ) : ParityVector :=
  (List.finRange j).map (fun i => decide (X (T_iter i.val n) = 1))

@[simp]
lemma V_length (j n : ℕ) : (V j n).length = j := by
  simp [V]

lemma V_get (j n : ℕ) (i : Fin j) :
    (V j n).get ⟨i.val, by simp [V_length]⟩ = decide (X (T_iter i.val n) = 1) := by
  simp [V]

/-- E_vec is the same as V without the ParityVector structure
-/
lemma E_vec_eq_V_toNat (j n : ℕ) (i : Fin j) :
    E_vec j n i = ParityVector.toNat ((V j n).get ⟨i.val, by simp⟩) := by
  rw [V_get]
  simp only [E_vec_apply, ParityVector.toNat]
  rw [X_eq_mod]
  by_cases h : T_iter i.val n % 2 = 1
  · simp [h]
  · have : T_iter i.val n % 2 = 0 := by omega
    simp [this]

/-- The Garner correction ratio: `E j n = Q_j(n) / 2^j`, where `Q_j` is the
    Garner correction term. This is the rational contribution of the correction
    in the normalised Garner formula `T^j(n) = C_j(n) · n + E_j(n)`. -/
def E (j n : ℕ) : ℚ := (garner_correction j n : ℚ) / (2 ^ j : ℚ)

-- ===== Helper lemmas for E_lt_of_V_precedes =====

/-- Base case: `E 0 n = 0`. -/
lemma E_zero (n : ℕ) : E 0 n = 0 := by
  simp [E, garner_correction]

/-- Recurrence for E: `E (k+1) n = (3^(x_k) / 2) · E k n + x_k / 2`,
    where `x_k = X(T^k n)`. -/
lemma E_succ (k n : ℕ) :
    E (k + 1) n = (3 ^ X (T_iter k n) : ℚ) / 2 * E k n +
      (X (T_iter k n) : ℚ) / 2 := by
  simp only [E, garner_correction]
  rw [show (2 : ℚ) ^ (k + 1) = 2 * 2 ^ k from by ring]
  have h2k : (2 ^ k : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- `garner_correction` only depends on the parity bits. If two sequences
    agree on the first `k` parities, their Garner corrections are equal.
    (This strengthens `garner_correction_eq_of_E_vec_eq` from C2 to work
    with the `V` representation.) -/
lemma garner_correction_eq_of_V_prefix_eq (k j m n : ℕ) (hk : k ≤ j)
    (hpre : ∀ i : Fin k, (V j m).get ⟨i.val, by simp; omega⟩ =
      (V j n).get ⟨i.val, by simp; omega⟩) :
    garner_correction k m = garner_correction k n := by
  induction k with
  | zero => simp [garner_correction]
  | succ k ih =>
    simp only [garner_correction]
    have hk' : k ≤ j := by omega
    have ih' := ih hk' (fun i => hpre ⟨i.val, by omega⟩)
    -- Extract X equality from V prefix agreement
    have hXk : X (T_iter k m) = X (T_iter k n) := by
      have hv := hpre ⟨k, Nat.lt_succ_iff.mpr le_rfl⟩
      simp only [V] at hv
      have hd : (X (T_iter k m) = 1 ↔ X (T_iter k n) = 1) := by simpa using hv
      have hm_le : X (T_iter k m) ≤ 1 := by rw [X_eq_mod]; omega
      have hn_le : X (T_iter k n) ≤ 1 := by rw [X_eq_mod]; omega
      omega
    rw [ih', hXk]

/-- Equal prefix of `V` implies equal `E` up to that prefix length. -/
lemma E_eq_of_V_prefix_eq (k j m n : ℕ) (hk : k ≤ j)
    (hpre : ∀ i : Fin k, (V j m).get ⟨i.val, by simp; omega⟩ =
      (V j n).get ⟨i.val, by simp; omega⟩) :
    E k m = E k n := by
  simp only [E, garner_correction_eq_of_V_prefix_eq k j m n hk hpre]

/-- The step map `e ↦ (3^x / 2) · e + x / 2` is strictly monotone in `e`
    for any `x ∈ {0, 1}`. -/
lemma E_step_strict_mono (x : ℕ) (a b : ℚ) (hab : a < b) :
    (3 ^ x : ℚ) / 2 * a + (x : ℚ) / 2 < (3 ^ x : ℚ) / 2 * b + (x : ℚ) / 2 := by
  have h3 : (3 ^ x : ℚ) / 2 > 0 := by positivity
  nlinarith [sq_nonneg (3 : ℚ)]
