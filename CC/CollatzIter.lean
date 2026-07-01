/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Terras

namespace CC

/-- One step of the raw (uncompressed) Collatz map: halve if even, else `3n + 1`. -/
def collatz_step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

lemma collatz_step_even {n : ℕ} (h : n % 2 = 0) : collatz_step n = n / 2 := if_pos h

lemma collatz_step_odd {n : ℕ} (h : n % 2 = 1) : collatz_step n = 3 * n + 1 :=
  if_neg (by omega)

/-- `collatz_iter k n` applies `collatz_step` to `n` a total of `k` times. -/
def collatz_iter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatz_step (collatz_iter k n)

lemma collatz_iter_add (a b n : ℕ) :
    collatz_iter (a + b) n = collatz_iter a (collatz_iter b n) := by
  induction a with
  | zero => simp [collatz_iter]
  | succ a ih => rw [Nat.succ_add]; simp only [collatz_iter, ih]

/-- One `T` step equals one or two `collatz_step`s. -/
lemma T_step_collatz (n : ℕ) : ∃ j, j ≥ 1 ∧ collatz_iter j n = T n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 : (k + k) % 2 = 0 := by omega
    exact ⟨1, le_refl _, by simp [collatz_iter, collatz_step, h1, T_even h1]⟩
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (3 * (2 * k + 1) + 1) % 2 = 0 := by omega
    exact ⟨2, by omega, by simp [collatz_iter, collatz_step, h1, h2, T_odd h1]⟩

/-- Every `T_iter` step can be realized as a `collatz_iter` at some later index. -/
lemma T_iter_implies_collatz_iter (k n : ℕ) : ∃ j ≥ k, collatz_iter j n = T_iter k n := by
  induction k generalizing n with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    obtain ⟨j1, h1, eq1⟩ := T_step_collatz n
    obtain ⟨j2, h2, eq2⟩ := ih (T n)
    refine ⟨j1 + j2, by omega, ?_⟩
    rw [T_iter_succ_right, ← eq2, ← eq1, ← collatz_iter_add, Nat.add_comm j2 j1]

end CC
