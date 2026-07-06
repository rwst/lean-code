/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RT.FinitePar

/-!
# Excursion lower bounds from parity runs (toward `hpigeon`)

The *physical* half of the pigeonhole excursion bound `2^{j/(2R)} - 1 ≤ Exc j n`
(hypothesis `hpigeon` of `Paradoxical.finite_of_pigeonhole`): **a long run of one
parity forces a large orbit term**, hence a large excursion.

* `two_pow_dvd_of_even_run` — a run of `e` even steps (a *gap*) from position `p`
  makes `Tᵖ(n)` divisible by `2^e` (`e` successive halvings), so `Tᵖ(n) ≥ 2^e`.
* `two_pow_dvd_succ_of_odd_run` — a run of `a` odd steps (a *burst*) from `p` makes
  `Tᵖ(n) + 1` divisible by `2^a` (each odd step `x ↦ (3x+1)/2` sends
  `x+1 ↦ 3(x+1)/2`, halving `v₂(x+1)`), so `Tᵖ(n) ≥ 2^a - 1`.
* `pow_le_maxExcursion_of_even_run`, `pow_pred_le_maxExcursion_of_odd_run` — the
  resulting bounds on `RT.maxExcursion n`.

What is proved here is the run → excursion step for a *single* run.  To reach the
exact `hpigeon` statement one still needs the run-length **pigeonhole** (`R`
circuits ⟹ some run has length `≥ j/(2R)`) and the real-number packaging; that
combinatorial glue is not yet formalized.

`sorry`-free (`propext, Classical.choice, Quot.sound`).
-/

namespace Paradoxical

open CC RT

/-- A run of `e` even steps from position `p` makes `Tᵖ(n)` divisible by `2^e`. -/
lemma two_pow_dvd_of_even_run (n e p : ℕ) (h : ∀ i, i < e → T_iter (p + i) n % 2 = 0) :
    2 ^ e ∣ T_iter p n := by
  induction e generalizing p with
  | zero => simp
  | succ e ih =>
      have hp0 : T_iter p n % 2 = 0 := by simpa using h 0 (Nat.succ_pos e)
      have hstep : T_iter (p + 1) n = T_iter p n / 2 := by
        show T (T_iter p n) = _; rw [T_even hp0]
      have hrec : ∀ i, i < e → T_iter (p + 1 + i) n % 2 = 0 := by
        intro i hi; have := h (1 + i) (by omega)
        rwa [show p + (1 + i) = p + 1 + i by ring] at this
      obtain ⟨c, hc⟩ := hstep ▸ ih (p + 1) hrec
      have heven : T_iter p n = 2 * (T_iter p n / 2) := by omega
      exact ⟨c, by rw [heven, hc]; ring⟩

/-- A run of `a` odd steps from position `p` makes `Tᵖ(n) + 1` divisible by `2^a`. -/
lemma two_pow_dvd_succ_of_odd_run (n a p : ℕ) (h : ∀ i, i < a → T_iter (p + i) n % 2 = 1) :
    2 ^ a ∣ (T_iter p n + 1) := by
  induction a generalizing p with
  | zero => simp
  | succ a ih =>
      have hp1 : T_iter p n % 2 = 1 := by simpa using h 0 (Nat.succ_pos a)
      have hstep : T_iter (p + 1) n = (3 * T_iter p n + 1) / 2 := by
        show T (T_iter p n) = _; rw [T_odd hp1]
      have hrec : ∀ i, i < a → T_iter (p + 1 + i) n % 2 = 1 := by
        intro i hi; have := h (1 + i) (by omega)
        rwa [show p + (1 + i) = p + 1 + i by ring] at this
      have hdvd : 2 ^ a ∣ (T_iter p n / 2 + 1) * 3 := by
        have h0 := hstep ▸ ih (p + 1) hrec
        have hval : (3 * T_iter p n + 1) / 2 + 1 = (T_iter p n / 2 + 1) * 3 := by omega
        rwa [hval] at h0
      have hcop : Nat.Coprime (2 ^ a) 3 := Nat.Coprime.pow_left a (by decide)
      obtain ⟨c, hc⟩ := hcop.dvd_of_dvd_mul_right hdvd
      have hodd : T_iter p n + 1 = 2 * (T_iter p n / 2 + 1) := by omega
      exact ⟨c, by rw [hodd, hc]; ring⟩

/-- A run of `e` even steps forces the excursion up to `2^e`. -/
lemma pow_le_maxExcursion_of_even_run (n e p : ℕ) (hn : 1 ≤ n)
    (h : ∀ i, i < e → T_iter (p + i) n % 2 = 0) : ((2 ^ e : ℕ) : ℕ∞) ≤ maxExcursion n := by
  have hle : 2 ^ e ≤ T_iter p n := Nat.le_of_dvd (T_iter_pos hn p) (two_pow_dvd_of_even_run n e p h)
  exact le_trans (Nat.cast_le.mpr hle) (le_maxExcursion n p)

/-- A run of `a` odd steps forces the excursion up to `2^a - 1`. -/
lemma pow_pred_le_maxExcursion_of_odd_run (n a p : ℕ)
    (h : ∀ i, i < a → T_iter (p + i) n % 2 = 1) : ((2 ^ a - 1 : ℕ) : ℕ∞) ≤ maxExcursion n := by
  have hle : 2 ^ a ≤ T_iter p n + 1 :=
    Nat.le_of_dvd (by positivity) (two_pow_dvd_succ_of_odd_run n a p h)
  exact le_trans (Nat.cast_le.mpr (by omega : 2 ^ a - 1 ≤ T_iter p n)) (le_maxExcursion n p)

end Paradoxical
