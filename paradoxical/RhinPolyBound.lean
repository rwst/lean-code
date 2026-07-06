/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RT.FinitePar
import CITED.RhinLogForm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Rhin polynomial bound on `H j` — discharging `hmH`

Discharges the remaining hypothesis `hmH : m ≤ C·j^{14.3}` of
`Paradoxical.finite_of_pigeonhole` (`length-bound.html` §4d, step (b): "RT Cor 4.4 +
Rhin").  [Roz25] never states this bound — in §6 they apply Rhin to the drift
`Λ = j·log2 − q·log3` of the sequence itself — but their Proposition 6.3
(`Rhin.logForm_lower_bound`, `CITED.RhinLogForm`) holds for *arbitrary* integer
coefficients, so we may instead feed it the denominator of Corollary 4.4's size
function `H j = 1/(2^{r(j)} − 3)`, `r(j) = j/⌊ξj⌋`, `ξ = log2/log3`:

* with `(u₀, u₁, u₂) = (0, j, −⌊ξj⌋)` the height is `max(j, ⌊ξj⌋) = j` (the floor is
  `< j` since `ξ < 1`), and `Λ₀ = j·log2 − ⌊ξj⌋·log3 ≥ 0` by the floor, so Rhin gives
  `Λ₀ ≥ j^{−13.3}`;
* `2^{r(j)} = 3·e^{Λ₀/⌊ξj⌋}`, so `2^{r(j)} − 3 ≥ 3·Λ₀/⌊ξj⌋` (`e^x ≥ 1 + x`), whence
  `H j ≤ ⌊ξj⌋/(3Λ₀) ≤ j·j^{13.3}/3 = j^{14.3}/3` — the exponent `14.3 = 13.3 + 1`.

Chaining with the (transcendence-free) Corollary 4.4′ bridge `RT.m_le_H` bounds the
least odd term of any paradoxical `Ωⱼ(n)` polynomially in the length:

* `H_le_rpow` — `2 ≤ j → H j ≤ j^{14.3}/3`;
* `least_odd_poly_bound` — `m ≤ (1/3)·j^{14.3}`, verbatim the `hmH` hypothesis of
  `finite_of_pigeonhole` (`C = 1/3`, `Pw = 14.3`).

With `RunPigeonhole` (which discharges `hpigeon`) the sole remaining input to the
per-`R` finiteness reduction is the excursion hypothesis `hexc : Exc ≤ m^β`
(RT Conjecture 6.2).

`sorry`-free; rests only on the cited `Rhin.logForm_lower_bound` ([Rhi87]).

## References
* [Rhi87] Rhin, Georges. "Approximants de Padé et mesures effectives d'irrationalité."
  *Séminaire de Théorie des Nombres, Paris 1985–86*, 155–164. Birkhäuser, 1987.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz
  sequences." arXiv:2502.00948 (2025). Corollary 4.4, Proposition 6.3.
-/

namespace Paradoxical

open RT CC

/-- **The Rhin polynomial bound on `H`.**  For `j ≥ 2` the Corollary-4.4 size function
`H j = 1/(2^{r(j)} − 3)`, `r(j) = j/⌊ξj⌋`, satisfies `H j ≤ j^{14.3}/3`.

Rhin's Proposition 6.3 applied to `(u₀, u₁, u₂) = (0, j, −⌊ξj⌋)` — height exactly `j` —
gives `Λ₀ = j·log2 − ⌊ξj⌋·log3 ≥ j^{−13.3}`, and `2^{r(j)} − 3 = 3(e^{Λ₀/⌊ξj⌋} − 1) ≥
3Λ₀/⌊ξj⌋` turns this into the polynomial bound. -/
theorem H_le_rpow (j : ℕ) (hj : 2 ≤ j) : H j ≤ (j : ℝ) ^ (14.3 : ℝ) / 3 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  set Q : ℤ := ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ with hQ_def
  -- `1 ≤ Q`: `j·log2 ≥ 2·log2 = log4 ≥ log3`.
  have hlog34 : Real.log 3 ≤ 2 * Real.log 2 := by
    have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hξj : (1 : ℝ) ≤ (j : ℝ) * Real.log 2 / Real.log 3 := by
    rw [le_div_iff₀ hlog3, one_mul]
    calc Real.log 3 ≤ 2 * Real.log 2 := hlog34
      _ ≤ (j : ℝ) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hlog2); exact_mod_cast hj
  have hQ1 : 1 ≤ Q := Int.le_floor.mpr (by exact_mod_cast hξj)
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < Q)
  -- `Q < j`: `ξ < 1`.
  have hQltj : Q < (j : ℤ) := by
    rw [hQ_def, Int.floor_lt]
    push_cast
    rw [div_lt_iff₀ hlog3]
    have hlt := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
    nlinarith
  have hQj : (Q : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_of_lt hQltj
  -- the linear form `Λ₀` and its floor nonnegativity
  set Λ : ℝ := (j : ℝ) * Real.log 2 - (Q : ℝ) * Real.log 3 with hΛ_def
  have hΛ0 : 0 ≤ Λ := by
    have hfl : (Q : ℝ) ≤ (j : ℝ) * Real.log 2 / Real.log 3 := hQ_def ▸ Int.floor_le _
    rw [hΛ_def, sub_nonneg]
    exact (le_div_iff₀ hlog3).mp hfl
  -- Rhin with `(u₀,u₁,u₂) = (0, j, −Q)`: height `max(j, Q) = j ≥ 2`.
  have hH_eq : Rhin.logHeight (j : ℤ) (-Q) = (j : ℤ) := by
    simp only [Rhin.logHeight, abs_neg]
    rw [abs_of_nonneg (show (0 : ℤ) ≤ (j : ℤ) by positivity),
      abs_of_nonneg (by omega : (0 : ℤ) ≤ Q)]
    omega
  have hrhin := Rhin.logForm_lower_bound 0 (j : ℤ) (-Q)
    (by rw [hH_eq]; exact_mod_cast hj)
  have hform : Rhin.logForm 0 (j : ℤ) (-Q) = Λ := by
    simp only [Rhin.logForm, hΛ_def]; push_cast; ring
  rw [hH_eq, hform, abs_of_nonneg hΛ0] at hrhin
  have hΛlb : (j : ℝ) ^ (-(13.3 : ℝ)) ≤ Λ := by exact_mod_cast hrhin
  have hΛpos : 0 < Λ := lt_of_lt_of_le (Real.rpow_pos_of_pos hj0 _) hΛlb
  -- `2^{r(j)} = 3·e^{Λ/Q}`, so the denominator of `H` is `≥ 3Λ/Q > 0`.
  have hr_eq : rExp j = (j : ℝ) / (Q : ℝ) := by rw [rExp]
  have hexp_eq : (2 : ℝ) ^ rExp j = 3 * Real.exp (Λ / (Q : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hr_eq,
      show Real.log 2 * ((j : ℝ) / (Q : ℝ)) = Real.log 3 + Λ / (Q : ℝ) by
        rw [hΛ_def]; field_simp; ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hden_lb : 3 * (Λ / (Q : ℝ)) ≤ (2 : ℝ) ^ rExp j - 3 := by
    rw [hexp_eq]
    have hx := Real.add_one_le_exp (Λ / (Q : ℝ))
    nlinarith
  have hden_pos : (0 : ℝ) < 3 * (Λ / (Q : ℝ)) := by positivity
  -- `H j ≤ Q/(3Λ) ≤ (j/3)·j^{13.3} = j^{14.3}/3`.
  have hH_le : H j ≤ (Q : ℝ) / (3 * Λ) := by
    rw [H]
    calc 1 / ((2 : ℝ) ^ rExp j - 3) ≤ 1 / (3 * (Λ / (Q : ℝ))) :=
          one_div_le_one_div_of_le hden_pos hden_lb
      _ = (Q : ℝ) / (3 * Λ) := by
          rw [show 3 * (Λ / (Q : ℝ)) = 3 * Λ / (Q : ℝ) by ring, one_div_div]
  have hinv : 1 / Λ ≤ (j : ℝ) ^ (13.3 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt hj0)] at hΛlb
    have h := one_div_le_one_div_of_le (by positivity) hΛlb
    simpa [one_div, inv_inv] using h
  calc H j ≤ (Q : ℝ) / (3 * Λ) := hH_le
    _ = (Q : ℝ) / 3 * (1 / Λ) := by rw [div_mul_div_comm, mul_one]
    _ ≤ (j : ℝ) / 3 * (j : ℝ) ^ (13.3 : ℝ) := by
        apply mul_le_mul (by linarith) hinv (by positivity) (by positivity)
    _ = (j : ℝ) ^ (14.3 : ℝ) / 3 := by
        rw [show (14.3 : ℝ) = 13.3 + 1 by norm_num, Real.rpow_add hj0, Real.rpow_one]
        ring

/-- **`hmH`, discharged** (`length-bound.html` §4d, step (b): "RT Cor 4.4 + Rhin").
The least odd term of a paradoxical `Ωⱼ(n)` is polynomially bounded in the length:
`m ≤ (1/3)·j^{14.3}` — verbatim the hypothesis `hmH` of `finite_of_pigeonhole` with
`C = 1/3`, `Pw = 14.3`.  Chains the transcendence-free Corollary 4.4′ bridge
`RT.m_le_H` with the Rhin polynomial bound `H_le_rpow`. -/
theorem least_odd_poly_bound (j n m : ℕ) (hn : 1 ≤ n) (hm_pos : 0 < m)
    (h_odd_bounded : ∀ k, k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m)
    (h_para : IsParadoxical j n) :
    (m : ℝ) ≤ 1 / 3 * (j : ℝ) ^ (14.3 : ℝ) := by
  have hj2 : 2 ≤ j := two_le_j_of_paradoxical j n h_para hn
  have h := le_trans (m_le_H hj2 (by omega) hm_pos h_odd_bounded h_para) (H_le_rpow j hj2)
  linarith

end Paradoxical
