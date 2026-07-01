/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RT.ProductIdentity
import Mathlib.Analysis.Complex.ExponentialBounds
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Crossing lemmas for Theorem 5.3 (Step 3)

The proof of Theorem 5.3 of [Roz25] threads the excursion/delay records (`RT.ExcursionRecords`)
through Corollaries 4.3/4.4 and three arithmetic "crossing" facts about the size function
`H j = 1 / (2^{r(j)} − 3)`, `r(j) = j / ⌊(log2/log3)·j⌋` — the Corollary-4.4 upper bound on the
smallest odd term (and on the harmonic mean).

* `q_lower_from_j0` — the **closed-form** crossing `q ≥ ⌈j₀·log2/log(3+m₀⁻¹)⌉ = 971`, **proved
  here**. The transcendental content `1539·log 2 > 970·log(3 + 1/113383)` is discharged by
  exponentiating to the algebraic inequality `(3 + 1/113383)^970 < 2^1539` (an exp bound plus one
  big-integer `norm_num`), sidestepping numeric bounds on `log 3`.
* `H_cross_j0` (`j₀ = 1539`) and `j1_cross` (`j₁ = 301994`) — the two **floor-crossing** facts.
  [Roz25] establishes these by direct computation ("a straightforward computation shows that
  `j₀ = 1539`…"; "using a computer, one verifies that `j₁ = 301994`…", p. 16): they assert that a
  given value is the *smallest* `j > 1` at which `H j` reaches a record threshold, which is a finite
  verification of `⌊(log2/log3)·j⌋` over a long range (up to `301994`), essentially a
  continued-fraction computation for `log2/log3`. Per the layered-QA convention these are recorded
  as cited `axiom`s carrying `@[ref "Roz25"]` (status `cited`), not re-run in Lean.

## References
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). Theorem 5.3 proof (p. 16), constants `j₀,q₀,j₁`.
-/

open Classical

namespace RT

/-- The exponent `r(j) = j / ⌊(log2/log3)·j⌋` of Corollary 4.4 (`paradoxical_m_bound`). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_53"]
noncomputable def rExp (j : ℕ) : ℝ := (j : ℝ) / (⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℝ)

/-- The Corollary-4.4 size bound `H j = 1 / (2^{r(j)} − 3)`: the upper bound that
`paradoxical_m_bound`/`paradoxical_m_bound_harmonic` place on the smallest odd term / harmonic
mean of a paradoxical `Ωⱼ(n)`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_53"]
noncomputable def H (j : ℕ) : ℝ := 1 / ((2 : ℝ) ^ rExp j - 3)

set_option exponentiation.threshold 3000 in
set_option maxRecDepth 100000 in
/-- The thin but true big-integer bound `3^971 ≤ 2^1539` (`2^1539 / 3^971 ≈ 1.001`), the exact
crossing behind `q₀ = 971`. Checked by kernel `decide` on GMP naturals (raised thresholds). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_53"]
private lemma pow_bound_j0 : (3 : ℕ) ^ 971 ≤ 2 ^ 1539 := by decide

/-- **Crossing lemma for `q₀`** (Corollary 4.3 at `j ≥ j₀ = 1539`). If the ones-ratio lower bound
of Corollary 4.3 with `m₀ = 113383` holds and `j ≥ 1539`, then `q ≥ 971`.

Proved by exponentiating `1539·log 2 > 970·log(3 + 1/113383)` to `(3 + 1/113383)^970 < 2^1539`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_thm_53"]
theorem q_lower_from_j0 (j q : ℕ) (hj : 1539 ≤ j)
    (hratio : Real.log 2 / Real.log (3 + 1 / (113383 : ℝ)) ≤ (q : ℝ) / (j : ℝ)) :
    971 ≤ q := by
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hden : (0 : ℝ) < Real.log (3 + 1 / (113383 : ℝ)) := Real.log_pos (by norm_num)
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hratio_pos : 0 < Real.log 2 / Real.log (3 + 1 / (113383 : ℝ)) := div_pos hlog2pos hden
  -- The algebraic core: (3 + 1/113383)^970 < 2^1539.
  have h1 : (3 + 1 / (113383 : ℝ)) ^ 970 < (2 : ℝ) ^ 1539 := by
    have e1 : (3 + 1 / (113383 : ℝ)) = 3 * (1 + 1 / (340149 : ℝ)) := by norm_num
    have hb : (1 + 1 / (340149 : ℝ)) ≤ Real.exp (1 / 340149) := by
      linarith [Real.add_one_le_exp (1 / (340149 : ℝ))]
    have hlt3 : (1 + 1 / (340149 : ℝ)) ^ 970 < 3 :=
      calc (1 + 1 / (340149 : ℝ)) ^ 970
          ≤ Real.exp (1 / 340149) ^ 970 := by gcongr
        _ = Real.exp ((970 : ℕ) * (1 / 340149 : ℝ)) := (Real.exp_nat_mul _ _).symm
        _ < Real.exp 1 := by apply Real.exp_lt_exp.mpr; push_cast; norm_num
        _ < 3 := by linarith [Real.exp_one_lt_d9]
    calc (3 + 1 / (113383 : ℝ)) ^ 970
        = 3 ^ 970 * (1 + 1 / (340149 : ℝ)) ^ 970 := by rw [e1, mul_pow]
      _ < 3 ^ 970 * 3 := by apply mul_lt_mul_of_pos_left hlt3 (by positivity)
      _ = (3 : ℝ) ^ 971 := by rw [← pow_succ]
      _ ≤ (2 : ℝ) ^ 1539 := by exact_mod_cast pow_bound_j0
  -- Exponentiated form ⇒ the log inequality.
  have hkey : (970 : ℝ) * Real.log (3 + 1 / (113383 : ℝ)) < 1539 * Real.log 2 := by
    have h := Real.log_lt_log (by positivity) h1
    rw [Real.log_pow, Real.log_pow] at h
    exact_mod_cast h
  -- q ≥ j·ratio ≥ 1539·ratio > 970.
  have step1 : (j : ℝ) * (Real.log 2 / Real.log (3 + 1 / (113383 : ℝ))) ≤ (q : ℝ) := by
    rw [mul_comm]; exact (le_div_iff₀ hj0).mp hratio
  have step2 : (1539 : ℝ) * (Real.log 2 / Real.log (3 + 1 / (113383 : ℝ)))
      ≤ (j : ℝ) * (Real.log 2 / Real.log (3 + 1 / (113383 : ℝ))) := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hratio_pos); exact_mod_cast hj
  have step3 : (970 : ℝ) < 1539 * (Real.log 2 / Real.log (3 + 1 / (113383 : ℝ))) := by
    rw [← mul_div_assoc, lt_div_iff₀ hden]; linarith [hkey]
  have hqR : (970 : ℝ) < (q : ℝ) := by linarith [step1, step2, step3]
  by_contra hlt
  push Not at hlt
  have : (q : ℝ) ≤ 970 := by exact_mod_cast (by omega : q ≤ 970)
  linarith [hqR]

/-- **Crossing lemma for `j₀`** ([Roz25], p. 16: "a straightforward computation shows that
`j₀ = 1539` is the smallest integer greater than 1 for which `H(j₀) ≥ m₀`"). Cited computation
(`m₀ = 113383`). -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_thm_53"]
axiom H_cross_j0 (j : ℕ) (hj : 1 < j) (hH : (113383 : ℝ) ≤ H j) : 1539 ≤ j

/-- **Crossing lemma for `j₁`** ([Roz25], p. 16: "using a computer, one verifies that
`j₁ = 301994` is the smallest integer greater than 1 for which `H(j₁) ≥ m₁`"). Cited computation
(`m₁ = 23035537407`). -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_thm_53"]
axiom j1_cross (j : ℕ) (hj : 1 < j) (hH : (23035537407 : ℝ) ≤ H j) : 301994 ≤ j

end RT
