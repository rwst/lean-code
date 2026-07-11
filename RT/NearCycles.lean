/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.IntervalCases
import CITED.EllisonsTheorem
import CITED.RhinLogForm
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# A quantitative "no near-cycle" bound (Rozier–Terracol, Appendix B)

How closely can a Collatz excursion return to its start?  A return after `j` steps with `q` odd
steps is governed by the gap `|2ʲ − 3^q|`: the smaller this gap, the nearer the trajectory comes to
a genuine cycle.  **Lemma B.1** makes the gap explicit — it is never smaller than `2.56^q / 2`.

**Lemma B.1** ([Roz25]).  For all `j` and all `q > 12`, there holds `|2ʲ − 3^q| > 2.56^q / 2`.

## Proof outline
Put `c = 2 e^{−1/10} ≈ 1.809` (`nearCycleBase`), `ρ = log₂ 3` (`nearCycleExp`), and
`A = c^ρ = 2.560278… > 2.56` (`nearCycleConst`).  For `q ≥ 19` split on the position of `3^q`:

* `3^q ≤ 2ʲ`: Ellison's bound (`Ellison.pillai_lower_bound`) gives `|Δ| > cʲ ≥ c^{ρq} = A^q > 2.56^q`.
* `2ʲ < 3^q ≤ 2^{j+1}`: Ellison again, `|Δ| > cʲ ≥ c^{ρq−1} = A^q / c > A^q / 2` (as `c < 2`).
* `2^{j+1} < 3^q`: elementary, `|Δ| = 3^q − 2ʲ > 3^q / 2 > 2.56^q / 2`.

The range `13 ≤ q ≤ 18` is handled by a direct finite check (`nearCycle_small_q`), and `A > 2.56`
(`nearCycleConst_gt`) is proved from an exact integer certificate for `log₂ 3` plus a Taylor bound
for `exp`.  Both avoid `native_decide` and any configuration change, so **the only cited input is
Ellison's theorem** (`Ellison.pillai_lower_bound`).

## The Rhin companion (`plan-formalize-logforms.html` M-5, F-5b)

`nearCycle_rhin_bound` is a second, *complementary* gap bound resting on Rhin's linear-form
estimate (`CITED/RhinLogForm.lean`, [Rhi87]) rather than Ellison's: for `max(j, q) ≥ 2`,
`|2ʲ − 3^q| ≥ (3^q / e) · max(j, q)^(−13.3)`.  Its loss factor is *polynomial* in `max(j, q)`
where Ellison's `nearCycle_lower_bound` loses an *exponential* `e^{−j/10}` — so the Rhin bound
is asymptotically far stronger and wins for `q ≳ 550`, while Ellison wins for small `q`.  The two
are complementary; `Ellison.pillai_lower_bound` stays untouched (it is what [Roz25] Appendix B
actually cites).  Proof: with `Λ = j·log 2 − q·log 3`, `2ʲ − 3^q = 3^q(e^Λ − 1)`, and Rhin's
`|Λ| ≥ max(j,q)^(−13.3)` is turned into the gap by `|e^x − 1| ≥ |x|e^{−|x|}` (small `Λ`) and
`|e^x − 1| ≥ 1 − 1/e` (`|Λ| ≥ 1`).  Footprint std3 + [Rhi87] only — no new axiom.

## Contents
* `RT.nearCycleBase` / `RT.nearCycleExp` / `RT.nearCycleConst` — the constants `c`, `ρ`, `A`.
* `RT.nearCycleConst_gt` — `2.56 < A` (the paper's constant `A = 2.560278…`); proved via `exp` Taylor bound.
* `RT.nearCycle_small_q` — the base range `13 ≤ q ≤ 18`; proved by a finite `interval_cases` check.
* `RT.nearCycle_lower_bound` — **Lemma B.1** ([Roz25]).
* `RT.nearCycle_rhin_bound` — the **Rhin companion** ([Rhi87]): `|2ʲ − 3^q| ≥ (3^q/e)·max(j,q)^(−13.3)`.

## References
* [Ell71] Ellison, W. J. "On a theorem of S. Sivasankaranarayana Pillai."
  *Séminaire de théorie des nombres de Bordeaux* (1971): 1–10.
* [Rhi87] Rhin, Georges. "Approximants de Padé et mesures effectives d'irrationalité."
  *Séminaire de Théorie des Nombres, Paris 1985–86*, 155–164. Birkhäuser, 1987.
  (Via `CITED/RhinLogForm.lean`.)
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). Appendix B, Lemma B.1, eq. (24).
-/

open Real

namespace RT

/-- The base `c = 2 e^{−1/10} ≈ 1.809…` of Ellison's geometric gap `|2ʲ − 3^q| > cʲ`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_lemma_b1"]
noncomputable def nearCycleBase : ℝ := 2 * Real.exp (-(1 / 10))

/-- The exponent `ρ = log₂ 3 = log 3 / log 2`, the "cost" in base `c` of one factor of `3`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_lemma_b1"]
noncomputable def nearCycleExp : ℝ := Real.log 3 / Real.log 2

/-- The constant `A = c^ρ = (2 e^{−1/10})^{log₂ 3} = 2.560278…`, so that Ellison's bound reads
`|2ʲ − 3^q| > A^q` when `2ʲ ≥ 3^q`.  It exceeds `2.56` (see `nearCycleConst_gt`). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_lemma_b1"]
noncomputable def nearCycleConst : ℝ := nearCycleBase ^ nearCycleExp

/-- The numerical constant of [Roz25], Appendix B: `A = (2 e^{−1/10})^{log₂ 3} = 2.560278… > 2.56`.

Proved (no `native_decide`, no configuration changes): since `2^{log₂ 3} = 3`, one has
`A = 3 · e^{−ρ/10}` with `ρ = log₂ 3`, so `2.56 < A ⟺ e^{ρ/10} < 3/2.56 = 1.171875`.  The exponent
is pinned by the exact integer certificate `3^200 < 2^317`, giving `ρ < 317/200 = 1.585`; then a
degree-5 Taylor bound for `exp` (`Real.exp_bound`) yields `e^{0.1585} < 1.171875`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_lemma_b1"]
theorem nearCycleConst_gt : (2.56 : ℝ) < nearCycleConst := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `A = 3 · e^{−ρ/10}`, using `2^ρ = 2^{log₂ 3} = 3`.
  have hA : nearCycleConst = 3 * Real.exp (-(nearCycleExp / 10)) := by
    unfold nearCycleConst nearCycleBase
    rw [Real.mul_rpow (by norm_num) (le_of_lt (Real.exp_pos _))]
    have h2ρ : (2 : ℝ) ^ nearCycleExp = 3 := by
      unfold nearCycleExp
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        show Real.log 2 * (Real.log 3 / Real.log 2) = Real.log 3 from by field_simp]
      exact Real.exp_log (by norm_num)
    have hexpρ : (Real.exp (-(1 / 10))) ^ nearCycleExp = Real.exp (-(nearCycleExp / 10)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; ring
    rw [h2ρ, hexpρ]
  -- `ρ = log₂ 3 < 317/200 = 1.585`, from the exact integer inequality `3^200 < 2^317`.
  have hρ_lt : nearCycleExp < 1585 / 1000 := by
    unfold nearCycleExp
    rw [div_lt_iff₀ hlog2]
    have hnat : (3 : ℕ) ^ 200 < 2 ^ 317 := by
      have h : (2 : ℕ) ^ 317 = 2 ^ 159 * 2 ^ 158 := by rw [← pow_add]
      rw [h]; norm_num
    have hreal : (3 : ℝ) ^ 200 < (2 : ℝ) ^ 317 := by exact_mod_cast hnat
    have h2 := Real.log_lt_log (by positivity) hreal
    rw [Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    nlinarith [h2, hlog2]
  -- `e^{ρ/10} < 1.171875`, via a degree-5 Taylor bound at `0.1585`.
  have hexp_ub : Real.exp (nearCycleExp / 10) < 1171875 / 1000000 := by
    have hmono : Real.exp (nearCycleExp / 10) ≤ Real.exp (1585 / 10000) :=
      Real.exp_le_exp.mpr (by linarith [hρ_lt])
    have hbound : Real.exp (1585 / 10000 : ℝ) < 1171875 / 1000000 := by
      have h := Real.exp_bound (x := (1585 / 10000 : ℝ)) (by norm_num) (n := 5) (by norm_num)
      rw [abs_le] at h
      have hsum : ∑ i ∈ Finset.range 5, (1585 / 10000 : ℝ) ^ i / (Nat.factorial i) =
          1 + 1585 / 10000 + (1585 / 10000) ^ 2 / 2 + (1585 / 10000) ^ 3 / 6
            + (1585 / 10000) ^ 4 / 24 := by
        simp [Finset.sum_range_succ, Nat.factorial]
      rw [hsum] at h; norm_num at h; nlinarith [h.2]
    linarith [hmono, hbound]
  -- Combine: `2.56 < 3 / e^{ρ/10}` since `2.56 · 1.171875 = 3`.
  rw [hA]
  have hexppos : (0 : ℝ) < Real.exp (nearCycleExp / 10) := Real.exp_pos _
  have hrw : (3 : ℝ) * Real.exp (-(nearCycleExp / 10)) = 3 / Real.exp (nearCycleExp / 10) := by
    rw [Real.exp_neg]; ring
  rw [hrw, lt_div_iff₀ hexppos]
  nlinarith [hexp_ub]

/-- The base range of **Lemma B.1**: for `13 ≤ q ≤ 18` and every `j`, `|2ʲ − 3^q| > 2.56^q / 2`.

Proved directly (no `native_decide`, no configuration changes): for `j ≥ 30` the power `2ʲ`
overshoots `2·3^q` (as `2^30 > 2·3^18`), so `|Δ| = 2ʲ − 3^q > 3^q > 2.56^q`; the finitely many
`j ≤ 29` across `13 ≤ q ≤ 18` are discharged by `interval_cases` + `norm_num`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_lemma_b1"]
theorem nearCycle_small_q (j q : ℕ) (h1 : 13 ≤ q) (h2 : q ≤ 18) :
    (2.56 : ℝ) ^ q / 2 < |(2 : ℝ) ^ j - 3 ^ q| := by
  by_cases hj : j ≤ 29
  · -- Finite check for `j ≤ 29`, `13 ≤ q ≤ 18` (180 cases).
    interval_cases q <;> interval_cases j <;> (rw [lt_abs]; norm_num)
  · -- `j ≥ 30`: `2ʲ ≥ 2^30 > 2·3^18 ≥ 2·3^q`, so `|Δ| = 2ʲ − 3^q > 3^q > 2.56^q`.
    have hj30 : 30 ≤ j := by omega
    have h2j : (2 : ℝ) ^ 30 ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj30
    have h3q18 : (3 : ℝ) ^ q ≤ (3 : ℝ) ^ 18 := pow_le_pow_right₀ (by norm_num) h2
    have hkey : (2 : ℝ) * 3 ^ q < 2 ^ j := by
      have h30 : (2 : ℝ) * 3 ^ 18 < 2 ^ 30 := by norm_num
      calc (2 : ℝ) * 3 ^ q ≤ 2 * 3 ^ 18 := by linarith [h3q18]
        _ < 2 ^ 30 := h30
        _ ≤ 2 ^ j := h2j
    have h3qpos : (0 : ℝ) < 3 ^ q := by positivity
    have habs : |(2 : ℝ) ^ j - 3 ^ q| = (2 : ℝ) ^ j - 3 ^ q := by
      rw [abs_of_pos]; linarith [hkey, h3qpos]
    rw [habs]
    have h256 : (2.56 : ℝ) ^ q < 3 ^ q := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have h256pos : (0 : ℝ) < (2.56 : ℝ) ^ q := by positivity
    linarith [hkey, h256, h256pos]

/-- **Lemma B.1** ([Roz25], Appendix B, eq. (24)).  For every positive integer `j` and every
integer `q > 12`, the prime powers `2ʲ` and `3^q` satisfy `|2ʲ − 3^q| > 2.56^q / 2`.  (The bound
holds for all `j : ℕ`; the paper states it for positive `j`.)

Proof: for `13 ≤ q ≤ 18` this is the base range `nearCycle_small_q`.  For `q ≥ 19` split
on the size of `3^q` relative to `2ʲ` and `2^{j+1}`; the first two cases invoke Ellison's bound
`Ellison.pillai_lower_bound` (which forces `j ≥ 28` here) together with `A = c^ρ > 2.56`
(`nearCycleConst_gt`), the third is elementary. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_lemma_b1"]
theorem nearCycle_lower_bound (j q : ℕ) (hq : 12 < q) :
    (2.56 : ℝ) ^ q / 2 < |(2 : ℝ) ^ j - 3 ^ q| := by
  by_cases hq18 : q ≤ 18
  · exact nearCycle_small_q j q (by omega) hq18
  · have hq19 : 19 ≤ q := by omega
    -- The constants `c`, `A` and their basic estimates `1 < c < 2`, `0 < A`.
    have hc0 : (0 : ℝ) < nearCycleBase := by unfold nearCycleBase; positivity
    have hc1 : (1 : ℝ) < nearCycleBase := by
      unfold nearCycleBase
      have : (0.9 : ℝ) ≤ Real.exp (-(1 / 10)) := by nlinarith [Real.add_one_le_exp (-(1 / 10 : ℝ))]
      nlinarith [this]
    have hc2 : nearCycleBase < 2 := by
      unfold nearCycleBase
      have h : Real.exp (-(1 / 10)) < 1 := by
        have := Real.exp_lt_exp.mpr (show (-(1 / 10) : ℝ) < 0 by norm_num)
        rwa [Real.exp_zero] at this
      nlinarith [h]
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    -- `c^(j:ℝ) = 2ʲ · e^{−j/10}`, the right-hand side of Ellison's bound.
    have hcj_eq : nearCycleBase ^ (j : ℝ) = (2 : ℝ) ^ j * Real.exp (-(j : ℝ) / 10) := by
      rw [Real.rpow_natCast]; unfold nearCycleBase; rw [mul_pow, ← Real.exp_nat_mul]
      rw [show (j : ℝ) * (-(1 / 10)) = -(j : ℝ) / 10 from by ring]
    have hA0 : (0 : ℝ) < nearCycleConst := by unfold nearCycleConst; positivity
    have h256Aq : (2.56 : ℝ) ^ q < nearCycleConst ^ q :=
      pow_lt_pow_left₀ nearCycleConst_gt (by norm_num) (by omega)
    have h256pos : (0 : ℝ) < (2.56 : ℝ) ^ q := by positivity
    by_cases hcase1 : (3 : ℕ) ^ q ≤ 2 ^ j
    · -- Case 1: `3^q ≤ 2ʲ`.  Then `A^q = c^{ρq} ≤ cʲ < |Δ|`.
      have hj28 : 28 ≤ j := by
        have hb : (3 : ℕ) ^ 19 ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h30 : (2 : ℕ) ^ 30 < 2 ^ j := by
          calc (2 : ℕ) ^ 30 < 3 ^ 19 := by norm_num
            _ ≤ 3 ^ q := hb
            _ ≤ 2 ^ j := hcase1
        have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h30
        omega
      have h3q2j : (3 : ℝ) ^ q ≤ (2 : ℝ) ^ j := by exact_mod_cast hcase1
      have hqρ : (q : ℝ) * nearCycleExp ≤ (j : ℝ) := by
        have hle := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ q) h3q2j
        rw [Real.log_pow, Real.log_pow] at hle
        have hρ : nearCycleExp = Real.log 3 / Real.log 2 := rfl
        rw [hρ, ← mul_div_assoc, div_le_iff₀ hlog2]
        linarith [hle]
      have hcore : nearCycleConst ^ q ≤ (2 : ℝ) ^ j * Real.exp (-(j : ℝ) / 10) := by
        have hAq : nearCycleConst ^ q = nearCycleBase ^ ((q : ℝ) * nearCycleExp) := by
          unfold nearCycleConst
          rw [← Real.rpow_natCast (nearCycleBase ^ nearCycleExp) q,
            ← Real.rpow_mul (le_of_lt hc0), mul_comm nearCycleExp]
        have hmono : nearCycleBase ^ ((q : ℝ) * nearCycleExp) ≤ nearCycleBase ^ (j : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (le_of_lt hc1) hqρ
        rw [hAq, ← hcj_eq]; exact hmono
      linarith [hcore, Ellison.pillai_lower_bound j q hj28, h256Aq, h256pos]
    · push Not at hcase1
      by_cases hcase2 : (3 : ℕ) ^ q ≤ 2 ^ (j + 1)
      · -- Case 2: `2ʲ < 3^q ≤ 2^{j+1}`.  Then `A^q / 2 < A^q / c = c^{ρq−1} ≤ cʲ < |Δ|`.
        have hj28 : 28 ≤ j := by
          have hb : (3 : ℕ) ^ 19 ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h30 : (2 : ℕ) ^ 30 < 2 ^ (j + 1) := by
            calc (2 : ℕ) ^ 30 < 3 ^ 19 := by norm_num
              _ ≤ 3 ^ q := hb
              _ ≤ 2 ^ (j + 1) := hcase2
          have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h30
          omega
        have h3q2j1 : (3 : ℝ) ^ q ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast hcase2
        have hqρ2 : (q : ℝ) * nearCycleExp ≤ (j : ℝ) + 1 := by
          have hle := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ q) h3q2j1
          rw [Real.log_pow, Real.log_pow] at hle
          have hρ : nearCycleExp = Real.log 3 / Real.log 2 := rfl
          rw [hρ, ← mul_div_assoc, div_le_iff₀ hlog2]
          push_cast at hle ⊢; linarith [hle]
        have hcore2 : nearCycleConst ^ q / nearCycleBase ≤ (2 : ℝ) ^ j * Real.exp (-(j : ℝ) / 10) := by
          have hexp : (q : ℝ) * nearCycleExp - 1 ≤ (j : ℝ) := by linarith [hqρ2]
          have hmono : nearCycleBase ^ ((q : ℝ) * nearCycleExp - 1) ≤ nearCycleBase ^ (j : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (le_of_lt hc1) hexp
          have heq : nearCycleBase ^ ((q : ℝ) * nearCycleExp - 1)
              = nearCycleConst ^ q / nearCycleBase := by
            rw [Real.rpow_sub hc0, Real.rpow_one]
            congr 1
            unfold nearCycleConst
            rw [← Real.rpow_natCast (nearCycleBase ^ nearCycleExp) q,
              ← Real.rpow_mul (le_of_lt hc0), mul_comm nearCycleExp]
          rw [heq, hcj_eq] at hmono; exact hmono
        have hstep : (2.56 : ℝ) ^ q / 2 < nearCycleConst ^ q / nearCycleBase := by
          have hAqpos : (0 : ℝ) < nearCycleConst ^ q := by positivity
          have h1 : nearCycleConst ^ q / 2 < nearCycleConst ^ q / nearCycleBase := by
            rw [div_lt_div_iff₀ (by norm_num) hc0]; nlinarith [hAqpos, hc2]
          have h2 : (2.56 : ℝ) ^ q / 2 < nearCycleConst ^ q / 2 := by linarith [h256Aq]
          linarith [h1, h2]
        linarith [hcore2, Ellison.pillai_lower_bound j q hj28, hstep]
      · -- Case 3: `2^{j+1} < 3^q`.  Then `|Δ| = 3^q − 2ʲ > 3^q / 2 > 2.56^q / 2`.
        push Not at hcase2
        have h2j1 : (2 : ℝ) ^ (j + 1) < (3 : ℝ) ^ q := by exact_mod_cast hcase2
        have h2j : (2 : ℝ) ^ j < (3 : ℝ) ^ q / 2 := by rw [pow_succ] at h2j1; linarith [h2j1]
        have hneg : (2 : ℝ) ^ j - 3 ^ q < 0 := by
          have : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
          linarith [h2j]
        have hDeq : |(2 : ℝ) ^ j - 3 ^ q| = (3 : ℝ) ^ q - 2 ^ j := by rw [abs_of_neg hneg]; ring
        have h256lt3 : (2.56 : ℝ) ^ q < (3 : ℝ) ^ q :=
          pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
        rw [hDeq]; linarith [h2j, h256lt3]

/-! ## The Rhin companion bound (`plan-formalize-logforms.html` M-5, F-5b) -/

/-- Elementary: `|x| e^{−|x|} ≤ |e^x − 1|` for every real `x` (the exponential is at
least linear away from `0`).  The small-`Λ` half of `nearCycle_rhin_bound`. -/
private lemma abs_exp_sub_one_ge (x : ℝ) :
    |x| * Real.exp (-|x|) ≤ |Real.exp x - 1| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx,
      abs_of_nonneg (by linarith [Real.add_one_le_exp x] : (0 : ℝ) ≤ Real.exp x - 1)]
    have h1 : Real.exp (-x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h2 : x * Real.exp (-x) ≤ x * 1 := mul_le_mul_of_nonneg_left h1 hx
    linarith [h2, Real.add_one_le_exp x]
  · rw [abs_of_neg hx]
    have hexp1 : Real.exp x < 1 := by rw [Real.exp_lt_one_iff]; exact hx
    rw [abs_of_neg (by linarith [hexp1] : Real.exp x - 1 < 0), neg_neg]
    have h := Real.add_one_le_exp (-x)
    have hepos : (0 : ℝ) < Real.exp x := Real.exp_pos x
    have hmul : (-x + 1) * Real.exp x ≤ 1 := by
      calc (-x + 1) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
            mul_le_mul_of_nonneg_right h (le_of_lt hepos)
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [hmul]

/-- Elementary: `1 − 1/e ≤ |e^x − 1|` once `|x| ≥ 1` (the exponential is bounded away
from `1` outside `(−1, 1)`).  The large-`Λ` half of `nearCycle_rhin_bound`. -/
private lemma abs_exp_sub_one_ge_one (x : ℝ) (hx : 1 ≤ |x|) :
    1 - (Real.exp 1)⁻¹ ≤ |Real.exp x - 1| := by
  have hinvpos : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr (Real.exp_pos 1)
  rcases le_abs.mp hx with hpos | hneg
  · rw [abs_of_nonneg (by nlinarith [Real.add_one_le_exp x] : (0 : ℝ) ≤ Real.exp x - 1)]
    have hexp : Real.exp 1 ≤ Real.exp x := Real.exp_le_exp.mpr hpos
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    linarith [hexp, hinvpos, he2]
  · have hxle : x ≤ -1 := by linarith
    have hexp : Real.exp x ≤ Real.exp (-1) := Real.exp_le_exp.mpr hxle
    have hexpinv : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
    have hx1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonpos (by linarith : Real.exp x - 1 ≤ 0)]
    linarith [hexp, hexpinv]

/-- **The Rhin near-cycle bound** ([Rhi87], `plan-formalize-logforms.html` M-5, F-5b): a proved
companion to `nearCycle_lower_bound` (Lemma B.1) resting on Rhin's linear-form estimate
(`CITED/RhinLogForm.lean`) instead of Ellison's.  For every `j, q` with `max(j, q) ≥ 2`,

  `|2ʲ − 3^q| ≥ (3^q / e) · max(j, q)^(−13.3)`.

Proof: with `Λ = j·log 2 − q·log 3`, one has `2ʲ − 3^q = 3^q(e^Λ − 1)`; Rhin's
`Rhin.logForm_lower_bound` gives `|Λ| ≥ max(j,q)^(−13.3)`, converted to the gap by the elementary
`abs_exp_sub_one_ge` (`|Λ| ≤ 1`) and `abs_exp_sub_one_ge_one` (`|Λ| ≥ 1`).  The loss factor is
**polynomial** `max(j,q)^{−13.3}` where Ellison's bound loses an **exponential** `e^{−j/10}`
(`nearCycle_lower_bound`): the two are complementary — this wins for `q ≳ 550`, Ellison for small
`q`, and `Ellison.pillai_lower_bound` is untouched ([Roz25] App B cites it).  Footprint
std3 + [Rhi87] only — no new axiom. -/
@[category research solved, AMS 11 37, ref "Rhi87", group "roz_lemma_b1"]
theorem nearCycle_rhin_bound (j q : ℕ) (hH : 2 ≤ max j q) :
    (3 : ℝ) ^ q / Real.exp 1 * ((max j q : ℕ) : ℝ) ^ (-(13.3 : ℝ))
      ≤ |(2 : ℝ) ^ j - 3 ^ q| := by
  set H : ℝ := ((max j q : ℕ) : ℝ) with hHdef
  have hH2 : 2 ≤ H := by rw [hHdef]; exact_mod_cast hH
  -- ## the linear form `Λ = j·log 2 − q·log 3` and its Rhin lower bound
  set Λ : ℝ := (j : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3 with hΛdef
  have hHeight : Rhin.logHeight (j : ℤ) (-(q : ℤ)) = ((max j q : ℕ) : ℤ) := by
    unfold Rhin.logHeight
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (j : ℤ)), abs_neg,
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ)), Nat.cast_max]
  have hHge2 : 2 ≤ Rhin.logHeight (j : ℤ) (-(q : ℤ)) := by rw [hHeight]; exact_mod_cast hH
  have hForm : Rhin.logForm 0 (j : ℤ) (-(q : ℤ)) = Λ := by
    rw [hΛdef]; unfold Rhin.logForm; push_cast; ring
  have hcastH : ((Rhin.logHeight (j : ℤ) (-(q : ℤ)) : ℤ) : ℝ) = H := by
    rw [hHeight, hHdef]; push_cast; ring
  have hRhin : H ^ (-(13.3 : ℝ)) ≤ |Λ| := by
    have h := Rhin.logForm_lower_bound 0 (j : ℤ) (-(q : ℤ)) hHge2
    rwa [hForm, hcastH] at h
  -- ## the factorization `2ʲ − 3^q = 3^q(e^Λ − 1)`
  have e2 : Real.exp ((j : ℝ) * Real.log 2) = (2 : ℝ) ^ j := by
    rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  have e3 : Real.exp ((q : ℝ) * Real.log 3) = (3 : ℝ) ^ q := by
    rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_natCast]
  have h3q : (3 : ℝ) ^ q ≠ 0 := by positivity
  have hΛexp : (3 : ℝ) ^ q * Real.exp Λ = (2 : ℝ) ^ j := by
    rw [hΛdef, Real.exp_sub, e2, e3]; field_simp
  have hfactor : (2 : ℝ) ^ j - 3 ^ q = 3 ^ q * (Real.exp Λ - 1) := by
    rw [mul_sub, hΛexp, mul_one]
  have habs : |(2 : ℝ) ^ j - 3 ^ q| = 3 ^ q * |Real.exp Λ - 1| := by
    rw [hfactor, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ q)]
  -- ## `H^(−13.3) / e ≤ |e^Λ − 1|`
  have hHpow_le1 : H ^ (-(13.3 : ℝ)) ≤ 1 := by
    rw [← Real.rpow_zero H]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hkey : H ^ (-(13.3 : ℝ)) / Real.exp 1 ≤ |Real.exp Λ - 1| := by
    rcases le_or_gt (|Λ|) 1 with hle | hgt
    · -- `|Λ| ≤ 1`: `H^(−13.3)/e ≤ |Λ|/e ≤ |Λ| e^{−|Λ|} ≤ |e^Λ − 1|`.
      have hhelp := abs_exp_sub_one_ge Λ
      have he : (Real.exp 1)⁻¹ ≤ Real.exp (-|Λ|) := by
        rw [← Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith)
      have h1 : |Λ| * (Real.exp 1)⁻¹ ≤ |Λ| * Real.exp (-|Λ|) :=
        mul_le_mul_of_nonneg_left he (abs_nonneg _)
      have h2 : H ^ (-(13.3 : ℝ)) * (Real.exp 1)⁻¹ ≤ |Λ| * (Real.exp 1)⁻¹ :=
        mul_le_mul_of_nonneg_right hRhin (by positivity)
      calc H ^ (-(13.3 : ℝ)) / Real.exp 1
          = H ^ (-(13.3 : ℝ)) * (Real.exp 1)⁻¹ := div_eq_mul_inv _ _
        _ ≤ |Λ| * (Real.exp 1)⁻¹ := h2
        _ ≤ |Λ| * Real.exp (-|Λ|) := h1
        _ ≤ |Real.exp Λ - 1| := hhelp
    · -- `|Λ| ≥ 1`: `H^(−13.3)/e ≤ 1/e ≤ 1 − 1/e ≤ |e^Λ − 1|`.
      have hge := abs_exp_sub_one_ge_one Λ (le_of_lt hgt)
      have hstep : H ^ (-(13.3 : ℝ)) / Real.exp 1 ≤ (Real.exp 1)⁻¹ := by
        rw [div_eq_mul_inv]
        calc H ^ (-(13.3 : ℝ)) * (Real.exp 1)⁻¹ ≤ 1 * (Real.exp 1)⁻¹ :=
              mul_le_mul_of_nonneg_right hHpow_le1 (by positivity)
          _ = (Real.exp 1)⁻¹ := one_mul _
      have hinvle : (Real.exp 1)⁻¹ ≤ 1 - (Real.exp 1)⁻¹ := by
        have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
        have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h2inv : 2 * (Real.exp 1)⁻¹ ≤ 1 := by rw [mul_inv_le_iff₀ hpos]; linarith
        linarith [h2inv]
      linarith [hstep, hinvle, hge]
  -- ## combine
  rw [habs]
  calc (3 : ℝ) ^ q / Real.exp 1 * H ^ (-(13.3 : ℝ))
      = 3 ^ q * (H ^ (-(13.3 : ℝ)) / Real.exp 1) := by ring
    _ ≤ 3 ^ q * |Real.exp Λ - 1| := mul_le_mul_of_nonneg_left hkey (by positivity)

end RT
