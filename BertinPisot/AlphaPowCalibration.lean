/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# A calibration lemma for the proof of Theorem 5.1.1 (Bertin §5.1)

Bertin's (unnumbered) **Lemma** of §5.1 (*Pisot and Salem Numbers*, [Ber92]), supplying the two
inequalities (6) and (7) used to calibrate the recurrence length and the coefficient bound in the
proof of Theorem 5.1.1.

Let `0 < ρ < 1/e` and let `r` be the (unique) integer with `1/(ρe) - 1 ≤ r < 1/(ρe)`. Then
* **(6)** `(r + 1) · log(ρ(r + 1)) < ρe - 1/(ρe)`,
* **(7)** `r · log(ρ(r + 1)) < ρe - 1/(ρe) + 1`.

**Proof idea.** The function `x ↦ x · log(ρx)` is convex with derivative `log(ρx) + 1`, hence attains
its global minimum `-1/(ρe)` at `x = 1/(ρe)` and is increasing on `[1/(ρe), ∞)`. From
`1/(ρe) ≤ r + 1 < 1/(ρe) + 1` and that monotonicity,
`(r+1) log(ρ(r+1)) ≤ (1/(ρe)+1)·log(ρ(1/(ρe)+1)) = (1/(ρe)+1)(log(1+ρe) - 1)`. The elementary
inequality `log x < x - 1` applied to `x = 1 + ρe` gives `log(1+ρe) - 1 < ρe - 1`, and
`(1/(ρe)+1)(ρe - 1) = ρe - 1/(ρe)`, proving (6). Subtracting one copy of `log(ρ(r+1))` and using
`ρ(r+1) ≥ 1/e`, i.e. `log(ρ(r+1)) ≥ -1`, yields (7).

This is the analytic heart of the calibration step (c) in the proof of Theorem 5.1.1
(`Bertin.AlphaPow.pisotSalem_theorem_5_1_1'`): with `ρ ≈ 1/(2eα(1+log λ))` and `r ≈ s`, the minimum
`-1/(ρe)` is what produces the `2e`-type constant tuning the recurrence length `s` and the
coefficient bound `A`. The lemma is proved here in full (no `sorry`, no extra axioms).

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.1.
-/

open Real Set

namespace Bertin.AlphaPow

/-- **Calibration lemma (Bertin §5.1, inequalities (6) and (7)).** For real `ρ` with `0 < ρ < 1/e`
and an integer `r` with `1/(ρe) - 1 ≤ r < 1/(ρe)`:
* (6) `(r + 1) · log(ρ(r + 1)) < ρe - 1/(ρe)`;
* (7) `r · log(ρ(r + 1)) < ρe - 1/(ρe) + 1`.

The function `x ↦ x · log(ρx)` has minimum `-1/(ρe)` at `x = 1/(ρe)`; combined with `log x < x - 1`
this gives both bounds. -/
@[category research solved, AMS 11, ref "Ber92"]
theorem calib_log_estimate (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / Real.exp 1) (r : ℕ)
    (hr_lo : 1 / (ρ * Real.exp 1) - 1 ≤ (r : ℝ)) (hr_hi : (r : ℝ) < 1 / (ρ * Real.exp 1)) :
    ((r : ℝ) + 1) * Real.log (ρ * ((r : ℝ) + 1)) < ρ * Real.exp 1 - 1 / (ρ * Real.exp 1) ∧
      (r : ℝ) * Real.log (ρ * ((r : ℝ) + 1)) <
        ρ * Real.exp 1 - 1 / (ρ * Real.exp 1) + 1 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hρe : 0 < ρ * Real.exp 1 := mul_pos hρ0 he
  have hρe1 : ρ * Real.exp 1 < 1 := (lt_div_iff₀ he).mp hρ1
  set m := 1 / (ρ * Real.exp 1) with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hm1 : 1 < m := by rw [hm]; exact (one_lt_div hρe).mpr hρe1
  set y : ℝ := (r : ℝ) + 1 with hy
  have hy_lo : m ≤ y := by rw [hy]; linarith [hr_lo]
  have hy_hi : y < m + 1 := by rw [hy]; linarith [hr_hi]
  have hy0 : 0 < y := by linarith
  have hρy : 0 < ρ * y := mul_pos hρ0 hy0
  -- The function `x ↦ x · log(ρx)` is increasing on `[1/(ρe), ∞)` (minimum at `1/(ρe)`).
  have hmono : MonotoneOn (fun x => x * Real.log (ρ * x)) (Set.Ici m) := by
    have hd : ∀ x : ℝ, 0 < x →
        HasDerivAt (fun x => x * Real.log (ρ * x)) (Real.log (ρ * x) + 1) x := by
      intro x hx0
      have hρx : ρ * x ≠ 0 := (mul_pos hρ0 hx0).ne'
      have h1 : HasDerivAt (fun x => ρ * x) ρ x := by simpa using (hasDerivAt_id' x).const_mul ρ
      have h2 : HasDerivAt (fun x => Real.log (ρ * x)) ((ρ * x)⁻¹ * ρ) x :=
        (Real.hasDerivAt_log hρx).comp x h1
      have h3 : HasDerivAt (fun x => x * Real.log (ρ * x))
          (1 * Real.log (ρ * x) + x * ((ρ * x)⁻¹ * ρ)) x := (hasDerivAt_id' x).mul h2
      convert h3 using 1
      field_simp
    have hcont : ContinuousOn (fun x => x * Real.log (ρ * x)) (Set.Ici m) := by
      apply ContinuousOn.mul continuousOn_id
      apply ContinuousOn.log (continuousOn_const.mul continuousOn_id)
      intro x hx
      exact (mul_pos hρ0 (lt_of_lt_of_le hm0 hx)).ne'
    apply monotoneOn_of_deriv_nonneg (convex_Ici m) hcont
    · intro x hx
      rw [interior_Ici] at hx
      exact (hd x (lt_trans hm0 hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans hm0 hx
      rw [(hd x hx0).deriv]
      have hρm : ρ * m = Real.exp (-1) := by rw [hm, Real.exp_neg]; field_simp
      have hexp : Real.exp (-1) < ρ * x := by rw [← hρm]; exact mul_lt_mul_of_pos_left hx hρ0
      have hlog := Real.log_lt_log (Real.exp_pos (-1)) hexp
      rw [Real.log_exp] at hlog
      linarith
  -- Evaluate at the right endpoint `m + 1 = 1/(ρe) + 1`.
  have hfle : y * Real.log (ρ * y) ≤ (m + 1) * Real.log (ρ * (m + 1)) :=
    hmono (Set.mem_Ici.mpr hy_lo) (Set.mem_Ici.mpr (by linarith)) hy_hi.le
  have hρM : ρ * (m + 1) = (1 + ρ * Real.exp 1) / Real.exp 1 := by rw [hm]; field_simp
  have hlogM : Real.log (ρ * (m + 1)) = Real.log (1 + ρ * Real.exp 1) - 1 := by
    rw [hρM, Real.log_div (by positivity) he.ne', Real.log_exp]
  have hlog_lt : Real.log (1 + ρ * Real.exp 1) < ρ * Real.exp 1 := by
    have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 1 + ρ * Real.exp 1 by positivity)
      (lt_add_of_pos_right 1 hρe).ne'
    linarith
  have hmρe : m * (ρ * Real.exp 1) = 1 := by rw [hm]; field_simp
  -- Inequality (6).
  have hsix : y * Real.log (ρ * y) < ρ * Real.exp 1 - m := by
    have h1 : (m + 1) * (Real.log (1 + ρ * Real.exp 1) - 1) <
        (m + 1) * (ρ * Real.exp 1 - 1) :=
      mul_lt_mul_of_pos_left (by linarith) (by linarith)
    have h2 : (m + 1) * (ρ * Real.exp 1 - 1) = ρ * Real.exp 1 - m := by nlinarith [hmρe]
    rw [hlogM] at hfle
    linarith
  refine ⟨hsix, ?_⟩
  -- Inequality (7): subtract one `log(ρ(r+1))`, bounded below by `-1` since `ρ(r+1) ≥ 1/e`.
  have hρm : ρ * m = Real.exp (-1) := by rw [hm, Real.exp_neg]; field_simp
  have hlogy_ge : -1 ≤ Real.log (ρ * y) := by
    rw [← Real.log_exp (-1)]
    apply Real.log_le_log (Real.exp_pos _)
    rw [← hρm]
    exact mul_le_mul_of_nonneg_left hy_lo hρ0.le
  have hexp7 : (r : ℝ) * Real.log (ρ * y) = y * Real.log (ρ * y) - Real.log (ρ * y) := by
    rw [hy]; ring
  linarith

end Bertin.AlphaPow
