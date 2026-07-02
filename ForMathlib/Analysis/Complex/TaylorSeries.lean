/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Taylor expansion of a complex function as a formal power series

For `f : ℂ → ℂ` we form the **Taylor expansion** `S(f) ∈ ℂ⟦X⟧`, the formal power series whose `n`-th
coefficient is `f⁽ⁿ⁾(0) / n!`.  It is defined as the total Taylor-coefficient map
`Complex.taylorSeries`, which on functions analytic near `0` coincides with their convergent
power-series expansion: if `f` has `∑ aₙ zⁿ` as its power series on a ball then `S(f) = ∑ aₙ Xⁿ`
(`Complex.taylorSeries_eq_mk`).

This is the opening notion of Bertin's chapter on compact families of rational functions
(*Pisot and Salem Numbers*, [Ber92], Chapter 2), where `S(f)` is introduced for `f` analytic in a
neighbourhood of `0`; it underlies the Schur-determinant data `δₙ(f) := δₙ(S(f))` studied in
`BertinPisot`.

## Contents
* `Complex.taylorSeries f` — the formal power series `∑ₙ (f⁽ⁿ⁾(0) / n!) Xⁿ`.
* `Complex.taylorSeries_coeff` — its `n`-th coefficient is `f⁽ⁿ⁾(0) / n!`.
* `Complex.taylorSeries_eq_mk` — for `f` analytic near `0` with power series `∑ aₙ zⁿ`, `S(f) = mk a`.

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open scoped PowerSeries

namespace Complex

/-- **Taylor expansion** `S(f)` of a function `f : ℂ → ℂ`: the formal power series in `ℂ⟦X⟧` whose
`n`-th coefficient is `f⁽ⁿ⁾(0) / n!` (`taylorSeries_coeff`).  Bertin denotes it `S(f)` and defines it
for `f` analytic near `0`; this total Taylor-coefficient map agrees with the analytic power-series
expansion on exactly those functions (`taylorSeries_eq_mk`). -/
noncomputable def taylorSeries (f : ℂ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- The `n`-th coefficient of the Taylor expansion `S(f)` is `f⁽ⁿ⁾(0) / n!`. -/
theorem taylorSeries_coeff (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  rw [taylorSeries, PowerSeries.coeff_mk]

/-- If `f` is analytic near `0` with power-series expansion `∑ aₙ zⁿ` on a ball
(`HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 ρ`), then its Taylor expansion `S(f)` is the formal
series `∑ aₙ Xⁿ` of those coefficients: `S(f) = mk a`.  This identifies the total Taylor-coefficient
map of `taylorSeries` with the convergent expansion used elsewhere in the development. -/
theorem taylorSeries_eq_mk {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ : ENNReal}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 ρ) :
    taylorSeries f = PowerSeries.mk a := by
  ext n
  rw [taylorSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hfs := hf.factorial_smul (1 : ℂ) n
  rw [FormalMultilinearSeries.ofScalars_apply_eq] at hfs
  rw [iteratedDeriv_eq_iteratedFDeriv]
  simp only [one_pow, smul_eq_mul, mul_one] at hfs ⊢
  rw [← hfs, nsmul_eq_mul, mul_comm, mul_div_assoc,
    div_self (by exact_mod_cast Nat.factorial_ne_zero n), mul_one]

end Complex
