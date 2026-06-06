/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Topology.Instances.ENat
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Formal power series: Taylor expansion, order, and convergence (Bertin, Chapter 2 intro)

The opening definitions of Bertin's chapter on compact families of rational functions
(*Pisot and Salem Numbers*, [Ber92]). The chapter studies families of rational functions with
coefficients in `ℤ` — for an algebraic number `θ` with minimal polynomial `P`, the function
`z ↦ P(z) / P⋆(z)` (`P⋆` the reciprocal polynomial) — and exhibits compact sets of them for the
topology of uniform convergence on the compacts of the unit disk `D(0,1)`. Three foundational
notions are recalled here.

* `Complex.taylorSeries f` — the **Taylor expansion** `S(f) ∈ ℂ⟦X⟧` of `f : ℂ → ℂ`, the formal power
  series whose `n`-th coefficient is `f⁽ⁿ⁾(0) / n!` (`taylorSeries_coeff`). Bertin introduces `S(f)`
  for `f` analytic in a neighborhood of `0`; we define it as the total Taylor-coefficient map, which
  on those `f` coincides with their convergent power-series expansion: if `f` has `∑ aₙ zⁿ` as its
  power series on a ball, then `S(f) = ∑ aₙ Xⁿ` (`taylorSeries_eq_mk`).
* **order** `ord G` is Mathlib's `PowerSeries.order`: for `G = ∑ aₙ Xⁿ`, `ord G = inf {n | aₙ ≠ 0}`,
  with `ord 0 = ⊤` (`= +∞`, `PowerSeries.order_zero`) and `ord G = ⊤ ↔ G = 0`
  (`PowerSeries.order_eq_top`). No redefinition is needed; the name `ord` from the book is exactly
  this `ℕ∞`-valued order.
* `PowerSeries.TendstoFormal F G` — **convergence of a sequence of formal series**: Bertin declares
  `(Fₙ) → F` in `ℂ⟦X⟧` iff `ord (F - Fₙ) → +∞`. This is convergence in the `X`-adic (order)
  topology; `tendstoFormal_iff` restates it as the book's condition, that for every bound `N` the
  order `ord (F - Fₙ)` eventually exceeds `N`. Stated over a general ring `R` (Bertin takes `R = ℂ`).

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open scoped PowerSeries
open Filter Topology

namespace Complex

/-- **Taylor expansion** `S(f)` of a function `f : ℂ → ℂ`: the formal power series in `ℂ⟦X⟧` whose
`n`-th coefficient is `f⁽ⁿ⁾(0) / n!` (`taylorSeries_coeff`). Bertin denotes it `S(f)` and defines it
for `f` analytic near `0`; this total Taylor-coefficient map agrees with the analytic power-series
expansion on exactly those functions (`taylorSeries_eq_mk`). -/
@[category API, AMS 30, ref "Ber92"]
noncomputable def taylorSeries (f : ℂ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- The `n`-th coefficient of the Taylor expansion `S(f)` is `f⁽ⁿ⁾(0) / n!`. -/
@[category API, AMS 30, ref "Ber92"]
theorem taylorSeries_coeff (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  rw [taylorSeries, PowerSeries.coeff_mk]

/-- If `f` is analytic near `0` with power-series expansion `∑ aₙ zⁿ` on a ball
(`HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 ρ`), then its Taylor expansion `S(f)` is the formal
series `∑ aₙ Xⁿ` of those coefficients: `S(f) = mk a`. This identifies the total Taylor-coefficient
map of `taylorSeries` with the convergent expansion used elsewhere in the development. -/
@[category API, AMS 30, ref "Ber92"]
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

namespace PowerSeries

/-- **Convergence of a sequence of formal power series** (Bertin). A sequence `(Fₙ)` in `R⟦X⟧`
*converges to* `G` when the order of the difference tends to infinity, `ord (G - Fₙ) → +∞` — i.e.
`G - Fₙ` agrees with `0` to ever higher order. This is convergence in the `X`-adic topology; Bertin
states it for `R = ℂ`. See `tendstoFormal_iff` for the book's bound-by-bound phrasing. -/
@[category API, AMS 13, ref "Ber92"]
def TendstoFormal {R : Type*} [Ring R] (F : ℕ → R⟦X⟧) (G : R⟦X⟧) : Prop :=
  Tendsto (fun n => (G - F n).order) atTop (𝓝 ⊤)

/-- Bertin's bound-by-bound form of `ord (G - Fₙ) → +∞`: the sequence `(Fₙ)` converges to `G` iff
for every `N : ℕ`, eventually `ord (G - Fₙ) > N`. -/
@[category API, AMS 13, ref "Ber92"]
theorem tendstoFormal_iff {R : Type*} [Ring R] (F : ℕ → R⟦X⟧) (G : R⟦X⟧) :
    TendstoFormal F G ↔ ∀ N : ℕ, ∀ᶠ n in atTop, (N : ℕ∞) < (G - F n).order := by
  rw [TendstoFormal, nhds_top_basis.tendsto_right_iff]
  constructor
  · intro h N
    exact h (N : ℕ∞) (WithTop.coe_lt_top N)
  · intro h a ha
    obtain ⟨N, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt ha)
    filter_upwards [h N] with n hn using hn

end PowerSeries
