/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Topology.Instances.ENat

/-!
# Coefficientwise stabilisation from order convergence of power series

`PowerSeries.coeff_eventuallyEq_of_order_tendsto_top`: if a sequence `F` of formal power series
converges to `G` in the `X`-adic (order) topology — the order of the difference `G - F n` tends to
`⊤` in `ℕ∞` — then every fixed coefficient eventually stabilises: for each `m`,
`coeff m (F n) = coeff m G` for all large `n`. This is the order-function form of convergence in the
coefficientwise (product) topology; the proof reads `coeff m (G - F n) = 0` off
`PowerSeries.coeff_of_lt_order` once the order exceeds `m`.
-/

open Filter Topology
open scoped PowerSeries

namespace PowerSeries

variable {R : Type*} [Ring R]

/-- If the order of `G - F n` tends to `⊤` (convergence of `F` to `G` in the `X`-adic topology), then
each coefficient eventually stabilises: for every `m`, `coeff m (F n) = coeff m G` for all large `n`.
-/
theorem coeff_eventuallyEq_of_order_tendsto_top {F : ℕ → R⟦X⟧} {G : R⟦X⟧}
    (h : Tendsto (fun n => (G - F n).order) atTop (𝓝 ⊤)) (m : ℕ) :
    ∀ᶠ n in atTop, (coeff m) (F n) = (coeff m) G := by
  have hev : ∀ᶠ n in atTop, (m : ℕ∞) < (G - F n).order :=
    h.eventually (Ioi_mem_nhds (WithTop.coe_lt_top m))
  filter_upwards [hev] with n hn
  have hz : (coeff m) G - (coeff m) (F n) = 0 := by
    rw [← map_sub]; exact coeff_of_lt_order m hn
  exact (sub_eq_zero.mp hz).symm

end PowerSeries
