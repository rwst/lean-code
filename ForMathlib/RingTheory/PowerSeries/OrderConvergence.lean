/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Topology.Instances.ENat

/-!
# Coefficientwise stabilisation from order convergence of power series

`PowerSeries.TendstoFormal F G` is **convergence of a sequence of formal power series** in the
`X`-adic (order) topology: the order of the difference `G - F n` tends to `⊤` in `ℕ∞`
(`tendstoFormal_iff` restates it bound-by-bound, as in Bertin [Ber92], Chapter 2).  Its consequence
`PowerSeries.coeff_eventuallyEq_of_order_tendsto_top`: under that convergence every fixed coefficient
eventually stabilises — for each `m`, `coeff m (F n) = coeff m G` for all large `n`. This is the
order-function form of convergence in the coefficientwise (product) topology; the proof reads
`coeff m (G - F n) = 0` off `PowerSeries.coeff_of_lt_order` once the order exceeds `m`.

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open Filter Topology
open scoped PowerSeries

namespace PowerSeries

variable {R : Type*} [Ring R]

/-- **Convergence of a sequence of formal power series** (Bertin [Ber92]). A sequence `(Fₙ)` in
`R⟦X⟧` *converges to* `G` when the order of the difference tends to infinity, `ord (G - Fₙ) → ⊤` —
i.e. `G - Fₙ` agrees with `0` to ever higher order.  This is convergence in the `X`-adic topology;
see `tendstoFormal_iff` for the book's bound-by-bound phrasing, and
`coeff_eventuallyEq_of_order_tendsto_top` for the resulting coefficientwise stabilisation. -/
def TendstoFormal (F : ℕ → R⟦X⟧) (G : R⟦X⟧) : Prop :=
  Tendsto (fun n => (G - F n).order) atTop (𝓝 ⊤)

/-- Bertin's bound-by-bound form of `ord (G - Fₙ) → ⊤`: the sequence `(Fₙ)` converges to `G` iff for
every `N : ℕ`, eventually `ord (G - Fₙ) > N`. -/
theorem tendstoFormal_iff (F : ℕ → R⟦X⟧) (G : R⟦X⟧) :
    TendstoFormal F G ↔ ∀ N : ℕ, ∀ᶠ n in atTop, (N : ℕ∞) < (G - F n).order := by
  rw [TendstoFormal, nhds_top_basis.tendsto_right_iff]
  constructor
  · intro h N
    exact h (N : ℕ∞) (WithTop.coe_lt_top N)
  · intro h a ha
    obtain ⟨N, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt ha)
    filter_upwards [h N] with n hn using hn

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
