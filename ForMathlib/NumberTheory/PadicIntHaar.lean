/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

/-!
# Haar measure of the level sets of `toZModPow` on `ℤ_[p]`

For a Haar probability measure `μ` on the `p`-adic integers `ℤ_[p]`, the residue map
`toZModPow n : ℤ_[p] → ZMod (pⁿ)` has level sets (fibers) of equal measure `p⁻ⁿ`:
the `pⁿ` fibers are translates of one another (cosets of `ker (toZModPow n) = pⁿ ℤ_[p]`, a closed
ball), they partition `ℤ_[p]`, and `μ` is translation-invariant, so each has measure `1/pⁿ`.

This is the statement that the first `n` base-`p` digits of a Haar-random `p`-adic integer are
uniformly distributed over `ZMod (pⁿ)` — equivalently, that the digits are i.i.d. uniform.

## Main result
* `PadicInt.measure_toZModPow_fiber` — `μ ((toZModPow n) ⁻¹' {c}) = (pⁿ)⁻¹`.
-/

namespace PadicInt

open MeasureTheory Metric
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime] [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]]

omit [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]] in
/-- The fiber `(toZModPow n) ⁻¹' {c}` is a translate of the kernel fiber by any representative `r`. -/
private theorem preimage_toZModPow_singleton_eq (n : ℕ) {c : ZMod (p ^ n)} {r : ℤ_[p]}
    (hr : toZModPow n r = c) :
    (toZModPow n) ⁻¹' {c} = (fun x => -r + x) ⁻¹' ((toZModPow n) ⁻¹' {0}) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, map_add, map_neg, hr]
  rw [neg_add_eq_zero, eq_comm]

/-- The kernel fiber `(toZModPow n) ⁻¹' {0}` is the closed ball of radius `p⁻ⁿ`, hence measurable. -/
private theorem measurableSet_toZModPow_ker (n : ℕ) :
    MeasurableSet ((toZModPow (p := p) n) ⁻¹' {0}) := by
  have h : (toZModPow (p := p) n) ⁻¹' {0} = {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ)} := by
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← RingHom.mem_ker, ker_toZModPow,
      Set.mem_setOf_eq]
    exact (norm_le_pow_iff_mem_span_pow x n).symm
  rw [h]
  exact (isClosed_le continuous_norm continuous_const).measurableSet

/-- Each fiber of `toZModPow n` is measurable. -/
private theorem measurableSet_toZModPow_fiber (n : ℕ) (c : ZMod (p ^ n)) :
    MeasurableSet ((toZModPow (p := p) n) ⁻¹' {c}) := by
  obtain ⟨r, hr⟩ := ZMod.ringHom_surjective (toZModPow n) c
  rw [preimage_toZModPow_singleton_eq n hr]
  exact (measurable_const_add (-r)) (measurableSet_toZModPow_ker n)

variable (μ : Measure ℤ_[p]) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Every fiber of `toZModPow n` has the same measure as the kernel fiber (translation invariance). -/
private theorem measure_toZModPow_fiber_eq_ker (n : ℕ) (c : ZMod (p ^ n)) :
    μ ((toZModPow n) ⁻¹' {c}) = μ ((toZModPow n) ⁻¹' {0}) := by
  obtain ⟨r, hr⟩ := ZMod.ringHom_surjective (toZModPow n) c
  rw [preimage_toZModPow_singleton_eq n hr]
  exact measure_preimage_add μ (-r) _

/-- **Haar measure of a `toZModPow` fiber.** For a Haar probability measure on `ℤ_[p]`, every fiber
`(toZModPow n) ⁻¹' {c}` has measure `p⁻ⁿ`. The `pⁿ` fibers are translates of one another and
partition `ℤ_[p]`, so each carries mass `1/pⁿ`. -/
theorem measure_toZModPow_fiber (n : ℕ) (c : ZMod (p ^ n)) :
    μ ((toZModPow n) ⁻¹' {c}) = ((p : ℝ≥0∞) ^ n)⁻¹ := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero Fact.out)⟩
  have hcover : ⋃ d : ZMod (p ^ n), (toZModPow n) ⁻¹' {d} = Set.univ := by
    rw [← Set.preimage_iUnion, show (⋃ d : ZMod (p ^ n), ({d} : Set (ZMod (p ^ n)))) = Set.univ from
      by ext y; simp, Set.preimage_univ]
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun d : ZMod (p ^ n) => (toZModPow n) ⁻¹' {d})) := by
    intro a b hab
    refine Set.disjoint_left.2 fun x hxa hxb => hab ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxa hxb
    exact hxa ▸ hxb
  have hsum : (1 : ℝ≥0∞) = (p : ℝ≥0∞) ^ n * μ ((toZModPow n) ⁻¹' {0}) := by
    calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
      _ = ∑' d : ZMod (p ^ n), μ ((toZModPow n) ⁻¹' {d}) := by
          rw [← hcover]; exact measure_iUnion hdisj (measurableSet_toZModPow_fiber n)
      _ = ∑ d : ZMod (p ^ n), μ ((toZModPow n) ⁻¹' {0}) := by
          rw [tsum_fintype]
          exact Finset.sum_congr rfl fun d _ => measure_toZModPow_fiber_eq_ker μ n d
      _ = (p : ℝ≥0∞) ^ n * μ ((toZModPow n) ⁻¹' {0}) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_pow]
  rw [measure_toZModPow_fiber_eq_ker μ n c]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum.symm)

end PadicInt
