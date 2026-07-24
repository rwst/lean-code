/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.ComputeDegree

@[expose] public section
/-!
# Pisot–Vijayaraghavan numbers

A *Pisot–Vijayaraghavan number* (or *PV number*) is a real algebraic integer
`θ > 1` all of whose Galois conjugates other than `θ` itself lie strictly
inside the complex unit disc. Equivalently, every root in `ℂ` of the minimal
polynomial of `θ` over `ℚ`, apart from `θ`, has modulus `< 1`.

*References*:
- [Wikipedia, Pisot–Vijayaraghavan number](https://en.wikipedia.org/wiki/Pisot%E2%80%93Vijayaraghavan_number)

## Main definitions

* `IsPisot`: a real number is a Pisot–Vijayaraghavan number.
* `IsSalem`: a real number is a Salem number.

## Main statements

* `isPisot_goldenRatio`: the golden ratio is a Pisot number.

-/

open Polynomial

/-- A **Pisot–Vijayaraghavan number** is a real algebraic integer `θ > 1` all of
whose other conjugates lie strictly inside the complex unit disc: every root in
`ℂ` of the minimal polynomial of `θ` over `ℚ`, except `θ` itself, has
modulus `< 1`. -/
def IsPisot (θ : ℝ) : Prop :=
  1 < θ ∧ IsIntegral ℤ θ ∧ ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1

/-- A **Salem number** is a real algebraic integer `τ > 1` all of whose other conjugates lie in the
*closed* complex unit disc, with at least one on the unit circle: every root in `ℂ` of the minimal
polynomial of `τ` over `ℚ`, apart from `τ` itself, has modulus `≤ 1`, and at least one such root has
modulus exactly `1`. This is the companion of `IsPisot` (which demands modulus `< 1` for every other
conjugate); the two together exhaust the real algebraic integers `> 1` whose conjugates stay in the
closed unit disc. -/
def IsSalem (τ : ℝ) : Prop :=
  1 < τ ∧ IsIntegral ℤ τ ∧ (∀ z ∈ (minpoly ℚ τ).aroots ℂ, z ≠ (τ : ℂ) → ‖z‖ ≤ 1) ∧
    ∃ z ∈ (minpoly ℚ τ).aroots ℂ, z ≠ (τ : ℂ) ∧ ‖z‖ = 1

open Real in
/-- The golden ratio `φ = (1 + √5) / 2` is a Pisot number: it is an algebraic
integer greater than `1`, its minimal polynomial over `ℚ` is `X ^ 2 - X - 1`, and
its only other conjugate `ψ = (1 - √5) / 2` has modulus `(√5 - 1) / 2 < 1`. -/
theorem isPisot_goldenRatio : IsPisot goldenRatio := by
  refine ⟨one_lt_goldenRatio, ?_, ?_⟩
  · -- `φ` is an algebraic integer: a root of the monic `X ^ 2 - X - 1 ∈ ℤ[X]`.
    refine ⟨X ^ 2 - X - 1, by monicity!, ?_⟩
    rw [← aeval_def]
    simp only [map_sub, map_pow, map_one, aeval_X]
    linarith [goldenRatio_sq]
  · -- Every complex root of `minpoly ℚ φ` other than `φ` is the conjugate `ψ`.
    intro z hz hzφ
    rw [Polynomial.mem_aroots'] at hz
    -- `minpoly ℚ φ ∣ X ^ 2 - X - 1`, so `z` is a root of `X ^ 2 - X - 1` as well.
    have hdvd : minpoly ℚ goldenRatio ∣ (X ^ 2 - X - 1 : ℚ[X]) := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, map_one, aeval_X]
      linarith [goldenRatio_sq]
    obtain ⟨g, hg⟩ := hdvd
    have hquad : z ^ 2 - z - 1 = 0 := by
      have hz1 : (aeval z) (X ^ 2 - X - 1 : ℚ[X]) = 0 := by
        rw [hg, map_mul, hz.2, zero_mul]
      simpa only [map_sub, map_pow, map_one, aeval_X] using hz1
    -- `X ^ 2 - X - 1 = (X - φ)(X - ψ)`, using `φ + ψ = 1` and `φ * ψ = -1`.
    have hsum : (goldenRatio : ℂ) + (goldenConj : ℂ) = 1 := by
      rw [← Complex.ofReal_add, goldenRatio_add_goldenConj]; norm_num
    have hprod : (goldenRatio : ℂ) * (goldenConj : ℂ) = -1 := by
      rw [← Complex.ofReal_mul, goldenRatio_mul_goldenConj]; norm_num
    have hfac : (z - (goldenRatio : ℂ)) * (z - (goldenConj : ℂ)) = 0 := by
      linear_combination hquad - z * hsum + hprod
    -- Hence `z = ψ`, whose modulus is `< 1`.
    have hzψ : z = (goldenConj : ℂ) := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) hzφ
      · exact sub_eq_zero.mp h
    rw [hzψ, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨neg_one_lt_goldenConj, by linarith [goldenConj_neg]⟩
