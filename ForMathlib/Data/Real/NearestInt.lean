/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import ForMathlib.Data.Rat.NearestInt

@[expose] public section

/-- The distance from a real number to the nearest integer. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ := |x - round x|

theorem distToNearestInt_nonneg (x : ℝ) : 0 ≤ distToNearestInt x := abs_nonneg _

/-- `round` is a nearest integer: the distance to any integer is at least
`distToNearestInt`. -/
theorem distToNearestInt_le_abs_sub_intCast (x : ℝ) (n : ℤ) :
    distToNearestInt x ≤ |x - n| :=
  round_le x n

/-- The `ℝ`-valued distance of a rational number to `ℤ` is the (computable) `ℚ`-valued
one (`Rat.distToNearestInt`) — the bridge between the two `NearestInt` files. -/
theorem distToNearestInt_ratCast (q : ℚ) :
    distToNearestInt (q : ℝ) = (q.distToNearestInt : ℝ) := by
  rw [distToNearestInt, Rat.distToNearestInt, Rat.round_cast]
  push_cast
  ring_nf

/-- An irrational number keeps positive distance from the integers. -/
theorem distToNearestInt_pos_of_irrational {x : ℝ} (hx : Irrational x) :
    0 < distToNearestInt x := by
  rw [distToNearestInt, abs_pos, sub_ne_zero]
  exact hx.ne_int (round x)
