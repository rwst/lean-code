/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Data.Real.NearestInt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# `distToNearestInt` of a ratio of naturals

`distToNearestInt (m / d)` is the exact-integer quantity `min(m % d, d - m % d) / d`: the distance
from `m / d` to the nearest integer is measured by the residue `m % d` and its complement.  This
turns a real nearest-integer statement about `m / d` into a decidable statement about naturals.
-/

/-- The distance to the nearest integer of a ratio of naturals `m / d` is the *exact-integer*
`min(m % d, d - m % d) / d`. -/
theorem distToNearestInt_natCast_div (m d : ℕ) (hd : 0 < d) :
    distToNearestInt ((m : ℝ) / (d : ℝ)) = (↑(min (m % d) (d - m % d)) : ℝ) / (d : ℝ) := by
  rw [distToNearestInt, abs_sub_round_eq_min, Int.fract_div_natCast_eq_div_natCast_mod]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hle : m % d ≤ d := le_of_lt (Nat.mod_lt _ hd)
  rw [Nat.cast_min, Nat.cast_sub hle,
    show (1 : ℝ) - (↑(m % d)) / (d : ℝ) = ((d : ℝ) - ↑(m % d)) / (d : ℝ) by field_simp,
    min_div_div_right (le_of_lt hdR)]
