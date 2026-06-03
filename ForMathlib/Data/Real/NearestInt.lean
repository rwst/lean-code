/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-- The distance from a real number to the nearest integer. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ := |x - round x|
