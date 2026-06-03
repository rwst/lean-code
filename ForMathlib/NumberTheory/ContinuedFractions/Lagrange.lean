/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.NumberTheory.Real.Irrational
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Lagrange's theorem on periodic continued fractions

A real number is a quadratic irrational — algebraic of degree exactly two over `ℚ` —
if and only if its simple continued fraction expansion is eventually periodic. This is
the formalized statement underlying the `cf-quadratic-periodicity` informal-result node
used by `DistributionModOne/Problem10_8.lean` (de Mathan–Teulié's quadratic case of the
`p`-adic Littlewood conjecture).

*References:*
  - [Bug12] Bugeaud, Yann. *Distribution modulo one and Diophantine approximation.*
    Vol. 193. Cambridge University Press, 2012.
-/

/-- The continued fraction expansion of `ξ` is **eventually periodic**: from some index
`N` on, the sequence of its terms repeats with a fixed positive period `p`. (For an
irrational `ξ` this sequence is infinite, so the condition is non-vacuous.) -/
@[category API, AMS 11]
def IsEventuallyPeriodicContFrac (ξ : ℝ) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n →
    (GenContFract.of ξ).s.get? (n + p) = (GenContFract.of ξ).s.get? n

/-- **Lagrange's theorem.** A real number `ξ` is a quadratic irrational — algebraic of
degree exactly two over `ℚ`, i.e. `(minpoly ℚ ξ).natDegree = 2` — if and only if it is
irrational and its simple continued fraction expansion is eventually periodic. -/
@[category research solved, AMS 11, ref "Bug12", solved_by "Lagrange" 1770]
theorem lagrange (ξ : ℝ) :
    (minpoly ℚ ξ).natDegree = 2 ↔ Irrational ξ ∧ IsEventuallyPeriodicContFrac ξ := by
  sorry
