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
if and only if its simple continued fraction expansion is eventually periodic. It is the
continued-fraction input to `DistributionModOne/Problem10_8.lean` (de Mathan–Teulié's
quadratic case of the `p`-adic Littlewood conjecture), whose proof formally uses the
`quadratic_partialQuotients_bounded` corollary below.

The two implications have very different histories and difficulty, so they are stated as
separate lemmas and combined into `lagrange`:
* `euler_periodic_imp_quadratic` — the easy half (Euler, 1737): an irrational whose
  expansion is eventually periodic is a quadratic irrational.
* `lagrange_quadratic_imp_periodic` — the hard half (Lagrange, 1770): every quadratic
  irrational has an eventually periodic expansion. Its engine
  `completeQuotient_isIntegral_bounded` (uniformly bounded integer coefficient-triples) also
  yields the cheaper `quadratic_partialQuotients_bounded` (bounded partial quotients) — the
  fact the Problem 10.8 application actually needs — without the pigeonhole step.

The hard direction follows the substitution/bounded-coefficient/pigeonhole proof common to
Hardy–Wright, Niven–Zuckerman–Montgomery, and Khinchin (the one that maps cleanly onto the
existing Mathlib continued-fraction API: `GenContFract.determinant`, `abs_sub_convs_le`,
`sub_convs_eq`), not the reduced-surd/Galois route of Olds.

*References:*
  - [HW79] Hardy, G.H. and Wright, E.M. *An Introduction to the Theory of Numbers.*
    5th ed., Oxford University Press, 1979. Ch. X, Theorem 177.
  - [NZM91] Niven, I., Zuckerman, H.S. and Montgomery, H.L. *An Introduction to the
    Theory of Numbers.* 5th ed., Wiley, 1991. Ch. 7.
  - [Khi64] Khinchin, A.Ya. *Continued Fractions.* Univ. of Chicago Press, 1964. Ch. 1, §5.
-/

/-- The continued fraction expansion of `ξ` is **eventually periodic**: from some index
`N` on, the sequence of its terms repeats with a fixed positive period `p`. (For an
irrational `ξ` this sequence is infinite, so the condition is non-vacuous.) -/
@[category API, AMS 11]
def IsEventuallyPeriodicContFrac (ξ : ℝ) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n →
    (GenContFract.of ξ).s.get? (n + p) = (GenContFract.of ξ).s.get? n

/-- **Euler's direction** (the easy half, 1737). If `ξ` is irrational and its continued
fraction expansion is eventually periodic, then `ξ` is a quadratic irrational:
`(minpoly ℚ ξ).natDegree = 2`.

*Idea.* Over one period the convergent recurrence expresses `ξ` as a fractional-linear
(Möbius) transform of itself, `ξ = (A·ξ + B)/(C·ξ + D)` with integer `A, B, C, D`; clearing
denominators yields an integer quadratic with `ξ` as a root, so `ξ` is algebraic of degree
`≤ 2`, and irrationality rules out degree `≤ 1`. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Euler" 1737]
theorem euler_periodic_imp_quadratic {ξ : ℝ} (hirr : Irrational ξ)
    (hper : IsEventuallyPeriodicContFrac ξ) :
    (minpoly ℚ ξ).natDegree = 2 := by
  sorry

/-- The `n`-th **complete quotient** of `ξ`: `ξ₀ = ξ` and `ξₙ₊₁ = 1/{ξₙ}`, the reciprocal of
the fractional part `{ξₙ} = ξₙ - ⌊ξₙ⌋`. This is exactly the sequence produced by the
continued fraction algorithm, and the partial quotients are its floors `aₙ = ⌊ξₙ⌋`; the
eventual periodicity of this sequence is what drives Lagrange's direction. -/
@[category API, AMS 11]
noncomputable def completeQuotient (ξ : ℝ) : ℕ → ℝ
  | 0 => ξ
  | n + 1 => (Int.fract (completeQuotient ξ n))⁻¹

/-- **Bounded coefficients** — the engine of Lagrange's direction. For a quadratic irrational
`ξ`, every complete quotient `ξₙ` is a root of an integer quadratic `aₙ X² + bₙ X + cₙ`
(`aₙ ≠ 0`) whose coefficients are bounded *uniformly in `n`*: they are the transforms of
`minpoly ℚ ξ` under the convergent substitution, so they keep its discriminant, and the
convergent bound `|ξ − pₖ/qₖ| < 1/qₖ²` forces `|aₙ|, |bₙ|, |cₙ| ≤ M`.

This is the shared heart of the hard direction: the cheap `quadratic_partialQuotients_bounded`
and the full `lagrange_quadratic_imp_periodic` both reduce to it, the latter by additionally
pigeonholing the finitely many bounded triples. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Lagrange" 1770]
theorem completeQuotient_isIntegral_bounded {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    ∃ M : ℤ, ∀ n, ∃ a b c : ℤ, a ≠ 0 ∧
      (a : ℝ) * completeQuotient ξ n ^ 2 + (b : ℝ) * completeQuotient ξ n + (c : ℝ) = 0 ∧
      |a| ≤ M ∧ |b| ≤ M ∧ |c| ≤ M := by
  sorry

/-- **Bounded partial quotients** — the cheap corollary actually consumed by the `p`-adic
Littlewood / Problem 10.8 quadratic case. A quadratic irrational has uniformly bounded
partial quotients `aₙ = ⌊ξₙ⌋`.

This follows from `completeQuotient_isIntegral_bounded` *without* the pigeonhole/periodicity
step: each `ξₙ` is a root of a bounded-coefficient quadratic with nonzero leading
coefficient, hence `|ξₙ| ≤ M'`, hence `⌊ξₙ⌋ ≤ M'`. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Lagrange" 1770,
  formal_uses completeQuotient_isIntegral_bounded]
theorem quadratic_partialQuotients_bounded {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    ∃ M : ℤ, ∀ n, ⌊completeQuotient ξ n⌋ ≤ M := by
  sorry

/-- **Lagrange's direction** (the hard half, 1770). A quadratic irrational
(`(minpoly ℚ ξ).natDegree = 2`) is irrational and has an eventually periodic continued
fraction expansion. The irrationality is immediate from the degree; the periodicity is
Lagrange's theorem proper.

By `completeQuotient_isIntegral_bounded` the complete quotients take finitely many values
(bounded integer triples, each quadratic having `≤ 2` roots), so `ξₘ = ξₙ` for some `m < n`
by pigeonhole, after which the partial quotients repeat with period `n − m`. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Lagrange" 1770,
  formal_uses completeQuotient_isIntegral_bounded]
theorem lagrange_quadratic_imp_periodic {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    Irrational ξ ∧ IsEventuallyPeriodicContFrac ξ := by
  sorry

/-- **Lagrange's theorem.** A real number `ξ` is a quadratic irrational — algebraic of
degree exactly two over `ℚ`, i.e. `(minpoly ℚ ξ).natDegree = 2` — if and only if it is
irrational and its simple continued fraction expansion is eventually periodic. Combines
`euler_periodic_imp_quadratic` (`⇐`, Euler 1737) and `lagrange_quadratic_imp_periodic`
(`⇒`, Lagrange 1770). -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Euler" 1737, solved_by "Lagrange" 1770]
theorem lagrange (ξ : ℝ) :
    (minpoly ℚ ξ).natDegree = 2 ↔ Irrational ξ ∧ IsEventuallyPeriodicContFrac ξ :=
  ⟨lagrange_quadratic_imp_periodic, fun h => euler_periodic_imp_quadratic h.1 h.2⟩
