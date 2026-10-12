/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.RouteA
import STForMathlib.NumberTheory.PisotNumber
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud, Chapter 10 — Problem 10.61

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, Cambridge University Press, 2012), Chapter 10, Problem 10.61.

> Let `α > 2` be a Pisot number and
> `C(α) = {(α-1) ∑_{k≥1} ε_k α^{-k} : ε ∈ {0,1}^ℕ}`.
> Show that `(ξ αⁿ)_{n≥0}` is never uniformly distributed modulo one, for `ξ ∈ C(α)`.

This file states the problem, and nothing else: it is the single place in the repository
carrying the open statement, so its one `sorry` warning is localised and self-explanatory
(the convention of `BL/Conjectures.lean`).  Everything actually proved about 10.61 lives
in the corpus root `BB61/`, and none of it consumes `problem_10_61`.

## Status

**Open in general.**  The problem is Problème 1 of Mendès France's 1967 thesis, and the
survey trail (`note-1061-L0*.html`) confirms it is still open; `note-1061-M3.html`
Corollary 10 shows that at a *fixed* `α` it is a `Σ₁` statement, i.e. every true instance
has a finite certificate, so the difficulty is uniformity in `α`.

What is machine-checked here:

* `BB61.two_add_sqrt5_not_equidistributed` — 10.61 at `α = 2 + √5`, unconditionally, by
  the Route A engine of `BB61/RouteA.lean`.  This is the smallest `α` of degree `≥ 2` at
  which Route A can fire at all, since a firing of degree `d` needs `α > 2^d`.
* `BB61.problem_10_61_two_add_sqrt3` — **10.61 at `α = 2 + √3`**, where Route A is blind, on
  the single cited axiom `LY.entropyRate_floor` (`CITED/LedrappierYoung.lean`): the
  Ledrappier–Young entropy floor of `note-1061-M3.html` Theorem 11, resting on the dimension
  theory of hyperbolic measures ([You82] at `d = 2`, [LY85], [BPS99]).  Every other link is a
  theorem: the pressure certificate (`BB61/Pressure.lean`, exact in `ℤ[√3]`), the Jensen half of
  the variational principle (`ForMathlib/Dynamics/TopologicalPressure.lean`), the transfer bridge
  (`ForMathlib/Dynamics/PressureTransfer.lean`), the criterion (`BB61/PressureCriterion.lean`),
  and the window modelling lemma with the Lebesgue mean of the cell potential
  (`BB61/Window.lean`).  `BB61.TwoAddSqrt3.two_add_sqrt3_not_equidistributed` is the same result
  with the floor as a hypothesis rather than an axiom, and is std3.
* `BB61.QuadSetup.not_equidistributed_of_no_invariant` — the **master target** of
  `note-1061-M1.html` Theorem 7, at degree two: 10.61 at `α` follows as soon as no
  `σ`-invariant Borel probability measure of the full `2`-shift pushes forward to Lebesgue
  measure under the factor map `F` of `BB61/Factor.lean` (M1 Lemma 6).  This is the
  reduction the whole plan runs on.  See `BB61/Invariant.lean`.
* `BB61.QuadSetup.equidistributed_iff_exists_invariant` — **M1 Corollary 9**: that target is
  an *equivalence*.  Some `ξ ∈ C(α)` has `(ξ αⁿ)` uniformly distributed modulo one **iff**
  some `σ`-invariant Borel probability measure of the full `2`-shift pushes forward to
  Lebesgue measure under `F`.  So nothing is lost in the reduction: a counterexample to the
  master target would be a counterexample to 10.61, not merely an obstruction to this proof
  strategy.  The forward half is Theorem 7; the converse is M1 Proposition 8 — its ergodic
  case (8(i)) runs Birkhoff's pointwise ergodic theorem, vendored as
  `lean_lib BirkhoffErgodicThm` since Mathlib has only the mean theorem
  (`BB61/Realization.lean`), and the general case (8(ii), *saturation* of the full shift) is
  `BB61/Saturation.lean`, which uses **no ergodic theorem**: invariance makes the target an
  exact mean of window averages, a greedy selection realizes that mean by an equal-weight
  sample, and the samples are concatenated into one digit word.
* `BB61.QuadSetup.forall_not_equidistributed_iff_exists_trigCertificate` — **completeness of
  the certificate scheme**, `note-1061-M3.html` Theorem 9, at degree two: 10.61 holds at `α`
  if and only if a *finite* certificate witnesses it, namely a real trigonometric polynomial
  `G` on `𝕋` with `∫ G dLeb = 0` and `∫ G ∘ F dμ ≥ c > 0` for every `σ`-invariant `μ`.  So no
  route can prove 10.61 at an `α` that a trigonometric certificate cannot; what a structural
  route buys is a lower degree, not more reach.
  `BB61.QuadSetup.not_equidistributed_of_trigPoly` exports the implication, and
  `BB61.QuadSetup.exists_trigCertificate_iff` the invariant-measure form.  M3 Cor. 10
  (`Σ₁`-ness of 10.61 at a fixed computable `α`) needs the variational principle for
  topological pressure and is not formalised.  See `BB61/Certificate.lean`.
-/

namespace Bugeaud

open BB61

/-- **Problem 10.61** ([Bug12] Ch. 10).  For a Pisot number `α > 2`, no point of the
Cantor set `C(α)` generates a sequence `(ξ αⁿ)` that is uniformly distributed modulo one.

Open in general; see the module docstring for the instances that are proved. -/
@[category research open, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem problem_10_61 (α : ℝ) (_hα : 2 < α) (_hPisot : IsPisot α)
    (ξ : ℝ) (_hξ : ξ ∈ cantorSet α) :
    ¬ IsEquidistributedModuloOne (fun n : ℕ => ξ * α ^ n) := by
  sorry

end Bugeaud
