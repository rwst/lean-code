/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Window
import CITED.LedrappierYoung
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Problem 10.61 at `α = 2 + √3`, unconditionally

Everything else in `BB61/` is axiom-free and citation-free; this file is the one place where the
root consumes a cited literature axiom, and it consumes exactly one:
`LY.entropyRate_floor` of `CITED/LedrappierYoung.lean` — M3 Theorem 11's entropy floor, resting on
the dimension theory of hyperbolic measures ([You82] at `d = 2`, [LY85], [BPS99]).

`BB61/Window.lean` reduced 10.61 at `2 + √3` to that floor and nothing else.  Discharging it here
gives

`problem_10_61_two_add_sqrt3` — **no point of `C(2+√3)` has `(ξ αⁿ)` uniformly distributed
modulo one**,

with no remaining hypothesis.  The chain behind it, all of it proved in this repository:

* `BB61/Saturation.lean` — M1 Cor. 9: equidistribution at some `ξ ∈ C(α)` **iff** some
  `σ`-invariant `μ` has `F_*μ = Leb`;
* `ForMathlib/Dynamics/TopologicalPressure.lean` — the Jensen half of the variational principle,
  `h_μ(σ,P) + ∫ψ dμ ≤ P(σ,ψ,P)`, over a finite partition;
* `ForMathlib/Dynamics/PressureTransfer.lean` — a potential dominated by a finite-state transfer
  operator has pressure at most the operator's certified growth rate;
* `BB61/Pressure.lean` — the `64`-state certificate at `2 + √3`, exact in `ℤ[√3]`:
  `log(a/b) - (1/8) log W = 0.600637 < 0.658479 = ½ log(2+√3)`;
* `BB61/Window.lean` — the window modelling lemma and the Lebesgue mean of the cell potential;
* `BB61/PressureCriterion.lean` — the one-line variational argument that joins them.

`2 + √3` is the smallest `α` of the M0 sweep at which Route A is blind (`A(α) = 1.0526 > 1`), so
this is out of reach of `BB61/RouteA.lean`, whose capstone at `2 + √5` is unconditional *and*
citation-free.

**This file is no longer the only proof of its statement.**  `BB61/GapSqrtThree.lean` proves the
same conclusion — `problem_10_61_two_add_sqrt3_axiom_free` — from M0 §6.2's support certificate,
which turns out to be a depth-`(2,2)` fact exact in `ℤ[√3]`, and consumes no citation and no axiom
beyond the standard three.  The two proofs are independent: this one goes through invariant
measures, pressure and the Ledrappier–Young floor, that one exhibits an interval of the circle
that `X(2+√3)` misses.  Both are kept — the pressure lane is the general machine, the certificate
is one `α` — but the root's headline unconditional result no longer *rests* on a citation.

## Where the citation bites

`LY.entropyRate_floor` is stated with `entropyRate σ μ coordPartition`, not `kolmogorovSinai σ μ`:
the two agree only by the Kolmogorov–Sinai generator theorem, which is folded into the citation
(see the module doc of `CITED/LedrappierYoung.lean`, item 5).  Any future consumer must keep that
spelling.
-/

namespace BB61

open MeasureTheory Dynamics QuadSetup TwoAddSqrt3

/-- The entropy floor, packaged in the exact shape the capstones of `BB61/Window.lean` take as
`hfloor`.  Cited: `LY.entropyRate_floor`. -/
@[category research solved, AMS 37 28 11, ref "You82" "LY85" "BPS99", group "bugeaud_10_61"]
theorem floor_of_quadratic_unit (P : QuadSetup) (hα : 2 < P.α) (hunit : P.b = 1 ∨ P.b = -1) :
    ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      Real.log P.α / 2 ≤ entropyRate shiftZ μ coordPartition :=
  fun μ hp hi hm => @LY.entropyRate_floor_unit P hα hunit μ hp hi hm

/-- **Problem 10.61 at `α = 2 + √3`, for any `QuadSetup` carrying that root.**  The trace and the
norm are both forced (`trace_eq_four`, `norm_eq_neg_one`), so `hα` is the only hypothesis. -/
@[category research solved, AMS 37 28 11, ref "You82" "LY85" "BPS99", group "bugeaud_10_61"]
theorem two_add_sqrt3_not_equidistributed_cited (P : QuadSetup)
    (hα : P.α = 2 + Real.sqrt 3) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  two_add_sqrt3_not_equidistributed P hα
    (floor_of_quadratic_unit P (by rw [hα]; linarith [one_lt_sqrt3])
      (Or.inr (norm_eq_neg_one P hα)))

/-- **Problem 10.61 at `α = 2 + √3`.**  No `ξ ∈ C(2+√3)` has `(ξ αⁿ)` uniformly distributed
modulo one.

Unconditional, on the single cited axiom `LY.entropyRate_floor` ([You82] Thm 4.4 at `d = 2`,
[LY85] II, [BPS99]).  This is the first `α` of the sweep settled by the pressure lane rather than
by Route A. -/
@[category research solved, AMS 37 28 11, ref "You82" "LY85" "BPS99", group "bugeaud_10_61"]
theorem problem_10_61_two_add_sqrt3 :
    ∀ ξ ∈ cantorSet (2 + Real.sqrt 3),
      ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * (2 + Real.sqrt 3) ^ n :=
  two_add_sqrt3_not_equidistributed_cited sqrtThree rfl

end BB61
