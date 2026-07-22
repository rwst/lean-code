/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Padics.PadicNorm
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The quantitative Ridout theorem of Bugeaud–Evertse (2008), Cor. 5.2 — cited

The **line cover** produced by the quantitative Subspace Theorem: for a fixed exponent budget
`2 + ε` distributed over the archimedean place and finitely many primes, all *high* solutions of
the associated approximation system lie on an explicitly bounded number of lines through the
origin.

## The source statement, verbatim

[BE08], §5, pp. 8–9.  Let `S₁, S₂` be finite, possibly empty sets of primes, `S := {∞} ∪ S₁ ∪ S₂`,
let `ξ` be an algebraic number of degree `d`, let `ε > 0`, and let `f_p` (`p ∈ S`) be reals with

> `f_p ≥ 0` for `p ∈ S`, `∑_{p ∈ S} f_p = 2 + ε`.  (5.10)

Consider the system of inequalities

> `|ξ − x/y| ≤ y^{−f_∞}`, `|x|_p ≤ y^{−f_p}` (`p ∈ S₁`), `|y|_p ≤ y^{−f_p}` (`p ∈ S₂`),
> in `(x, y) ∈ ℤ²` with `y > 0`.  (5.11)

Define the height of `ξ` by `H(ξ) := ∏_{v ∈ M_K} max(1, ‖ξ‖_v)`.

> **Corollary 5.2.** *The set of solutions of (5.11) with*
> `y > max(2H(ξ), 2^{4/ε})`  (5.12)
> *is contained in the union of at most*
> `2³²(1 + ε⁻¹)³ log(6d) log((1 + ε⁻¹) log(6d))`  (5.13)
> *one-dimensional linear subspaces of ℚ².*

Two features of the source are load-bearing and are reproduced below without weakening:

* the conclusion counts **one-dimensional subspaces** (lines), *not* solutions — [BE08] contains
  no per-line multiplicity statement anywhere, and Theorem 5.1 behind it has the same shape;
* the conclusion is restricted to **large height** `y > max(2H(ξ), 2^{4/ε})`; solutions below the
  threshold are not covered at all.

## What is recorded here

The instance actually used in this repository: `d = 1` (so `ξ ∈ ℚ` and `log(6d) = log 6`),
`S₁ = {2}`, `S₂ = {3}`.  A one-dimensional subspace of `ℚ²` meeting the region `y > 0` is
determined by the slope `x/y ∈ ℚ` of any of its points, so the line cover is recorded as a
`Finset ℚ` of slopes of cardinality at most `lineBound ε`.  Varying `(f_∞, f₂, f₃)` inside the
budget `2 + ε` is what lets one axiom serve every frame of the `‖(3/2)ⁿ‖` problems.

## Retirement notice (2026-07-21)

This file **replaces** `CITED/CorvajaZannierEffective.lean`, whose axiom
`CZ.pseudoPisot_approx_effective` asserted a bound on the *number of solutions*,
`#A(δ, ε) ≤ (|num δ| + den δ) · K(ε)`.  That statement is **not** Cor. 5.2: passing from the line
count to a solution count needs a uniform bound on the number of solutions per line, which is the
open problem [BE08] itself flags (Remark 7.4) and which Corvaja–Zannier's *ineffective* finiteness
cannot supply.  Under the house policy on cited axioms (literature-proved statements only, never
open ones) it was deleted, together with its consumers' count corollaries; the repaired counts are
conditional on an explicit per-line hypothesis (`BB13/FailureCount.lean`).  See
`plans/plan2-BB13.html`, and `plans/report-BB13.md`, `plans/report2-BB13.md` for the two referee
reports that identified the error.

## References

* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), 221–250 — Thm 5.1 ((5.7)–(5.9)) and Cor. 5.2 ((5.10)–(5.13)).
* [ES02] J.-H. Evertse, H. P. Schlickewei, *A quantitative version of the Absolute Subspace
  Theorem*, J. reine angew. Math. **548** (2002), 21–127 — the engine behind Thm 5.1.
* [Rid57] D. Ridout, *The p-adic generalization of the Thue–Siegel–Roth theorem*, Mathematika **4**
  (1957), 125–131 — the qualitative ancestor (`CITED/Ridout.lean`).
-/

namespace BugeaudEvertse

open scoped Real

/-- The Bugeaud–Evertse line count (5.13) at degree `d = 1`:
`⌈2³²(1 + ε⁻¹)³ · log 6 · log((1 + ε⁻¹) · log 6)⌉`.

At the sharp exponent `ε* = log(4/3)/log 3` of Bugeaud's Problem 10.13 this is
`1 856 360 182 227 < 1.86 · 10¹²`. -/
noncomputable def lineBound (ε : ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ 32 * (1 + ε⁻¹) ^ 3 * Real.log 6 * Real.log ((1 + ε⁻¹) * Real.log 6)⌉₊

/-- The height `H(ξ) = ∏_v max(1, ‖ξ‖_v)` of a rational number: `max(|num ξ|, den ξ)`. -/
def ratHeight (ξ : ℚ) : ℕ := max ξ.num.natAbs ξ.den

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem ratHeight_one : ratHeight 1 = 1 := by decide

/-- **Quantitative Ridout** ([BE08], Cor. 5.2), the instance `d = 1`, `S₁ = {2}`, `S₂ = {3}`:
for exponents `fInf, f₂, f₃ ≥ 0` (the source's `f_∞, f₂, f₃`) with `fInf + f₂ + f₃ = 2 + ε`
there is a set `R` of at most `lineBound ε` slopes such that **every** solution
`(x, y) ∈ ℤ²`, `y > 0`, of

* `|ξ − x/y| ≤ y^{−fInf}`,
* `|x|₂ ≤ y^{−f₂}`,
* `|y|₃ ≤ y^{−f₃}`

whose height exceeds `max(2H(ξ), 2^{4/ε})` has `x/y ∈ R` — i.e. lies on one of at most
`lineBound ε` lines through the origin.

Recorded as a cited `axiom` on the authority of [BE08] Cor. 5.2 (via [ES02]); the source statement
is quoted verbatim in the module docstring.  Note what is **not** asserted: nothing bounds the
number of solutions on a single line, and nothing is said about solutions of height below the
threshold. -/
@[category research solved, AMS 11, ref "BE08" "ES02", group "bugeaud_10_13"]
axiom ridout_line_cover (ξ : ℚ) (ε fInf f₂ f₃ : ℝ) (hε : 0 < ε)
    (hInf : 0 ≤ fInf) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (hsum : fInf + f₂ + f₃ = 2 + ε) :
    ∃ R : Finset ℚ, R.card ≤ lineBound ε ∧
      ∀ x y : ℤ, 0 < y →
        max (2 * (ratHeight ξ : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / ε)) < (y : ℝ) →
        |(ξ : ℝ) - (x : ℝ) / (y : ℝ)| ≤ (y : ℝ) ^ (-fInf) →
        ((padicNorm 2 (x : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-f₂) →
        ((padicNorm 3 (y : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-f₃) →
        (x : ℚ) / (y : ℚ) ∈ R

end BugeaudEvertse
