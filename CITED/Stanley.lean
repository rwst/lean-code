/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Stanley's closure property: algebraic ⇒ D-finite ⇒ P-recursive coefficients

The one cited axiom of plan-B1E2's eventual-periodicity engine ([B1E2] WP6): an algebraic power
series has **P-recursive** coefficients — they satisfy a nontrivial linear recurrence with
polynomial coefficients.

## The theorem

[Sta80] **Thm 2.1**: over a field of characteristic `0`, an algebraic power series is *D-finite*
(satisfies a linear ODE with polynomial coefficients).  [Sta80] **Thm 1.5**: `f` is D-finite iff
its coefficient sequence is P-recursive.  Composing gives the axiom below.  Both are textbook
closure properties (also Stanley, *Enumerative Combinatorics* vol. 2, Ch. 6).

`ℚ` has characteristic `0`, so the hypothesis is met.

## Why an axiom, and why *this* axiom

This replaces a **Carlson axiom**, which rev. 1 of [B1E2] proposed and Gate 0 deleted ([B1E2]
§0.1, G0.c). The reasons are worth keeping:

* **Pólya–Carlson is overkill.** The statement actually wanted is *Fatou's* theorem — *a power
  series whose coefficients take only finitely many values is either rational or transcendental*
  — which predates Carlson by 15 years. Pólya–Carlson exists to handle *unbounded* integer
  coefficients, which the `{0,1}`-valued word does not have.
* **A Carlson axiom is structurally unusable in Lean.** Invoking it needs a `PowerSeries ℚ` →
  analytic-function transport, radius of convergence, "natural boundary", and continuability of
  algebraic functions. Mathlib has *none* of the first, third or fourth — there is no
  `PowerSeries ℂ` → `FormalMultilinearSeries` bridge at all.
* **Provenance traps** (do not repeat them): Carlson's own hypothesis is *«im Einheitskreise
  konvergente Potenzreihe»* = radius `≥ 1`, not "exactly 1"; the `P(x)/(1−x^p)^q` pole structure
  usually attributed to Carlson is **Fatou's** lemma (Carlson says so himself); and
  Bell–Miles–Ward cite Pólya–Carlson as *«Über ganzwertige Funktionen»*, Math. Z. **11** (1921) —
  a *different* Carlson paper.

Stanley's closure property, by contrast, is purely formal-algebraic: it needs no analysis, it is
obviously faithful to the source, and it is a clean future **Mathlib discharge target**
("algebraic ⇒ D-finite" is a natural standalone contribution, ~1000–2500 lines). Everything
downstream of it (`RB.EventuallyPeriodic`) is *proved*, with **no** rationality intermediate:
Fatou's lemma, pole structure and Skolem–Mahler–Lech are all bypassed.

## Contents

* `Stanley.IsPRecursive` — the P-recursive (holonomic) predicate.
* **`Stanley.pRecursive_of_isAlgebraic`** — the cited axiom.

## References

* [Sta80] R. P. Stanley. *Differentiably finite power series.* European J. Combin. **1** (1980),
  175–188.  (**Thm 2.1** = algebraic ⇒ D-finite, char `0`; **Thm 1.5** = D-finite ⟺ P-recursive.)
* [Sta99] R. P. Stanley. *Enumerative Combinatorics*, vol. 2, CUP 1999, Ch. 6.  (Textbook form.)
* [vdPS96] van der Poorten, Shparlinski. Glasgow Math. J. **38** (1996), 147–155.  (Refereed
  anchor for the surrounding circle of ideas.)
* [BC17] Bell, Chen. J. Comput. System Sci. (2017).  (Ditto.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.1 G0.c (why Carlson was deleted), WP6.
-/

namespace Stanley

/-- A sequence `w : ℕ → ℚ` is **P-recursive** (holonomic): it satisfies a *nontrivial* linear
recurrence `∑ⱼ Qⱼ(n)·w(n+j) = 0` with polynomial coefficients `Qⱼ ∈ ℚ[t]`, not all zero.

Nontriviality (`∃ j, Q j ≠ 0`) is essential — without it every sequence qualifies. -/
@[category API, AMS 11 68 05, ref "Sta80", group "stanley_closure"]
def IsPRecursive (w : ℕ → ℚ) : Prop :=
  ∃ (s : ℕ) (Q : Fin (s + 1) → Polynomial ℚ), (∃ j, Q j ≠ 0) ∧
    ∀ n : ℕ, ∑ j : Fin (s + 1), (Q j).eval (n : ℚ) * w (n + j) = 0

/-- **[Sta80] Thm 2.1 + Thm 1.5**: the coefficients of a power series algebraic over `ℚ[X]` are
**P-recursive**.

Recorded as a cited `axiom` on the authority of [Sta80] (a textbook closure property:
algebraic ⇒ D-finite ⇒ P-recursive, valid in characteristic `0`).  A clean future Mathlib
discharge target; see the module doc for why this, and not Carlson. -/
@[category research solved, AMS 11 68 05, ref "Sta80" "Sta99", group "stanley_closure"]
axiom pRecursive_of_isAlgebraic {f : PowerSeries ℚ} (h : IsAlgebraic (Polynomial ℚ) f) :
    IsPRecursive (fun n => PowerSeries.coeff n f)

end Stanley
