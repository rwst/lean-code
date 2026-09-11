/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import CITED.StanleyProof
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Stanley's closure property: algebraic ⇒ D-finite ⇒ P-recursive coefficients

The engine behind plan-B1E2's eventual-periodicity argument ([B1E2] WP6): an algebraic power
series has **P-recursive** coefficients — they satisfy a nontrivial linear recurrence with
polynomial coefficients.  Carried as a cited axiom until 2026-09-06; **now proved**, in
`CITED.StanleyProof`, from Mathlib plus the missing localization-of-derivations infrastructure.

## The theorem

[Sta80] **Thm 2.1**: over a field of characteristic `0`, an algebraic power series is *D-finite*
(satisfies a linear ODE with polynomial coefficients).  [Sta80] **Thm 1.5**: `f` is D-finite iff
its coefficient sequence is P-recursive.  Composing gives the axiom below.  Both are textbook
closure properties (also Stanley, *Enumerative Combinatorics* vol. 2, Ch. 6).

`ℚ` has characteristic `0`, so the hypothesis is met.

## Provenance: why Stanley, and not Carlson

The statement recorded here replaced a **Carlson axiom**, which rev. 1 of [B1E2] proposed and
Gate 0 deleted ([B1E2] §0.1, G0.c).  The reasons are worth keeping — and the discharge below
vindicates them, since the Carlson route is *still* not formalizable while this one is:

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
obviously faithful to the source, and it was a clean **Mathlib discharge target**.  Everything
downstream of it (`RB.EventuallyPeriodic`) is *proved*, with **no** rationality intermediate:
Fatou's lemma, pole structure and Skolem–Mahler–Lech are all bypassed.

## How it is proved (`CITED.StanleyProof`, 2026-09-06)

The mathematically hard half of [Sta80] Thm 2.1 turned out to be **already in Mathlib**, a
by-product of the Liouville-theorem differential-field development:
`Mathlib/FieldTheory/Differential/Basic.lean` supplies
`instance (B : IntermediateField F K) [FiniteDimensional F B] : DifferentialAlgebra B K`, i.e.
*a finite intermediate field is stable under the ambient derivation* — precisely "`K(X)(f)` is
closed under `d/dX`", with separability (whence the `CharZero` hypothesis) and implicit
differentiation (`RingTheory/Derivation/DifferentialRing.lean`) included.  Also in place:
`PowerSeries.derivative` as a bundled `Derivation` with the extraction identity
`coeff k (D^[n] f) = (k+1).ascFactorial n * coeff (k+n) f`; `IsFractionRing K⟦X⟧ K⸨X⸩` and the
tower `K[X] → K(X) → K⸨X⸩`; and `IsLocalization.exist_integer_multiples` for denominators.

Four things were missing, and are what `StanleyProof.lean` contains:

1. **Derivations do not extend to localizations** — Mathlib connects `Derivation` to
   `IsLocalization` nowhere.  `Stanley.fracDeriv` supplies the extension by the dual-numbers
   trick (`r ↦ (r, D r)` is a ring hom into `S[ε]`, and `IsLocalization.lift` applies because
   `(u, b)` is a unit as soon as `u ≠ 0`), and `Stanley.eq_of_leibniz_of_isFractionRing` its
   uniqueness.  This is the one genuinely reusable piece, independent of Stanley.
2. **The differential fields themselves**: `Differential (RatFunc K)`, `Differential K⸨X⸩` and
   `DifferentialAlgebra (RatFunc K) K⸨X⸩` — all from (1), plus the compatibility that the
   derivation of `K⸨X⸩` restricted to `K⟦X⟧` *is* `PowerSeries.derivative`.
3. **`Stanley.exists_ode`** = [Sta80] Thm 2.1: transport `f` into `K⸨X⸩`, adjoin it to `K(X)`,
   read off from the Mathlib instance that every `f⁽ⁱ⁾` stays in that finite extension, take
   `finrank + 1` of them, clear denominators, and pull the relation back along
   `HahnSeries.ofPowerSeries`.
4. **`Stanley.sum_recCoeff_eq_zero` / `exists_recCoeff_ne_zero`** = the half of [Sta80] Thm 1.5
   that is needed: the coefficient extraction.  Nothing of the sort exists in Mathlib (no
   `holonomic`, `DFinite` or `PRecursive` anywhere).  Reading the `(n+N)`-th coefficient rather
   than the `n`-th is what makes every shift nonnegative, as `IsPRecursive` demands; and
   nontriviality — the clause `∃ j, Q j ≠ 0`, without which the predicate is vacuous — comes from
   the *largest* shift reached by a nonzero coefficient, where the largest derivative order
   occurring contributes the unique term of top degree, which therefore cannot cancel.

Cost: 540 lines, of which (1)–(2) — the reusable, Stanley-free half — are about 150.  Footprint
`std3`: no `sorry`, no new axiom.  Downstream, `RB.not_isAlgebraic_wminSeries`,
`RB.not_isAlgebraic_orbitSeries`, `RB.Gen.not_isAlgebraic_wordSeries` and
`RB.eventuallyPeriodic_of_isAlgebraic_of_finite_coeffs` are now **cited-axiom-free**, and
`RB.Alg.not_isAlgebraic_wordSeries_of_not_mem_U` carries only `Dubickas.periodic_imp_mem_U`.

## Contents

* `Stanley.IsPRecursive` — the P-recursive (holonomic) predicate.
* **`Stanley.pRecursive_of_isAlgebraic`** — the theorem; proved in `CITED.StanleyProof`, whose
  general form `Stanley.exists_polynomial_recurrence` holds over any field of characteristic `0`.

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

The textbook closure property algebraic ⇒ D-finite ⇒ P-recursive, valid in characteristic `0`.
Carried as a cited axiom until 2026-09-06; **proved** in `CITED.StanleyProof`, of which this is
the `ℚ`-instance.  See the module doc for the anatomy of the proof, and for why this statement and
not Carlson. -/
@[category research solved, AMS 11 68 05, ref "Sta80" "Sta99", group "stanley_closure"]
theorem pRecursive_of_isAlgebraic {f : PowerSeries ℚ} (h : IsAlgebraic (Polynomial ℚ) f) :
    IsPRecursive (fun n => PowerSeries.coeff n f) :=
  exists_polynomial_recurrence h

end Stanley
