/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Algebraic.Basic
import CITED.AlloucheShallitBasic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Adamczewski–Faverjon: the Mahler alternative at an algebraic point ([AF17] Cor 1.8)

The transcendence input of plan-B1E2's refereed lane, and the theorem that settled **Cobham's
1968 conjecture** on values of automatic power series at rational points.

## The theorem, verbatim

[AF17] **Corollaire 1.8** (transcribed from the source, 2026-07-16):

> *«Soient \(f(z)\) une fonction \(q\)-mahlérienne et \(\alpha\in\overline{\mathbb Q}\),
> \(0<|\alpha|<1\), qui n'est pas un pôle de \(f\). Soit \(k\) un corps de nombres contenant
> \(\alpha\) ainsi que les coefficients de \(f\). On a l'alternative suivante : soit
> \(f(\alpha)\) est transcendant, soit \(f(\alpha)\in k\).»*

That is: for `f` a `q`-Mahlerian function and `α` algebraic with `0 < |α| < 1` not a pole of
`f`, and `k` a number field containing `α` and the coefficients of `f` — **either `f(α)` is
transcendental, or `f(α) ∈ k`.**

## Read the branch structure literally

The `f(α) ∈ k` disjunct is **not** a degenerate corner to be simplified away — AF stress that it
cannot be removed: *«des exemples montrent que l'on ne peut se soustraire à l'alternative … même
en supposant la fonction \(f(z)\) transcendante»*, and their §8.1 exhibits a `{0,1}`-valued
`3`-automatic sequence with `f` transcendental over `ℚ(z)` and yet `f₁(φ) = −φ/2 ∈ ℚ(φ)`.

A "collision" argument that reads the corollary as forcing degeneracy from a *known rational
value* is therefore **invalid** — the rational value is the permitted branch. This misreading
sank plan-B1E2 rev. 1; see that plan's §0.1. The corollary has real force only in the
contrapositive direction used by `RB.not_automatic_of_K_algebraic_irrational`: an *algebraic
irrational* value is excluded by **both** branches at once.

(The transcendence-forcing shape *is* available, but only at **regular** points, via [AF17]
Thm 1.4 — *«En un point algébrique \(\alpha\) qui n'est pas dans \(E\), le théorème 1.4 implique
directement que \(f(\alpha)\) est transcendant»*. Cor 1.8 needs no regularity hypothesis, which
is exactly why it costs the alternative.)

## What is axiomatized here, and what that leaves on trust

Formalizing the general corollary needs the notion *`q`-mahlérienne* (a linear Mahler system
`F(z) = M(z)F(z^q)`), poles, and "the coefficients of `f`" over an arbitrary number field —
infrastructure the corpus does not have, and which would still leave the statement unusable
without also formalizing *automatic ⇒ Mahlerian*. So the axiom below is **the specialization AF
themselves name**: automatic coefficients, evaluated at a **rational** point, whence `k = ℚ`.
AF are explicit that this case is the paper's raison d'être — *«C'est précisément cette
conjecture [de Cobham, 1968] qui est à l'origine du présent travail»*.

Folded into the axiom, and thus taken on [AF17]'s authority rather than proved here:

* *automatic ⇒ `q`-Mahlerian* ([AF17] §1; Becker's theorem);
* *bounded coefficients ⇒ radius of convergence `≥ 1` ⇒ `α` with `|α| < 1` is not a pole* —
  elementary, but it is what discharges Cor 1.8's pole hypothesis;
* *`k = ℚ` contains `α ∈ ℚ` and the coefficients `a j ∈ ℕ ⊂ ℚ`* — whence the second branch reads
  `f(α) ∈ ℚ`.

The boundedness hypothesis `∀ j, a j ≤ B` is what makes `∑' j, a j · αʲ` the genuine value
`f(α)` (the series converges absolutely for `|α| < 1`), so the statement is not vacuous.

## Contents

* **`AF.transcendental_or_rat_of_automatic`** — the cited axiom: `f` automatic with bounded
  coefficients, `α ∈ ℚ` with `0 < |α| < 1` ⇒ `f(α)` transcendental over `ℚ`, or `f(α) ∈ ℚ`.

## References

* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* Proc. London Math. Soc. **115** (2017), 55–90.
  (**Cor 1.8** = this axiom; **Thm 1.4** = the regular-point version that *does* force
  transcendence; **§8.1** = the counterexample showing the alternative is irremovable.)
  Verified verbatim 2026-07-16.
* [Cob68] A. Cobham. *A proof of transcendence of certain power series* / the 1968 conjecture on
  automatic series at rational points, settled by [AF17].
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.1 (the misreading), §2.2 (the chain that
  consumes this), WP7, risk R2.
-/

namespace AF

/-- **[AF17] Corollaire 1.8**, in the specialization the corpus consumes: for an automatic
sequence `a` with bounded values and a rational `α` with `0 < |α| < 1`, the value
`f(α) = ∑ⱼ aⱼαʲ` is **either transcendental over `ℚ`, or rational**.

This is AF's own named case — Cobham's 1968 conjecture — with `k = ℚ` forced by `α ∈ ℚ` and
`a j ∈ ℕ ⊂ ℚ`.  Recorded as a cited `axiom` on the authority of [AF17] (a Mahler-method result
resting on Nishioka's theorem and Philippon's criterion, which we do not re-derive).

**Both disjuncts are real**; see the module doc before using this. -/
@[category research solved, AMS 11 68, ref "AF17", group "af_mahler_alternative"]
axiom transcendental_or_rat_of_automatic {a : ℕ → ℕ} {B : ℕ}
    (hbdd : ∀ j, a j ≤ B) (hauto : AS.IsAutomatic a)
    {α : ℚ} (hα0 : α ≠ 0) (hα1 : |α| < 1) :
    Transcendental ℚ (∑' j, (a j : ℝ) * (α : ℝ) ^ j) ∨
      ∃ r : ℚ, ∑' j, (a j : ℝ) * (α : ℝ) ^ j = (r : ℝ)

end AF
