/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.AutomaticValue
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

## No longer an axiom ([AF17f] WP5, milestone M2)

Until 2026-08-04 the declaration below was a **cited axiom**, with three facts folded into it on
[AF17]'s authority. All three are now discharged, and the declaration is a `theorem` whose
footprint is `std3` plus the two named axioms of [AF22] §2:

* *bounded coefficients ⇒ radius of convergence `≥ 1` ⇒ `α` with `|α| < 1` is not a pole* —
  `RB.one_le_genFunSeries_radius`, `RB.analyticAt_genFun` (WP2);
* *automatic ⇒ a `q`-Mahler system whose matrix is polynomial and has **nonzero determinant*** —
  `RB.exists_nonsingular_mahlerSystem` (gate G4), applied to the canonical kernel model
  `RB.isKernelModel_kKernel`. Note what this is *not*: the system itself is elementary
  ([Ran92] Thm 3.1, here `RB.mahlerSystem_formal`), and Becker's theorem does not supply the
  determinant condition in polynomial form, so nonsingularity is **proved** rather than cited —
  see `RB/MahlerNonsingular.lean` and the plan's §2.3;
* *`k = ℚ` contains `α ∈ ℚ` and the coefficients `a j ∈ ℕ ⊂ ℚ`* — `AF.corollaire_1_8_rat`.

What remains cited is **two** things, and both are stated at the level [AF17]/[AF22] state them.
Until 2026-08-06 it was one — `AF.lifting_regular`, the lifting theorem for linear relations at a
regular point ([AF17] Thm 1.4 restricted to degree one = [AF22] Thm 2.1) — and Stage 2 of the plan
([AF17f] WP7–WP20) replaced it by a proof from [AF22] §2, `AF.theoreme_2_1`, which rests on

* **`AF.lemme_2_2`** — [AF17] Lemme 2.2: the solution field of a Mahler system is a regular
  extension of `ℚ̄(z)` (`CITED/AdamczewskiFaverjonRegular.lean`);
* **`AF.lemma_2_8`** — [AF22] Lemma 2.8: the relation matrix has an analytic branch at
  `α^{q^k}` for `k ≫ 1` (`CITED/AdamczewskiFaverjonBranchFull.lean`).

The derivation of Corollaire 1.8 from the lifting theorem is in
`CITED/AdamczewskiFaverjonTheoreme17.lean`.

The boundedness hypothesis `∀ j, a j ≤ B` is what makes `∑' j, a j · αʲ` the genuine value
`f(α)` (the series converges absolutely for `|α| < 1`), so the statement is not vacuous. It is
also *redundant* — automaticity implies it — but is kept so that the statement, and hence every
consumer proof, is unchanged from the axiom it replaces.

## Contents

* **`AF.transcendental_or_rat_of_automatic`** — `f` automatic with bounded coefficients,
  `α ∈ ℚ` with `0 < |α| < 1` ⇒ `f(α)` transcendental over `ℚ`, or `f(α) ∈ ℚ`.

## References

* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* Proc. London Math. Soc. **115** (2017), 55–90.
  (**Cor 1.8** = this theorem; **Thm 1.4** = the regular-point version that *does* force
  transcendence; **§8.1** = the counterexample showing the alternative is irremovable.)
  Verified verbatim 2026-07-16.
* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022). (Thm 2.1 = `AF.theoreme_2_1`, **proved** here from §2; its two cited
  inputs are Lemma 2.8 and [AF17] Lemme 2.2.)
* [Cob68] A. Cobham. *A proof of transcendence of certain power series* / the 1968 conjecture on
  automatic series at rational points, settled by [AF17].
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.1 (the misreading), §2.2 (the chain that
  consumes this), WP7, risk R2.
* [AF17f] `plans/plan-formalize-AF17.html`: WP5 (this file's de-axiomatization), §2.3 (gate G4),
  milestone M2.
-/

namespace AF

/-- **[AF17] Corollaire 1.8**, in the specialization the corpus consumes: for an automatic
sequence `a` with bounded values and a rational `α` with `0 < |α| < 1`, the value
`f(α) = ∑ⱼ aⱼαʲ` is **either transcendental over `ℚ`, or rational**.

This is AF's own named case — Cobham's 1968 conjecture — with `k = ℚ` forced by `α ∈ ℚ` and
`a j ∈ ℕ ⊂ ℚ`.  **No longer an axiom** ([AF17f] WP5): it is `RB.transcendental_or_rat_of_automatic`,
whose footprint is `std3 + AF.lemme_2_2 + AF.lemma_2_8`.

**Both disjuncts are real**; see the module doc before using this. -/
@[category research solved, AMS 11 68, ref "AF17", group "af_mahler_alternative"]
theorem transcendental_or_rat_of_automatic {a : ℕ → ℕ} {B : ℕ}
    (hbdd : ∀ j, a j ≤ B) (hauto : AS.IsAutomatic a)
    {α : ℚ} (hα0 : α ≠ 0) (hα1 : |α| < 1) :
    Transcendental ℚ (∑' j, (a j : ℝ) * (α : ℝ) ^ j) ∨
      ∃ r : ℚ, ∑' j, (a j : ℝ) * (α : ℝ) ^ j = (r : ℝ) :=
  RB.transcendental_or_rat_of_automatic hbdd hauto hα0 hα1

end AF
