/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ForMathlib.Combinatorics.InfiniteComplexity
import Mathlib.Analysis.Real.OfDigits
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud–Evertse (2008), Theorem 2.1 — the `(log n)^{1/11}` complexity bound, cited

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250.

> **Theorem 2.1.**  *Let `b ≥ 2` be an integer and `ξ` an algebraic irrational real number with
> `0 < ξ < 1`.  Then for every real `η < 1/11`,*
> \[ \limsup_{n\to+\infty}\frac{p(n,\xi,b)}{n(\log n)^{\eta}}=+\infty . \]

This is the quantitative refinement of [AB07, Thm. 1] (`Real.tendsto_complexity_div_atTop`, Subspace-Theorems library): the
latter gives `p(n)/n → ∞` with no rate, this one gives `p(n) > n(\log n)^{0.09}` infinitely often.
The new ingredient is the **Quantitative Parametric Subspace Theorem** of Evertse–Schlickewei
([BE08, Thm. 5.1]), used in the systems-of-inequalities form that makes the number of subspaces
independent of the number of places — which is what removes the dependence on `b`.

The exponent `1/11` traces to the exponent on `ε⁻¹` in that subspace count, and [BE08, Rem. (2.4)]
notes the method is already at its natural limit: it also gives
`limsup p(n,ξ,b)(\log\log n)^{δ}/(n(\log n)^{1/11}) = +∞` for some `δ > 0`.  Improving `1/11` means
improving the subspace count.

The *other* theorem of this paper used in this repository, the quantitative Ridout line cover of
Cor. 5.2, is in `CITED/BugeaudEvertseRidout.lean` under the same namespace.

## Faithfulness of the transcription

* The alphabet is `Fin b` and the real number is Mathlib's `Real.ofDigits w = ∑ₖ wₖ b^{-(k+1)}`,
  matching `BB47/` and the Subspace-Theorems library (whose [AB07, Thm. 1] is
  `Real.tendsto_complexity_div_atTop`).
* [BE08]'s normalisation `0 < ξ < 1` is automatic for the value of a digit word.
* `limsup_n f(n) = +∞` is transcribed as `∀ C N, ∃ n ≥ N, C < f(n)`, the equivalent quantifier
  form and the one consumers produce.  Here `f(n) = p(n,ξ,b)/(n(\log n)^{η})` and the inequality
  is cleared of its denominator, which is harmless: for `n ≥ 2` the denominator is positive, and
  for the finitely many smaller `n` the statement is only weakened by taking `N` large.

## Planned discharge (2026-10-12)

Not yet derivable from the Subspace-Theorems package (ST): it has the qualitative [AB07, Thm. 1]
but no `(log n)^η` rate.  The formalization is planned there as a paper library,
`BugeaudEvertse2008/` (roadmap: `~/math/Subspace-Theorems/BugeaudEvertse2008/README.md`).  It has
most of the ingredients: EF13's subspace count with finite places, independent of the places
(`QuantitativeSubspace`, Q4.3), the Bugeaud–Evertse two-variable count (Q1.6), and the
complexity pigeonhole of `Bugeaud2013/Additions`.  ST's thresholds are larger than [BE08]'s, but
the proof of Thm. 2.1 has doubly exponential room at both steps.  With EF13's `δ⁻³` in place of
ES02's `δ⁻⁷` the expected exponent is `1/7`, i.e. better than `1/11`.  **When that library proves
Thm. 2.1 for some `η₀ ≥ 1/11`, this axiom can be discharged**: derive `exists_pComplexity_gt` from
it (moving the bridge `BB47.pComplexity_eq_complexity` into `CITED/`) and delete the `axiom`, as
was done for `CITED/CorvajaZannierProof.lean`.  This does not cover Cor. 5.2
(`CITED/BugeaudEvertseRidout.lean`), whose small threshold ST does not reach.

## Contents

* `BugeaudEvertse.exists_pComplexity_gt` — Theorem 2.1, as a cited axiom.
* `BugeaudEvertse.transcendental_of_pComplexity_log_bounded` — the form consumers use.

## References

* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), 221–250 — **Thm. 2.1**, with Thm. 5.1 and Rem. (2.4).
* [ES02] J.-H. Evertse, H. P. Schlickewei, *A quantitative version of the Absolute Subspace
  Theorem*, J. reine angew. Math. **548** (2002), 21–127 — the engine behind Thm. 5.1.
* [AB07] B. Adamczewski, Y. Bugeaud, Ann. of Math. **165** (2007), 547–565, Thm. 1 — the
  qualitative ancestor, proved as `Real.tendsto_complexity_div_atTop` (Subspace-Theorems).
-/

namespace BugeaudEvertse

open ForMathlib.SubwordComplexity

/-- **[BE08, Thm. 2.1].**  For an algebraic irrational `ξ` and every `η < 1/11`, the `b`-ary
complexity exceeds `C·n·(log n)^η` for arbitrarily large `n`; equivalently
`limsup_n p(n,ξ,b)/(n(\log n)^{η}) = +∞`.

Cited axiom; the engine is the quantitative parametric Subspace theorem of Evertse–Schlickewei. -/
@[category research solved, AMS 11 68, ref "BE08" "ES02", group "be08_complexity"]
axiom exists_pComplexity_gt {b : ℕ} (hb : 2 ≤ b) (w : ℕ → Fin b)
    (halg : IsAlgebraic ℚ (Real.ofDigits w))
    (hirr : Irrational (Real.ofDigits w))
    {η : ℝ} (hη : η < 1 / 11) (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ C * (n : ℝ) * Real.log n ^ η < pComplexity w n

/-- **[BE08, Thm. 2.1], contrapositive.**  If the complexity of the digit word is
`O(n (log n)^η)` for a single `η < 1/11`, the number is transcendental. -/
@[category research solved, AMS 11 68, ref "BE08", group "be08_complexity"]
theorem transcendental_of_pComplexity_log_bounded {b : ℕ} (hb : 2 ≤ b) (w : ℕ → Fin b)
    (hirr : Irrational (Real.ofDigits w))
    {η : ℝ} (hη : η < 1 / 11) (C : ℝ) (n₀ : ℕ)
    (h : ∀ n : ℕ, n₀ ≤ n → (pComplexity w n : ℝ) ≤ C * (n : ℝ) * Real.log n ^ η) :
    Transcendental ℚ (Real.ofDigits w) := by
  intro halg
  obtain ⟨n, hn, hgt⟩ := exists_pComplexity_gt hb w halg hirr hη C n₀
  exact absurd (h n hn) (not_le.mpr hgt)

end BugeaudEvertse
