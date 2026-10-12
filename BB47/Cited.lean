/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import DiophantineApproximation.ComplexityTranscendence
import CITED.BugeaudEvertseComplexity
import BB47.LemmaA0

/-!
# The Diophantine input

Milestone M2 of `plans/plan-1047.html` quotes theorems about algebraic numbers and derives
everything else from them.  This file is where the boundary between quoted and proved sits.

## The primary inputs are elsewhere, and are complexity theorems

After the horizon bound `p(n, w) ≤ s_n + p_∞(n, w)` (`BB47.pComplexity_le_horizon_add_pInf`),
Theorems A and A′ need no repetition function: the hypothesis on `s_n + p_∞(n)` is already a
hypothesis on the ordinary complexity, and the two theorems that forbid it for algebraic
irrationals are

* `Real.tendsto_complexity_div_atTop` — **[AB07, Thm. 1]**, `p(n, ξ, b)/n → +∞`, a theorem of
  the Subspace-Theorems library (`DiophantineApproximation/ComplexityTranscendence.lean`), used
  here through `BB47.transcendental_of_pComplexity_linear_io`, and
* `BugeaudEvertse.exists_pComplexity_gt` — **[BE08, Thm. 2.1]**, the `(log n)^{1/11}` refinement
  (`CITED/BugeaudEvertseComplexity.lean`).

Both are imported here so that every Diophantine input of this root is visible from one file;
the first is proved, the second is a cited axiom.  They are
what `BB47.theorem_A` and `BB47.theorem_Aprime` actually use; see `BB47/L0.md` §5.1 and
[M1M2, §5].

## The repetition-function route is kept as a second proof

The rest of this file records **[BK19, Thm. 10.4]**, the packaged criterion phrased against
`repLen`.  Fed by Lemma A0 it gives `BB47.theorem_A_via_repLen` and
`BB47.theorem_Aprime_via_repLen`, a longer route to the same conclusions from a formally weaker
hypothesis (`¬ IsEventuallyPeriodic w` rather than `Irrational (value b w)` — the two are
equivalent for digit words, but the implication `¬ eventually periodic ⇒ irrational` needs the
classical characterisation of rationals by eventually periodic expansions, which Mathlib does not
have).  It is also the criterion the sliver of `BB47/Sliver.lean` is phrased against.

> **[BK19, Thm. 10.4]** (after [ABL04], [AB07], [BE08], [Bug13]).  Let `A` be a finite set of
> integers and `w` an infinite word over `A` which is not eventually periodic.  If
> `liminf r(n, w)/n < ∞`, or `limsup r(n, w)/(n (log n)^η) < ∞` for some `η < 1/11`, then
> `∑ₖ wₖ b^{-k}` is transcendental for every integer `b ≥ 2`.

Neither clause is a Ridout argument, and that is the point of §3 of the plan.  The first clause is
a repackaging — through `rep(w) = dio(w)/(dio(w) − 1)` [BK19, Lem. 10.3] — of the condition
`dio(w) > 1` of the Adamczewski–Bugeaud combinatorial transcendence criterion [AB07, Thm. 5],
whose Condition `(∗)_w` tolerates a prefix `Uₙ` with `|Uₙ|/|Vₙ|` bounded by an **arbitrary**
constant and requires only `w > 1`; its engine is the `p`-adic Subspace theorem.  The second
clause comes from the *quantitative* Subspace theorem, via [BE08, Thm. 2.1].  So neither is
subject to the position-versus-period loss that caps the Ferenczi–Mauduit route at a fixed ratio
— the correction that milestone L0 of the plan had to make to its own §3.

## Faithfulness of the transcription

[BK19] allows any finite set of integers as the alphabet.  Here the alphabet is `Fin b`, the digit
set — the only case Problem 10.47 concerns — and the value is `BB47.value b w`, Mathlib's `Real.ofDigits w`,
the object the Subspace-Theorems library and `CITED/BugeaudEvertseComplexity.lean` state their
theorems about.

The hypotheses are transcribed in their equivalent quantifier form rather than as `Filter.liminf`
and `Filter.limsup` of a real sequence:

* `liminf r(n)/n < ∞` ⟺ for some natural `C`, `r(n) ≤ C·n` for infinitely many `n`;
* `limsup r(n)/(n (log n)^η) < ∞` ⟺ for some real `C` and some `n₀`, `r(n) ≤ C·n·(log n)^η`
  for all `n ≥ n₀`.

Both equivalences are immediate (round `C` up in the first).  This is the form the consumers in
`BB47/TheoremA.lean` produce from Lemma A0, and stating the axiom this way keeps the only
analytic step — the normalisation `0 < η < 1/11` of Theorem A′ — in the file that proves a
theorem rather than in the file that quotes one.

## References

* [BK19] Y. Bugeaud, D. H. Kim, *A new complexity function, repetitions in Sturmian words, and
  irrationality exponents of Sturmian numbers*, Trans. Amer. Math. Soc. **371** (2019),
  3281–3308 (arXiv:1510.00279) — **Thm. 10.4**, with Lem. 10.3 and Thms. 4.2/4.3.
* [AB07] B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in
  integer bases*, Ann. of Math. **165** (2007), 547–565 — Thm. 5 and Condition `(∗)_w`.
* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), 221–250 — Thm. 2.1, the source of the exponent `1/11`.
* [ABL04] B. Adamczewski, Y. Bugeaud, F. Luca, C. R. Acad. Sci. Paris **339** (2004), 11–14.
* [Bug13] Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci.
  Éc. Norm. Supér. **46** (2013), 1005–1022.
-/

namespace BB47

open ForMathlib.SubwordComplexity

/-- The real number in `[0, 1)` whose base-`b` expansion is the digit word `w`, i.e.
`∑ₖ wₖ b^{-(k+1)}`: Mathlib's `Real.ofDigits`, the number about which the Subspace-Theorems
library states [AB07]. -/
@[category API, AMS 11 37 68, ref "Bug12" "AB07", group "bugeaud_10_47"]
noncomputable def value (b : ℕ) (w : ℕ → Fin b) : ℝ := Real.ofDigits w

/-- The complexity of `ForMathlib.SubwordComplexity` (factors as `Fin n → α`) is the complexity
of the Subspace-Theorems library (factors as lists): `List.ofFn` matches the two factor sets. -/
@[category API, AMS 68]
theorem pComplexity_eq_complexity {α : Type*} (w : ℕ → α) (n : ℕ) :
    pComplexity w n = Function.complexity w n := by
  have h : Function.factors w n = List.ofFn '' factorSet w n := by
    ext l
    simp only [Function.factors, Function.factor, factorSet, Set.mem_range, Set.mem_image,
      exists_exists_eq_and]
    rfl
  rw [Function.complexity, h, Set.ncard_image_of_injective _ List.ofFn_injective, pComplexity]

/-- **[AB07, Thm. 1], contrapositive.**  If the complexity of the digit word is at most `C·n` for
infinitely many `n`, an irrational `value b w` is transcendental.  Formerly derived from the cited
axiom `AB.tendsto_pComplexity_div_atTop`; now from the Subspace-Theorems library's
`Real.transcendental_ofDigits_of_frequently_complexity_le` ([AB07, Thm. 5] and Thm. 1). -/
@[category research solved, AMS 11 68, ref "AB07", group "ab_complexity_thm1"]
theorem transcendental_of_pComplexity_linear_io {b : ℕ} (hb : 2 ≤ b) (w : ℕ → Fin b)
    (hirr : Irrational (value b w)) (C : ℝ)
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (pComplexity w n : ℝ) ≤ C * n) :
    Transcendental ℚ (value b w) :=
  Real.transcendental_ofDigits_of_frequently_complexity_le hb
    ((Real.irrational_ofDigits_iff hb).mp hirr)
    (Filter.frequently_atTop.mpr fun N ↦ by
      obtain ⟨n, hn, hle⟩ := h N
      exact ⟨n, hn, pComplexity_eq_complexity w n ▸ hle⟩)

/-- **[BK19, Thm. 10.4], clause 1.**  If the repetition function of a non-eventually-periodic
digit word is `O(n)` along a subsequence, the number it defines is transcendental.

Cited axiom: the proof rests on the Adamczewski–Bugeaud combinatorial transcendence criterion
[AB07, Thm. 5] and hence on the `p`-adic Subspace theorem — the same engine as
`Real.transcendental_ofDigits_of_isAutomatic` and `Padic.transcendental_ofDigits_of_isStammering`
in the Subspace-Theorems library. -/
@[category research solved, AMS 11 37 68, ref "BK19" "AB07", group "bugeaud_10_47"]
axiom transcendental_of_repLen_liminf {b : ℕ} (hb : 2 ≤ b) (w : ℕ → Fin b)
    (hw : ¬ IsEventuallyPeriodic w) (C : ℕ)
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ repLen w n ≤ C * n) :
    Transcendental ℚ (value b w)

/-- **[BK19, Thm. 10.4], clause 2.**  The same conclusion from the weaker, *two-sided* hypothesis
`r(n, w) = O(n (log n)^η)` for a single `η < 1/11`.

Cited axiom: this clause comes from the **quantitative** Subspace theorem through
[BE08, Thm. 2.1]; the exponent `1/11` traces to the exponent on `ε⁻¹` in the Quantitative
Parametric Subspace Theorem of Evertse–Schlickewei, which is why research bet R3 of the plan is
explicitly a bet on improving that count. -/
@[category research solved, AMS 11 37 68, ref "BK19" "BE08", group "bugeaud_10_47"]
axiom transcendental_of_repLen_limsup {b : ℕ} (hb : 2 ≤ b) (w : ℕ → Fin b)
    (hw : ¬ IsEventuallyPeriodic w) (η : ℝ) (hη : η < 1 / 11) (C : ℝ) (n₀ : ℕ)
    (h : ∀ n : ℕ, n₀ ≤ n → (repLen w n : ℝ) ≤ C * (n : ℝ) * Real.log n ^ η) :
    Transcendental ℚ (value b w)

end BB47
