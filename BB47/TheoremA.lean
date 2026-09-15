/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import BB47.Cited

/-!
# Theorems A and A′: the horizon theorems

This is §§5–6 of `BB47/M1M2.tex`, milestone M2 of `plans/plan-1047.html`.  Everything here is one
elementary inequality fed into a cited theorem (`BB47/Cited.lean`); the files are kept apart
precisely so that the boundary between what is proved and what is quoted is visible in the import
graph.

Throughout, `w : ℕ → Fin b` is the base-`b` digit word of an irrational number in `[0,1)`, and
`s_n = horizon w n`, `p_∞(n) = pInf w n`.

## Two routes, and which one is primary

**Primary (rewritten 2026-09-13).**  The horizon bound `p(n, w) ≤ s_n + p_∞(n, w)`
(`BB47.pComplexity_le_horizon_add_pInf`) makes each hypothesis below a hypothesis on the
*ordinary* complexity, and the complexity lower bounds for algebraic irrationals then apply
directly: `AB.tendsto_pComplexity_div_atTop` = [AB07, Thm. 1] for Theorem A, and
`BugeaudEvertse.exists_pComplexity_gt` = [BE08, Thm. 2.1] for Theorem A′.  Neither proof mentions
the repetition function, and Theorem A′ needs no normalisation of `η`.

**Secondary.**  `BB47.theorem_A_via_repLen` and `BB47.theorem_Aprime_via_repLen` run the same
hypotheses through Lemma A0 and the packaged criterion [BK19, Thm. 10.4].  They are kept because
that is the route [M1M2, §5] writes up second, because `repLen` is what `BB47/Sliver.lean` is
phrased against, and because in Lean they are formally slightly stronger: their hypothesis is
`¬ IsEventuallyPeriodic w`, which is weaker than `Irrational (value b w)` only because Mathlib
lacks the classical characterisation of rationals by eventually periodic expansions.

## Main results

* `BB47.theorem_A` — **Theorem A.**  If `liminf (s_n + p_∞(n))/n < ∞` then `value b w` is
  transcendental.  From [AB07, Thm. 1].
* `BB47.theorem_Aprime` — **Theorem A′.**  If `limsup (s_n + p_∞(n))/(n (log n)^η) < ∞` for some
  `η < 1/11`, the same conclusion.  From [BE08, Thm. 2.1].
* `BB47.theorem_A_via_repLen`, `BB47.theorem_Aprime_via_repLen` — the same two statements through
  Lemma A0 and [BK19, Thm. 10.4].
* `BB47.transcendental_of_minimal_pInf` — the case of Problem 10.47 itself: minimal eventual
  complexity plus a horizon that is `O(n)` infinitely often forces transcendence.
* `BB47.transcendental_of_pInf_linear` — **the whole `n + k` ladder, uniformly**: the same under
  `p_∞(n) ≤ C₀·n`, with no dependence on `k`.  This is why milestone M8 of the plan folded into
  M2 with no separate work.
* `BB47.structure_of_algebraic`, `BB47.structure_of_algebraic_log` — **the quotable form**: for an
  algebraic value the two `liminf`/`limsup` above are `+∞`.
* `BB47.exists_pInf_ge_of_algebraic` — the conditional form of Theorem W: for an algebraic value,
  either some `n` has `p_∞(n) ≥ n + 2`, or the horizon is superlinear.

## What is *not* here

Theorem W itself — "no algebraic irrational has `p_∞(n) = n + 1` for every `n`" — is **open**.
What the above delivers is the frontier: everything up to `s_n = O(n (log n)^η)`, `η < 1/11`, is
closed, and everything past it is open.  See §4.4 of the plan.

## Why no irrationality measure follows

[BK19, Thm. 4.2] gives `μ(ξ) ≥ rep(w)/(rep(w) − 1)`, which exceeds `2` exactly when `rep(w) < 2`.
Lemma A0 yields `rep(w) ≤ 1 + liminf (s_n + p_∞(n))/n`, and by `BB47.succ_le_pInf` the right-hand
side is always at least `2`.  So the pigeonhole route cannot produce an irrationality measure,
only transcendence.  See [M1M2, Rem. 6.7].

## References

* [M1M2] `BB47/M1M2.tex` (this repository, 2026-09) — §6, Thms. 6.1, 6.2, Cors. 6.3–6.5; §5,
  Thms. 5.1–5.3 for the three quoted inputs.
* [AB07] B. Adamczewski, Y. Bugeaud, Ann. of Math. **165** (2007), 547–565 — Thm. 1.
* [BK19] Y. Bugeaud, D. H. Kim, Trans. Amer. Math. Soc. **371** (2019), 3281–3308.
* [BE08] Y. Bugeaud, J.-H. Evertse, Acta Arith. **133** (2008), 221–250.
* [FM97] S. Ferenczi, C. Mauduit, *Transcendence of numbers with a low complexity expansion*,
  J. Number Theory **67** (1997), 146–161 — the bounded-horizon special case.
-/

namespace BB47

open ForMathlib.SubwordComplexity

variable {b : ℕ}

/-! ## The two growth hypotheses -/

/-- `liminf (s_n + p_∞(n))/n < ∞`: for some constant `C`, the horizon plus the eventual
complexity is at most `C·n` for infinitely many `n`. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
def HorizonLinearIO (w : ℕ → Fin b) : Prop :=
  ∃ C : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ horizon w n + pInf w n ≤ C * n

/-- `limsup (s_n + p_∞(n))/(n (log n)^η) < ∞`. -/
@[category API, AMS 11 37 68, ref "BE08", group "bugeaud_10_47"]
def HorizonLogBounded (w : ℕ → Fin b) (η : ℝ) : Prop :=
  ∃ (C : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n →
    ((horizon w n : ℝ) + (pInf w n : ℝ)) ≤ C * (n : ℝ) * Real.log n ^ η

/-- `liminf s_n / n < ∞`, the horizon alone. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
def HorizonSublinearIO (w : ℕ → Fin b) : Prop :=
  ∃ C : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ horizon w n ≤ C * n

/-! ## Theorem A -/

/-- **Theorem A** [M1M2, Thm. 6.1].  If the non-recurrent prefix and the eventual complexity
together grow linearly along a subsequence, the number is transcendental.

Proof: the horizon bound `p(n, w) ≤ s_n + p_∞(n, w)` turns the hypothesis into
`p(n, w) ≤ C·n` infinitely often, i.e. `liminf p(n, ξ, b)/n < ∞`, which [AB07, Thm. 1] forbids
for an algebraic irrational.  No repetition function, no pigeonhole; see
`BB47.theorem_A_via_repLen` for the longer route through [BK19, Thm. 10.4]. -/
@[category research solved, AMS 11 37 68, ref "AB07" "Bug12", group "bugeaud_10_47"]
theorem theorem_A (hb : 2 ≤ b) (w : ℕ → Fin b) (hirr : Irrational (value b w))
    (h : HorizonLinearIO w) : Transcendental ℚ (value b w) := by
  obtain ⟨C, hC⟩ := h
  refine AB.transcendental_of_pComplexity_linear_io hb w hirr (C : ℝ) fun N => ?_
  obtain ⟨n, hn, hnv⟩ := hC N
  refine ⟨n, hn, ?_⟩
  have : pComplexity w n ≤ C * n := le_trans (pComplexity_le_horizon_add_pInf w n) hnv
  exact_mod_cast this

/-- **Theorem A, second proof** — the route of [M1M2, §5] through the repetition function.

Lemma A0 turns the hypothesis into `r(n, w) ≤ (C+1)·n` infinitely often, which is clause 1 of
[BK19, Thm. 10.4].  Formally this is a slightly *stronger* statement than `BB47.theorem_A`,
because `¬ IsEventuallyPeriodic w` is a weaker hypothesis than `Irrational (value b w)` in Lean —
the two are equivalent for digit words, but that equivalence is not in Mathlib. -/
@[category research solved, AMS 11 37 68, ref "BK19" "Bug12", group "bugeaud_10_47"]
theorem theorem_A_via_repLen (hb : 2 ≤ b) (w : ℕ → Fin b) (hw : ¬ IsEventuallyPeriodic w)
    (h : HorizonLinearIO w) : Transcendental ℚ (value b w) := by
  obtain ⟨C, hC⟩ := h
  refine transcendental_of_repLen_liminf hb w hw (C + 1) fun N => ?_
  obtain ⟨n, hn, hnv⟩ := hC N
  refine ⟨n, hn, ?_⟩
  have hA0 := lemma_A0 w n
  have hexp : (C + 1) * n = C * n + n := by ring
  omega

/-- **Theorem A′** [M1M2, Thm. 6.2].  The same conclusion from the two-sided hypothesis
`s_n + p_∞(n) = O(n (log n)^η)` for a single `η < 1/11`.

The horizon bound sends the hypothesis straight into [BE08, Thm. 2.1]; unlike the route through
Lemma A0 (`BB47.theorem_Aprime_via_repLen`) there is no `+ n` to absorb, so the normalisation of
`η` that route needs disappears and the proof is two lines. -/
@[category research solved, AMS 11 37 68, ref "BE08" "Bug12", group "bugeaud_10_47"]
theorem theorem_Aprime (hb : 2 ≤ b) (w : ℕ → Fin b) (hirr : Irrational (value b w))
    {η : ℝ} (hη : η < 1 / 11) (h : HorizonLogBounded w η) :
    Transcendental ℚ (value b w) := by
  obtain ⟨C, n₀, hC⟩ := h
  refine BugeaudEvertse.transcendental_of_pComplexity_log_bounded hb w hirr hη C n₀ fun n hn => ?_
  have hsplit : (pComplexity w n : ℝ) ≤ (horizon w n : ℝ) + (pInf w n : ℝ) := by
    exact_mod_cast pComplexity_le_horizon_add_pInf w n
  linarith [hC n hn]

/-- **Theorem A′, second proof** — the route of [M1M2, §5] through the repetition function.

The only analytic step is the normalisation: for `n ≥ 3` the map `η ↦ (log n)^η` is increasing, so
the hypothesis for `η` implies it for `η' := max η (1/22) ∈ (0, 1/11)`, and then `(log n)^η' ≥ 1`
absorbs the `+ n` that Lemma A0 contributes. -/
@[category research solved, AMS 11 37 68, ref "BK19" "BE08", group "bugeaud_10_47"]
theorem theorem_Aprime_via_repLen (hb : 2 ≤ b) (w : ℕ → Fin b) (hw : ¬ IsEventuallyPeriodic w)
    {η : ℝ} (hη : η < 1 / 11) (h : HorizonLogBounded w η) :
    Transcendental ℚ (value b w) := by
  obtain ⟨C, n₀, hC⟩ := h
  set η' : ℝ := max η (1 / 22) with hη'def
  have hη'pos : 0 < η' := lt_of_lt_of_le (by norm_num) (le_max_right η (1 / 22))
  have hη'lt : η' < 1 / 11 := max_lt hη (by norm_num)
  have hηη' : η ≤ η' := le_max_left _ _
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : (0 : ℝ) ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  refine transcendental_of_repLen_limsup hb w hw η' hη'lt (C' + 1) (max n₀ 3) fun n hn => ?_
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := by linarith
  -- `log n ≥ 1` for `n ≥ 3`, since `exp 1 < 2.72 < 3`
  have hlog : (1 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log n := by linarith
  have hPη0 : (0 : ℝ) ≤ Real.log n ^ η := Real.rpow_nonneg hlog0 η
  have hmono : Real.log n ^ η ≤ Real.log n ^ η' := Real.rpow_le_rpow_of_exponent_le hlog hηη'
  have hone : (1 : ℝ) ≤ Real.log n ^ η' := by
    have := Real.rpow_le_rpow_of_exponent_le hlog (le_of_lt hη'pos)
    rwa [Real.rpow_zero] at this
  -- Lemma A0, cast to `ℝ`
  have hA0 : (repLen w n : ℝ) ≤ (horizon w n : ℝ) + (n : ℝ) + (pInf w n : ℝ) := by
    have := lemma_A0 w n
    exact_mod_cast this
  have hCn := hC n hn0
  -- assemble
  have e1 : C * (n : ℝ) * Real.log n ^ η ≤ C' * (n : ℝ) * Real.log n ^ η := by
    have : (0 : ℝ) ≤ (n : ℝ) * Real.log n ^ η := mul_nonneg hnpos hPη0
    nlinarith
  have e2 : C' * (n : ℝ) * Real.log n ^ η ≤ C' * (n : ℝ) * Real.log n ^ η' := by
    have : (0 : ℝ) ≤ C' * (n : ℝ) := mul_nonneg hC'0 hnpos
    nlinarith
  have e3 : (n : ℝ) ≤ (n : ℝ) * Real.log n ^ η' := by nlinarith
  have e4 : (C' + 1) * (n : ℝ) * Real.log n ^ η' = C' * (n : ℝ) * Real.log n ^ η' +
      (n : ℝ) * Real.log n ^ η' := by ring
  linarith

/-! ## Corollaries -/

/-- [M1M2, Cor. 6.3]: **minimal eventual complexity**.  If `p_∞(n) = n + 1` for every `n` — the
hypothesis of Problem 10.47 — and the horizon is `O(n)` infinitely often, the number is
transcendental. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BK19", group "bugeaud_10_47"]
theorem transcendental_of_minimal_pInf (hb : 2 ≤ b) (w : ℕ → Fin b)
    (hirr : Irrational (value b w)) (hp : ∀ n, pInf w n = n + 1) (hs : HorizonSublinearIO w) :
    Transcendental ℚ (value b w) := by
  obtain ⟨C, hC⟩ := hs
  refine theorem_A hb w hirr ⟨C + 2, fun N => ?_⟩
  obtain ⟨n, hn, hnv⟩ := hC (max N 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  refine ⟨n, le_trans (le_max_left N 1) hn, ?_⟩
  rw [hp n]
  have hexp : (C + 2) * n = C * n + n + n := by ring
  have : 1 ≤ n := hn1
  omega

/-- [M1M2, Cor. 6.4]: **the whole `n + k` ladder, uniformly**.  The hypothesis needed is only
`p_∞(n) ≤ C₀·n`, with no dependence on `C₀` in the argument; so Theorem A applies simultaneously
to every `k` under `p_∞(n) ≤ n + k`. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BK19", group "bugeaud_10_47"]
theorem transcendental_of_pInf_linear (hb : 2 ≤ b) (w : ℕ → Fin b)
    (hirr : Irrational (value b w)) {C₀ : ℕ} (hp : ∀ n, pInf w n ≤ C₀ * n)
    (hs : HorizonSublinearIO w) : Transcendental ℚ (value b w) := by
  obtain ⟨C, hC⟩ := hs
  refine theorem_A hb w hirr ⟨C + C₀, fun N => ?_⟩
  obtain ⟨n, hn, hnv⟩ := hC N
  refine ⟨n, hn, ?_⟩
  have hpn := hp n
  have hexp : (C + C₀) * n = C * n + C₀ * n := by ring
  omega

/-- The `n + k` form, for every `k` at once. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BK19", group "bugeaud_10_47"]
theorem transcendental_of_pInf_add_const (hb : 2 ≤ b) (w : ℕ → Fin b)
    (hirr : Irrational (value b w)) {k : ℕ} (hp : ∀ n, pInf w n ≤ n + k)
    (hs : HorizonSublinearIO w) : Transcendental ℚ (value b w) := by
  obtain ⟨C, hC⟩ := hs
  refine theorem_A hb w hirr ⟨C + k + 1, fun N => ?_⟩
  obtain ⟨n, hn, hnv⟩ := hC (max N 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  refine ⟨n, le_trans (le_max_left N 1) hn, ?_⟩
  have hpn := hp n
  have hexp : (C + k + 1) * n = C * n + k * n + n := by ring
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn1
  omega

/-! ## The quotable form: structure of hypothetical counterexamples -/

/-- [M1M2, Cor. 6.5], first half: for an **algebraic** value, `liminf (s_n + p_∞(n))/n = +∞`. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BK19", group "bugeaud_10_47"]
theorem structure_of_algebraic (hb : 2 ≤ b) (w : ℕ → Fin b) (hirr : Irrational (value b w))
    (halg : IsAlgebraic ℚ (value b w)) : ¬ HorizonLinearIO w :=
  fun h => theorem_A hb w hirr h halg

/-- [M1M2, Cor. 6.5], second half: and `limsup (s_n + p_∞(n))/(n (log n)^η) = +∞` for every
`η < 1/11`. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BE08", group "bugeaud_10_47"]
theorem structure_of_algebraic_log (hb : 2 ≤ b) (w : ℕ → Fin b) (hirr : Irrational (value b w))
    (halg : IsAlgebraic ℚ (value b w)) {η : ℝ} (hη : η < 1 / 11) : ¬ HorizonLogBounded w η :=
  fun h => theorem_Aprime hb w hirr hη h halg

/-- **The conditional form of Theorem W.**  For an algebraic irrational value: either some scale
already has more than the minimal number of recurrent blocks, or the non-recurrent prefix grows
faster than linearly.

Theorem W asserts the first alternative unconditionally.  That is open; this is the frontier. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BK19", group "bugeaud_10_47"]
theorem exists_pInf_ge_of_algebraic (hb : 2 ≤ b) (w : ℕ → Fin b) (hw : ¬ IsEventuallyPeriodic w)
    (hirr : Irrational (value b w)) (halg : IsAlgebraic ℚ (value b w)) :
    (∃ n, n + 2 ≤ pInf w n) ∨ ¬ HorizonSublinearIO w := by
  by_cases hp : ∃ n, n + 2 ≤ pInf w n
  · exact Or.inl hp
  · refine Or.inr fun hs => ?_
    have hpall : ∀ n, pInf w n = n + 1 := by
      intro n
      have h1 := succ_le_pInf hw n
      have h2 : ¬ (n + 2 ≤ pInf w n) := fun hc => hp ⟨n, hc⟩
      omega
    exact transcendental_of_minimal_pInf hb w hirr hpall hs halg

end BB47
