/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.InfiniteComplexity
import AB.ExpansionsInIntegerBases

/-!
# Adamczewski–Bugeaud — the complexity of an algebraic number is superlinear (AB07, Theorem 1)

Boris Adamczewski and Yann Bugeaud, *On the complexity of algebraic numbers I. Expansions in
integer bases*, Annals of Mathematics **165** (2007), 547–565.

This file records **Theorem 1** of that paper, the complexity lower bound:

> *Let `b ≥ 2` be an integer.  The complexity function of the `b`-ary expansion of every
> algebraic irrational real number `ξ` satisfies*
> \[ \lim_{n\to+\infty}\frac{p(n,\xi,b)}{n}=+\infty . \]

Theorem 2 of the same paper — irrational automatic numbers are transcendental,
`AB.irrational_automatic_transcendental` in `AB/ExpansionsInIntegerBases.lean` — is deduced there
from *this* theorem together with Cobham's `p(n) = O(n)` for automatic sequences.  That file's
docstring names Theorem 1 without stating it; this file supplies it.

Recorded as a cited `axiom`: the proof rests on the `p`-adic Schmidt Subspace Theorem, through the
combinatorial transcendence criterion [AB07, Thm. 5] whose Condition `(∗)_w` is
`AB.ConditionStar`.  It is the same engine as `AB.transcendental_of_conditionStar`, but the
deduction of Theorem 1 from it is a separate combinatorial argument (the construction of a
stammering subsequence out of a complexity plateau) and is not reconstructed here.

## Faithfulness of the transcription

* The alphabet is `Fin b` and the real number is `AB.baseValue b (fun k => (w k : ℕ))`, so the
  object named here is the same one the rest of this root names.
* [AB07] normalises `ξ` to lie in `(0, 1)`; that is automatic for the value of a digit word, and
  adding an integer changes neither the algebraicity of `ξ` nor the complexity of the digit word
  beyond a bounded prefix.
* `pComplexity w n` (`ForMathlib/Combinatorics/InfiniteComplexity.lean`) is `p(n, ξ, b)`: the
  number of distinct length-`n` factors of the digit word.

## Contents

* `AB.tendsto_pComplexity_div_atTop` — Theorem 1, as a cited axiom.
* `AB.transcendental_of_pComplexity_linear_io` — the form consumers use: a digit word whose
  complexity is `≤ C·n` for infinitely many `n` defines a transcendental number.

## References

* [AB07] B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in
  integer bases*, Ann. of Math. **165** (2007), 547–565 — **Theorem 1**; Theorem 5 and
  Condition `(∗)_w` are the criterion it is proved from.
* [ABL04] B. Adamczewski, Y. Bugeaud, F. Luca, *Sur la complexité des nombres algébriques*,
  C. R. Acad. Sci. Paris **339** (2004), 11–14 — the announcement.
* [BE08] Y. Bugeaud, J.-H. Evertse, Acta Arith. **133** (2008), 221–250, Thm. 2.1 — the
  quantitative refinement, `CITED/BugeaudEvertseComplexity.lean`.
-/

namespace AB

open ForMathlib.SubwordComplexity

/-- **Theorem 1 (Adamczewski–Bugeaud 2007).**  The `b`-ary complexity of an algebraic irrational
number grows faster than linearly: `p(n, ξ, b)/n → +∞`.

Cited axiom; see the module docstring for the transcription and the source of the proof. -/
@[category research solved, AMS 11 68, ref "AB07" "ABL04", group "ab_complexity_thm1"]
axiom tendsto_pComplexity_div_atTop {b : ℕ} (hb : 2 ≤ b) (w : ℕ → Fin b)
    (halg : IsAlgebraic ℚ (baseValue b fun k => (w k : ℕ)))
    (hirr : Irrational (baseValue b fun k => (w k : ℕ))) :
    Filter.Tendsto (fun n : ℕ => (pComplexity w n : ℝ) / n) Filter.atTop Filter.atTop

/-- **Theorem 1, contrapositive.**  If the complexity of the digit word is at most `C·n` for
infinitely many `n` — i.e. `liminf_n p(n, ξ, b)/n < ∞` — then the number is transcendental.

This is the form the consumers use.  Irrationality is a genuine hypothesis: a rational number has
an eventually periodic expansion, whose complexity is bounded. -/
@[category research solved, AMS 11 68, ref "AB07", group "ab_complexity_thm1"]
theorem transcendental_of_pComplexity_linear_io {b : ℕ} (hb : 2 ≤ b) (w : ℕ → Fin b)
    (hirr : Irrational (baseValue b fun k => (w k : ℕ))) (C : ℝ)
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (pComplexity w n : ℝ) ≤ C * n) :
    Transcendental ℚ (baseValue b fun k => (w k : ℕ)) := by
  intro halg
  have hT := tendsto_pComplexity_div_atTop hb w halg hirr
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp hT (C + 1)).exists_forall_of_atTop
  obtain ⟨n, hn, hle⟩ := h (max N 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hdiv : C + 1 ≤ (pComplexity w n : ℝ) / n := hN n (le_trans (le_max_left N 1) hn)
  have : (C + 1) * n ≤ (pComplexity w n : ℝ) := by
    rw [le_div_iff₀ hnpos] at hdiv; exact hdiv
  nlinarith

end AB
