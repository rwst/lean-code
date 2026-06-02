/-
Copyright 2026 The lean-code Authors. Licensed under the Apache License, v2.0.

Ported from the Formal Conjectures project
(FormalConjectures/Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean)
to this repository's annotation set. Changes from the original:
  * `distToNearestInt` is defined locally (was in `FormalConjecturesForMathlib`),
    so it is a bespoke corpus def and shows up as a `states_with` target;
  * Problem 10.1 is stated as a plain existence proposition (the FC `answer(…)`
    question-wrapper is not part of this repo);
  * references / attributions / groupings use this repo's attributes
    (`ref`, `group`, `conjectured_by`, `extern_id`, `formal_uses`,
    `informal_uses`, and the `informal_result` registry).
-/
import Mathlib
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Bugeaud, *Distribution Modulo One*: fractional parts of powers (Chapter 10)

Formalizes Problems 10.1, 10.2, 10.3 and the unnumbered Waldschmidt conjecture.

*References:*
  - [Bug12] Bugeaud, Yann. *Distribution modulo one and Diophantine approximation.*
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Har19] Hardy, G. H. "A problem of Diophantine approximation." J. Indian Math. Soc 11 (1919).
  - [Kok45] Koksma, J. F. "Sur la théorie métrique des approximations diophantiques." Indag. Math 7 (1945).
  - [Mah53] Mahler, Kurt. "On the approximation of logarithms of algebraic numbers." Phil. Trans. R. Soc. A 245 (1953).
  - [Wal03] Waldschmidt, Michel. "Linear independence measures for logarithms of algebraic numbers." CIME 2000, Springer (2003).
-/

namespace Bugeaud

/-- The distance from a real number to the nearest integer. -/
@[category API, AMS 11, group "bugeaud_ch10"]
noncomputable def distToNearestInt (x : ℝ) : ℝ := |x - round x|

/--
Problem 10.1. Are there a transcendental number $\alpha$ with $|\alpha| > 1$ and a
positive real $\xi$ such that $\lVert \xi \alpha^n \rVert \to 0$ as $n \to \infty$?
(Trivial for $|\alpha| < 1$.) Originally raised by Hardy [Har19].
-/
@[category research open, AMS 11, group "bugeaud_ch10",
  ref "Bug12" "Har19", conjectured_by "Hardy" 1919]
theorem problem_10_1 : ∃ (α ξ : ℝ), 1 < |α| ∧ Transcendental ℚ α ∧ 0 < ξ ∧
    Filter.Tendsto (fun n : ℕ ↦ distToNearestInt (ξ * α ^ n)) Filter.atTop (nhds 0) := by
  sorry

/--
Problem 10.2. To prove that $\lVert e^n \rVert$ does not tend to $0$ as $n \to \infty$.
-/
@[category research open, AMS 11, group "bugeaud_ch10",
  ref "Bug12", conjectured_by "Bugeaud" 2012]
theorem problem_10_2 :
    ¬ Filter.Tendsto (fun n : ℕ ↦ distToNearestInt (Real.exp n)) Filter.atTop (nhds 0) := by
  sorry

/--
Problem 10.3. To prove that there exists $c > 0$ with $\lVert e^n \rVert > e^{-cn}$
for every $n \ge 1$. Posed by Mahler [Mah53].
-/
@[category research open, AMS 11, group "bugeaud_ch10",
  ref "Bug12" "Mah53", conjectured_by "Mahler" 1953]
theorem problem_10_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → Real.exp (-c * n) < distToNearestInt (Real.exp n) := by
  sorry

/--
Waldschmidt [Wal03] conjectured a stronger result: there exists $c > 0$ such that
$\lVert e^n \rVert > n^{-c}$ for every $n \ge 1$. Supported by metrical results [Kok45].
-/
@[category research open, AMS 11, group "bugeaud_ch10",
  ref "Bug12" "Wal03" "Kok45", conjectured_by "Waldschmidt" 2003,
  extern_id "https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/Cetraro.pdf"]
theorem waldschmidt :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (-c) < distToNearestInt (Real.exp n) := by
  sorry

/--
Waldschmidt's conjecture is stronger than Mahler's: since $\log n \le n$ for $n \ge 1$,
the polynomial lower bound $n^{-c}$ dominates the exponential bound $e^{-cn}$. This is
a proved reduction. It `formal_uses` `waldschmidt` (the statement it consumes as
hypothesis); it does *not* `formal_uses problem_10_3`, which it concludes.
-/
@[category test, AMS 11, group "bugeaud_ch10",
  formal_uses waldschmidt]
theorem problem_10_3_of_waldschmidt (h : type_of% waldschmidt) : type_of% problem_10_3 := by
  obtain ⟨c, hc, hyp⟩ := h
  refine ⟨c, hc, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  refine lt_of_le_of_lt ?_ (hyp n hn)
  rw [Real.rpow_def_of_pos hn_pos]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.log_le_self hn_pos.le])

end Bugeaud
