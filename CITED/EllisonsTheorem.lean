/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Ellison's effective lower bound for `|2ʲ − 3^q|` (Pillai's problem)

W. J. Ellison's effective solution of a problem of S. Sivasankaranarayana Pillai: the two prime
powers `2ʲ` and `3^q` cannot be too close together.  Precisely, once `j` is beyond an explicit
bound the gap satisfies
`|2ʲ − 3^q| > 2ʲ · e^{−j/10}`.
Since `2ʲ · e^{−j/10} = (2 e^{−1/10})ʲ`, the gap grows geometrically in `j`.

This is the linear-forms-in-two-logarithms input used by Rozier–Terracol ([Roz25], Appendix B,
Lemma B.1, citing Ellison's Theorem 3) to bound how closely a Collatz excursion can return to its
starting value.

## Contents
* `Ellison.pillai_lower_bound` — **Ellison's Theorem 3** ([Ell71]):
  `28 ≤ j → 2ʲ · e^{−j/10} < |2ʲ − 3^q|`; a cited transcendence estimate recorded as an `axiom`.

## References
* [Ell71] Ellison, W. J. "On a theorem of S. Sivasankaranarayana Pillai."
  *Séminaire de théorie des nombres de Bordeaux* (1971): 1–10.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). Appendix B, Lemma B.1.
-/

namespace Ellison

/-- **Ellison's Theorem 3** ([Ell71]), an effective form of a theorem of S. S. Pillai: for every
`j ≥ 28` and every `q`, the powers `2ʲ` and `3^q` satisfy
`|2ʲ − 3^q| > 2ʲ · e^{−j/10}`.

This is the effective linear-forms-in-logarithms lower bound quoted by Rozier–Terracol ([Roz25],
Appendix B): with `2ʲ · e^{−j/10} = (2 e^{−1/10})ʲ` the two prime powers stay geometrically far
apart.  Recorded as a cited `axiom` on the authority of Ellison's paper — a Padé-approximant /
transcendence estimate we do not re-derive. -/
@[category research solved, AMS 11, ref "Ell71", group "roz_lemma_b1"]
axiom pillai_lower_bound (j q : ℕ) (hj : 28 ≤ j) :
    (2 : ℝ) ^ j * Real.exp (-(j : ℝ) / 10) < |(2 : ℝ) ^ j - 3 ^ q|

end Ellison
