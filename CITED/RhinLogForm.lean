/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# A linear form in `log 2` and `log 3` (Rhin)

Georges Rhin's effective irrationality measure for the linear form `u₀ + u₁·log 2 + u₂·log 3`
in the natural logarithms of `2` and `3`.  This is the linear-forms-in-logarithms input to the §6
finiteness argument of Rozier–Terracol ([Roz25], Proposition 6.3): combined with the heuristic
inequality (21) of `RT.Heuristic` it bounds the length `j` of a paradoxical Collatz excursion.

## Contents
* `Rhin.logForm` — the linear form `Λ = u₀ + u₁·log 2 + u₂·log 3` (`u₀, u₁, u₂ ∈ ℤ`).
* `Rhin.logHeight` — its height `H = max(|u₁|, |u₂|)`.
* `Rhin.logForm_lower_bound` — **Proposition 6.3**: `H ≥ 2 → |Λ| ≥ H^(-13.3)` (eq. (22)); a cited
  transcendence estimate recorded as an `axiom` on the authority of [Rhi87].

## References
* [Rhi87] Rhin, Georges. "Approximants de Padé et mesures effectives d'irrationalité."
  *Séminaire de Théorie des Nombres, Paris 1985–86*, 155–164. Boston, MA: Birkhäuser Boston, 1987.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). Proposition 6.3, eq. (22).
-/

namespace Rhin

/-- Rhin's **linear form** `Λ = u₀ + u₁·log 2 + u₂·log 3` in the natural logarithms of `2` and `3`,
for (rational) integers `u₀, u₁, u₂`. -/
@[category API, AMS 11, ref "Rhi87"]
noncomputable def logForm (u₀ u₁ u₂ : ℤ) : ℝ :=
  (u₀ : ℝ) + (u₁ : ℝ) * Real.log 2 + (u₂ : ℝ) * Real.log 3

/-- The **height** `H = max(|u₁|, |u₂|)` of the linear form `u₀ + u₁·log 2 + u₂·log 3`
(it does not involve the constant term `u₀`). -/
@[category API, AMS 11, ref "Rhi87"]
def logHeight (u₁ u₂ : ℤ) : ℤ := max |u₁| |u₂|

/-- **Proposition 6.3** (Rhin, [Rhi87]). An effective lower bound — an irrationality measure — for
the linear form in the logarithms of `2` and `3`: if `u₀, u₁, u₂` are rational integers whose height
`H = max(|u₁|, |u₂|)` is at least `2`, then
`|u₀ + u₁·log 2 + u₂·log 3| ≥ H^(-13.3)`   (eq. (22) of [Roz25]).

The finiteness endpoint of the §6 argument of [Roz25]: together with the heuristic bound (21) of
`RT.Heuristic` it forces the excursion length `j` of a paradoxical sequence to be bounded.  Recorded
as a cited `axiom` on the authority of Rhin's paper (a Padé-approximant transcendence estimate we do
not re-derive). -/
@[category research solved, AMS 11, ref "Rhi87", group "roz_heuristic"]
axiom logForm_lower_bound (u₀ u₁ u₂ : ℤ) (hH : 2 ≤ logHeight u₁ u₂) :
    (logHeight u₁ u₂ : ℝ) ^ (-(13.3 : ℝ)) ≤ |logForm u₀ u₁ u₂|

end Rhin
