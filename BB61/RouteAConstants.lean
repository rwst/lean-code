/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Route A constants, collected in one module

`routeAExponent`, `logAlpha`, `coverTotal` and `familyConjBound` are the four definitions of the
comparator-compared closure whose bodies mention a real numeral `≥ 2`.  Elaborating `(2 : ℝ)`
inside a *definition* forces `instOfNatAtLeastTwo`, whose `Nat.AtLeastTwo` argument is a
proposition, and Lean lifts that proof into an auxiliary `_proof_` constant named after the
enclosing declaration.  That cache is **module-local**: a witness in an imported module is never
reused, so four definitions in four modules mint four distinct witnesses, while the same four
definitions in one module all share the first one's.

`comparator` compares definitions by value and does not quotient by proof irrelevance, so a
single-file challenge — which the Palomar registry requires, its challenge import closure being
restricted to Lean core and Mathlib — can only agree with this development if the development
also mints exactly one witness.  Hence this module, and hence the order below: `routeAExponent`
comes first here and is the first numeral-bearing definition of the flattened challenge, so both
environments name the shared witness `BB61.QuadSetup.routeAExponent._proof_1`.

The standing rule for new statements: **a definition in the compared closure whose body mentions
a real numeral `≥ 2` belongs here.**  A numeral in a *theorem's type* is harmless —
`abstractNestedProofs` skips theorems, so the instance stays inline.

Nothing here is mathematical.  The definitions are verbatim those that used to live in
`BB61/Criterion.lean`, `BB61/RouteANormalForm.lean`, `BB61/RouteADepth.lean` and
`BB61/RouteAFamily.lean`, and each of those modules still owns everything proved about them.
See the paper repo's `COMPARATOR.md` for the full account.
-/

noncomputable section

namespace BB61

namespace QuadSetup

variable (P : QuadSetup)

/-- **The Route A exponent** `A(α) = log2/log α + log2/log(1/ρ)` of M1 Corollary 5, the sum
of the box dimensions of the Cantor set `C(α)` and of the window `K`. -/
noncomputable def routeAExponent : ℝ :=
  Real.log 2 / Real.log P.α + Real.log 2 / Real.log |P.β|⁻¹

/-- `L = log₂ α`, the first of the two coordinates of the normal form: the reciprocal of
`dim_B C(α)`. -/
def logAlpha : ℝ := Real.logb 2 P.α

end QuadSetup

/-- **The note's covering total** `T(M,M') = 2^{M+M'}(α^{-M} + C ρ^{M'}/(1-ρ))`: the number
of covering intervals times a bound for each one's length.  `C` is left free — the note uses
`C_α = Σ_{j≥2}|α_j - 1|`, `BB61/Covering.lean` uses the bound `1 + ρ`. -/
def coverTotal (α ρ C : ℝ) (M M' : ℕ) : ℝ :=
  2 ^ (M + M') * ((α⁻¹) ^ M + C * ρ ^ M' / (1 - ρ))

/-- The note's `(2/a)^{1/(d-1)}`. -/
def familyConjBound (d a : ℕ) : ℝ := ((2 : ℝ) / (a : ℝ)) ^ (((d - 1 : ℕ) : ℝ)⁻¹)

end BB61

end
