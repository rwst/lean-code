/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.Solenoid.Haar
import ForMathlib.Dynamics.KolmogorovSinai
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# `p`-adic entropy of solenoid automorphisms: `h_Haar(×2) = log 2` on `Σ₆` (Lind–Ward)

[LW88] computes the measure entropy of an automorphism `α` of a solenoid with respect to Haar
measure as the sum of the positive logarithmic valuations,

`h(α) = ∑_v log⁺ |α|_v`,

the sum over the places of the relevant number field.  For `α = ×2` on `Σ₆` the three places
contribute `log⁺|2|_∞ = log 2`, `log⁺|2|₂ = log⁺ (1/2) = 0` and `log⁺|2|₃ = 0`, so the value is
`log 2` — the archimedean direction is the only expanding one for `σ₂`.

## Why this is a *second* axiom, and not a consequence of `EL.rigidity_decomposition`

The rigidity axiom of `CITED/EinsiedlerLindenstrauss.lean` applied to `μ = Haar` returns some
`c ∈ [0, 1]` and `ν₀` with `Haar = c · Haar + (1 - c) · ν₀`, `h_{ν₀}(σ₂) = 0` and
`h_Haar(σ₂) = c · log 2`.  The choice `c = 0`, `ν₀ = Haar` satisfies every conjunct whenever
`h_Haar(σ₂) = 0`, so the decomposition alone does **not** pin the value: the entropy-mass link is
calibrated by this axiom, not by that one.  (Gate G1 records the same point from the literature
side: the identity `c = h_μ(σ₂)/log 2` appears in none of the four rigidity sources.)

Only the **lower** bound `log 2 ≤ h_Haar(σ₂)` is consumed downstream — by `TH.S6.M7_iff_bridge`,
whose forward direction must certify that Haar itself satisfies `EntropyProduction ξ (log 2)`.
The `M6`/`M7` implications (`TH.S6.M6_of_bridge`, `TH.S6.M7_of_bridge`) and the trichotomy do not
use this file at all.

## De-axiomatization target

This is provable in the corpus as it stands, and should eventually be discharged (precedent: the
H1 discharge of `Bertin.uniformlyDistributedModOne_of_weylCriterion`).  Route: the archimedean
binary-digit partition — `f x = 0` or `1` according to the half of `[0,1)` containing the real
coordinate of the fundamental-domain representative — has, after `n` steps of
`ForMathlib.Dynamics.KolmogorovSinai.joinIter` along `σ₂`, exactly `2ⁿ` atoms, each a cell of Haar
mass `2⁻ⁿ` by `TH.S6.haar_cell`.  Hence `partitionEntropy = n log 2`, `entropyRate = log 2`, and
`le_kolmogorovSinai` gives the bound.  What that costs is the identification of the atoms of the
join with dyadic cells, i.e. the binary-digit bookkeeping for `σ₂` acting on the real coordinate —
a self-contained piece of work that W6 declined to take on in order to ship the bridge.

## References

* [LW88] D. Lind & T. Ward, "Automorphisms of solenoids and `p`-adic entropy", *Ergodic Theory
  Dynam. Systems* **8** (1988), 411–419.
* Plan A1+ §4 L7 (gate-G1 verdict box, item 6(c)) and §3.1.
-/

namespace LindWard

open MeasureTheory TH.S6

/-- **The `p`-adic entropy formula, evaluated at `×2` on `Σ₆`** ([LW88]): the Haar entropy of the
solenoid automorphism `σ₂` is `log 2`, the archimedean place being the only expanding one.

Recorded as a cited `axiom`; see the module doc for why it does not follow from
`EL.rigidity_decomposition`, and for the route by which it should eventually be discharged. -/
@[category research solved, AMS 37 28 11, ref "LW88", group "lindward_solenoid_entropy"]
axiom kolmogorovSinai_σ2_haar :
    kolmogorovSinai σ2 haar = ENNReal.ofReal (Real.log 2)

/-- The only consequence consumed downstream: Haar has at least `log 2` of `σ₂`-entropy. -/
@[category API, AMS 37 28 11, ref "LW88", group "lindward_solenoid_entropy"]
theorem le_kolmogorovSinai_σ2_haar :
    ENNReal.ofReal (Real.log 2) ≤ kolmogorovSinai σ2 haar :=
  le_of_eq kolmogorovSinai_σ2_haar.symm

end LindWard
