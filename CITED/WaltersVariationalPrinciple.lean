/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Price
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The variational principle for the pressure, on the full `2`-shift

The second cited axiom of the 10.61 root, and the only external input of the *duality* Theorem
3.4 of `paper.tex` (Theorem B(iii), "the exact price"):

`P(σ, ψ, P₀) ≤ sup_{μ ∈ M(σ)} (h_μ(σ, P₀) + ∫ψ dμ)`   for continuous `ψ`,

with `P₀` the time-zero coordinate partition of `{0,1}^ℤ`.

## Why only one inequality

The **other** inequality is a theorem in this repository:
`MeasureTheory.entropyRate_add_integral_le_partitionPressure` of
`ForMathlib/Dynamics/TopologicalPressure.lean` is the Jensen half, and
`BB61.measurePressure_le_partitionPressure` packages it as
`measurePressure ψ ≤ partitionPressure σ ψ P₀`.  So the axiom below is exactly the half that is
missing, and `Walters.partitionPressure_eq_measurePressure` puts the two together.

## What the citation covers

[Wal82] Theorem 9.10 is the variational principle `P_top(T, ψ) = sup_μ (h_μ(T) + ∫ψ dμ)` for a
continuous map of a compact metric space.  Two identifications turn it into the statement below,
and both are folded into the citation:

1. **`partitionPressure σ ψ P₀` is the topological pressure `P_top(σ, ψ)`.**  The cells of
   `⋁_{i<n} σ^{-i}P₀` are the cylinders on the coordinate window `[0, n)`, which do *not* shrink
   in the two-sided metric — they say nothing about the negative coordinates.  What makes the two
   agree for a **continuous** `ψ` is that the oscillation of `ψ` over the set of points agreeing on
   `[-i, n-i)` tends to `0` with `i`, so the Cesàro average of those oscillations vanishes and
   `sup_{[w]} S_nψ` may be replaced by the value at any point of `[w]`.  This is the standard
   cylinder formula for the pressure on a subshift ([Wal82] Ch. 9; Bowen, *Equilibrium States*,
   §1).  For a merely bounded measurable `ψ` it is **false**, which is why the axiom is stated for
   `ψ : Shift →ᵇ ℝ`.
2. **`entropyRate σ μ P₀` is the Kolmogorov–Sinai entropy `h_μ(σ)`.**  The coordinate partition
   generates the Borel σ-algebra two-sidedly, so this is the Kolmogorov–Sinai generator theorem
   ([Wal82] Ch. 4) — the same identification the root's other cited axiom,
   `LY.entropyRate_floor`, already folds in (see `CITED/LedrappierYoung.lean`, item 5).  Stating
   the axiom in the *relative* form keeps every consumer citation-consistent with that one.

## What this axiom is **not** used for

Nothing in `BB61/Price.lean`.  The duality itself —
`BB61.iInf_measurePressure_eq_priceEntropy`, which is Theorem 3.4 with the measure side of the
variational principle in place of the topological pressure — is proved from Lean's three standard
axioms alone, by geometric Hahn–Banach.  This axiom is consumed only where the paper's statement
mentions the *topological* pressure: `BB61.iInf_partitionPressure_eq_priceEntropy` and the
implication (iii) ⇒ (iv) of Corollary 3.5, both in `BB61/PriceCompleteness.lean`.

## References

* [Wal82] P. Walters, *An Introduction to Ergodic Theory*, GTM 79, Springer 1982, Theorem 9.10
  (the variational principle) and Chapter 4 (the Kolmogorov–Sinai generator theorem).
* [Bow75] R. Bowen, *Equilibrium States and the Ergodic Theory of Anosov Diffeomorphisms*, LNM
  470, Springer 1975, §1 (the cylinder formula for the pressure of a subshift).
* [Mis76] M. Misiurewicz, "A short proof of the variational principle for a `ℤ₊^N` action on a
  compact space", *Astérisque* **40** (1976), 147–157.
-/

namespace Walters

open MeasureTheory Dynamics BB61 BoundedContinuousFunction

/-- **The variational principle, hard half** ([Wal82] Thm 9.10).  For a continuous potential on the
full `2`-shift, the pressure computed over cylinders is at most the supremum of
`h_μ(σ, P₀) + ∫ψ dμ` over the shift-invariant probability measures.

Recorded as a cited `axiom`.  The reverse inequality is proved
(`BB61.measurePressure_le_partitionPressure`), and the two identifications the citation absorbs —
cylinders compute the topological pressure of a *continuous* potential, and the coordinate
partition is a generator — are set out in the module doc. -/
@[category research solved, AMS 37 28 11, ref "Wal82" "Bow75" "Mis76", group "bugeaud_10_61"]
axiom partitionPressure_le_measurePressure (ψ : Shift →ᵇ ℝ) :
    partitionPressure shiftZ (⇑ψ) coordPartition ≤ measurePressure (⇑ψ)

/-- **The variational principle** on the full `2`-shift, as an equality: the cited hard half above
together with the proved Jensen half. -/
@[category research solved, AMS 37 28 11, ref "Wal82" "Bow75" "Mis76", group "bugeaud_10_61"]
theorem partitionPressure_eq_measurePressure (ψ : Shift →ᵇ ℝ) :
    partitionPressure shiftZ (⇑ψ) coordPartition = measurePressure (⇑ψ) :=
  le_antisymm (partitionPressure_le_measurePressure ψ)
    (measurePressure_le_partitionPressure ψ.continuous (fun ω => by
      simpa [Real.norm_eq_abs] using (le_abs_self (ψ ω)).trans (ψ.norm_coe_le_norm ω)))

end Walters
