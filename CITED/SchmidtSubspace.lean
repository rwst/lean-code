/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.SubspaceTheorem
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Schmidt's Theorem 1D′: the Subspace Theorem with *algebraic* coefficients, cited

`CITED/SubspaceTheorem.lean` records the Evertse–Schlickewei **number-field** form of the Subspace
Theorem: the points range over `Kⁿ` and the threshold is the height *relative to* `K`.  That form
is the right one when the data lives in `K`.  It is the **wrong** one when the data is rational
and only the *coefficients* are algebraic, because Mathlib's `Height.mulHeight` is the relative
height, so a rational point acquires `H_K(x) = H_ℚ(x)^{[K:ℚ]}`
(`NumberField.mulHeight_ratCast`): the exponent `−n−ε` is then measured against an inflated
height while the approximation is small at *one* place only.

The cleanest illustration is Roth.  Over `K` the theorem gives
`|α − β| < H_K(β)^{-2-ε}` finitely often for `β ∈ K`; specialised to `β = p/q ∈ ℚ` that reads
`|α − p/q| < H(p/q)^{-D(2+ε)}`, which is *weaker* than Roth's theorem by the factor
`D = [K : ℚ]` in the exponent — it says nothing about the classical range.  The same factor is
what confined the anchored family of `RB/AnchoredEscape.lean` to the scales
`θ < (3/2)^{n_∞+1−2D} ≤ 2/3`.

The classical tool for rational data with algebraic coefficients is Schmidt's Theorem 1D′ (the
`S`-arithmetic Subspace Theorem, Schlickewei's `p`-adic extension of Schmidt's norm-form theorem),
recorded here:

> Let `S` be a finite set of places of `ℚ` containing the archimedean one.  For each `v ∈ S` let
> `L_{1,v}, …, L_{n,v}` be linearly independent linear forms in `n` variables with **algebraic**
> coefficients (in `ℚ̄ ⊆ ℚ̄_v`).  Then for every `ε > 0` the solutions `x ∈ ℤⁿ` of
> $$ \prod_{v\in S}\prod_{i=1}^n |L_{i,v}(x)|_v \ \le\ |x|^{-\varepsilon} $$
> lie in finitely many proper subspaces of `ℚⁿ`.

Here `|x| = maxᵢ|x_i|` and the absolute values are normalized by `|p|_p = p⁻¹`; the extension of
`|·|_v` to `ℚ̄_v` is unique, so "the" value `|L_{i,v}(x)|_v` is well defined.

## Encoding conventions (and safe weakenings)

* **Projective normalization.** For a *primitive* integer vector `x` one has `‖x‖_v = 1` at every
  finite place and `‖x‖_∞ = |x| = H_ℚ(x)`, so the displayed inequality is equivalent to
  `∏_{v} ∏_i |L_{i,v}(x)|_v/‖x‖_v ≤ H(x)^{-n-ε}`.  That is the form recorded here; both sides are
  invariant under scaling `x ↦ cx`, so it extends from primitive integer vectors to all of `ℚⁿ`
  with no change of content, and it matches `Subspace.approxProduct` (the same shape as the
  sibling axiom).
* **Algebraic coefficients at one place.** Every consumer of this statement — and every
  application in the literature of the `S`-unit/`(3/2)ⁿ` type — puts the algebraic coefficients at
  a *single* distinguished place `v₀` (where the approximation happens) and coordinate or
  rational-coefficient forms elsewhere.  The axiom is therefore recorded in that shape:
  `L₀` with coefficients in a number field `K` at `v₀`, and `ℚ`-linear `L v` at the remaining
  places `v ∈ S` (`v₀ ∉ S`).  This is a *special case* of 1D′ (rational coefficients are
  algebraic), hence a safe weakening.
* **The place `v₀` and its extension.** `w₀ : AbsoluteValue K ℝ` is the chosen extension of `v₀`
  to the coefficient field, pinned by `hw₀ : ∀ q : ℚ, w₀ (q : K) = v₀ q`.  For `v₀` archimedean
  this is an infinite place of `K`, i.e. a choice of embedding `K ↪ ℂ` — exactly the choice of
  which conjugate of the algebraic coefficients is meant.
* **Places.** `S ∪ {v₀}` is intended to be a finite set of places of `ℚ` containing the
  archimedean one (`Rat.AbsoluteValue.real`, `Rat.AbsoluteValue.padic p`).  As with the sibling
  cited axioms, this membership is documented, not enforced structurally.  `v₀ ∉ S` *is*
  enforced, so that no place is counted twice.
* **Conclusion.** Finitely many proper subspaces of `ℚⁿ` — of `ℚⁿ`, not of `Kⁿ`: the subspaces
  are cut out over the field of the *points*.  The finiteness is ineffective.

## Relation to `Subspace.evertseSchlickewei`

Neither statement implies the other by a formal specialization: this one is about `ℚ`-points with
algebraic coefficients, that one about `K`-points with `K`-coefficients.  Both are recorded as
cited axioms on the authority of [S]; the corpus's `ℚ`-coefficient consumers
(`CZ.pseudoPisot_approx_of_subspace`, `NKR`, `Ridout.finite_ratios`) use the sibling axiom,
where the two coincide, and everything with an **algebraic irrational multiplier** rests on the
present one: the anchored/RPF derivations (`RB/AnchoredRational.lean`,
`RB/OnePowerRational.lean`) and, since 2026-08-07, the algebraic-multiplier Corvaja–Zannier
Main Theorem itself (`CZ.pseudoPisot_approx_alg` via `Ridout.finite_ratios_alg`, which retired
a cited axiom of its own).

## Contents

* `Subspace.schmidt1D'` — **the Subspace Theorem with algebraic coefficients** ([S], Thm 1D′), a
  cited `axiom`.

## References

* [S] W. M. Schmidt, *Diophantine Approximation and Diophantine Equations*, Lecture Notes in Math.
  **1467**, Springer 1991 — Chapter V, Theorem 1D′.
* [Sch72] W. M. Schmidt, *Norm form equations*, Ann. of Math. **96** (1972), 526–551 — the
  archimedean Subspace Theorem.
* [Sli77] H. P. Schlickewei, *The p-adic Thue–Siegel–Roth–Schmidt theorem*, Arch. Math. (Basel)
  **29** (1977), 267–270 — the `S`-arithmetic extension quoted as 1D′.
* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, Cambridge 2006, Ch. 7 — the
  number-field form (`CITED/SubspaceTheorem.lean`) and the absolute normalization.
-/

namespace Subspace

open Height

/-- **The Subspace Theorem with algebraic coefficients** ([S], Theorem 1D′; Schlickewei's
`S`-arithmetic form): for a distinguished place `v₀` of `ℚ` carrying `n` linearly independent
linear forms `L₀` with coefficients in a number field `K` (measured by the extension `w₀` of
`v₀`), and rational-coefficient forms at the remaining places `v ∈ S`, the nonzero rational
solutions `x` of

  `(∏ᵢ |L₀ᵢ(x)|_{w₀}/‖x‖_{v₀}) · ∏_{v ∈ S} ∏ᵢ |L_{v,i}(x)|_v/‖x‖_v ≤ H(x)^{-n-ε}`

lie in finitely many proper subspaces of `ℚⁿ`.

Recorded as a cited `axiom` on the authority of [S].  Unlike its sibling
`Subspace.evertseSchlickewei`, the points here are **rational** and the height is the naive one:
that is what makes it usable when only the coefficients are algebraic.  See the module doc for
the encoding conventions and for why the two statements are genuinely different on rational
data. -/
@[category research solved, AMS 11, ref "Schmidt91" "Sli77", group "three_halves_m4"]
axiom schmidt1D' {n : ℕ} (hn : 2 ≤ n) {K : Type*} [Field K] [NumberField K]
    (v₀ : AbsoluteValue ℚ ℝ) (w₀ : AbsoluteValue K ℝ)
    (hw₀ : ∀ q : ℚ, w₀ ((q : K)) = v₀ q)
    (L₀ : Fin n → ((Fin n → K) →ₗ[K] K)) (hL₀ : LinearIndependent K L₀)
    (S : Finset (AbsoluteValue ℚ ℝ)) (hv₀ : v₀ ∉ S)
    (L : AbsoluteValue ℚ ℝ → Fin n → ((Fin n → ℚ) →ₗ[ℚ] ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (Fin n → ℚ)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin n → ℚ, x ≠ 0 →
        (∏ i, w₀ (L₀ i (fun j ↦ ((x j : ℚ) : K))) / localNorm v₀ x) * approxProduct S L x
          ≤ Height.mulHeight x ^ (-(n : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W

end Subspace
