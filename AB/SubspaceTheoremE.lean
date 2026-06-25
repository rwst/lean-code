/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.LinearAlgebra.Dual.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The multidimensional p-adic Subspace Theorem (AB07, Theorem E / Evertse)

This file records **Theorem E** of Adamczewski–Bugeaud, *On the complexity of algebraic numbers I*
(Annals 165 (2007), 547–565) — the **multidimensional Subspace Theorem over number fields**, covering all
places (archimedean *and* finite/`p`-adic). It is the deep Diophantine engine behind the paper's whole
transcendence machinery: Theorem 5 (real case), Theorem 6 (`p`-adic case,
`AB.transcendental_of_conditionStar`), and Theorems 1–4. AB quote it (their page 8) "as formulated by
Evertse [Eve96]"; it is the `p`-adic generalization of Schmidt's Subspace Theorem due to Schlickewei.

> **Theorem E.** *Let `K` be a number field, `m ≥ 2`, and `S` a finite set of places of `K` containing
> all infinite places. For each `v ∈ S` let `L₁,ᵥ, …, L_{m,v}` be linear forms (with algebraic
> coefficients) of rank `m`. Let `0 < ε < 1`. Then the set of solutions `x ∈ Kᵐ` of*
> `∏_{v∈S} ∏_{i=1}^m |Lᵢ,ᵥ(x)|ᵥ / |x|ᵥ ≤ H(x)^{−m−ε}`
> *lies in finitely many proper subspaces of `Kᵐ`.*

## Formalisation choices (and their faithfulness)

* **Places** are Mathlib's `Height.AdmissibleAbsValues` data for a number field: `archAbsVal` (the
  archimedean places, a `Multiset (AbsoluteValue K ℝ)`) and `nonarchAbsVal` (the finite places, a
  `Set (AbsoluteValue K ℝ)`), satisfying the product formula. `S : Finset (AbsoluteValue K ℝ)` is the
  finite place set, required to contain every archimedean place (`hS_inf`) and to consist of genuine
  places (`hS_place`).
* **The height** is Mathlib's projective multiplicative (Weil) height `Height.mulHeight`, and the vector
  norm is `|x|ᵥ = ⨆ j, v (x j)` — the **sup-norm** convention used throughout Mathlib. Evertse normalises
  the archimedean `|x|ᵥ` by an `L²`-norm instead; the two heights differ only by a bounded factor
  depending on `(m, d)`, and the Subspace Theorem is invariant under such a change (the `ε`-slack absorbs
  it). So the statement below *is* Theorem E, in the sup-norm normalisation.
* **Linear forms** are taken with coefficients in `K` (functionals `Module.Dual K (Fin m → K)`), and the
  rank-`m` condition is `LinearIndependent K (L v)` (`m` independent functionals span the `m`-dimensional
  dual). The paper allows *algebraic* coefficients and continues `|·|ᵥ` to `ℚ̄`; this is **no loss of
  generality**, since `H(x)` is independent of the field containing the coordinates, so one enlarges `K`
  to contain the finitely many form coefficients (AB07 p. 7).
* **"Finitely many proper subspaces"** is encoded as: a `Finset` `W` of submodules, each `≠ ⊤`, whose
  union contains every nonzero solution.

## How AB apply it (the instantiation to come)

In the proof of Theorem 6 (AB07 §6, the `p`-adic case = the case relevant to the `3x+1` `Φ`-side), one
takes `K = ℚ(β)`, `m = 3`, `S = {p} ∪ {∞ places}`, the three forms `L₁(x,y,z) = x`, `L₂ = y`,
`L₃ = α'x + α'y + z`, and the points `xₙ = (p^{sₙ}, −1, −pₙ)` built from the truncate-and-complete
approximants `αₙ = pₙ/(p^{sₙ}−1)`; the over-approximation `|α' − αₙ|_p ≤ p^{−rₙ−w·sₙ}` (the `w > 1`
repetition) makes `∏∏ |Lᵢ,ᵥ(xₙ)|ᵥ/|xₙ|ᵥ` beat `H(xₙ)^{−3−ε}`, so the `xₙ` lie in finitely many
subspaces — a contradiction with `α'` algebraic. The `B3` "Missing Lemma" Φ-side application
([[b3-automatic-cc-corpus-root]]) is exactly this scheme with the **base-3** Bernstein–Lagarias series
`Φ(v) = −∑ 3^{−(i+1)}2^{dᵢ}`: the approximants' denominators are `3^{cₘ} − 2^{pₘ}`, so it is `Theorem E`
that supplies the slack a single-variable (Roth/Ridout) bound cannot.

Recorded as a cited **`axiom`** (the Subspace-Theorem machinery — Schmidt/Schlickewei/Evertse — is not
reconstructed). It carries a literature `ref` and is a *theorem* of the literature, not an open
conjecture.

## Contents
* `subspace_theorem_E` — **Theorem E** (cited): the multidimensional Subspace Theorem over a number
  field, all places, in Mathlib's height normalisation.

## References
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311 (the formulation AB07 quote as "Theorem E").
* [Sch76] Schlickewei, Hans Peter. *On products of special linear forms with algebraic coefficients.*
  Acta Arith. 31 (1976), 389–398 (Theorem 4.1, the precise form applied in AB07 §6).
* [Sch77] Schlickewei, Hans Peter. *The `p`-adic Thue–Siegel–Roth–Schmidt theorem.* Arch. Math. (Basel)
  29 (1977), 267–270 (the `p`-adic Subspace Theorem).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I. Expansions in
  integer bases.* Annals of Mathematics 165 (2007), 547–565 (Theorem E, §4 and §6).
-/

namespace AB

open Height Height.AdmissibleAbsValues

/-- **Theorem E (Adamczewski–Bugeaud 2007, p. 8; Evertse's form of the Schmidt Subspace Theorem).** *The
multidimensional Subspace Theorem over a number field, covering all places (archimedean and
finite/`p`-adic).*

Let `K` be a number field, `m ≥ 2`, and `S` a finite set of places (absolute values) containing every
archimedean place (`hS_inf`) and consisting of genuine places (`hS_place`). For each `v ∈ S`, let
`L v 0, …, L v (m−1)` be linear forms (functionals `Module.Dual K (Fin m → K)`) of rank `m`
(`LinearIndependent K (L v)`). For `0 < ε < 1`, the set of **nonzero** solutions `x ∈ Kᵐ` of
`∏_{v∈S} ∏_{i} |Lᵢ,ᵥ(x)|ᵥ / |x|ᵥ ≤ H(x)^{−m−ε}`
(with `|x|ᵥ = ⨆ j, v (x j)` and `H = Height.mulHeight`) lies in **finitely many proper subspaces** of
`Kᵐ`: there is a finite set `W` of submodules, each `≠ ⊤`, whose union contains all such `x`.

This is the engine behind `AB.transcendental_of_conditionStar` (Theorem 6) and the target of the
`B3` Missing-Lemma `Φ`-side application — the multidimensional, `p`-adic statement that single-variable
Roth/Ridout cannot replace. Cited; see the module doc for the normalisation conventions and the
no-loss-of-generality reduction of algebraic coefficients to `K`. -/
@[category research solved, AMS 11, ref "Eve96" "Sch76" "Sch77" "AB07", group "ab_subspace_theorem"]
axiom subspace_theorem_E (K : Type*) [Field K] [NumberField K] (m : ℕ) (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue K ℝ))
    (hS_inf : ∀ v ∈ archAbsVal (K := K), v ∈ S)
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := K) ∨ v ∈ nonarchAbsVal (K := K))
    (L : AbsoluteValue K ℝ → Fin m → Module.Dual K (Fin m → K))
    (hL : ∀ v ∈ S, LinearIndependent K (L v))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ W : Finset (Submodule K (Fin m → K)), (∀ U ∈ W, U ≠ ⊤) ∧
      ∀ x : Fin m → K, x ≠ 0 →
        (∏ v ∈ S, ∏ i : Fin m, v ((L v i) x) / (⨆ j, v (x j))) ≤
          Height.mulHeight x ^ (-(m : ℝ) - ε) →
        ∃ U ∈ W, x ∈ U

end AB
