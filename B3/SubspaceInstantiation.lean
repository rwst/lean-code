/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.BlockConstruction
import AB.SubspaceTheoremE
import Mathlib.LinearAlgebra.Dual.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Instantiating the Subspace Theorem on the `Φ`-side (Route (i), the Missing Lemma)

This file sets up the application of the multidimensional Subspace Theorem (`AB.subspace_theorem_E`,
Theorem E) to the `Φ`-side of the Missing Lemma — the genuinely open step of Route (i)
([[b3-automatic-cc-corpus-root]]). It separates, honestly, the **algebraic inputs** (proved here) from the
**analytic core** (`research open`).

## The plan (Adamczewski–Bugeaud §6, adapted to base 3)

Suppose `v` is automatic and irrational and, for contradiction, `Φ v = m ∈ ℤ`. The truncate-and-complete
approximants (`B3.conditionStar_tooWellApproximated`) give rationals `Φ(αₙ) = −Pₙ/(3^{cₙ} − 2^{pₙ})` with
`‖m − Φ(αₙ)‖₂ ≤ 2^{−Nₙ} → 0`. Mirroring AB's §6 proof of Theorem 6, one applies `subspace_theorem_E`
over `K = ℚ`, `m = 3`, at the places `S = {2, ∞}`, with the three forms

> `L₁(x,y,z) = x`,  `L₂(x,y,z) = y`,  `L₃(x,y,z) = m·x + m·y + z`   (`subForms m`)

evaluated at the points `xₙ = (3^{cₙ} − 2^{pₙ}, −1, −Pₙ)` built from the approximants' **base-3
denominator** `3^{cₙ} − 2^{pₙ}` (`subspaceDen`). The over-approximation makes
`|L₃(xₙ)|₂ = ‖m − Φ(αₙ)‖₂ · |3^{cₙ} − 2^{pₙ}|₂ ≤ 2^{−Nₙ}`, so the Subspace product undercuts
`H(xₙ)^{−3−ε}` — provided the **height-vs-rate** estimate holds (the base-2 rate `Nₙ` against the base-3
height `≈ 3^{cₙ}`, the `ℓ`-versus-`dₗ` index). Then the `xₙ` lie in finitely many proper subspaces; an
infinite subfamily lies in one, giving a fixed linear relation, which (non-confinement) contradicts the
approximation. Hence `Φ v` is transcendental — impossible for `m ∈ ℤ`.

## What is proved here, and what is open

* **Proved (the algebraic inputs to `subspace_theorem_E`).** `subForms_linearIndependent`: the three
  forms have rank `3` (the Subspace Theorem's rank hypothesis), for every integer coefficient.
  `subspaceDen_odd`/`subspaceDen_ne_zero`: the base-3 height denominator `3^c − 2^p` is odd, hence a
  nonzero integer (a `2`-adic unit) — the height carrier.
* **The target (now in `B3.NoDivergence`).** `phi_value_transcendental`: the `Φ`-image `Φ(v)` of an
  automatic irrational `v` is transcendental — the converse-direction analogue of
  `parityVector_transcendental` (which gives `v` transcendental), but genuinely harder: the base-2/base-3
  Subspace step above, the `ℓ`-versus-`dₗ` over-approximation (Cobham/Mahler territory). The forms and
  height denominator proved *here* are its algebraic inputs. It is **relocated** to `B3.NoDivergence` (so
  it sits with the no-divergence capstone it feeds), where it is proved from the `Φ`-image stammering
  criterion `B3.phi_transcendental_of_conditionStar` (a `research open` axiom). The Subspace-argument
  reduction of that criterion is formalized across
  `B3.{HeightVsRate, SubspaceConfinement, NonConfinement, InfinitePlaceFactor}`; the non-confinement of the
  Subspace points is isolated as `B3.phiPoints_nonConfined` (`B3.NonConfinement`), the `hncf` input of
  `B3.subspace_contradiction_of_rate`.

## References
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311.
* [Sch77] Schlickewei, Hans Peter. *The `p`-adic Thue–Siegel–Roth–Schmidt theorem.* Arch. Math. (Basel)
  29 (1977), 267–270.
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6, the `p`-adic Theorem 6 = the template for this instantiation).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the formula `(1.6)` giving the base-3 denominators).
-/

namespace B3

open BL AB Function

/-! ### The algebraic inputs to the Subspace Theorem -/

/-- The **base-3 height denominator** `3^c − 2^p` of the `Φ`-image approximant `Φ(blockVal c p e)`
(`Φ_blockValue_mem_ratInt`: `Φ(blockVal) = −N/(3^c − 2^p)`). With `c =` odd-step count `ℓ` and `p =`
total-step count, this denominator carries the height of the Subspace point `xₙ`; its base-3 growth
`3^{cₙ}` against the base-2 approximation rate is the crux of the `Φ`-side estimate. -/
@[category API, AMS 11 37, ref "BL96" "AB07"]
def subspaceDen (c p : ℕ) : ℤ := 3 ^ c - 2 ^ p

/-- The height denominator is **odd**: `3^c` is odd and `2^p` is even (`p > 0`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem subspaceDen_odd (c p : ℕ) (hp : 0 < p) : Odd (subspaceDen c p) :=
  (Odd.pow ⟨1, by ring⟩).sub_even (Int.even_pow.mpr ⟨even_two, hp.ne'⟩)

/-- The **three Adamczewski–Bugeaud forms** for the `Φ`-side Subspace application, over `K = ℚ`, with the
assumed integer value `a = Φ v` as coefficient: `L₁ = x`, `L₂ = y`, `L₃ = a·x + a·y + z`
(`Module.Dual ℚ (Fin 3 → ℚ)`). These are the forms `subspace_theorem_E` is instantiated with at the
points `(3^c − 2^p, −1, −P)`. -/
noncomputable def subForms (a : ℤ) : Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) :=
  ![LinearMap.proj 0, LinearMap.proj 1,
    (a : ℚ) • LinearMap.proj 0 + (a : ℚ) • LinearMap.proj 1 + LinearMap.proj 2]

/-- **The forms have rank `3` (proved).** `subForms a` is `ℚ`-linearly independent for every integer
`a` — exactly the rank hypothesis `subspace_theorem_E` requires of `{L₁, L₂, L₃}` at each place. *Proof:*
evaluate `∑ gᵢ Lᵢ = 0` at the standard basis vectors `e₀, e₁, e₂`: `e₂` gives `g₂ = 0`, then `e₀`/`e₁`
give `g₀ = g₁ = 0` (the coefficient matrix `[[1,0,0],[0,1,0],[a,a,1]]` has determinant `1`). -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem subForms_linearIndependent (a : ℤ) : LinearIndependent ℚ (subForms a) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun (congrArg DFunLike.coe hg) (Pi.single 0 1)
  have h1 := congrFun (congrArg DFunLike.coe hg) (Pi.single 1 1)
  have h2 := congrFun (congrArg DFunLike.coe hg) (Pi.single 2 1)
  simp only [subForms, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.zero_apply, Pi.single_eq_same, smul_eq_mul] at h0 h1 h2
  intro i
  fin_cases i <;> simp_all

/-! ### The `Φ`-image transcendence — see `B3.NoDivergence`

The transcendence theorem `B3.phi_value_transcendental` (the `Φ`-side of the Missing Lemma) is **relocated**
to `B3.NoDivergence`, where it is proved from the `Φ`-image stammering criterion
`B3.phi_transcendental_of_conditionStar` (a `research open` axiom). The algebraic inputs it consumes —
`subForms`, `subForms_linearIndependent`, `subspaceDen` — are the content of this file; the Subspace-argument
reduction of the criterion is formalized across
`B3.{HeightVsRate, SubspaceConfinement, NonConfinement, InfinitePlaceFactor}`. -/

end B3
