/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.SubspaceConfinement
import B3.PlaceTwoProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Non-confinement of the `Φ`-side Subspace points (Route (i), the Missing Lemma — the open crux)

This file addresses the **one genuinely open mathematical input** of Route (i)
([[b3-automatic-cc-corpus-root]]): **non-confinement** (`¬ Confinable`, `B3.SubspaceConfinement`) of the
`Φ`-side approximant points. It proves the structural part — turning the abstract "not confined to finitely
many proper subspaces" into a concrete Diophantine non-degeneracy of the base-`3` denominators — and
isolates the irreducible base-`2`/base-`3` core as a single `research open` statement.

## The structural reduction (proved)

`confinable_iff_exists_dual`: a family `x : ℕ → ℚᵐ` is **confinable** iff some **nonzero linear
functional** `f` vanishes on infinitely many `xₖ` (a proper subspace is exactly the kernel of a nonzero
functional, `Submodule.exists_le_ker_of_lt_top`). For the `Φ`-side points `placePoint Dₖ Pₖ = ![Dₖ, −1, Pₖ]`,
`placePoint_dual_apply` evaluates `f` to the **linear relation**

> `f(xₖ) = a·Dₖ − b + c·Pₖ`,  where `(a, b, c) = (f e₀, f e₁, f e₂)`.

So **non-confinement ⇔ no nonzero `(a, b, c)` has `a·Dₖ − b + c·Pₖ = 0` for infinitely many `k`**.

## The open core (base-`2`/base-`3`)

With `Pₖ = −Dₖ·Φ(αₖ)` (`hrel`, `Φ(αₖ) = qₖ`), the relation becomes `Dₖ·(a − c·qₖ) = b`. Two regimes, both
governed by base-`2`/base-`3` independence — this is the genuine research content:

* **`c = 0`:** `a·Dₖ = b` for infinitely many `k`. Since the heights are `Dₖ = 3^{cₖ} − 2^{pₖ}`, this needs
  `|3^{cₖ} − 2^{pₖ}|` *not* to be bounded on an infinite set — a **Pillai-type** statement (each fixed
  value `|3^c − 2^p| = m` has only finitely many solutions, and bounded values occur finitely often),
  itself open in the relevant generality.
* **`c ≠ 0`:** `Dₖ·(a − c·qₖ) = b` would pin `qₖ → a/c` along the subfamily, while the construction only
  gives `qₖ → n` **`2`-adically** (`hconv`) with `qₖ ≠ n` (`hdist`). Reconciling an *archimedean* linear
  relation with *`2`-adic* convergence is exactly what the **multidimensional Subspace Theorem**
  (`AB.subspace_theorem_E`, via the over-approximation) resolves — the base-`3`-height-vs-base-`2`-rate
  independence.

`phiPoints_nonConfined` records the resulting non-confinement as a research `axiom`: the provable
structural reduction (to the linear relation) is captured by `confinable_iff_exists_dual` and
`placePoint_dual_apply`, while the base-`2`/base-`3` obstruction above is isolated in the axiom. This is
precisely the `hncf` input of `B3.subspace_contradiction_of_rate`; with it, the assembled `Φ`-side
argument is complete.

## Contents
* `confinable_iff_exists_dual` — (proved) confinement ⇔ a nonzero functional vanishes on infinitely many
  points.
* `placePoint_dual_apply` — (proved) `f(placePoint D P) = D·(f e₀) − (f e₁) + P·(f e₂)`, the linear
  relation.
* `phiPoints_nonConfined` — (`research axiom`) the `Φ`-side approximant points are not confined; the
  structural reduction is proved, the base-`2`/base-`3` core is isolated in the axiom.

## References
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311 (the Subspace Theorem behind both regimes).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6: the points lie in finitely many subspaces, and the contradiction
  from confinement — the template here, in base `3`).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the base-`3` denominators `Dₖ = 3^{cₖ} − 2^{pₖ}`).
-/

namespace B3

open Function Filter

/-! ### The structural reduction: confinement ⇔ a vanishing functional -/

/-- **Confinement ⇔ a vanishing functional (proved).** A family `x : ℕ → ℚᵐ` is `Confinable` (some proper
subspace contains infinitely many `xₖ`) **iff** some **nonzero** linear functional `f` vanishes on
infinitely many `xₖ`. *Proof:* (→) a proper subspace `U ≠ ⊤` lies in the kernel of a nonzero functional
(`Submodule.exists_le_ker_of_lt_top`), which then vanishes on the infinitely many `xₖ ∈ U`; (←) `ker f` is
a proper subspace (`f ≠ 0`) containing those `xₖ`. This turns the abstract `¬ Confinable` into a concrete
Diophantine non-degeneracy. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem confinable_iff_exists_dual {m : ℕ} (x : ℕ → (Fin m → ℚ)) :
    Confinable x ↔ ∃ f : Module.Dual ℚ (Fin m → ℚ), f ≠ 0 ∧ {k | f (x k) = 0}.Infinite := by
  constructor
  · rintro ⟨U, hU, hUinf⟩
    obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.mpr hU)
    exact ⟨f, hf0, hUinf.mono (fun k hk => LinearMap.mem_ker.mp (hfU hk))⟩
  · rintro ⟨f, hf0, hinf⟩
    refine ⟨LinearMap.ker f, ?_, hinf.mono (fun k hk => LinearMap.mem_ker.mpr hk)⟩
    rw [Ne, LinearMap.ker_eq_top]
    exact hf0

/-- **The functional as a linear relation (proved).** Applying a functional `f` to a `Φ`-side point
`placePoint D P = ![D, −1, P]` gives the linear relation `f(placePoint D P) = D·(f e₀) − (f e₁) + P·(f e₂)`
in the coordinates `(a, b, c) = (f e₀, f e₁, f e₂)` (`eᵢ = Pi.single i 1`). So a functional vanishing on a
point is exactly the relation `a·D − b + c·P = 0`. -/
@[category API, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem unused_placePoint_dual_apply (f : Module.Dual ℚ (Fin 3 → ℚ)) (D P : ℚ) :
    f (placePoint D P) = D * f (Pi.single 0 1) - f (Pi.single 1 1) + P * f (Pi.single 2 1) := by
  have hdecomp : placePoint D P
      = D • Pi.single 0 1 - Pi.single 1 1 + P • Pi.single (2 : Fin 3) 1 := by
    funext i; fin_cases i <;> simp [placePoint]
  rw [hdecomp]; simp [map_add, map_sub, map_smul, smul_eq_mul]

/-! ### The open core: non-confinement of the `Φ`-side points -/

/-- **Non-confinement of the `Φ`-side approximant points (`research axiom`).** Let `n = Φ v` (the assumed
integer value), `Dₖ` the base-`3` denominators (`Odd`, i.e. `Dₖ = 3^{cₖ} − 2^{pₖ}`), `Pₖ` the numerators,
and `qₖ = Φ(αₖ) = −Pₖ/Dₖ` (`hrel`) the approximants, with `qₖ → n` `2`-adically (`hconv`) and `qₖ ≠ n`
(`hdist`). Then the Subspace points `placePoint Dₖ Pₖ = ![Dₖ, −1, Pₖ]` are **not confined** to finitely
many proper subspaces.

By `confinable_iff_exists_dual` and `placePoint_dual_apply`, confinement would give a nonzero `(a, b, c)`
with `a·Dₖ − b + c·Pₖ = 0` for infinitely many `k`, i.e. `Dₖ·(a − c·qₖ) = b`. Excluding this is the
base-`2`/base-`3` independence (the `c = 0` Pillai height-growth and the `c ≠ 0`
archimedean-vs-`2`-adic Subspace obstruction; see the module doc) — the genuine open content of the
Missing Lemma. Recorded as a research `axiom` so that it can be used as the `hncf` non-confinement input
of `B3.subspace_contradiction_of_rate` in the eventual proof of `B3.phi_value_transcendental`. -/
@[category research open, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
axiom phiPoints_nonConfined (n : ℤ) (D P : ℕ → ℤ) (q : ℕ → ℚ)
    (hodd : ∀ k, Odd (D k)) (hrel : ∀ k, (D k : ℚ) * q k = -(P k : ℚ))
    (hconv : Tendsto (fun k => Rat.AbsoluteValue.padic 2 ((n : ℚ) - q k)) atTop (nhds 0))
    (hdist : ∀ k, q k ≠ (n : ℚ)) :
    ¬ Confinable (fun k => placePoint (D k : ℚ) (P k : ℚ))

end B3
