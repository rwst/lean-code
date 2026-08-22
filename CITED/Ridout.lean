/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Set.Finite.Basic
import CITED.SubspaceTheorem
import CITED.SchmidtSubspace
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Ridout's theorem, as the two-variable case of the Subspace Theorem

**Ridout's theorem** ([Rid57]) — the `p`-adic (`S`-arithmetic) generalization of
Roth's theorem — is the `n = 2` case of the Subspace Theorem.  This file derives
its **projective form over `ℚ`, for `ℚ`-linear forms**, from the single cited
axiom `Subspace.evertseSchlickewei` rather than adding a second axiom, executing
the first step of the one-axiom refactor of `report-formalize-subspace.html` §6.
(The forms being `ℚ`-linear is a real restriction; see "From ratios to
`|δ − p/q|`" below.)

The engine over `ℚ`: for a finite set `S` of places and, at each place, two
linearly independent linear forms in `(x₀, x₁)`, the nonzero rational points
whose Subspace product falls below `H(x)^{-2-ε}` lie on **finitely many lines**
through the origin — equivalently, the ratios `x₁/x₀` of the good solutions form
a **finite set**.  That is `Ridout.finite_ratios` below, Ridout's theorem in
projective (ratio) form.

## From ratios to `|δ − p/q|`

The classical statement — *only finitely many `p/q` approximate a fixed `δ` with
`∏_{v∈S} \|δ − p/q\|_v < H(p/q)^{-2-ε}`* — is the case in which the archimedean
forms are `x₀ − δ·x₁` and `x₁` and the finite places `ℓ ∈ S` contribute the
coordinate forms `x₀, x₁` (so `|x₀|_ℓ`, `|x₁|_ℓ` measure the `ℓ`-adic size of
numerator and denominator).  A rational point `x = (p, q)` on one of the finitely
many output lines has a fixed ratio `p/q`, i.e. one approximant.

**Which `δ` this covers.**  `Ridout.finite_ratios` quantifies over `ℚ`-linear
forms, so `x₀ − δ·x₁` is admissible exactly when `δ ∈ ℚ`.  That is the
configuration Corvaja–Zannier invoke over `ℚ`
(`report-formalize-subspace.html` §3): with `δ ∈ ℚ` and `S = {∞, 2, 3}` it is the
sole deep input surviving in their Main Theorem, the denominators ranging over
the `S`-units `2^a 3^b`.  For an **algebraic irrational** `δ` the form is not
`ℚ`-linear and this file's statement does not apply: Ridout's theorem in that
generality is the `n = 2` case of Schmidt's Theorem 1D′ — rational points,
algebraic coefficients — recorded as the sibling axiom `Subspace.schmidt1D'` in
`CITED/SchmidtSubspace.lean`.  (Instantiating `Subspace.evertseSchlickewei` at
`K = ℚ(δ)` and feeding it rational points is *not* a substitute: it loses the
factor `[K : ℚ]` in the exponent, as that file's module doc explains.)

Choosing those forms and verifying the archimedean/`ℓ`-adic bound
`approxProduct ≤ H(x)^{-2-ε}` for a good approximant is the analytic step that
turns `finite_ratios` into the Corvaja–Zannier Main Theorem — carried out in
`CITED/CorvajaZannierProof.lean` (`CZ.pseudoPisot_approx_of_subspace`,
sorry-free, 2026-07-14).  What is established *here*, axiom-cleanly modulo
`Subspace.evertseSchlickewei`, is the projective finiteness that every such
instantiation consumes.

## Contents

* `Ridout.finite_ratios` — **Ridout's theorem** (projective form, `ℚ`-linear
  forms): the ratios `x₁/x₀` of the good rational solutions of the `n = 2`
  Subspace inequality form a finite set.  Derived from
  `Subspace.evertseSchlickewei` at `n = 2`, `K = ℚ`.

## References

* [Rid57] D. Ridout, *The p-adic generalization of the Thue–Siegel–Roth
  theorem*, Mathematika **4** (1957), 125–131.
* [S] W. M. Schmidt, *Diophantine Approximation and Diophantine Equations*, LNM
  **1467**, Springer 1991 (Theorem 1D′; Ridout for algebraic `δ` is its `n = 2`
  case — `CITED/SchmidtSubspace.lean`, not the axiom used here).
* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004) — the consumer over `ℚ`
  (derived in `CITED/CorvajaZannierProof.lean`).
* `report-formalize-subspace.html` (this repository, 2026-07): §3 (CZ → Ridout),
  §6 (the one-axiom refactor this file begins).
-/

namespace Ridout

open Subspace

/-- On a proper subspace `W` of `ℚ²` the ratio `x₁/x₀` is the same for every
member with nonzero `0`-coordinate: a line has a single slope.  This is the
linear-algebra core that turns "finitely many proper subspaces" into "finitely
many ratios". -/
private lemma ratio_determined {W : Submodule ℚ (Fin 2 → ℚ)} (hW : W ≠ ⊤)
    {x y : Fin 2 → ℚ} (hx : x ∈ W) (hy : y ∈ W) (hx0 : x 0 ≠ 0) (hy0 : y 0 ≠ 0) :
    x 1 / x 0 = y 1 / y 0 := by
  have hxne : x ≠ 0 := by intro h; apply hx0; rw [h]; rfl
  have hdim : Module.finrank ℚ (Fin 2 → ℚ) = 2 := by rw [Module.finrank_pi]; simp
  have hWlt : Module.finrank ℚ W < 2 := by
    have := Submodule.finrank_lt (K := ℚ) (V := Fin 2 → ℚ) hW; omega
  have hle : (ℚ ∙ x) ≤ W := (Submodule.span_singleton_le_iff_mem x W).mpr hx
  have hspan1 : Module.finrank ℚ (ℚ ∙ x) = 1 := finrank_span_singleton hxne
  have hWge : 1 ≤ Module.finrank ℚ W := by have := Submodule.finrank_mono hle; omega
  have hWeq : Module.finrank ℚ W = 1 := by omega
  have heq : (ℚ ∙ x) = W := Submodule.eq_of_le_of_finrank_le hle (by rw [hspan1, hWeq])
  have hyx : y ∈ (ℚ ∙ x) := heq ▸ hy
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hyx
  have hy0' : y 0 = c * x 0 := by rw [← hc]; rfl
  have hy1' : y 1 = c * x 1 := by rw [← hc]; rfl
  have hcne : c ≠ 0 := by rintro rfl; apply hy0; rw [hy0']; ring
  rw [hy0', hy1', mul_div_mul_left _ _ hcne]

/-- **Ridout's theorem**, projective form over `ℚ` ([Rid57]; the `n = 2` case of
the Subspace Theorem).  For a finite place set `S` and per-place linearly
independent **`ℚ`-linear** forms `L` on `ℚ²`, the ratios `x₁/x₀` of the nonzero
rational solutions of `approxProduct S L x ≤ H(x)^{-2-ε}` form a **finite set**.

Derived from `Subspace.evertseSchlickewei` at `n = 2`, `K = ℚ`: the theorem
confines the solutions to finitely many proper subspaces (lines) of `ℚ²`, and on
each line the ratio is constant (`ratio_determined`).  Axiom footprint: the
Subspace axiom only.  The classical `|δ − p/q|` statement is the instantiation
with `L` the forms `x₀ − δ·x₁`, `x₁` and coordinate forms — admissible here
exactly for `δ ∈ ℚ`; for algebraic irrational `δ` see the module doc and
`Subspace.schmidt1D'`. -/
@[category research solved, AMS 11, ref "Rid57", group "three_halves_m4"]
theorem finite_ratios
    (S : Finset (AbsoluteValue ℚ ℝ))
    (L : AbsoluteValue ℚ ℝ → Fin 2 → ((Fin 2 → ℚ) →ₗ[ℚ] ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) :
    {r : ℚ | ∃ x : Fin 2 → ℚ, x ≠ 0 ∧ x 0 ≠ 0 ∧ r = x 1 / x 0 ∧
      approxProduct S L x ≤ Height.mulHeight x ^ (-(2 : ℝ) - ε)}.Finite := by
  classical
  obtain ⟨T, hTproper, hTcover⟩ :=
    evertseSchlickewei_rat (n := 2) (by norm_num) S L hL ε hε
  -- slope of a line: the ratio of any representative with nonzero 0-coordinate
  refine Set.Finite.subset (Set.Finite.image
    (fun W : Submodule ℚ (Fin 2 → ℚ) =>
      if h : ∃ z : Fin 2 → ℚ, z ∈ W ∧ z 0 ≠ 0
      then (Classical.choose h) 1 / (Classical.choose h) 0 else 0)
    T.finite_toSet) ?_
  rintro r ⟨x, hxne, hx0, rfl, hineq⟩
  obtain ⟨W, hWT, hxW⟩ := hTcover x hxne (by exact_mod_cast hineq)
  refine ⟨W, Finset.mem_coe.mpr hWT, ?_⟩
  have hex : ∃ z : Fin 2 → ℚ, z ∈ W ∧ z 0 ≠ 0 := ⟨x, hxW, hx0⟩
  have hcs := Classical.choose_spec hex
  simp only [dite_eq_left hex]
  exact ratio_determined (hTproper W hWT) hcs.1 hxW hcs.2 hx0

/-- **Ridout's theorem for algebraic `δ`**, projective form ([Rid57]; the `n = 2` case of
Schmidt's Theorem 1D′).  Same conclusion as `Ridout.finite_ratios` — the ratios `x₁/x₀` of the
good *rational* solutions form a finite set — but the forms at the distinguished place `v₀` may
now have coefficients in a number field `K`, measured by the chosen extension `w₀` of `v₀`.

This is the form the `|δ − p/q|` statement needs for an algebraic irrational `δ`: the forms
`X₀ − δ·X₁`, `X₁` are `K`-linear, not `ℚ`-linear.  Derived from `Subspace.schmidt1D'` exactly
as the rational version is derived from `Subspace.evertseSchlickewei`, with the same
line-has-one-slope core (`ratio_determined`) — the output subspaces live over `ℚ` in both
cases, which is what makes that core reusable. -/
@[category research solved, AMS 11, ref "Rid57" "Schmidt91", group "three_halves_m4"]
theorem finite_ratios_alg {K : Type*} [Field K] [NumberField K]
    (v₀ : AbsoluteValue ℚ ℝ) (w₀ : AbsoluteValue K ℝ)
    (hw₀ : ∀ q : ℚ, w₀ ((q : K)) = v₀ q)
    (L₀ : Fin 2 → ((Fin 2 → K) →ₗ[K] K)) (hL₀ : LinearIndependent K L₀)
    (S : Finset (AbsoluteValue ℚ ℝ)) (hv₀ : v₀ ∉ S)
    (L : AbsoluteValue ℚ ℝ → Fin 2 → ((Fin 2 → ℚ) →ₗ[ℚ] ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) :
    {r : ℚ | ∃ x : Fin 2 → ℚ, x ≠ 0 ∧ x 0 ≠ 0 ∧ r = x 1 / x 0 ∧
      (∏ i, w₀ (L₀ i (fun j ↦ ((x j : ℚ) : K))) / localNorm v₀ x) * approxProduct S L x
        ≤ Height.mulHeight x ^ (-(2 : ℝ) - ε)}.Finite := by
  classical
  obtain ⟨T, hTproper, hTcover⟩ :=
    Subspace.schmidt1D' (n := 2) (K := K) (by norm_num) v₀ w₀ hw₀ L₀ hL₀ S hv₀ L hL ε hε
  refine Set.Finite.subset (Set.Finite.image
    (fun W : Submodule ℚ (Fin 2 → ℚ) =>
      if h : ∃ z : Fin 2 → ℚ, z ∈ W ∧ z 0 ≠ 0
      then (Classical.choose h) 1 / (Classical.choose h) 0 else 0)
    T.finite_toSet) ?_
  rintro r ⟨x, hxne, hx0, rfl, hineq⟩
  obtain ⟨W, hWT, hxW⟩ := hTcover x hxne (by exact_mod_cast hineq)
  refine ⟨W, Finset.mem_coe.mpr hWT, ?_⟩
  have hex : ∃ z : Fin 2 → ℚ, z ∈ W ∧ z 0 ≠ 0 := ⟨x, hxW, hx0⟩
  have hcs := Classical.choose_spec hex
  simp only [dite_eq_left hex]
  exact ratio_determined (hTproper W hWT) hcs.1 hxW hcs.2 hx0

end Ridout
