/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Relatively algebraically closed base fields are linearly disjoint from algebraic extensions

A field extension `E / F` is **regular** when `F` is relatively algebraically closed in `E` and
`E / F` is separable; in characteristic zero the second condition is automatic, so *regular* is
exactly Mathlib's `algebraicClosure F E = ⊥`.  The classical reason to care (Lang, *Algebra*,
Chap. VIII) is that a regular extension is **linearly disjoint from every algebraic extension of
the base**.  Mathlib has both ingredients — the relative algebraic closure `algebraicClosure F E`
and the full `IntermediateField.LinearDisjoint` API — but not the implication between them.  This
file supplies it, in the tower `F ≤ E ≤ Ω`:

* `algebraicClosure.minpoly_eq_map_of_eq_bot` — the minimal polynomial over `F` of an element of
  `Ω` algebraic over `F` survives the enlargement of the base to `E`;
* `algebraicClosure.natDegree_minpoly_eq_of_eq_bot` — hence its degree does not drop;
* `algebraicClosure.linearIndependent_pow_of_eq_bot` — hence the powers `x ^ j`,
  `j < deg (minpoly F x)`, stay linearly independent over `E`;
* `algebraicClosure.eq_zero_of_sum_pow_eq_zero` — the same, in the form in which a splitting
  argument consumes it: a vanishing combination `∑ⱼ cⱼ xʲ = 0` with `cⱼ ∈ E` has all `cⱼ = 0`;
* `algebraicClosure.linearDisjoint_adjoin_of_eq_bot` — and, in Mathlib's own vocabulary,
  `F(x)` and `E` are linearly disjoint over `F`.

The proof of the first statement is the standard one and is short because the arithmetic half is
already in Mathlib: `minpoly E x` divides `(minpoly F x).map (algebraMap F E)`, so its coefficients
are integral over `F` (`Polynomial.isIntegral_coeff_of_dvd`, Stacks 00H6); being in `E` they lie in
`algebraicClosure F E = ⊥`, i.e. in `F`; the resulting monic `F`-lift is annihilated by `x`, so it
is divisible by `minpoly F x`, and two monic polynomials dividing each other agree.

Only the direction *regular ⇒ linearly disjoint* is proved.

## Beyond a simple extension

The statements above are about the powers of one element, which is what a primitive element gives.
That is **not** enough for every splitting argument: a splitting along an arbitrary
`F`-linearly-independent family — the coordinates of a free module, say — needs the disjointness
against the whole finite subextension the family generates.  In characteristic zero that costs
nothing beyond a primitive element for *that* field, so the second half of this file is:

* `algebraicClosure.linearDisjoint_of_finiteDimensional` — a finite-dimensional separable
  intermediate field of `Ω/F` is linearly disjoint from `E`;
* `algebraicClosure.linearIndependent_of_eq_bot` — hence a finite family of elements of `Ω`
  algebraic over `F` and linearly independent over `F` stays linearly independent over `E`;
* `algebraicClosure.eq_zero_of_sum_smul_eq_zero` — the same, in the form a splitting argument
  consumes it.
-/

open Polynomial IntermediateField

namespace algebraicClosure

variable {F E Ω : Type*} [Field F] [Field E] [Field Ω]
  [Algebra F E] [Algebra E Ω] [Algebra F Ω] [IsScalarTower F E Ω]

/-- If `F` is relatively algebraically closed in `E`, then the minimal polynomial over `F` of an
element of `Ω` algebraic over `F` is unchanged by enlarging the base field to `E`. -/
theorem minpoly_eq_map_of_eq_bot (h : algebraicClosure F E = ⊥) {x : Ω} (hx : IsIntegral F x) :
    minpoly E x = (minpoly F x).map (algebraMap F E) := by
  have hxE : IsIntegral E x := hx.tower_top
  have hdvd : minpoly E x ∣ (minpoly F x).map (algebraMap F E) :=
    minpoly.dvd_map_of_isScalarTower F E x
  have hlift : minpoly E x ∈ Polynomial.lifts (algebraMap F E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    have hint : IsIntegral F ((minpoly E x).coeff i) :=
      Polynomial.isIntegral_coeff_of_dvd _ _ (minpoly.monic hx) (minpoly.monic hxE) hdvd i
    have hmem : (minpoly E x).coeff i ∈ algebraicClosure F E := mem_algebraicClosure_iff'.2 hint
    rw [h] at hmem
    exact IntermediateField.mem_bot.mp hmem
  obtain ⟨p, hpmap, -, -⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlift (minpoly.monic hxE)
  have hp0 : Polynomial.aeval x p = 0 := by
    have h0 := minpoly.aeval E x
    rw [← hpmap, Polynomial.aeval_map_algebraMap] at h0
    exact h0
  have hdvd' : (minpoly F x).map (algebraMap F E) ∣ minpoly E x := by
    rw [← hpmap]; exact Polynomial.map_dvd _ (minpoly.dvd F x hp0)
  exact Polynomial.eq_of_monic_of_associated (minpoly.monic hxE)
    ((minpoly.monic hx).map _) (associated_of_dvd_dvd hdvd hdvd')

/-- The degree of the minimal polynomial does not drop either. -/
theorem natDegree_minpoly_eq_of_eq_bot (h : algebraicClosure F E = ⊥) {x : Ω}
    (hx : IsIntegral F x) : (minpoly E x).natDegree = (minpoly F x).natDegree := by
  rw [minpoly_eq_map_of_eq_bot h hx, (minpoly.monic hx).natDegree_map]

/-- The powers of an element algebraic over `F` stay linearly independent over `E`. -/
theorem linearIndependent_pow_of_eq_bot (h : algebraicClosure F E = ⊥) {x : Ω}
    (hx : IsIntegral F x) :
    LinearIndependent E fun i : Fin (minpoly F x).natDegree => x ^ (i : ℕ) :=
  natDegree_minpoly_eq_of_eq_bot h hx ▸ _root_.linearIndependent_pow (K := E) x

/-- The form a splitting argument consumes: if `∑ⱼ cⱼ xʲ = 0` with coefficients `cⱼ` in `E` and
`j` below the degree of `x` over `F`, then every `cⱼ` vanishes. -/
theorem eq_zero_of_sum_pow_eq_zero (h : algebraicClosure F E = ⊥) {x : Ω} (hx : IsIntegral F x)
    (c : Fin (minpoly F x).natDegree → E)
    (hc : ∑ j, algebraMap E Ω (c j) * x ^ (j : ℕ) = 0) (j) : c j = 0 := by
  have hli := linearIndependent_pow_of_eq_bot h hx
  rw [Fintype.linearIndependent_iff] at hli
  exact hli c (by simpa [Algebra.smul_def] using hc) j

/-- ... and, in Mathlib's own vocabulary, `F(x)` and `E` are linearly disjoint over `F`. -/
theorem linearDisjoint_adjoin_of_eq_bot (h : algebraicClosure F E = ⊥) {x : Ω}
    (hx : IsIntegral F x) : (IntermediateField.adjoin F {x}).LinearDisjoint E := by
  refine IntermediateField.LinearDisjoint.of_basis_left (adjoin.powerBasis hx).basis ?_
  have hb : (F⟮x⟯.val ∘ (adjoin.powerBasis hx).basis) =
      fun i : Fin (minpoly F x).natDegree => x ^ (i : ℕ) := by
    funext i
    simp
  rw [hb]
  exact linearIndependent_pow_of_eq_bot h hx

/-- A **finite-dimensional** separable intermediate field of `Ω / F` is linearly disjoint from a
regular extension `E / F`.  The simple case above is `A = F(x)`; the general one costs no more,
because a power basis of `A` is a family of powers of a single element. -/
theorem linearDisjoint_of_finiteDimensional (h : algebraicClosure F E = ⊥)
    (A : IntermediateField F Ω) [FiniteDimensional F A] [Algebra.IsSeparable F A] :
    A.LinearDisjoint E := by
  set pb := Field.powerBasisOfFiniteOfSeparable F A with hpb
  set x : Ω := (pb.gen : Ω) with hx
  have hxint : IsIntegral F x := (IsIntegral.of_finite F pb.gen).map A.val
  have hdeg : (minpoly F x).natDegree = pb.dim := by
    rw [hx, show minpoly F ((pb.gen : Ω)) = minpoly F pb.gen from
      minpoly.algebraMap_eq (algebraMap A Ω).injective pb.gen]
    exact pb.natDegree_minpoly
  refine IntermediateField.LinearDisjoint.of_basis_left pb.basis ?_
  have hb : (⇑A.val ∘ ⇑pb.basis) = fun i : Fin pb.dim => x ^ (i : ℕ) := by
    funext i
    simp [hx]
  rw [hb]
  have hli := linearIndependent_pow_of_eq_bot h hxint
  have h2 := hli.comp (finCongr hdeg.symm) (finCongr hdeg.symm).injective
  have heq : ((fun i : Fin (minpoly F x).natDegree => x ^ (i : ℕ)) ∘ ⇑(finCongr hdeg.symm))
      = fun i : Fin pb.dim => x ^ (i : ℕ) := rfl
  rwa [heq] at h2

/-- A finite family of elements of `Ω` algebraic over `F` and linearly independent over `F` stays
linearly independent over a regular extension `E / F`.  This is the form in which a splitting along
a basis — rather than along the powers of a primitive element — consumes regularity. -/
theorem linearIndependent_of_eq_bot [CharZero F] (h : algebraicClosure F E = ⊥)
    {ι : Type*} [Finite ι] {v : ι → Ω} (hint : ∀ i, IsIntegral F (v i))
    (hli : LinearIndependent F v) : LinearIndependent E v := by
  classical
  haveI : Finite (Set.range v) := (Set.finite_range v).to_subtype
  set A : IntermediateField F Ω := IntermediateField.adjoin F (Set.range v) with hA
  haveI : FiniteDimensional F A :=
    IntermediateField.finiteDimensional_adjoin (fun y hy => by
      obtain ⟨i, rfl⟩ := hy
      exact hint i)
  have hmem : ∀ i, v i ∈ A := fun i =>
    IntermediateField.subset_adjoin F (Set.range v) ⟨i, rfl⟩
  set v' : ι → A := fun i => ⟨v i, hmem i⟩ with hv'
  have hli' : LinearIndependent F v' := LinearIndependent.of_comp A.val.toLinearMap hli
  exact (linearDisjoint_of_finiteDimensional h A).linearIndependent_left hli'

/-- The form a splitting argument consumes: a vanishing combination `∑ᵢ cᵢvᵢ = 0` with coefficients
`cᵢ` in `E` and `v` an `F`-linearly-independent family of algebraic elements has all `cᵢ = 0`. -/
theorem eq_zero_of_sum_smul_eq_zero [CharZero F] (h : algebraicClosure F E = ⊥)
    {ι : Type*} [Fintype ι] {v : ι → Ω} (hint : ∀ i, IsIntegral F (v i))
    (hli : LinearIndependent F v) (c : ι → E)
    (hc : ∑ i, algebraMap E Ω (c i) * v i = 0) (i : ι) : c i = 0 := by
  have h1 := linearIndependent_of_eq_bot h hint hli
  rw [Fintype.linearIndependent_iff] at h1
  exact h1 c (by simpa [Algebra.smul_def] using hc) i

end algebraicClosure
