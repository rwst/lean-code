/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonSpecialization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] §2.4 without the denominator, and the endgame of Theorem 2.1

plan-formalize-AF17's **WP19**, the first half of gap (6)'s final assembly.

[AF22] §2.4 turns the conclusion of Lemma 2.11 into Theorem 2.1 in five moves: substitute
`z ↦ z^{q^{k₀}}`, clear `A_{k₀}(z)^{-1}`, expand the coefficients in a primitive element `ϕ` of the
relation matrix's field, split along the powers of `ϕ`, and re-sum with the *numbers* `ϕ(ξ)ʲ`.
`CITED/AdamczewskiFaverjonAssembly` has the algebra of that, and
`CITED/AdamczewskiFaverjonSpecialization` has the branch's side of it.  This file replaces the
middle move, for a reason that only shows up when the pieces are joined.

## The denominator of (2.36) cannot be assumed harmless

[AF22] write `φ(z) = ∑ⱼ φⱼ(z)ϕ(z)ʲ` with `φⱼ` over `ℚ̄(z)` and let `d(z)` be a common denominator
of their coordinates.  The specialization at the end needs `d` not to vanish at the point, and they
get that from *«we can assume that `k₀` has been chosen large enough so that `ϕ(z)` is analytic at
`ξ = α^{q^{k₀}}` and `d(α^{q^{k₀}}) ≠ 0`»* — legitimate for them because **their `d` is chosen
before `k₀`**, from the untwisted matrix, and the points `α^{q^k}` are pairwise distinct, so all but
finitely many avoid the finitely many roots of `d`.

The corpus cannot follow that route.  `AF.exists_hspec_of_branch` decomposes the **twisted** matrix
`φ(z^{q^{k₀}})`, whose primitive element and denominator therefore depend on `k₀`, and there is no
second «for `k₀ ≫ 1`» left to spend.  Nor can the paper's own order be imitated: `ϕ(z^{q^{k₀}})`
may have **smaller** degree than `ϕ` — for `ϕ = √z` and `q` even it is a rational function — so the
untwisted `δ` is not available to split along, and re-expanding in the twisted power basis
reintroduces a `k₀`-dependent denominator.  `d(α) ≠ 0` is then a genuinely unprovable step.

## The primitive element is not needed at all

The way out removes the difficulty rather than working around it.  Let `c₁,…,cₙ` be the
coefficients of the relation.  The `K[z]`-module they generate inside the ambient field is finitely
generated and torsion-free, and **`K[z]` is a principal ideal domain**, so it is *free*
(`Module.basisOfFiniteTypeTorsionFree'`).  A basis `e₁,…,e_δ` of it expresses every `cᵢ` with
coefficients in `K[z]` — **polynomials, not rational functions** — so there is no denominator to
clear and no condition on `α` to arrange.

Two things have to be checked, and both are cheap:

* the `eₘ` stay linearly independent over the solution field.  They are `K(z)`-linearly independent,
  being a `K[z]`-basis of a module spanning the same space; regularity of `K(z)(f)/K(z)` then gives
  independence over `K(z)(f)` — but against the *whole* finite subextension the `eₘ` generate, not
  against a simple one, which is the extension of `ForMathlib/FieldTheory/RegularExtension.lean`
  this file consumes;
* the `eₘ` lie in the branch's subring, because they are `K[z]`-combinations of the `cᵢ`, so the
  branch evaluates them and their values `E(eₘ)` are algebraic (`AF.branchEval_mem_range`) — which
  is exactly what the final linear form `L(z,X) := ∑ₘ Lₘ(z,X)·E(eₘ)` needs.

So §2.4's «primitive element + common denominator» is replaced by «basis of a free module», and
the normalizing constant of the lift shrinks from [AF22]'s `d(ξ)q(α)` to `q(α)` alone — the
determinant `det A_{k₀}(α)`, non-zero by regularity of `α` and by nothing else.

## The numerical identity

What is left of §2.4 is arithmetic: `AF.sum_mul_adjugate_eval` is *«since `Θ_{k₀}(α^{q^{k₀}}) =
Θ_{k₀}(ξ) = A_{k₀}(α)`, we deduce that `Q(α,X) = τX = L(X)`»*, i.e.

  `∑ⱼ (τ·M·Φ₀)ⱼ · adj(A_{k₀})(α)ⱼᵢ = det A_{k₀}(α) · τᵢ`,

which is `M·Φ₀ = A_{k₀}(α)` — the branch's value at `ξ`, read in `K` — followed by
`B·adj B = det B·1`.

## Contents

* `AF.toAmbient_injective`, **`AF.exists_polynomialFamily`** — the free `K[z]`-module and its basis;
* **`AF.linearForm_split_free`**, **`AF.exists_lift_free`** — §2.4's splitting and final linear
  form along a free family, with no denominator;
* **`AF.exists_hspec_free_of_branch`** — gap (5) in the same shape: the branch supplies the values
  `E(eₘ)` and the specialization, with no condition on `α`;
* `AF.sum_mul_adjugate_eval` — the numerical identity `Θ_{k₀}(ξ) = A_{k₀}(α)`;
* **`AF.exists_lift_of_branch`** — [AF22] §2.4 end to end: a relation with coefficient row
  `τΘ_{k₀}(z)` in, Theorem 2.1's conclusion out;
* **`AF.exists_lift_of_eventually_formVal_eq_zero`** — the same with WP16's reverse transport
  prefixed, so that the input is Lemma 2.11's own conclusion.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.4 ((2.36), (2.37), the final `L(z,X)`).
* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.*  Proc. LMS 115 (2017), 55–90, Lemme 2.2.
* [AF17f] `plans/plan-formalize-AF17.html`: WP19, gap (6), milestone M4.
-/

open Filter Topology

open scoped Polynomial nonZeroDivisors

namespace AF

/-! ## The coefficients generate a free `K[z]`-module -/

section FreeFamily

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra (RatFunc K) Ω]

/-- `K[z] → Ω` is injective — `K[z] → K(z)` is, and `K(z) → Ω` is a homomorphism of fields. -/
@[category API, AMS 12 13, ref "AF22", group "af_mahler_alternative"]
theorem toAmbient_injective : Function.Injective (toAmbient K Ω) := fun _ _ hab =>
  RatFunc.algebraMap_injective K ((algebraMap (RatFunc K) Ω).injective hab)

/-- **[AF22] (2.36) with no denominator.**  The `K[z]`-module generated by a finite family of
elements of the ambient field is finitely generated and torsion-free, hence — `K[z]` being a
principal ideal domain — *free*.  A basis of it expresses every member of the family with
**polynomial** coefficients, and is itself a family of `K[z]`-combinations of the original one.

This is what replaces the primitive element and its common denominator: see the module doc for why
the denominator of (2.36) cannot be assumed to be non-zero at `α` in the corpus's order of
quantifiers. -/
@[category research solved, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem exists_polynomialFamily {ι : Type*} [Fintype ι] (c : ι → Ω) :
    ∃ (δ : ℕ) (e : Fin δ → Ω) (μ : Fin δ → ι → K[X]) (lam : ι → Fin δ → K[X]),
      (∀ m, e m = ∑ i, toAmbient K Ω (μ m i) * c i) ∧
      LinearIndependent (RatFunc K) e ∧
      (∀ i, c i = ∑ m, toAmbient K Ω (lam i m) * e m) := by
  classical
  letI : Algebra K[X] Ω := (toAmbient K Ω).toAlgebra
  haveI : IsScalarTower K[X] (RatFunc K) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : NoZeroSMulDivisors K[X] Ω := by
    refine ⟨fun {r x} h => ?_⟩
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.1 h with h1 | h1
    · refine Or.inl (toAmbient_injective (Ω := Ω) ?_)
      rw [map_zero]
      exact h1
    · exact Or.inr h1
  set M : Submodule K[X] Ω := Submodule.span K[X] (Set.range c) with hM
  haveI : Module.Finite K[X] M :=
    Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range c))
  obtain ⟨δ, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := K[X]) (M := M)
  have hcmem : ∀ i, c i ∈ M := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hμ : ∀ m : Fin δ, ∃ g : ι → K[X], ∑ i, g i • c i = ((b m : M) : Ω) := fun m =>
    (Submodule.mem_span_range_iff_exists_fun K[X]).1 (b m).2
  choose μ hμ using hμ
  refine ⟨δ, fun m => ((b m : M) : Ω), μ, fun i m => b.repr ⟨c i, hcmem i⟩ m, fun m => ?_, ?_,
    fun i => ?_⟩
  · show ((b m : M) : Ω) = ∑ i, toAmbient K Ω (μ m i) * c i
    rw [← hμ m]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _)
  · have h1 : LinearIndependent K[X] fun m => ((b m : M) : Ω) :=
      b.linearIndependent.map' M.subtype (by simp)
    exact h1.localization (S := (K[X])⁰) (Rₛ := RatFunc K)
  · show c i = ∑ m, toAmbient K Ω (b.repr ⟨c i, hcmem i⟩ m) * ((b m : M) : Ω)
    have h := congrArg (fun y : M => (y : Ω)) (b.sum_repr ⟨c i, hcmem i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm.trans (Finset.sum_congr rfl fun m _ => (Algebra.smul_def _ _))

end FreeFamily

/-! ## The splitting, and the final linear form -/

section SplitFree

variable {K : Type*} [Field K] [CharZero K] {Ω : Type*} [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι]

/-- **[AF22] §2.4's splitting, along a free family.**  *«Since `ℚ̄(z)(f(z))` and `A` are linearly
disjoint over `ℚ̄(z)`, [the `eₘ`] remain linearly independent over `ℚ̄(z)(f(z))`.  Thus, splitting
the linear form, we deduce that `Qₘ(z,f(z)) = 0` for all `m`.»*

`AF.linearForm_split_solField` does this for the powers of a primitive element; here the family is
arbitrary, which is what `algebraicClosure.eq_zero_of_sum_smul_eq_zero` was added to
`ForMathlib/FieldTheory/RegularExtension.lean` for. -/
@[category research solved, AMS 11 12 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem linearForm_split_free {f : ι → Ω} (hreg : IsRegularSolField K f)
    {δ : ℕ} {e : Fin δ → Ω} (hint : ∀ m, IsIntegral (RatFunc K) (e m))
    (hli : LinearIndependent (RatFunc K) e) (lam : ι → Fin δ → K[X])
    (hrel : ∑ i, (∑ m, toAmbient K Ω (lam i m) * e m) * f i = 0) (m : Fin δ) :
    ∑ i, toAmbient K Ω (lam i m) * f i = 0 := by
  classical
  set E := solField K f with hE
  set g : Fin δ → E := fun m => ∑ i,
    algebraMap (RatFunc K) E (algebraMap K[X] (RatFunc K) (lam i m)) * ⟨f i, mem_solField K f i⟩
    with hg
  have hgΩ : ∀ m, algebraMap E Ω (g m) = ∑ i, toAmbient K Ω (lam i m) * f i := by
    intro m
    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply, toAmbient_apply]
    rfl
  have hzero : ∑ m, algebraMap E Ω (g m) * e m = 0 := by
    calc ∑ m, algebraMap E Ω (g m) * e m
        = ∑ m, ∑ i, toAmbient K Ω (lam i m) * f i * e m := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hgΩ m, Finset.sum_mul]
      _ = ∑ i, (∑ m, toAmbient K Ω (lam i m) * e m) * f i := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := hrel
  have h := algebraicClosure.eq_zero_of_sum_smul_eq_zero hreg hint hli g hzero m
  rw [← hgΩ m, h, map_zero]

/-- **[AF22] §2.4's last paragraph, with no denominator.**  *«Setting `L(z,X) := ∑ⱼ Qⱼ(z,X)ϕ(ξ)ʲ`,
we obtain `L(z,f(z)) = 0` and `L(α,X) = L(X)`, as wanted.»*

The analogue of `AF.exists_lift`, with the powers `ϕ(ξ)ʲ` replaced by the branch's values at the
members of the free family.  The normalizing scalar `u` is [AF22]'s `d(ξ)q(α)` with the `d` gone:
in the assembly it is `det A_{k₀}(α)` alone. -/
@[category research solved, AMS 11 12 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem exists_lift_free {f : ι → Ω} (hreg : IsRegularSolField K f)
    {δ : ℕ} {e : Fin δ → Ω} (hint : ∀ m, IsIntegral (RatFunc K) (e m))
    (hli : LinearIndependent (RatFunc K) e) (lam : ι → Fin δ → K[X])
    (hrel : ∑ i, (∑ m, toAmbient K Ω (lam i m) * e m) * f i = 0)
    {α : K} {ev : Fin δ → K} {u : K} (hu : u ≠ 0) {τ : ι → K}
    (hspec : ∀ i, ∑ m, (lam i m).eval α * ev m = u * τ i) :
    ∃ L : ι → K[X], (∑ i, toAmbient K Ω (L i) * f i = 0) ∧ ∀ i, (L i).eval α = τ i := by
  refine ⟨fun i => Polynomial.C u⁻¹ * ∑ m, Polynomial.C (ev m) * lam i m, ?_, fun i => ?_⟩
  · have hsplit := linearForm_split_free hreg hint hli lam hrel
    calc ∑ i, toAmbient K Ω (Polynomial.C u⁻¹ * ∑ m, Polynomial.C (ev m) * lam i m) * f i
        = toAmbient K Ω (Polynomial.C u⁻¹) *
            ∑ m, toAmbient K Ω (Polynomial.C (ev m)) * ∑ i, toAmbient K Ω (lam i m) * f i := by
          rw [Finset.mul_sum]
          simp only [map_mul, map_sum, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by
          rw [Finset.sum_congr rfl fun m _ => by rw [hsplit m, mul_zero], Finset.sum_const_zero,
            mul_zero]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
    have hs : ∑ m, (Polynomial.C (ev m) * lam i m).eval α = u * τ i := by
      rw [← hspec i]
      exact Finset.sum_congr rfl fun m _ => by
        rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]
    rw [hs, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

end SplitFree

/-! ## Gap (5) in the same shape -/

section HspecFree

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {φ : K →+* ℂ} {Φ' : Matrix ι ι Ω} {α : K} {V : Set ℂ} {R : Subring Ω}
  {real : R →+* Germ (𝓟 V) ℂ} {Ψ : ℂ → Matrix ι ι ℂ} {Φ₁ : Matrix ι ι K}

/-- **Gap (5) of Stage 2, for a free family.**  `AF.exists_hspec_of_branch` with the primitive
element replaced by a basis of the free `K[z]`-module: the branch evaluates the basis — its members
being `K[z]`-combinations of the coefficients, hence in `AF.branchRing` — its values are algebraic
by `AF.branchEval_mem_range`, and the specialization is then the ring-homomorphism property of
`AF.branchEval` and nothing else.

Note what has disappeared: there is no denominator `d`, hence no hypothesis `d(α) ≠ 0`, hence no
second appeal to «for `k₀ ≫ 1`». -/
@[category research solved, AMS 11 12 13 30, ref "AF22", group "af_mahler_alternative"]
theorem exists_hspec_free_of_branch (hb : IsAnalyticBranch φ Φ' (φ α) V R real Ψ Φ₁)
    {c : ι → Ω} (hint : ∀ i, IsIntegral (RatFunc K) (c i))
    (hcT : ∀ i, c i ∈ branchRing K Φ') :
    ∃ (δ : ℕ) (e : Fin δ → Ω) (lam : ι → Fin δ → K[X]) (ev : Fin δ → K),
      (∀ m, IsIntegral (RatFunc K) (e m)) ∧ LinearIndependent (RatFunc K) e ∧
      (∀ i, c i = ∑ m, toAmbient K Ω (lam i m) * e m) ∧
      ∀ (i : ι) (w : K), branchEval hb ⟨c i, branchRing_le hb.isBranch (hcT i)⟩ = φ w →
        ∑ m, (lam i m).eval α * ev m = w := by
  classical
  obtain ⟨δ, e, μ, lam, hμ, hli, hdec⟩ := exists_polynomialFamily (K := K) c
  have heT : ∀ m, e m ∈ branchRing K Φ' := by
    intro m
    rw [hμ m]
    exact Subring.sum_mem _ fun i _ =>
      Subring.mul_mem _ (toAmbient_mem_branchRing _) (hcT i)
  have heint : ∀ m, IsIntegral (RatFunc K) (e m) := by
    intro m
    have hmem : e m ∈ integralClosure (RatFunc K) Ω := by
      rw [hμ m]
      refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ ?_ (hint i)
      rw [toAmbient_apply]
      exact isIntegral_algebraMap
    exact hmem
  have hevpoly : ∀ w : K[X],
      branchEval hb ⟨toAmbient K Ω w, hb.isBranch.poly_mem w⟩ = φ (w.eval α) := by
    intro w
    rw [branchEval_poly, Polynomial.eval_map, Polynomial.eval₂_hom]
  choose ev hev using fun m => branchEval_mem_range hb (β := α) rfl (heT m)
  refine ⟨δ, e, lam, ev, heint, hli, hdec, fun i w hw => ?_⟩
  have hu : (⟨c i, branchRing_le hb.isBranch (hcT i)⟩ : R)
      = ∑ m, (⟨toAmbient K Ω (lam i m), hb.isBranch.poly_mem _⟩ : R) *
          ⟨e m, branchRing_le hb.isBranch (heT m)⟩ := by
    apply Subtype.ext
    push_cast
    exact hdec i
  have h := congrArg (branchEval hb) hu
  rw [hw, map_sum] at h
  refine φ.injective ?_
  rw [h, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_mul, map_mul, hevpoly, hev m]

end HspecFree

/-! ## The numerical identity `Θ_{k₀}(ξ) = A_{k₀}(α)` -/

section Numerical

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] §2.4's arithmetic step.**  *«Moreover, since `Θ_{k₀}(α^{q^{k₀}}) = Θ_{k₀}(ξ) =
A_{k₀}(α)`, we deduce that `Q(α,X) = τX = L(X)`.»*

The coefficient row of (2.37), evaluated at `α`, is `τ·(M·Φ₀)·adj(A_{k₀})(α)`; the branch's value
clause `M·Φ₀ = A_{k₀}(α)` and `B·adj B = (det B)·1` collapse it to `det A_{k₀}(α)·τ`.  This is the
whole of the analytic input of §2.4, and it is not analytic. -/
@[category research solved, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem sum_mul_adjugate_eval (τ : ι → K) (Mm Φ₀ : Matrix ι ι K) (B : Matrix ι ι K[X])
    {α : K} (hMΦ : Mm * Φ₀ = evalMat α B) (i : ι) :
    ∑ j, (∑ i', τ i' * ∑ l, Mm i' l * Φ₀ l j) * (B.adjugate j i).eval α
      = (B.det).eval α * τ i := by
  have hadj : ∀ j : ι, (B.adjugate j i).eval α = (evalMat α B).adjugate j i := by
    intro j
    have h : (Polynomial.evalRingHom α).mapMatrix B.adjugate
        = (evalMat α B).adjugate := (Polynomial.evalRingHom α).map_adjugate B
    exact congrFun (congrFun (congrArg (fun N : Matrix ι ι K => (N : ι → ι → K)) h) j) i
  have hdet : (B.det).eval α = (evalMat α B).det :=
    (Polynomial.evalRingHom α).map_det B
  have hml : ∀ i' j : ι, ∑ l, Mm i' l * Φ₀ l j = evalMat α B i' j := by
    intro i' j
    rw [← hMΦ, Matrix.mul_apply]
  calc ∑ j, (∑ i', τ i' * ∑ l, Mm i' l * Φ₀ l j) * (B.adjugate j i).eval α
      = ∑ j, ∑ i', τ i' * (evalMat α B i' j * (evalMat α B).adjugate j i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [hadj j, hml i' j]
        ring
    _ = ∑ i', τ i' * ∑ j, evalMat α B i' j * (evalMat α B).adjugate j i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i' _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ i', τ i' * ((evalMat α B) * (evalMat α B).adjugate) i' i :=
        Finset.sum_congr rfl fun i' _ => by rw [Matrix.mul_apply]
    _ = (B.det).eval α * τ i := by
        rw [Matrix.mul_adjugate, hdet, Finset.sum_eq_single i]
        · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, mul_comm]
        · intro b _ hb
          rw [Matrix.smul_apply, Matrix.one_apply_ne hb, smul_zero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h

end Numerical

/-! ## [AF22] §2.4, end to end -/

section Endgame

variable {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] §2.4, from the relation to Theorem 2.1's conclusion.**

The input is the relation Lemma 2.11 produces after WP16's reverse transport — coefficient row
`τ·M·Φ(z)` against the solutions — and the output is [AF22] Theorem 2.1: a linear form with
coefficients in `K[z]`, vanishing on the solutions, and specializing at `α` to the given `τ`.

Between them, and in this order: the Mahler substitution `σ` of (2.37) with `A_{k₀}(z)^{-1}`
cleared by its determinant (`AF.relation_subst`), the free `K[z]`-module of the resulting
coefficients (`AF.exists_polynomialFamily`), the branch's evaluation of its basis
(`AF.exists_hspec_free_of_branch`), the numerical identity (`AF.sum_mul_adjugate_eval`), and the
splitting (`AF.exists_lift_free`).

The hypotheses are exactly [AF22]'s: `σ` fixes the constants and carries the system, `α` is a
regular point at level `k₀` (`hdet` — this is their `q(α) ≠ 0`), the value of the branch at `ξ` is
defined over `K` and satisfies `M·Φ₀ = A_{k₀}(α)`, and the *twisted* matrix has an analytic branch
at `φ(α)` with that same value — which is the one clause gap (5) adds to `AF.lemma_2_8`. -/
@[category research solved, AMS 11 12 15 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem exists_lift_of_branch {q k₀ : ℕ} {A : Matrix ι ι K[X]} {α : K}
    {fΩ : ι → Ω} (hreg : IsRegularSolField K fΩ)
    (σ : Ω →+* Ω) (hσC : ∀ a : K, σ (ambC K Ω a) = ambC K Ω a)
    (hf : ∀ i, fΩ i = ∑ j, toAmbient K Ω (iterMatrix q A k₀ i j) * σ (fΩ j))
    {Φalg : Matrix ι ι Ω} {φ : K →+* ℂ} {τ : ι → K} {Mm Φ₀ : Matrix ι ι K}
    (hr : ∑ j, (∑ i, ambC K Ω (τ i) * ∑ l, ambC K Ω (Mm i l) * Φalg l j) * fΩ j = 0)
    (hMΦ : Mm * Φ₀ = evalMat α (iterMatrix q A k₀))
    (hdet : ((iterMatrix q A k₀).det).eval α ≠ 0)
    {V : Set ℂ} {R : Subring Ω} {real : R →+* Germ (𝓟 V) ℂ} {Ψ : ℂ → Matrix ι ι ℂ}
    (hb : IsAnalyticBranch φ (Matrix.of fun l j => σ (Φalg l j)) (φ α) V R real Ψ Φ₀)
    (hσint : ∀ l j, IsIntegral (RatFunc K) (σ (Φalg l j))) :
    ∃ L : ι → K[X], (∑ i, toAmbient K Ω (L i) * fΩ i = 0) ∧ ∀ i, (L i).eval α = τ i := by
  classical
  set B := iterMatrix q A k₀ with hB
  set Φ'' : Matrix ι ι Ω := Matrix.of fun l j => σ (Φalg l j) with hΦ''
  set r : ι → Ω := fun j => ∑ i, ambC K Ω (τ i) * ∑ l, ambC K Ω (Mm i l) * Φalg l j with hrdef
  have hσr : ∀ j, σ (r j) = ∑ i, ambC K Ω (τ i) * ∑ l, ambC K Ω (Mm i l) * Φ'' l j := by
    intro j
    rw [hrdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hσC, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun l _ => by rw [map_mul, hσC]; rfl)
  -- (2.37): the substitution, with `A_{k₀}(z)⁻¹` written as `adj/det`
  have hBdet : B.det ≠ 0 := fun h => hdet (by rw [h]; simp)
  have hBdetΩ : toAmbient K Ω B.det ≠ 0 := fun h =>
    hBdet (toAmbient_injective (by rw [h, map_zero]))
  set MΩ : Matrix ι ι Ω := Matrix.of fun i j => toAmbient K Ω (B i j) with hMΩ
  set NΩ : Matrix ι ι Ω :=
    Matrix.of fun j i => (toAmbient K Ω B.det)⁻¹ * toAmbient K Ω (B.adjugate j i) with hNΩ
  have hNM : NΩ * MΩ = 1 := by
    ext j i
    have h1 : ∑ l, NΩ j l * MΩ l i
        = (toAmbient K Ω B.det)⁻¹ * toAmbient K Ω ((B.adjugate * B) j i) := by
      rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [hNΩ, hMΩ, map_mul]
        simp only [Matrix.of_apply]
        ring
    rw [Matrix.mul_apply, h1, Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases hji : j = i
    · subst hji
      rw [Matrix.one_apply_eq, mul_one, inv_mul_cancel₀ hBdetΩ, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hji, mul_zero, map_zero, mul_zero, Matrix.one_apply_ne hji]
  have h237 := relation_subst σ hNM (fun i => hf i) hr
  -- the coefficient row, with the determinant cleared
  set c : ι → Ω := fun i => ∑ j, σ (r j) * toAmbient K Ω (B.adjugate j i) with hc
  have hcrel : ∑ i, c i * fΩ i = 0 := by
    have hcl : ∀ i, c i = toAmbient K Ω B.det * (∑ j, σ (r j) * NΩ j i) := by
      intro i
      rw [hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hNΩ]
      simp only [Matrix.of_apply]
      rw [← mul_assoc, mul_comm (toAmbient K Ω B.det) (σ (r j)), mul_assoc,
        mul_inv_cancel_left₀ hBdetΩ]
    calc ∑ i, c i * fΩ i
        = toAmbient K Ω B.det * ∑ i, (∑ j, σ (r j) * NΩ j i) * fΩ i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hcl i, mul_assoc]
      _ = 0 := by rw [h237, mul_zero]
  -- it lies in the branch's subring and is algebraic over `K(z)`
  have hcT : ∀ i, c i ∈ branchRing K Φ'' := by
    intro i
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (toAmbient_mem_branchRing _)
    rw [hσr j]
    refine Subring.sum_mem _ fun i' _ => Subring.mul_mem _ (toAmbient_mem_branchRing _) ?_
    exact Subring.sum_mem _ fun l _ =>
      Subring.mul_mem _ (toAmbient_mem_branchRing _) (mat_mem_branchRing l j)
  have hcint : ∀ i, IsIntegral (RatFunc K) (c i) := by
    intro i
    have hpoly : ∀ w : K[X], toAmbient K Ω w ∈ integralClosure (RatFunc K) Ω := by
      intro w
      rw [toAmbient_apply]
      exact isIntegral_algebraMap
    have hmem : c i ∈ integralClosure (RatFunc K) Ω := by
      refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ (hpoly _)
      rw [hσr j]
      refine Subalgebra.sum_mem _ fun i' _ => Subalgebra.mul_mem _ (hpoly _) ?_
      exact Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ (hpoly _) (hσint l j)
    exact hmem
  -- the numerical identity, read through the branch
  have hevpoly : ∀ w : K[X],
      branchEval hb ⟨toAmbient K Ω w, hb.isBranch.poly_mem w⟩ = φ (w.eval α) := by
    intro w
    rw [branchEval_poly, Polynomial.eval_map, Polynomial.eval₂_hom]
  have hevC : ∀ a : K,
      branchEval hb ⟨ambC K Ω a, hb.isBranch.poly_mem (Polynomial.C a)⟩ = φ a := by
    intro a
    have h := hevpoly (Polynomial.C a)
    rw [Polynomial.eval_C] at h
    exact h
  have hcev : ∀ i, branchEval hb ⟨c i, branchRing_le hb.isBranch (hcT i)⟩
      = φ ((B.det).eval α * τ i) := by
    intro i
    have hkey : (⟨c i, branchRing_le hb.isBranch (hcT i)⟩ : R)
        = ∑ j, (∑ i', (⟨ambC K Ω (τ i'), hb.isBranch.poly_mem (Polynomial.C (τ i'))⟩ : R) *
            ∑ l, (⟨ambC K Ω (Mm i' l), hb.isBranch.poly_mem (Polynomial.C (Mm i' l))⟩ : R) *
              ⟨Φ'' l j, hb.isBranch.mat_mem l j⟩) *
              ⟨toAmbient K Ω (B.adjugate j i), hb.isBranch.poly_mem _⟩ := by
      apply Subtype.ext
      push_cast
      rw [hc]
      exact Finset.sum_congr rfl fun j _ => by rw [hσr j]
    have h := congrArg (branchEval hb) hkey
    rw [h, map_sum, ← sum_mul_adjugate_eval τ Mm Φ₀ B hMΦ i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i' _ => ?_
      rw [map_mul, map_mul, map_sum, map_sum]
      congr 1
      · exact hevC (τ i')
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_mul, map_mul]
        congr 1
        · exact hevC (Mm i' l)
        · exact branchEval_mat hb l j
    · exact hevpoly (B.adjugate j i)
  obtain ⟨δ, e, lam, ev, heint, hli, hdec, hspec⟩ := exists_hspec_free_of_branch hb hcint hcT
  refine exists_lift_free hreg heint hli lam ?_ (u := (B.det).eval α) hdet
    (fun i => hspec i _ (hcev i))
  rw [← hcrel]
  exact Finset.sum_congr rfl fun i _ => by rw [← hdec i]

/-- **[AF22] Lemma 2.11 in, Theorem 2.1 out.**  `AF.exists_lift_of_branch` with WP16's reverse
transport (`AF.relation_of_eventually_formVal_eq_zero`) prefixed, so that the input is the
conclusion of Lemma 2.11 itself: the linear form `F(Θ_{k₀}(z),z)` vanishes identically near `ξ`.

What separates this from `AF.theoreme_2_1` is the instantiation of Lemma 2.11's own hypotheses
at the Mahler data — the relation matrix of §2.2, the number field of WP17, and the branch of
`AF.lemma_2_8` — and nothing of §2.4. -/
@[category research solved, AMS 11 12 15 30 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem exists_lift_of_eventually_formVal_eq_zero {q k₀ : ℕ} {A : Matrix ι ι K[X]} {α : K}
    {fΩ : ι → Ω} (hreg : IsRegularSolField K fΩ)
    (σ : Ω →+* Ω) (hσC : ∀ a : K, σ (ambC K Ω a) = ambC K Ω a)
    (hf : ∀ i, fΩ i = ∑ j, toAmbient K Ω (iterMatrix q A k₀ i j) * σ (fΩ j))
    {Φalg : Matrix ι ι Ω} {φ : K →+* ℂ} {τ : ι → K} {Mm Φ₀ : Matrix ι ι K}
    {U : Set ℂ} {R₁ : Subring Ω} {real₁ : R₁ →+* Germ (𝓟 U) ℂ} {Ψ₁ : ℂ → Matrix ι ι ℂ}
    {fs : ι → ℂ → ℂ} {ξ : ℂ}
    (hbr : IsBranchRealization φ (𝓟 U) Φalg R₁ real₁ Ψ₁)
    (hsr : IsSolutionRealization (𝓟 U) fΩ R₁ real₁ fs)
    (han : IsAnalyticRealization U R₁ real₁) (hinj : Function.Injective real₁)
    (hUo : IsOpen U) (hconn : IsPreconnected U) (hξU : ξ ∈ U)
    (h0 : ∀ᶠ z in 𝓝 ξ, formVal (fun i => φ (τ i)) fs (Mm.map φ * Ψ₁ z) z = 0)
    (hMΦ : Mm * Φ₀ = evalMat α (iterMatrix q A k₀))
    (hdet : ((iterMatrix q A k₀).det).eval α ≠ 0)
    {V : Set ℂ} {R : Subring Ω} {real : R →+* Germ (𝓟 V) ℂ} {Ψ : ℂ → Matrix ι ι ℂ}
    (hb : IsAnalyticBranch φ (Matrix.of fun l j => σ (Φalg l j)) (φ α) V R real Ψ Φ₀)
    (hσint : ∀ l j, IsIntegral (RatFunc K) (σ (Φalg l j))) :
    ∃ L : ι → K[X], (∑ i, toAmbient K Ω (L i) * fΩ i = 0) ∧ ∀ i, (L i).eval α = τ i :=
  exists_lift_of_branch hreg σ hσC hf
    (relation_of_eventually_formVal_eq_zero hbr hsr han hinj hUo hconn hξU τ Mm h0)
    hMΦ hdet hb hσint

end Endgame

end AF
