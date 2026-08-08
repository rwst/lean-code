/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CITED.AdamczewskiFaverjonRelationIdeal
import CITED.AdamczewskiFaverjonTools

/-!
# [AF22] §2.2.2: relation matrices

The first half of plan-formalize-AF17's **WP8**.  [AF22] attach to the relation ideal `𝓘` of
`CITED/AdamczewskiFaverjonRelationIdeal` — the ideal of all functional relations satisfied by the
iterates `(A_k(α), α^{q^k})` — an invertible matrix `φ(z)` over an algebraic closure `A` of `ℚ̄(z)`
which *realizes* those relations:

  `P ∈ 𝓘 ⟹ P(φ(z), z) = 0`   (**Lemma 2.5**, `AF.exists_relationMatrix`)

and which then automatically realizes all of their *twists*:

  `P ∈ 𝓘 ⟹ P(φ(z)A_k(z), z^{q^k}) = 0`   (**Lemma 2.7**, `AF.lemma_2_7`).

Lemma 2.7 is the identity that carries the whole proof of [AF22] Theorem 2.1: it is what makes the
auxiliary function of their §2.3 vanish to high order at every iterate simultaneously.

## No Puiseux series

[AF22] take `A` concretely as the algebraic closure of `ℚ̄(z)` *inside the field of Puiseux
series*, which Mathlib cannot currently express.  Gate **G3** of the plan established that §2 uses
nothing of that realization except algebraic closedness (no valuation, no order of vanishing, no
fractional exponent), so here

  `A := AlgebraicClosure (RatFunc K)`.

The one genuinely analytic use of the Puiseux realization — analyticity of the coordinates of
`φ` near a *non-zero* point, [AF22] Lemma 2.8(b) — is a separate matter, treated by an analytic
branch in `CITED/AdamczewskiFaverjonAnalyticBranch`; nothing in this file is analytic.

## Both halves of Lemma 2.5 come from one Mathlib theorem

[AF22] prove the existence of `φ` from the *weak* Nullstellensatz and the invertibility of `φ`
from the *strong* one, applied to the polynomial `det Y`.  Mathlib's
`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` is already stated **relatively** (an ideal over
a field `k`, points in an algebraically closed extension `K`), which is exactly the shape needed,
and it gives both halves at once: `det Y ∉ 𝓘` and `𝓘` radical force a point of the zero locus at
which `det Y` does not vanish, and such a point is *both* a common zero of `𝓘` and an invertible
matrix.  The hypothesis `det Y ∉ 𝓘` is where regularity of `α` enters, through
`det A_k(α) = ∏_{j<k} det A(α^{q^j}) ≠ 0`.

## The twist, and why it is a ring homomorphism

[AF22]'s proof of Lemma 2.7 sets `Q(Y, z) := P(Y·A_k(z), z^{q^k})` and checks `Q ∈ 𝓘` by the
cocycle identity `A_ℓ(α)A_k(α^{q^ℓ}) = A_{k+ℓ}(α)`.  Here `Q = twist q A k P` for a ring
homomorphism `twist q A k` of `K(z)[Y]`, built by substituting `z ↦ z^{q^k}` in the coefficients
(`AF.substPowRat`, a `RatFunc` substitution obtained by `IsLocalization.lift` from
`Polynomial.expand`) and `Y ↦ Y·A_k(z)` in the indeterminates.  That `twist` maps `𝓘` into `𝓘` is
then the single equation

  `germEval ∘ twist q A k = germShift k ∘ germEval`,

an identity between two ring homomorphisms out of `K(z)[Y]`, so it needs checking only on
constants and on indeterminates — the first case is the substitution `(α^{q^ℓ})^{q^k} =
α^{q^{k+ℓ}}`, the second is the cocycle identity.  `AF.germShift` is the shift `ℓ ↦ ℓ + k` acting
on germs at infinity, which is where «for all `k ≫ 1`» is absorbed.

## Contents

* `AF.substPow_eq_expand`, `AF.iterMatrix_det`, `AF.iterMatrix_det_eval` — `det A_k(z)` as a
  product of substituted copies of `det A(z)`;
* `AF.iterMatrix_det_eval_ne_zero` — at a **regular** point `det A_k(α) ≠ 0` for every `k`;
* `AF.detX`, `AF.germEval_detX`, `AF.detX_notMem_relationIdeal` — the polynomial `det Y` and the
  reason it is not a relation;
* **`AF.exists_relationMatrix`** — [AF22] Lemma 2.5;
* `AF.IsRelationMatrix` — [AF22] Definition 2.6;
* `AF.substPowRat`, `AF.germShift`, `AF.twist` — the twist and its ingredients;
* **`AF.twist_mem_relationIdeal`**, **`AF.lemma_2_7`** — [AF22] Lemma 2.7;
* `AF.exists_relationMatrix_mahler`, `AF.lemma_2_7_mahler` — the same for the relation ideal of an
  actual Mahler system at a regular point.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.2.2 (Lemmas 2.5–2.7) and §2.2.3.
* [AF17f] `plans/plan-formalize-AF17.html`: WP8, gate G3, milestone M4 (Stage 2).
-/

open Filter MvPolynomial
open scoped Polynomial nonZeroDivisors

namespace AF

/-! ## `det A_k(z)` and regular points -/

section Det

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A ring homomorphism commutes with determinants — Mathlib's `RingHom.map_det` in the direction
and shape used here. -/
@[category API, AMS 15, ref "AF22", group "af_mahler_alternative"]
theorem det_map_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix ι ι R) : (M.map f).det = f M.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

/-- The same for an algebra homomorphism. -/
@[category API, AMS 15, ref "AF22", group "af_mahler_alternative"]
theorem det_map_algHom {T R S : Type*} [CommRing T] [CommRing R] [CommRing S] [Algebra T R]
    [Algebra T S] (f : R →ₐ[T] S) (M : Matrix ι ι R) : (M.map f).det = f M.det := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply]

/-- WP7's substitution `z ↦ z^q` is Mathlib's `Polynomial.expand`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem substPow_eq_expand (q : ℕ) (p : K[X]) : substPow K q p = Polynomial.expand K q p := rfl

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem substPow_eval (q : ℕ) (p : K[X]) (α : K) : (substPow K q p).eval α = p.eval (α ^ q) := by
  rw [substPow_eq_expand, Polynomial.expand_eval]

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem substPow_ne_zero {q : ℕ} (hq : 0 < q) {p : K[X]} (hp : p ≠ 0) : substPow K q p ≠ 0 := by
  rw [substPow_eq_expand]
  exact (Polynomial.expand_ne_zero hq).2 hp

/-- **`det A_k(z) = ∏_{j<k} (det A)(z^{q^j})`** — the determinant of the iterated matrix
`A_k(z) = A(z)A(z^q)⋯A(z^{q^{k-1}})` of [AF22] (2.1). -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem iterMatrix_det (q : ℕ) (A : Matrix ι ι K[X]) (k : ℕ) :
    (iterMatrix q A k).det = ∏ j ∈ Finset.range k, substPow K (q ^ j) A.det := by
  induction k with
  | zero => simp [iterMatrix_zero]
  | succ n ih =>
      rw [iterMatrix_succ, Matrix.det_mul, det_map_ringHom, ih, map_prod,
        Finset.prod_range_succ' (fun j => substPow K (q ^ j) A.det) n, pow_zero, substPow_one]
      simp only [RingHom.id_apply]
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← RingHom.comp_apply, substPow_comp]

/-- The same, evaluated: `det A_k(α) = ∏_{j<k} det A(α^{q^j})`. -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem iterMatrix_det_eval (q : ℕ) (A : Matrix ι ι K[X]) (k : ℕ) (α : K) :
    (iterMatrix q A k).det.eval α = ∏ j ∈ Finset.range k, A.det.eval (α ^ q ^ j) := by
  rw [iterMatrix_det, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun j _ => substPow_eval _ _ _

/-- **At a regular point, every iterate is invertible** — [AF22]'s «`A_k(α)` is invertible for all
`k ≥ 0`», the fact their proof of Lemma 2.5 spends to get `det φ ≠ 0`.  Regularity is exactly the
non-vanishing of `det A` at all the points `α^{q^l}` (`AF.IsRegularPoint`). -/
@[category research solved, AMS 11 12 13 15, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem iterMatrix_det_eval_ne_zero {q : ℕ} {A : Matrix ι ι K[X]} {α : K}
    (hreg : IsRegularPoint q A α) (k : ℕ) : (iterMatrix q A k).det.eval α ≠ 0 := by
  rw [iterMatrix_det_eval]
  refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
  have := hreg j
  rwa [Polynomial.coe_aeval_eq_eval] at this

end Det

/-! ## `det Y` is not a relation -/

section DetX

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (K ι) in
/-- The matrix of indeterminates `Y = (y_{i,j})`, as a matrix over `K(z)[Y]`. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def matX : Matrix ι ι (MvPolynomial (ι × ι) (RatFunc K)) :=
  Matrix.of fun i j => X (i, j)

variable (K ι) in
/-- **The polynomial `det Y`** — [AF22] apply the Nullstellensatz to it in the proof of their
Lemma 2.5. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def detX : MvPolynomial (ι × ι) (RatFunc K) := (matX K ι).det

/-- Evaluating `det Y` along the points is evaluating the determinants of the matrices. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem germEval_detX {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → ι × ι → K) :
    germEval hpt Yval (detX K ι) =
      ((fun n => (Matrix.of fun i j => Yval n (i, j) : Matrix ι ι K).det : ℕ → K) :
        Germ (atTop : Filter ℕ) K) := by
  classical
  set M : Matrix ι ι (ℕ → K) := Matrix.of fun i j n => Yval n (i, j) with hM
  have hmap : (matX K ι).map (germEval hpt Yval) = M.map (Germ.coeRingHom (atTop : Filter ℕ)) := by
    ext i j
    simp [matX, hM, germEval, Germ.coeRingHom]
  have hdet : M.det = fun n => (Matrix.of fun i j => Yval n (i, j) : Matrix ι ι K).det := by
    funext n
    have h : (M.map (Pi.evalRingHom (fun _ : ℕ => K) n)).det = M.det n :=
      det_map_ringHom _ _
    rw [← h]
    congr 1
  calc germEval hpt Yval (detX K ι) = ((matX K ι).map (germEval hpt Yval)).det :=
        (det_map_ringHom _ _).symm
    _ = (M.map (Germ.coeRingHom (atTop : Filter ℕ))).det := by rw [hmap]
    _ = Germ.coeRingHom (atTop : Filter ℕ) M.det := det_map_ringHom _ _
    _ = _ := by rw [hdet]; rfl

/-- Evaluating `det Y` at a matrix is taking its determinant. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem aeval_detX {A' : Type*} [CommRing A'] [Algebra (RatFunc K) A'] (x : ι × ι → A') :
    aeval x (detX K ι) = (Matrix.of fun i j => x (i, j) : Matrix ι ι A').det := by
  have h := det_map_algHom (aeval (R := RatFunc K) x) (matX K ι)
  rw [detX, ← h]
  congr 1
  ext i j
  simp [matX]

/-- **`det Y` is not a relation**, as soon as the matrices are eventually invertible.  This is the
contradiction [AF22] reach in the proof of Lemma 2.5. -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem detX_notMem_relationIdeal {pt : ℕ → K} (hpt : Function.Injective pt)
    (Yval : ℕ → ι × ι → K)
    (hdet : ∀ᶠ n in atTop, (Matrix.of fun i j => Yval n (i, j) : Matrix ι ι K).det ≠ 0) :
    detX K ι ∉ relationIdeal hpt Yval := by
  intro hmem
  rw [relationIdeal, RingHom.mem_ker, germEval_detX, ← Germ.coe_zero, Germ.coe_eq] at hmem
  obtain ⟨n, hn⟩ := (hmem.and hdet).exists
  exact hn.2 hn.1

end DetX

/-! ## Lemma 2.5: existence of a relation matrix -/

section RelationMatrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] Definition 2.6.**  A *relation matrix* for an ideal `I ⊆ K(z)[Y]` is a matrix over an
algebraically closed extension `A` of `K(z)` all of whose entries satisfy every relation in `I`,
and which is invertible. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
def IsRelationMatrix {A : Type*} [Field A] [Algebra (RatFunc K) A]
    (I : Ideal (MvPolynomial (ι × ι) (RatFunc K))) (φ : Matrix ι ι A) : Prop :=
  (∀ P ∈ I, aeval (fun s : ι × ι => φ s.1 s.2) P = 0) ∧ φ.det ≠ 0

/-- **[AF22] Lemma 2.5.**  *«There exists a matrix `φ(z) ∈ GLₘ(A)` such that `P(φ(z), z) = 0` for
all polynomials `P ∈ 𝓘`.»*

Both halves at once, from the relative Nullstellensatz: `𝓘` is radical (Lemma 2.4) and `det Y`
is not in it (the matrices `A_k(α)` are invertible), so `det Y` does not vanish identically on the
zero locus of `𝓘`, and a point where it does not vanish is a relation matrix.

Stated over an **arbitrary** algebraically closed extension `A'` of `K(z)` rather than over
`AlgebraicClosure (RatFunc K)`: [AF22]'s `A` also has to contain the functions `f_i` when §2.4
splits the lifted relation, and `AlgebraicClosure (LaurentSeries K)` is then the ambient field of
choice.  Nothing in the proof cares which one. -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem exists_relationMatrix (A' : Type*) [Field A'] [Algebra (RatFunc K) A'] [IsAlgClosed A']
    {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → ι × ι → K)
    (hdet : ∀ᶠ n in atTop, (Matrix.of fun i j => Yval n (i, j) : Matrix ι ι K).det ≠ 0) :
    ∃ φ : Matrix ι ι A', IsRelationMatrix (relationIdeal hpt Yval) φ := by
  classical
  set I := relationIdeal hpt Yval with hI
  have hrad : I.radical = I := (lemma_2_4 hpt Yval).radical
  have hnot : detX K ι ∉ vanishingIdeal (RatFunc K) (zeroLocus A' I) := by
    rw [vanishingIdeal_zeroLocus_eq_radical, hrad]
    exact detX_notMem_relationIdeal hpt Yval hdet
  rw [mem_vanishingIdeal_iff] at hnot
  push Not at hnot
  obtain ⟨x, hx, hxdet⟩ := hnot
  refine ⟨Matrix.of fun i j => x (i, j), fun P hP => hx P hP, ?_⟩
  intro hzero
  exact hxdet ((aeval_detX x).trans hzero)

/-- **[AF22] Lemma 2.5 with algebraic entries.**  [AF22]'s `A` is *the algebraic closure of `ℚ̄(z)`
inside* the Puiseux series, so their `φ(z)` has entries algebraic over `ℚ̄(z)` — which is what §2.4
spends when it writes them as polynomials in a primitive element.  Here the same is obtained inside
any algebraically closed extension `Ω`, by looking for the relation matrix in the relative
algebraic closure of `K(z)` in `Ω`, which is itself algebraically closed
(`algebraicClosure.isAlgClosure`).

This is the form `CITED/AdamczewskiFaverjonPrimitive` consumes: the relation matrix and the
solutions `fᵢ` of the Mahler system then live in one and the same field. -/
@[category research solved, AMS 11 12 13 15, ref "AF22", group "af_mahler_alternative"]
theorem exists_relationMatrix_algebraic (Ω : Type*) [Field Ω] [Algebra (RatFunc K) Ω]
    [IsAlgClosed Ω] {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → ι × ι → K)
    (hdet : ∀ᶠ n in atTop, (Matrix.of fun i j => Yval n (i, j) : Matrix ι ι K).det ≠ 0) :
    ∃ φ : Matrix ι ι Ω, IsRelationMatrix (relationIdeal hpt Yval) φ ∧
      ∀ i j, IsIntegral (RatFunc K) (φ i j) := by
  classical
  haveI : IsAlgClosed ↥(algebraicClosure (RatFunc K) Ω) := IsAlgClosure.isAlgClosed (RatFunc K)
  obtain ⟨ψ, hψrel, hψdet⟩ := exists_relationMatrix ↥(algebraicClosure (RatFunc K) Ω) hpt Yval hdet
  refine ⟨ψ.map (algebraMap ↥(algebraicClosure (RatFunc K) Ω) Ω), ⟨fun P hP => ?_, ?_⟩,
    fun i j => ?_⟩
  · have h := congrArg (algebraMap ↥(algebraicClosure (RatFunc K) Ω) Ω) (hψrel P hP)
    rw [map_zero] at h
    rw [← h]
    exact (MvPolynomial.comp_aeval_apply (f := fun s : ι × ι => ψ s.1 s.2)
      (IsScalarTower.toAlgHom (RatFunc K) ↥(algebraicClosure (RatFunc K) Ω) Ω) P).symm
  · rw [det_map_ringHom]
    exact fun h => hψdet ((algebraMap ↥(algebraicClosure (RatFunc K) Ω) Ω).injective
      (by simpa using h))
  · exact mem_algebraicClosure_iff'.1 (ψ i j).2

end RelationMatrix

/-! ## The twist `P(Y·A_k(z), z^{q^k})` -/

section Twist

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Substitution `z ↦ z^n` on rational functions**, `n ≥ 1`.  Built from `Polynomial.expand` by
the universal property of the localization: `z ↦ z^n` sends non-zero polynomials to non-zero
polynomials, hence to units of `K(z)`. -/
@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def substPowRat (K : Type*) [Field K] {n : ℕ} (hn : 0 < n) :
    RatFunc K →+* RatFunc K :=
  IsLocalization.lift (M := (K[X])⁰) (S := RatFunc K)
    (g := (algebraMap K[X] (RatFunc K)).comp (substPow K n))
    (fun y => by
      refine isUnit_iff_ne_zero.2 ?_
      simp only [RingHom.coe_comp, Function.comp_apply, ne_eq]
      intro h
      refine substPow_ne_zero hn (nonZeroDivisors.ne_zero y.2) ?_
      exact RatFunc.algebraMap_injective K (by simpa using h))

@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem substPowRat_algebraMap {n : ℕ} (hn : 0 < n) (p : K[X]) :
    substPowRat K hn (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (substPow K n p) :=
  IsLocalization.lift_eq _ _

/-- **The shift `ℓ ↦ ℓ + k` on germs at infinity**, as a ring homomorphism.  This is where
[AF22]'s «for all `k ≫ 1`» is absorbed: shifting the index does not change what a germ is. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def germShift (K : Type*) [Field K] (k : ℕ) :
    Germ (atTop : Filter ℕ) K →+* Germ (atTop : Filter ℕ) K where
  toFun g := g.compTendsto (fun n => n + k) (Filter.tendsto_add_atTop_nat k)
  map_one' := by
    rw [← Germ.coe_one, Germ.coe_compTendsto]
    rfl
  map_mul' x y := by
    induction x using Germ.inductionOn with
    | _ f =>
        induction y using Germ.inductionOn with
        | _ g =>
            rw [← Germ.coe_mul, Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto,
              ← Germ.coe_mul]
            rfl
  map_zero' := by
    rw [← Germ.coe_zero, Germ.coe_compTendsto]
    rfl
  map_add' x y := by
    induction x using Germ.inductionOn with
    | _ f =>
        induction y using Germ.inductionOn with
        | _ g =>
            rw [← Germ.coe_add, Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto,
              ← Germ.coe_add]
            rfl

/-- A finite sum of germs is the germ of the pointwise sum. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem germ_coe_sum {ι' : Type*} (s : Finset ι') (g : ι' → ℕ → K) :
    ((fun n => ∑ l ∈ s, g l n : ℕ → K) : Germ (atTop : Filter ℕ) K) =
      ∑ l ∈ s, (g l : Germ (atTop : Filter ℕ) K) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [← Germ.coe_zero]
      rfl
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [← ih, ← Germ.coe_add]
      rfl

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem germShift_coe (k : ℕ) (f : ℕ → K) :
    germShift K k (f : Germ (atTop : Filter ℕ) K) = ((fun n => f (n + k) : ℕ → K) :
      Germ (atTop : Filter ℕ) K) :=
  Germ.coe_compTendsto f (Filter.tendsto_add_atTop_nat k)

/-- Substituting `z ↦ z^{q^k}` in a rational function shifts the evaluation sequence by `k`, as
soon as the points are the Mahler iterates `pt n = α^{q^n}`. -/
@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem germRatFuncEval_substPowRat {pt : ℕ → K} (hpt : Function.Injective pt) {m k : ℕ}
    (hm : 0 < m) (hshift : ∀ n, pt (n + k) = pt n ^ m) (c : RatFunc K) :
    germRatFuncEval hpt (substPowRat K hm c) = germShift K k (germRatFuncEval hpt c) := by
  have h : (germRatFuncEval hpt).comp (substPowRat K hm) =
      (germShift K k).comp (germRatFuncEval hpt) := by
    refine IsLocalization.ringHom_ext (M := (K[X])⁰) ?_
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply]
    rw [substPowRat_algebraMap, germRatFuncEval_algebraMap, germRatFuncEval_algebraMap,
      germPolyEval_apply, germPolyEval_apply, germShift_coe]
    refine Germ.coe_eq.2 (Filter.Eventually.of_forall fun n => ?_)
    simp only [substPow_eval, hshift]
  exact DFunLike.congr_fun h c

variable (q : ℕ) (A : Matrix ι ι K[X])

/-- **The twist `P(Y, z) ↦ P(Y·A_k(z), z^{q^k})`** of [AF22]'s proof of Lemma 2.7, as a ring
homomorphism of `K(z)[Y]`. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def twist {q : ℕ} (hq : 0 < q) (A : Matrix ι ι K[X]) (k : ℕ) :
    MvPolynomial (ι × ι) (RatFunc K) →+* MvPolynomial (ι × ι) (RatFunc K) :=
  eval₂Hom (C.comp (substPowRat K (pow_pos hq k))) fun s : ι × ι =>
    ∑ l, X (s.1, l) * C (algebraMap K[X] (RatFunc K) (iterMatrix q A k l s.2))

@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem twist_C {q : ℕ} (hq : 0 < q) (A : Matrix ι ι K[X]) (k : ℕ) (c : RatFunc K) :
    twist hq A k (C c) = C (substPowRat K (pow_pos hq k) c) := by
  simp [twist]

@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem twist_X {q : ℕ} (hq : 0 < q) (A : Matrix ι ι K[X]) (k : ℕ) (s : ι × ι) :
    twist hq A k (X s) =
      ∑ l, X (s.1, l) * C (algebraMap K[X] (RatFunc K) (iterMatrix q A k l s.2)) := by
  simp [twist]

/-- **The engine of [AF22] Lemma 2.7**: evaluating a twisted polynomial along the Mahler iterates
is evaluating the original polynomial along the *shifted* iterates.  Both sides are ring
homomorphisms out of `K(z)[Y]`, so the identity is checked on constants — where it is the
substitution `(α^{q^ℓ})^{q^k} = α^{q^{k+ℓ}}` — and on the indeterminates, where it is the cocycle
identity `A_ℓ(α)·A_k(α^{q^ℓ}) = A_{k+ℓ}(α)` of [AF22] (2.1). -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem germEval_twist {q : ℕ} (hq : 0 < q) (A : Matrix ι ι K[X]) {α : K}
    (hpt : Function.Injective fun k : ℕ => α ^ q ^ k) (k : ℕ)
    (P : MvPolynomial (ι × ι) (RatFunc K)) :
    germEval hpt (fun n s => (iterMatrix q A n s.1 s.2).eval α) (twist hq A k P) =
      germShift K k (germEval hpt (fun n s => (iterMatrix q A n s.1 s.2).eval α) P) := by
  classical
  set pt : ℕ → K := fun k => α ^ q ^ k with hptdef
  set Yval : ℕ → ι × ι → K := fun n s => (iterMatrix q A n s.1 s.2).eval α with hY
  have hshift : ∀ n, pt (n + k) = pt n ^ q ^ k := by
    intro n
    simp [hptdef, ← pow_mul, ← pow_add, Nat.add_comm]
  have h : (germEval hpt Yval).comp (twist hq A k) =
      (germShift K k).comp (germEval hpt Yval) := by
   refine MvPolynomial.ringHom_ext (fun c => ?_) (fun s => ?_)
   · simp only [RingHom.comp_apply, twist_C]
     rw [germEval, eval₂Hom_C, eval₂Hom_C]
     exact germRatFuncEval_substPowRat hpt (pow_pos hq k) hshift c
   · simp only [RingHom.comp_apply, twist_X]
     rw [map_sum]
     have hX : germEval hpt Yval (X s) = ((fun n => Yval n s : ℕ → K) :
         Germ (atTop : Filter ℕ) K) := by
       simp [germEval]
     rw [hX, germShift_coe]
     have hterm : ∀ l : ι, germEval hpt Yval
         (X (s.1, l) * C (algebraMap K[X] (RatFunc K) (iterMatrix q A k l s.2))) =
         ((fun n => Yval n (s.1, l) * (iterMatrix q A k l s.2).eval (pt n) : ℕ → K) :
           Germ (atTop : Filter ℕ) K) := by
       intro l
       rw [map_mul]
       have h1 : germEval hpt Yval (X (s.1, l)) =
           ((fun n => Yval n (s.1, l) : ℕ → K) : Germ (atTop : Filter ℕ) K) := by
         simp [germEval]
       have h2 : germEval hpt Yval (C (algebraMap K[X] (RatFunc K) (iterMatrix q A k l s.2))) =
           ((fun n => (iterMatrix q A k l s.2).eval (pt n) : ℕ → K) :
             Germ (atTop : Filter ℕ) K) := by
         rw [germEval, eval₂Hom_C, germRatFuncEval_algebraMap, germPolyEval_apply]
       rw [h1, h2, ← Germ.coe_mul]
       rfl
     simp only [hterm]
     rw [← germ_coe_sum]
     refine Germ.coe_eq.2 (Filter.Eventually.of_forall fun n => ?_)
     have hcoc := iterMatrix_add (K := K) q A k n
     have hval : (iterMatrix q A (k + n) s.1 s.2).eval α =
         ∑ l, Yval n (s.1, l) * (iterMatrix q A k l s.2).eval (pt n) := by
       rw [hcoc]
       simp only [Matrix.mul_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul, hY, Matrix.map]
       refine Finset.sum_congr rfl fun l _ => ?_
       simp only [Matrix.of_apply]
       rw [substPow_eval]
     show ∑ l, Yval n (s.1, l) * Polynomial.eval (pt n) (iterMatrix q A k l s.2) = Yval (n + k) s
     rw [show n + k = k + n from Nat.add_comm _ _]
     exact hval.symm
  exact DFunLike.congr_fun h P

/-- **[AF22] Lemma 2.7, first half**: the twist of a relation is a relation.  *«Set
`Q(Y,z) := P(Y·A_k(z), z^{q^k})`.  Then `Q ∈ 𝓘`.»* -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem twist_mem_relationIdeal {q : ℕ} (hq : 0 < q) (A : Matrix ι ι K[X]) {α : K}
    (hpt : Function.Injective fun k : ℕ => α ^ q ^ k) (k : ℕ)
    {P : MvPolynomial (ι × ι) (RatFunc K)}
    (hP : P ∈ relationIdeal hpt fun n s => (iterMatrix q A n s.1 s.2).eval α) :
    twist hq A k P ∈ relationIdeal hpt fun n s => (iterMatrix q A n s.1 s.2).eval α := by
  rw [relationIdeal, RingHom.mem_ker] at hP ⊢
  rw [germEval_twist, hP, map_zero]

/-- **[AF22] Lemma 2.7.**  *«Let `φ(z) ∈ GLₘ(A)` be a relation matrix.  Then
`P(φ(z)A_k(z), z^{q^k}) = 0` for all `P ∈ 𝓘` and all `k ≥ 0`.»*

The left-hand side is spelled as the relation matrix evaluated at the twisted polynomial, which is
literally «substitute `Y ↦ φ(z)A_k(z)` and `z ↦ z^{q^k}`» — see `AF.aeval_twist` for the
unfolded form. -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem lemma_2_7 {A' : Type*} [Field A'] [Algebra (RatFunc K) A'] {q : ℕ} (hq : 0 < q)
    (A : Matrix ι ι K[X]) {α : K} (hpt : Function.Injective fun k : ℕ => α ^ q ^ k)
    {φ : Matrix ι ι A'}
    (hφ : IsRelationMatrix (relationIdeal hpt fun n s => (iterMatrix q A n s.1 s.2).eval α) φ)
    (k : ℕ) {P : MvPolynomial (ι × ι) (RatFunc K)}
    (hP : P ∈ relationIdeal hpt fun n s => (iterMatrix q A n s.1 s.2).eval α) :
    aeval (fun s : ι × ι => φ s.1 s.2) (twist hq A k P) = 0 :=
  hφ.1 _ (twist_mem_relationIdeal hq A hpt k hP)

/-- The twisted evaluation, unfolded: `aeval φ (twist P)` really is «`P` evaluated at
`Y = φ·A_k(z)`, with `z ↦ z^{q^k}` in the coefficients». -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem aeval_twist {A' : Type*} [Field A'] [Algebra (RatFunc K) A'] {q : ℕ} (hq : 0 < q)
    (A : Matrix ι ι K[X]) (k : ℕ) (φ : Matrix ι ι A')
    (P : MvPolynomial (ι × ι) (RatFunc K)) :
    aeval (fun s : ι × ι => φ s.1 s.2) (twist hq A k P) =
      eval₂ ((algebraMap (RatFunc K) A').comp (substPowRat K (pow_pos hq k)))
        (fun s : ι × ι =>
          (φ * (iterMatrix q A k).map ((algebraMap (RatFunc K) A').comp
            (algebraMap K[X] (RatFunc K)))) s.1 s.2) P := by
  classical
  have h : (aeval (R := RatFunc K) (fun s : ι × ι => φ s.1 s.2)).toRingHom.comp
      (twist hq A k) =
      eval₂Hom ((algebraMap (RatFunc K) A').comp (substPowRat K (pow_pos hq k)))
        (fun s : ι × ι =>
          (φ * (iterMatrix q A k).map ((algebraMap (RatFunc K) A').comp
            (algebraMap K[X] (RatFunc K)))) s.1 s.2) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun s => ?_)
    · simp [twist_C]
    · simp only [RingHom.comp_apply, twist_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum,
        map_mul, aeval_X, aeval_C, eval₂Hom_X']
      simp [Matrix.mul_apply, Matrix.map_apply]
  exact DFunLike.congr_fun h P

end Twist

/-! ## The relation matrix of an actual Mahler system -/

section Mahler

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {q : ℕ} {A : Matrix ι ι K[X]} {α : K}

/-- **[AF22] Lemma 2.5 for the relation ideal of a Mahler system at a regular point.**  This is
the form WP10 consumes: a matrix `φ` over `AlgebraicClosure (RatFunc K)`, invertible, all of whose
entries satisfy every functional relation of the system. -/
@[category research solved, AMS 11 12 13 15, ref "AF22", group "af_mahler_alternative"]
theorem exists_relationMatrix_mahler (A' : Type*) [Field A'] [Algebra (RatFunc K) A']
    [IsAlgClosed A'] (f : K →+* ℂ) (hq : 2 ≤ q) (h0 : α ≠ 0) (h1 : ‖f α‖ < 1)
    (A : Matrix ι ι K[X]) (hreg : IsRegularPoint q A α) :
    ∃ φ : Matrix ι ι A', IsRelationMatrix (mahlerRelationIdeal f hq h0 h1 A) φ := by
  refine exists_relationMatrix A' _ _ (Filter.Eventually.of_forall fun n => ?_)
  have h := iterMatrix_det_eval_ne_zero hreg n
  have hm : (Matrix.of fun i j => (iterMatrix q A n i j).eval α : Matrix ι ι K) =
      (iterMatrix q A n).map (Polynomial.evalRingHom α) := by
    ext i j
    simp
  show (Matrix.of fun i j => (iterMatrix q A n i j).eval α : Matrix ι ι K).det ≠ 0
  rw [hm, det_map_ringHom]
  simpa using h

/-- **[AF22] Lemma 2.7 for the relation ideal of a Mahler system.** -/
@[category research solved, AMS 11 12 13 15, ref "AF22", group "af_mahler_alternative"]
theorem lemma_2_7_mahler {A' : Type*} [Field A'] [Algebra (RatFunc K) A'] (f : K →+* ℂ)
    (hq : 2 ≤ q) (h0 : α ≠ 0) (h1 : ‖f α‖ < 1) (A : Matrix ι ι K[X]) {φ : Matrix ι ι A'}
    (hφ : IsRelationMatrix (mahlerRelationIdeal f hq h0 h1 A) φ) (k : ℕ)
    {P : MvPolynomial (ι × ι) (RatFunc K)} (hP : P ∈ mahlerRelationIdeal f hq h0 h1 A) :
    aeval (fun s : ι × ι => φ s.1 s.2) (twist (by omega : 0 < q) A k P) = 0 :=
  lemma_2_7 (by omega) A _ hφ k hP

end Mahler

end AF
