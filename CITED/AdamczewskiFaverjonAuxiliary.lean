/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import CITED.AdamczewskiFaverjonBidegree
import CITED.AdamczewskiFaverjonRelationMatrix

/-!
# [AF22] §2.3 Step (AF): the auxiliary function

The first half of plan-formalize-AF17's **WP10**.  [AF22] build the auxiliary function of their key
lemma by a *dimension count* — this is the single biggest simplification of their proof over the
classical Mahler method, since no Siegel lemma is needed: a linear map from a larger space to a
smaller one has a non-trivial kernel, and that is the whole of Lemma 2.12.

The three maps of [AF22] Step (AF) are composed here into one `K`-linear map

  `afMap : (Fin (δ₁+1) → 𝓘^⊥(δ₁,δ₂)) →ₗ[K] K(z)[Y] ⧸ 𝓘`,
  `(P₀,…,P_{δ₁}) ↦ (E_p mod 𝓘)`,   `E := ∑_j P_j F^j`,

where `E_p` is the truncation of `E` at order `p` in `z`, twisted by the fixed invertible matrix
`M` of the normalization `Θ_k(z) = Mφ(z)A_{k-k₀}(z)`.  Its source has dimension
`(δ₁+1)·d(δ₁,δ₂)` and its range sits inside the image of `K[Y,z]_{D,p-1}`, of dimension
`d(D,p-1)`; whenever the first exceeds the second there is a non-zero kernel element, and its
components are the polynomials of Lemma 2.12.

## Three departures from the printed proof

**One ideal, not two.**  [AF22] introduce a second ideal
`𝓙 := {P : P(MY,z) ∈ 𝓘}` and quotient by `𝓙(2δ₁,p-1)`.  Here the substitution `M` is applied to
`E_p` instead, and the quotient is by `𝓘` throughout.  The two are equivalent, but the second
avoids re-running Lemmas 2.2–2.3 for a second ideal.

**[AF22]'s bidegree claim is false, and the repair costs a constant.**  [AF22] justify
`dim 𝓙(δ₁,δ₂) = dim 𝓘(δ₁,δ₂)` by «the map `P(Y,z) ↦ P(MY,z)` is an automorphism of
`K[Y,z]_{δ₁,δ₂}`».  It is not: `K[Y,z]_{δ₁,δ₂}` is bounded *in each* indeterminate `y_{i,j}`
(their own definition in §2.2.1), and a linear substitution does not preserve that — for `m = 2`,
`y₁₁y₂₁ ↦ (M₁₁y₁₁+M₁₂y₂₁)(M₂₁y₁₁+M₂₂y₂₁)` has degree `2` in `y₁₁`.  What *is* preserved is the
**total** degree in `Y`, so the substitution maps `K[Y,z]_{u,v}` into `K[Y,z]_{m²u,v}`.  The
argument survives: the extra factor `m²` in the first index is absorbed by iterating Lemma 2.3,
which costs a constant depending on `m` alone — and only constants independent of `δ₁` matter for
the final contradiction.  This is `AF.relDim_le_of_le_two_pow`: a factor `c ≤ 2^j` in the first
index costs at most `(2^{m²})^j`.  The first index Step (AF) actually needs is `(m²+1)δ₁` — the
`m²δ₁` above plus the `δ₁` from the powers of `F` — so the constant is
`AF.afConst = 2^{m²⌈log₂(m²+1)⌉}`, defined in `CITED/AdamczewskiFaverjonStepAF.lean`.

**Polynomial coefficients.**  `𝓘^⊥(δ₁,δ₂)` lives in `K(z)[Y]`, but the auxiliary function has to
be multiplied by powers of `F(Y,z) = τYf(z)`, whose coefficients are *power series*.  The two are
reconciled by transporting the complement to `K[Y,z]` once and for all (`AF.relComplP`, of the
same dimension as `𝓘^⊥(δ₁,δ₂)`), and mapping `K[z] → K⟦z⟧` from there; the truncation
`PowerSeries.trunc p` maps back.

## Contents

* `AF.zSpan`, `AF.coeffSpan`, `AF.mem_bidegPiece_iff` — membership in `K[Y,z]_{u,v}`, spelled out;
* `AF.bidegP`, `AF.toRat`, `AF.relComplP`, `AF.finrank_relComplP` — the polynomial-coefficient
  copy of `𝓘^⊥(δ₁,δ₂)`;
* `AF.relDim_mono_left`, `AF.relDim_two_pow_mul_le`, `AF.relDim_le_of_le_two_pow` — Lemma 2.3
  iterated, the repair of the bidegree claim;
* `AF.subMat`, `AF.totalDegree_subMat_le`, `AF.coeff_subMat_mem`, `AF.eval₂_subMat`,
  `AF.aeval_subMat` — the linear substitution `Y ↦ MY`, the two degree bounds it respects, and
  the evaluation identity `P(MY,z)|_{Y=x} = P(Y,z)|_{Y=Mx}`;
* `AF.truncMv`, `AF.toPS`, `AF.afTerm`, `AF.afMap`, `AF.range_afMap_le` — the map of Step (AF);
* **`AF.exists_auxiliary`** — [AF22] Lemma 2.12, the dimension count;
* `AF.toRat_notMem_of_mem_relComplP`, **`AF.frequently_evalAt_ne_zero`** — [AF22] Step (NV).

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3, Step (AF) (Lemma 2.12) and Step (NV).
* [AF17f] `plans/plan-formalize-AF17.html`: WP10, milestone M4 (Stage 2).
-/

open Filter MvPolynomial
open scoped Polynomial

namespace AF

/-! ## Membership in `K[Y,z]_{u,v}` -/

section Membership

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The `K`-span of `1, z, …, z^v` inside `K(z)`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def zSpan (K : Type*) [Field K] (v : ℕ) : Submodule K (RatFunc K) :=
  Submodule.span K (Set.range fun a : Fin (v + 1) => (RatFunc.X : RatFunc K) ^ (a : ℕ))

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem pow_mem_zSpan {a v : ℕ} (h : a ≤ v) : (RatFunc.X : RatFunc K) ^ a ∈ zSpan K v :=
  Submodule.subset_span ⟨⟨a, Nat.lt_succ_of_le h⟩, rfl⟩

/-- Polynomials whose coefficients all lie in `zSpan K v`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def coeffSpan (K : Type*) [Field K] (σ : Type*) (v : ℕ) :
    Submodule K (MvPolynomial σ (RatFunc K)) where
  carrier := {P | ∀ ν, P.coeff ν ∈ zSpan K v}
  add_mem' hx hy ν := by
    simpa only [MvPolynomial.coeff_add] using add_mem (hx ν) (hy ν)
  zero_mem' ν := by simp
  smul_mem' c x hx ν := by
    rw [MvPolynomial.coeff_smul]
    exact Submodule.smul_mem _ c (hx ν)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem mem_coeffSpan_iff {v : ℕ} {P : MvPolynomial σ (RatFunc K)} :
    P ∈ coeffSpan K σ v ↔ ∀ ν, P.coeff ν ∈ zSpan K v := Iff.rfl

/-- **Membership in `K[Y,z]_{u,v}`, spelled out**: degree at most `u` in every indeterminate, and
every coefficient a `K`-combination of `1, z, …, z^v`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem mem_bidegPiece_iff (P : MvPolynomial σ (RatFunc K)) (u v : ℕ) :
    P ∈ bidegPiece K σ u v ↔
      ((∀ ν ∈ P.support, ∀ i, ν i ≤ u) ∧ ∀ ν, P.coeff ν ∈ zSpan K v) := by
  classical
  constructor
  · intro hP
    have hsub : bidegPiece K σ u v ≤
        (restrictDegree σ (RatFunc K) u).restrictScalars K ⊓ coeffSpan K σ v := by
      rw [bidegPiece, Submodule.span_le]
      rintro _ ⟨⟨k, a⟩, ⟨hk, ha⟩, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
      refine ⟨?_, ?_⟩
      · rw [mem_restrictDegree]
        intro s hs i
        have := MvPolynomial.support_monomial_subset hs
        rw [Finset.mem_singleton] at this
        subst this
        exact hk i
      · intro ν
        rw [MvPolynomial.coeff_monomial]
        split
        · exact pow_mem_zSpan ha
        · exact Submodule.zero_mem _
    obtain ⟨h1, h2⟩ := hsub hP
    exact ⟨(mem_restrictDegree _ _ _).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ (ν : σ →₀ ℕ), (∀ i, ν i ≤ u) → ∀ c ∈ zSpan K v,
        (monomial ν c : MvPolynomial σ (RatFunc K)) ∈ bidegPiece K σ u v := by
      intro ν hν c hc
      rw [zSpan] at hc
      induction hc using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨a, rfl⟩ := hx
          exact monomial_mem_bidegPiece hν (Nat.lt_succ_iff.1 a.2)
      | zero => simpa using Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
          rw [← MvPolynomial.smul_monomial]
          exact Submodule.smul_mem _ c hx
    rw [MvPolynomial.as_sum P]
    exact Submodule.sum_mem _ fun ν hν => key ν (h1 ν hν) _ (h2 ν)

/-- The sufficient form used below: a total-degree bound plus a coefficient bound. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem mem_bidegPiece_of_totalDegree {P : MvPolynomial σ (RatFunc K)} {u v : ℕ}
    (hu : P.totalDegree ≤ u) (hv : P ∈ coeffSpan K σ v) : P ∈ bidegPiece K σ u v := by
  classical
  refine (mem_bidegPiece_iff P u v).2 ⟨fun ν hν i => ?_, hv⟩
  have h1 : ν i ≤ ν.sum fun _ e => e := by
    show ν i ≤ ∑ a ∈ ν.support, ν a
    by_cases hi : i ∈ ν.support
    · exact Finset.single_le_sum (f := fun j => ν j) (fun j _ => Nat.zero_le _) hi
    · simp [Finsupp.notMem_support_iff.1 hi]
  exact le_trans h1 (le_trans (MvPolynomial.le_totalDegree hν) hu)

end Membership

/-! ## The polynomial-coefficient copy of `𝓘^⊥(δ₁,δ₂)` -/

section PolyCopy

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The inclusion `K[Y,z] ↪ K(z)[Y]`, as a `K`-algebra map. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def toRat (K : Type*) [Field K] (σ : Type*) :
    MvPolynomial σ K[X] →ₐ[K] MvPolynomial σ (RatFunc K) :=
  MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom K K[X] (RatFunc K))

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem toRat_apply (P : MvPolynomial σ K[X]) :
    toRat K σ P = MvPolynomial.map (algebraMap K[X] (RatFunc K)) P := rfl

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem injective_toRat : Function.Injective (toRat K σ) :=
  MvPolynomial.map_injective _ (RatFunc.algebraMap_injective K)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem toRat_monomial (ν : σ →₀ ℕ) (a : ℕ) :
    toRat K σ (monomial ν ((Polynomial.X : K[X]) ^ a)) =
      monomial ν ((RatFunc.X : RatFunc K) ^ a) := by
  rw [toRat_apply, MvPolynomial.map_monomial, map_pow, RatFunc.algebraMap_X]

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem totalDegree_toRat_le (P : MvPolynomial σ K[X]) :
    (toRat K σ P).totalDegree ≤ P.totalDegree := by
  classical
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)

/-- `K[Y,z]_{u,v}` with *polynomial* coefficients written out. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def bidegP (K : Type*) [Field K] (σ : Type*) (u v : ℕ) :
    Submodule K (MvPolynomial σ K[X]) :=
  Submodule.span K ((fun p : (σ →₀ ℕ) × ℕ => monomial p.1 ((Polynomial.X : K[X]) ^ p.2)) ''
    {p | (∀ i, p.1 i ≤ u) ∧ p.2 ≤ v})

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem map_bidegP (u v : ℕ) :
    (bidegP K σ u v).map (toRat K σ).toLinearMap = bidegPiece K σ u v := by
  refine le_antisymm ?_ ?_
  · rw [bidegP, Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    show toRat K σ (monomial p.1 ((Polynomial.X : K[X]) ^ p.2)) ∈ bidegPiece K σ u v
    rw [toRat_monomial]
    exact monomial_mem_bidegPiece hp.1 hp.2
  · rw [bidegPiece, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨monomial p.1 ((Polynomial.X : K[X]) ^ p.2), Submodule.subset_span ⟨p, hp, rfl⟩,
      toRat_monomial p.1 p.2⟩

instance instFiniteDimensionalBidegP (u v : ℕ) : FiniteDimensional K (bidegP K σ u v) := by
  refine FiniteDimensional.span_of_finite K (Set.Finite.image _ ?_)
  exact ((finite_boundedExponents (σ := σ) u).prod (Set.finite_Iic v)).subset fun p hp =>
    ⟨hp.1, Set.mem_Iic.mpr hp.2⟩

variable (I : Ideal (MvPolynomial σ (RatFunc K)))

/-- `𝓘^⊥(δ₁,δ₂)` read inside `K[Y,z]`: the polynomial preimages of the chosen complement. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def relComplP (δ₁ δ₂ : ℕ) : Submodule K (MvPolynomial σ K[X]) :=
  (relCompl I δ₁ δ₂).comap (toRat K σ).toLinearMap ⊓ bidegP K σ δ₁ δ₂

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem map_relComplP (δ₁ δ₂ : ℕ) :
    (relComplP I δ₁ δ₂).map (toRat K σ).toLinearMap = relCompl I δ₁ δ₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨P, ⟨hP, -⟩, rfl⟩
    exact hP
  · intro x hx
    have hxb : x ∈ (bidegP K σ δ₁ δ₂).map (toRat K σ).toLinearMap := by
      rw [map_bidegP]; exact relCompl_le_bidegPiece I δ₁ δ₂ hx
    obtain ⟨P, hP, rfl⟩ := hxb
    exact ⟨P, ⟨hx, hP⟩, rfl⟩

instance instFiniteDimensionalRelComplP (δ₁ δ₂ : ℕ) :
    FiniteDimensional K (relComplP I δ₁ δ₂) :=
  Submodule.finiteDimensional_of_le (inf_le_right : relComplP I δ₁ δ₂ ≤ bidegP K σ δ₁ δ₂)

instance instFreeRelComplP (δ₁ δ₂ : ℕ) : Module.Free K ↥(relComplP I δ₁ δ₂) := by
  exact Module.Free.of_divisionRing K ↥(relComplP I δ₁ δ₂)

/-- The polynomial copy has the same dimension `d(δ₁,δ₂)`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem finrank_relComplP (δ₁ δ₂ : ℕ) :
    Module.finrank K ↥(relComplP I δ₁ δ₂) = relDim I δ₁ δ₂ := by
  have h := (Submodule.equivMapOfInjective (toRat K σ).toLinearMap
    (injective_toRat (K := K) (σ := σ)) (relComplP I δ₁ δ₂)).finrank_eq
  rw [map_relComplP] at h
  exact h.trans rfl

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem totalDegree_le_of_mem_bidegP {u v : ℕ} {P : MvPolynomial σ K[X]}
    (hP : P ∈ bidegP K σ u v) : P.totalDegree ≤ Fintype.card σ * u := by
  classical
  induction hP using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨k, a⟩, ⟨hk, -⟩, rfl⟩ := hx
      refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
      calc (k.sum fun _ => id) = ∑ i ∈ k.support, k i := rfl
        _ ≤ ∑ _i ∈ k.support, u := Finset.sum_le_sum fun i _ => hk i
        _ = k.support.card * u := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Fintype.card σ * u :=
            Nat.mul_le_mul_right _ (Finset.card_le_univ _)
  | zero => simp
  | add x y _ _ hx hy => exact le_trans (MvPolynomial.totalDegree_add x y) (max_le hx hy)
  | smul c x _ hx => exact le_trans (MvPolynomial.totalDegree_smul_le c x) hx

end PolyCopy

/-! ## Lemma 2.3, iterated -/

section IterLemma23

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (I : Ideal (MvPolynomial σ (RatFunc K)))

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem bidegPiece_mono_left {u u' v : ℕ} (h : u ≤ u') :
    bidegPiece K σ u v ≤ bidegPiece K σ u' v :=
  Submodule.span_mono (Set.image_mono fun _ hp => ⟨fun i => (hp.1 i).trans h, hp.2⟩)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem relImage_mono_left {u u' v : ℕ} (h : u ≤ u') :
    relImage I u v ≤ relImage I u' v :=
  Submodule.map_mono (bidegPiece_mono_left h)

/-- `d(δ₁,δ₂)` is monotone in its first argument. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem relDim_mono_left {u u' v : ℕ} (h : u ≤ u') : relDim I u v ≤ relDim I u' v := by
  rw [relDim_eq_finrank_relImage, relDim_eq_finrank_relImage]
  exact Submodule.finrank_mono (relImage_mono_left I h)

/-- Lemma 2.3 iterated `j` times: `d(2ʲu, v) ≤ 2^{jm²} d(u,v)`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem relDim_two_pow_mul_le (u v : ℕ) : ∀ j : ℕ,
    relDim I (2 ^ j * u) v ≤ (2 ^ Fintype.card σ) ^ j * relDim I u v
  | 0 => by simp
  | j + 1 => by
      have h1 : relDim I (2 ^ (j + 1) * u) v ≤ 2 ^ Fintype.card σ * relDim I (2 ^ j * u) v := by
        have : 2 ^ (j + 1) * u = 2 * (2 ^ j * u) := by ring
        rw [this]
        exact lemma_2_3 I (2 ^ j * u) v
      calc relDim I (2 ^ (j + 1) * u) v ≤ 2 ^ Fintype.card σ * relDim I (2 ^ j * u) v := h1
        _ ≤ 2 ^ Fintype.card σ * ((2 ^ Fintype.card σ) ^ j * relDim I u v) :=
            Nat.mul_le_mul_left _ (relDim_two_pow_mul_le u v j)
        _ = (2 ^ Fintype.card σ) ^ (j + 1) * relDim I u v := by ring

/-- **The repair of [AF22]'s bidegree claim.**  Enlarging the first index by any factor `c ≤ 2ʲ`
costs only the factor `2^{jm²}`, which does not depend on `δ₁`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem relDim_le_of_le_two_pow {c j u v : ℕ} (hc : c ≤ 2 ^ j) :
    relDim I (c * u) v ≤ (2 ^ Fintype.card σ) ^ j * relDim I u v :=
  le_trans (relDim_mono_left I (Nat.mul_le_mul_right u hc)) (relDim_two_pow_mul_le I u v j)

end IterLemma23

/-! ## The linear substitution `Y ↦ MY` -/

section SubMat

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The substitution `Y ↦ MY`** for a matrix `M` over `K`, as a `K`-algebra endomorphism of
`R[Y]` for any `K`-algebra `R`. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def subMat (R : Type*) [CommRing R] [Algebra K R] (M : Matrix ι ι K) :
    MvPolynomial (ι × ι) R →ₐ[R] MvPolynomial (ι × ι) R :=
  aeval fun s : ι × ι => ∑ l, C (algebraMap K R (M s.1 l)) * X (l, s.2)

@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem subMat_X (R : Type*) [CommRing R] [Algebra K R] (M : Matrix ι ι K) (s : ι × ι) :
    subMat R M (X s) = ∑ l, C (algebraMap K R (M s.1 l)) * X (l, s.2) := by
  rw [subMat, aeval_X]

@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem subMat_C (R : Type*) [CommRing R] [Algebra K R] (M : Matrix ι ι K) (c : R) :
    subMat R M (C c) = C c := by
  rw [subMat, aeval_C, algebraMap_eq]

/-- The substituted indeterminates have total degree at most `1`. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem totalDegree_subMat_gen_le (R : Type*) [CommRing R] [Algebra K R] (M : Matrix ι ι K)
    (s : ι × ι) : (∑ l, C (algebraMap K R (M s.1 l)) * X (l, s.2) :
      MvPolynomial (ι × ι) R).totalDegree ≤ 1 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have h1 : (C (algebraMap K R (M s.1 l)) : MvPolynomial (ι × ι) R).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  have h2 : (X (l, s.2) : MvPolynomial (ι × ι) R).totalDegree ≤ 1 := by
    have := MvPolynomial.totalDegree_monomial_le
      (Finsupp.single ((l, s.2) : ι × ι) 1) (1 : R)
    simpa [MvPolynomial.X, Finsupp.sum_single_index] using this
  omega

/-- **The substitution does not raise the total degree.**  This is what survives of [AF22]'s
claim that `P ↦ P(MY,z)` preserves `K[Y,z]_{δ₁,δ₂}`. -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem totalDegree_subMat_le (R : Type*) [CommRing R] [Algebra K R] (M : Matrix ι ι K)
    (P : MvPolynomial (ι × ι) R) : (subMat R M P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun ν hν => ?_
  rw [subMat, MvPolynomial.aeval_monomial]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have h0 : (algebraMap R (MvPolynomial (ι × ι) R) (P.coeff ν)).totalDegree = 0 := by
    rw [algebraMap_eq]; exact MvPolynomial.totalDegree_C _
  have h1 : (ν.prod fun n e => (∑ l, C (algebraMap K R (M n.1 l)) * X (l, n.2) :
      MvPolynomial (ι × ι) R) ^ e).totalDegree ≤ ν.sum fun _ e => e := by
    refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
    refine Finset.sum_le_sum fun n _ => ?_
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    simpa using Nat.mul_le_mul_left _ (totalDegree_subMat_gen_le R M n)
  have h2 : (ν.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hν
  omega

/-- **The substitution acts on coefficients through `K`.**  Every coefficient of `P(MY,z)` is a
`K`-combination of coefficients of `P`, so any `K`-submodule of the coefficient ring containing
the coefficients of `P` contains those of `P(MY,z)` — in particular the polynomials of degree
`< p`, which is what keeps the `z`-degree of the truncation. -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem coeff_subMat_mem {R : Type*} [CommRing R] [Algebra K R] (M : Matrix ι ι K)
    (V : Submodule K R) {P : MvPolynomial (ι × ι) R} (hP : ∀ ν, P.coeff ν ∈ V)
    (μ : ι × ι →₀ ℕ) : (subMat R M P).coeff μ ∈ V := by
  classical
  have hrange : ∀ ν : ι × ι →₀ ℕ,
      (ν.prod fun s e => (∑ l, C (algebraMap K R (M s.1 l)) * X (l, s.2) :
        MvPolynomial (ι × ι) R) ^ e) ∈
      (MvPolynomial.map (algebraMap K R) :
        MvPolynomial (ι × ι) K →+* MvPolynomial (ι × ι) R).range := by
    intro ν
    refine Subring.prod_mem _ fun s _ => Subring.pow_mem _ ?_ _
    refine ⟨∑ l, C (M s.1 l) * X ((l, s.2) : ι × ι), ?_⟩
    simp [map_sum, MvPolynomial.map_C, MvPolynomial.map_X]
  have hPsum : subMat R M P = ∑ ν ∈ P.support, subMat R M (monomial ν (P.coeff ν)) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum]
  rw [hPsum, MvPolynomial.coeff_sum]
  refine Submodule.sum_mem _ fun ν _ => ?_
  rw [subMat, MvPolynomial.aeval_monomial]
  obtain ⟨Q, hQ⟩ := hrange ν
  rw [← hQ, algebraMap_eq, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm,
    ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (hP ν)

/-- **Evaluating a substituted polynomial** is evaluating the original one at `M·x`. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem eval₂_subMat {R S : Type*} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (M : Matrix ι ι K) (f : R →+* S) (hf : ∀ c : K, f (algebraMap K R c) = algebraMap K S c)
    (x : Matrix ι ι S) (P : MvPolynomial (ι × ι) R) :
    eval₂ f (fun s : ι × ι => x s.1 s.2) (subMat R M P) =
      eval₂ f (fun s : ι × ι => (M.map (algebraMap K S) * x) s.1 s.2) P := by
  classical
  have h : (eval₂Hom f fun s : ι × ι => x s.1 s.2).comp (subMat R M).toRingHom =
      eval₂Hom f fun s : ι × ι => (M.map (algebraMap K S) * x) s.1 s.2 := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun s => ?_)
    · simp [subMat_C]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subMat_X, map_sum,
        map_mul, eval₂Hom_X', eval₂Hom_C, hf]
      simp [Matrix.mul_apply, Matrix.map_apply]
  exact DFunLike.congr_fun h P

/-- The `aeval` form of `AF.eval₂_subMat`. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem aeval_subMat {R S : Type*} [CommRing R] [CommRing S] [Algebra K R] [Algebra R S]
    [Algebra K S] [IsScalarTower K R S] (M : Matrix ι ι K) (x : Matrix ι ι S)
    (P : MvPolynomial (ι × ι) R) :
    aeval (fun s : ι × ι => x s.1 s.2) (subMat R M P) =
      aeval (fun s : ι × ι => (M.map (algebraMap K S) * x) s.1 s.2) P :=
  eval₂_subMat M (algebraMap R S) (fun c => (IsScalarTower.algebraMap_apply K R S c).symm) x P

end SubMat

/-! ## Truncation, and the map of Step (AF) -/

section AfMap

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **Truncation at order `p` in `z`**, coefficientwise, as a `K`-linear map
`K⟦z⟧[Y] →ₗ[K] K[z][Y]`.  This is [AF22]'s `E ↦ E_p`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def truncMv (K : Type*) [Field K] (σ : Type*) (p : ℕ) :
    MvPolynomial σ (PowerSeries K) →ₗ[K] MvPolynomial σ K[X] :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (PowerSeries.trunc p) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem coeff_truncMv (p : ℕ) (E : MvPolynomial σ (PowerSeries K)) (ν : σ →₀ ℕ) :
    (truncMv K σ p E).coeff ν = PowerSeries.trunc p (E.coeff ν) := rfl

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem support_truncMv_subset (p : ℕ) (E : MvPolynomial σ (PowerSeries K)) :
    (truncMv K σ p E).support ⊆ E.support := by
  intro ν hν
  by_contra h
  rw [MvPolynomial.notMem_support_iff] at h
  rw [MvPolynomial.mem_support_iff, coeff_truncMv, h] at hν
  exact hν (by simp)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem totalDegree_truncMv_le (p : ℕ) (E : MvPolynomial σ (PowerSeries K)) :
    (truncMv K σ p E).totalDegree ≤ E.totalDegree :=
  Finset.sup_mono (support_truncMv_subset p E)

/-- A polynomial of degree at most `v` becomes an element of `zSpan K v`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem algebraMap_mem_zSpan {v : ℕ} {q : K[X]} (hq : ∀ a ∈ q.support, a ≤ v) :
    algebraMap K[X] (RatFunc K) q ∈ zSpan K v := by
  classical
  rw [Polynomial.as_sum_support q, map_sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_X]
  have hC : algebraMap K[X] (RatFunc K) (Polynomial.C (q.coeff a)) =
      algebraMap K (RatFunc K) (q.coeff a) := by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
    simp
  rw [hC, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (pow_mem_zSpan (hq a ha))

/-- Coefficients of degree `< p` put the image in `K[Y,z]_{·,p-1}`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem toRat_mem_coeffSpan {p : ℕ} {P : MvPolynomial σ K[X]}
    (hP : ∀ ν, P.coeff ν ∈ Polynomial.degreeLT K p) : toRat K σ P ∈ coeffSpan K σ (p - 1) := by
  intro ν
  rw [toRat_apply, MvPolynomial.coeff_map]
  refine algebraMap_mem_zSpan fun a ha => ?_
  have hd := Polynomial.mem_degreeLT.1 (hP ν)
  have := (Polynomial.degree_lt_iff_coeff_zero _ _).1 hd a
  rw [Polynomial.mem_support_iff] at ha
  by_contra hcon
  exact ha (this (by exact_mod_cast Nat.le_of_lt_succ (by omega)))

/-- The truncation really does have coefficients of degree `< p`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem coeff_truncMv_mem_degreeLT (p : ℕ) (E : MvPolynomial σ (PowerSeries K)) (ν : σ →₀ ℕ) :
    (truncMv K σ p E).coeff ν ∈ Polynomial.degreeLT K p := by
  rw [coeff_truncMv, Polynomial.mem_degreeLT]
  refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [PowerSeries.coeff_trunc, if_neg]
  exact_mod_cast Nat.not_lt.2 (by exact_mod_cast hm)

/-- The truncation lands in `K[Y,z]_{·,p-1}`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem toRat_truncMv_mem_coeffSpan (p : ℕ) (E : MvPolynomial σ (PowerSeries K)) :
    toRat K σ (truncMv K σ p E) ∈ coeffSpan K σ (p - 1) :=
  toRat_mem_coeffSpan (coeff_truncMv_mem_degreeLT p E)

/-- The inclusion `K[Y,z] ↪ K⟦z⟧[Y]`, as a `K`-algebra map. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def toPS (K : Type*) [Field K] (σ : Type*) :
    MvPolynomial σ K[X] →ₐ[K] MvPolynomial σ (PowerSeries K) :=
  MvPolynomial.mapAlgHom (Polynomial.coeToPowerSeries.algHom K)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem totalDegree_toPS_le (P : MvPolynomial σ K[X]) :
    (toPS K σ P).totalDegree ≤ P.totalDegree := by
  classical
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)

end AfMap

/-! ## [AF22] Lemma 2.12, the dimension count -/

section Lemma212

/-- **The pigeonhole of Step (AF)**: a linear map out of a space of dimension larger than that of
its range kills a non-zero vector.  This is the *only* thing [AF22] need where the classical
Mahler method uses Siegel's lemma. -/
@[category API, AMS 15, ref "AF22", group "af_mahler_alternative"]
theorem exists_ne_zero_mem_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] (L : V →ₗ[K] W)
    (h : Module.finrank K ↥(LinearMap.range L) < Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 := by
  have hrk : Module.finrank K ↥(LinearMap.range L) + Module.finrank K ↥(LinearMap.ker L) =
      Module.finrank K V := by exact LinearMap.finrank_range_add_finrank_ker L
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hrk
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, hv⟩

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (I : Ideal (MvPolynomial (ι × ι) (RatFunc K))) (M : Matrix ι ι K)
variable (F : MvPolynomial (ι × ι) (PowerSeries K)) (δ₁ δ₂ p : ℕ)

/-- One term `P_j ↦ (P_j F^j)_p mod 𝓘` of the map of Step (AF). -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def afTerm (j : ℕ) :
    ↥(relComplP I δ₁ δ₂) →ₗ[K] (MvPolynomial (ι × ι) (RatFunc K) ⧸ I) :=
  (relQuot I).comp
    (((toRat K (ι × ι)).toLinearMap.comp
        (AlgHom.restrictScalars K (subMat K[X] M)).toLinearMap).comp
      ((truncMv K (ι × ι) p).comp
        ((LinearMap.mulRight K (F ^ j)).comp
          ((toPS K (ι × ι)).toLinearMap.comp (relComplP I δ₁ δ₂).subtype))))

@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem afTerm_apply (j : ℕ) (P : ↥(relComplP I δ₁ δ₂)) :
    afTerm I M F δ₁ δ₂ p j P =
      relQuot I (toRat K (ι × ι) (subMat K[X] M
        (truncMv K (ι × ι) p (toPS K (ι × ι) (P : MvPolynomial (ι × ι) K[X]) * F ^ j)))) := rfl

/-- **The map of [AF22] Step (AF)**: `(P₀,…,P_{δ₁}) ↦ E_p mod 𝓘`, where `E = ∑_j P_j F^j`. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def afMap :
    (Fin (δ₁ + 1) → ↥(relComplP I δ₁ δ₂)) →ₗ[K] (MvPolynomial (ι × ι) (RatFunc K) ⧸ I) :=
  ∑ j : Fin (δ₁ + 1), (afTerm I M F δ₁ δ₂ p (j : ℕ)).comp (LinearMap.proj j)

@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem afMap_apply (P : Fin (δ₁ + 1) → ↥(relComplP I δ₁ δ₂)) :
    afMap I M F δ₁ δ₂ p P =
      relQuot I (toRat K (ι × ι) (subMat K[X] M (truncMv K (ι × ι) p
        (∑ j : Fin (δ₁ + 1), toPS K (ι × ι) (P j : MvPolynomial (ι × ι) K[X]) * F ^ (j : ℕ))))) := by
  rw [afMap]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    afTerm_apply, map_sum]

/-- The image of the map of Step (AF) lands in `K[Y,z]_{D,p-1}` modulo `𝓘`. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem range_afMap_le (hF : F.totalDegree ≤ 1) {D : ℕ}
    (hD : Fintype.card (ι × ι) * δ₁ + δ₁ ≤ D) :
    LinearMap.range (afMap I M F δ₁ δ₂ p) ≤ relImage I D (p - 1) := by
  classical
  rintro _ ⟨P, rfl⟩
  rw [afMap_apply]
  refine ⟨_, ?_, rfl⟩
  refine mem_bidegPiece_of_totalDegree ?_ ?_
  · -- the total degree in `Y`
    refine le_trans (totalDegree_toRat_le _) ?_
    refine le_trans (totalDegree_subMat_le K[X] M _) ?_
    refine le_trans (totalDegree_truncMv_le _ _) ?_
    refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1 : (toPS K (ι × ι) (P j : MvPolynomial (ι × ι) K[X])).totalDegree ≤
        Fintype.card (ι × ι) * δ₁ :=
      le_trans (totalDegree_toPS_le _) (totalDegree_le_of_mem_bidegP (P j).2.2)
    have h2 : (F ^ (j : ℕ)).totalDegree ≤ δ₁ := by
      refine le_trans (MvPolynomial.totalDegree_pow F (j : ℕ)) ?_
      have : (j : ℕ) ≤ δ₁ := Nat.lt_succ_iff.1 j.2
      nlinarith [F.totalDegree.zero_le]
    omega
  · -- the degree in `z`
    exact toRat_mem_coeffSpan fun ν =>
      coeff_subMat_mem M (Polynomial.degreeLT K p)
        (fun μ => coeff_truncMv_mem_degreeLT p _ μ) ν

/-- **[AF22] Lemma 2.12 — Step (AF), the auxiliary function.**  *«Let `δ₁ ≥ 0` and `δ₂ ≫ δ₁`.
Then there exist polynomials `P_i ∈ 𝓘^⊥(δ₁,δ₂)`, `0 ≤ i ≤ δ₁`, not all zero, such that the formal
power series `E := ∑_j P_j F^j` satisfies `E_p(Θ_k(z), z^{q^{k-k₀}}) = 0` for all `k ≥ k₀`.»*

The conclusion is stated as `E_p(MY,z) ∈ 𝓘`, which is what [AF22]'s `(2.11)` turns into the
displayed vanishing once Lemma 2.7 is applied — see `CITED/AdamczewskiFaverjonRelationMatrix`.

No Siegel lemma: the whole content is that a `K`-linear map out of a space of dimension
`(δ₁+1)d(δ₁,δ₂)` into one of dimension `d(D,p-1)` has a non-trivial kernel. -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem exists_auxiliary (hF : F.totalDegree ≤ 1) {D : ℕ}
    (hD : Fintype.card (ι × ι) * δ₁ + δ₁ ≤ D)
    (hdim : relDim I D (p - 1) < (δ₁ + 1) * relDim I δ₁ δ₂) :
    ∃ P : Fin (δ₁ + 1) → ↥(relComplP I δ₁ δ₂), P ≠ 0 ∧
      toRat K (ι × ι) (subMat K[X] M (truncMv K (ι × ι) p
        (∑ j : Fin (δ₁ + 1),
          toPS K (ι × ι) (P j : MvPolynomial (ι × ι) K[X]) * F ^ (j : ℕ)))) ∈ I := by
  classical
  set L := afMap I M F δ₁ δ₂ p with hL
  have hfr : Module.finrank K ↥(LinearMap.range L) ≤ relDim I D (p - 1) := by
    rw [relDim_eq_finrank_relImage]
    exact Submodule.finrank_mono (range_afMap_le I M F δ₁ δ₂ p hF hD)
  haveI hfree : ∀ _ : Fin (δ₁ + 1), Module.Free K ↥(relComplP I δ₁ δ₂) := fun _ => inferInstance
  have hpi := Module.finrank_pi_fintype (R := K) (ι := Fin (δ₁ + 1))
    (M := fun _ : Fin (δ₁ + 1) => ↥(relComplP I δ₁ δ₂))
  have hsrc : Module.finrank K (Fin (δ₁ + 1) → ↥(relComplP I δ₁ δ₂)) =
      (δ₁ + 1) * relDim I δ₁ δ₂ := by
    rw [hpi, finrank_relComplP]
    simp [Finset.sum_const, Finset.card_univ]
  obtain ⟨P, hP0, hPmem⟩ :
      ∃ v : Fin (δ₁ + 1) → ↥(relComplP I δ₁ δ₂), v ≠ 0 ∧ L v = 0 := by
    refine exists_ne_zero_mem_ker (V := Fin (δ₁ + 1) → ↥(relComplP I δ₁ δ₂)) L ?_
    rw [hsrc]
    omega
  refine ⟨P, hP0, ?_⟩
  have : L P = 0 := hPmem
  rw [hL, afMap_apply] at this
  rwa [relQuot_apply, Ideal.Quotient.eq_zero_iff_mem] at this

end Lemma212

/-! ## [AF22] Step (NV): the auxiliary function does not vanish identically -/

section StepNV

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (I : Ideal (MvPolynomial σ (RatFunc K)))

/-- A non-zero element of the complement `𝓘^⊥(δ₁,δ₂)` is not a relation.  This is what makes the
first non-zero `P_{v₀}` of Lemma 2.12 usable in Step (NV). -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem toRat_notMem_of_mem_relComplP {δ₁ δ₂ : ℕ} {P : MvPolynomial σ K[X]}
    (hP : P ∈ relComplP I δ₁ δ₂) (hP0 : P ≠ 0) : toRat K σ P ∉ I := by
  intro hmem
  have h1 : toRat K σ P ∈ relPiece I δ₁ δ₂ :=
    ⟨hmem, relCompl_le_bidegPiece I δ₁ δ₂ hP.1⟩
  have h2 : toRat K σ P ∈ relCompl I δ₁ δ₂ := hP.1
  have h3 : toRat K σ P ∈ relPiece I δ₁ δ₂ ⊓ relCompl I δ₁ δ₂ := ⟨h1, h2⟩
  rw [relPiece_inf_relCompl] at h3
  exact hP0 (injective_toRat (by simpa using h3))

/-- **[AF22] Step (NV).**  *«There exists an infinite set `𝓔` of positive integers such that
`P_{v₀}(A_k(α), α^{q^k}) ≠ 0` for all `k ∈ 𝓔`.»*

A polynomial that is not a relation fails to vanish at the iterates **frequently** — which is the
`Filter`-theoretic form of «for infinitely many `k`», and is exactly the negation of the
germ-theoretic definition of the relation ideal. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem frequently_evalAt_ne_zero {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → σ → K)
    {P : MvPolynomial σ K[X]} (hP : toRat K σ P ∉ relationIdeal hpt Yval) :
    ∃ᶠ n in atTop, evalAt pt Yval n P ≠ 0 := by
  rw [toRat_apply, mem_relationIdeal_map_iff] at hP
  exact Filter.not_eventually.1 hP

end StepNV

end AF
