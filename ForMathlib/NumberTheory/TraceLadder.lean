/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

@[expose] public section

/-!
# Trace ladders: the integer solutions of the minimal-polynomial recurrence

Let `α` be an algebraic integer generating a number field `L` over `ℚ`, with minimal polynomial
`f = X^d + c₁X^{d-1} + ⋯ + c_d ∈ ℤ[X]`.  Two `ℤ`-modules are attached to it:

* `recModule f`, the module `𝓡` of **integer sequences obeying `α`'s recurrence**,
  `h_{k+d} + c₁h_{k+d-1} + ⋯ + c_d h_k = 0`;
* `codiff α`, the **codifferent** `𝔡⁻¹ = {γ ∈ L : Tr(γ · ℤ[α]) ⊆ ℤ}`, the `ℤ`-dual of `ℤ[α]`
  under the trace form.

`isRecSeq_iff_exists_codiff` identifies them: the integer solutions are **exactly** the
*trace ladders* `h_k = Tr_{L/ℚ}(λ αᵏ)` with `λ` in the codifferent, and `codiffEquivRec` bundles
that as a `ℤ`-module isomorphism `𝔡⁻¹ ≅ 𝓡`.  `recEquivInit` adds `𝓡 ≅ ℤ^d`, a solution being
free on its first `d` terms.

Three separate facts are involved and are proved separately, because they need different
inputs:

* **the recurrence** (`isRecSeq_ladder`) holds for *every* `λ ∈ L`, integrality nowhere in
  sight: `∑ᵢ fᵢ αⁱ = f(α) = 0`, and the trace is `ℚ`-linear.  No conjugates are needed —
  the usual proof, "each `α_jᵏ` obeys it", is a detour through a splitting field.
* **integrality** (`mem_codiff_iff`) is where the codifferent enters, and it is a tautology
  once one knows `ℤ[α]` is spanned by the powers of `α`: `Tr(λ αᵏ) ∈ ℤ` for all `k` *is*
  `Tr(λ ℤ[α]) ⊆ ℤ`.  The recurrence then propagates integrality forward from the first `d`
  terms, since `f` is monic (`IsRecSeq.mem_of_init_mem`).
* **surjectivity** (`exists_ladder_eq_init`) is the nondegeneracy of the trace form: `λ ↦
  (Tr(λ αⁱ))_{i<d}` is an injective `ℚ`-linear map between two `d`-dimensional spaces.

`codiff_eq_smul_adjoin` records **Euler's identity** `𝔡⁻¹ = f'(α)⁻¹ ℤ[α]` in this notation;
it is Mathlib's `traceForm_dualSubmodule_adjoin` and needs nothing from this file.

## Main results

* `isRecSeq_ladder` — a trace ladder obeys `α`'s recurrence, for every `λ`;
* `mem_codiff_iff` — `λ ∈ 𝔡⁻¹` iff its whole trace ladder is integral;
* `isRecSeq_iff_exists_codiff` — `𝓡 = {(Tr(λ αᵏ))_k : λ ∈ 𝔡⁻¹}`;
* `codiffEquivRec`, `recEquivInit` — `𝔡⁻¹ ≃ₗ[ℤ] 𝓡 ≃ₗ[ℤ] ℤ^d`;
* `codiff_eq_smul_adjoin` — Euler: `𝔡⁻¹ = f'(α)⁻¹ ℤ[α]`.

## Implementation notes

`IsRecSeq` is stated for sequences in an arbitrary additive group, so that the `ℤ`-valued and
`ℚ`-valued forms of the recurrence are the same definition; `IsRecSeq.map` and
`IsRecSeq.of_map` move between them along `ℤ ↪ ℚ`.  The integer sequence underlying an
integer-valued rational sequence is extracted canonically by `numSeq u k = (u k).num`, so no
choice is involved anywhere.
-/

open Polynomial Algebra Pointwise

namespace TraceLadder

/-! ## Linear recurrences with integer coefficients -/

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {f : ℤ[X]} {u v : ℕ → M}

/-- `u` obeys the linear recurrence whose characteristic polynomial is `f`:
`∑_{i ≤ deg f} f_i · u_{k+i} = 0` for every `k`.  For `f` monic of degree `d` this is
`u_{k+d} + c₁ u_{k+d-1} + ⋯ + c_d u_k = 0` with `f = X^d + c₁X^{d-1} + ⋯ + c_d`. -/
def IsRecSeq (f : ℤ[X]) (u : ℕ → M) : Prop :=
  ∀ k, ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i • u (k + i) = 0

theorem isRecSeq_zero : IsRecSeq f (fun _ : ℕ => (0 : M)) := by
  intro k; simp

theorem IsRecSeq.tail_eq (hf : f.Monic) (hu : IsRecSeq f u) (k : ℕ) :
    u (k + f.natDegree) = -∑ i ∈ Finset.range f.natDegree, f.coeff i • u (k + i) := by
  have h := hu k
  rw [Finset.sum_range_succ, hf.coeff_natDegree, one_smul] at h
  have h2 : u (k + f.natDegree) + ∑ i ∈ Finset.range f.natDegree, f.coeff i • u (k + i) = 0 := by
    rw [add_comm]; exact h
  exact eq_neg_of_add_eq_zero_left h2

/-- A solution of a monic recurrence is determined by its first `deg f` terms. -/
theorem IsRecSeq.ext (hf : f.Monic) (hu : IsRecSeq f u) (hv : IsRecSeq f v)
    (h : ∀ i < f.natDegree, u i = v i) : u = v := by
  funext k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k f.natDegree with hk | hk
    · exact h k hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + f.natDegree := ⟨k - f.natDegree, by omega⟩
      rw [hu.tail_eq hf, hv.tail_eq hf]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ih (j + i) (by simp only [Finset.mem_range] at hi; omega)]

/-- A monic recurrence keeps its solutions inside any `ℤ`-submodule containing the first
`deg f` terms — this is how integrality propagates along a ladder. -/
theorem IsRecSeq.mem_of_init_mem (hf : f.Monic) (hu : IsRecSeq f u) (P : Submodule ℤ M)
    (h : ∀ i < f.natDegree, u i ∈ P) (k : ℕ) : u k ∈ P := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k f.natDegree with hk | hk
    · exact h k hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + f.natDegree := ⟨k - f.natDegree, by omega⟩
      rw [hu.tail_eq hf]
      refine neg_mem (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
      exact ih (j + i) (by simp only [Finset.mem_range] at hi; omega)

theorem IsRecSeq.map (g : M →+ N) (hu : IsRecSeq f u) : IsRecSeq f (fun k => g (u k)) := by
  intro k
  rw [← map_zero g, ← hu k, map_sum]
  exact Finset.sum_congr rfl fun i _ => (map_zsmul g _ _).symm

theorem IsRecSeq.of_map {g : M →+ N} (hg : Function.Injective g)
    (h : IsRecSeq f (fun k => g (u k))) : IsRecSeq f u := by
  intro k
  refine hg ?_
  rw [map_zero, ← h k, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_zsmul g _ _

/-- `𝓡`: the `ℤ`-module of **integer** solutions of the recurrence. -/
def recModule (f : ℤ[X]) : Submodule ℤ (ℕ → ℤ) where
  carrier := {u | IsRecSeq f u}
  add_mem' {u v} hu hv k := by
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, hu k, hv k, add_zero]
  zero_mem' k := by simp
  smul_mem' c u hu k := by
    have hsc : ∀ i : ℕ, f.coeff i • (c • u (k + i)) = c • (f.coeff i • u (k + i)) :=
      fun i => smul_comm _ _ _
    simp only [Pi.smul_apply, hsc, ← Finset.smul_sum, hu k, smul_zero]

@[simp]
theorem mem_recModule {u : ℕ → ℤ} : u ∈ recModule f ↔ IsRecSeq f u := Iff.rfl

/-! ## The trace ladder of an algebraic integer -/

variable {L : Type*} [Field L] [NumberField L]

/-- The **trace ladder** attached to `λ`: the sequence `h_k = Tr_{L/ℚ}(λ αᵏ)`. -/
noncomputable def ladder (α lam : L) (k : ℕ) : ℚ := Algebra.trace ℚ L (lam * α ^ k)

/-- `λ ↦ (Tr(λ αᵏ))_{k ≥ 0}`, as a `ℚ`-linear map. -/
noncomputable def ladderMap (α : L) : L →ₗ[ℚ] (ℕ → ℚ) where
  toFun := ladder α
  map_add' lam mu := by funext k; simp [ladder, add_mul]
  map_smul' c lam := by funext k; simp [ladder]

@[simp]
theorem ladderMap_apply (α lam : L) (k : ℕ) : ladderMap α lam k = ladder α lam k := rfl

/-- `Tr(λ · p(α))` read off the coefficients of `p`: the only computation this file makes. -/
theorem trace_mul_aeval {R : Type*} [CommRing R] [Algebra R ℚ] [Algebra R L]
    [IsScalarTower R ℚ L] (α lam : L) (p : R[X]) :
    Algebra.trace ℚ L (lam * aeval α p)
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • ladder α lam i := by
  rw [aeval_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, ← IsScalarTower.algebraMap_smul (R := R) ℚ (p.coeff i), map_smul,
    IsScalarTower.algebraMap_smul, ladder]

variable {α : L}

/-- **The trace ladder obeys `α`'s recurrence**, for *every* `λ` — no integrality involved,
neither of `λ` nor of `α`: `∑ᵢ fᵢ αⁱ = f(α) = 0`, and the trace is linear.  (For `α` not
integral over `ℤ` the statement is vacuous, `minpoly ℤ α` being `0` there.) -/
theorem isRecSeq_ladder (lam : L) :
    IsRecSeq (minpoly ℤ α) (ladder α lam) := by
  intro k
  have key : ∑ i ∈ Finset.range ((minpoly ℤ α).natDegree + 1),
      (minpoly ℤ α).coeff i • (lam * α ^ k * α ^ i) = lam * α ^ k * aeval α (minpoly ℤ α) := by
    rw [aeval_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_smul_comm _ _ _).symm
  calc ∑ i ∈ Finset.range ((minpoly ℤ α).natDegree + 1),
        (minpoly ℤ α).coeff i • ladder α lam (k + i)
      = Algebra.trace ℚ L (∑ i ∈ Finset.range ((minpoly ℤ α).natDegree + 1),
          (minpoly ℤ α).coeff i • (lam * α ^ k * α ^ i)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul]
        congr 1
        rw [ladder, pow_add, ← mul_assoc]
    _ = 0 := by rw [key, minpoly.aeval ℤ α, mul_zero, map_zero]

/-! ## The codifferent -/

/-- The **codifferent** `𝔡⁻¹ = {γ ∈ L : Tr(γ · ℤ[α]) ⊆ ℤ}`, the `ℤ`-dual of `ℤ[α]` under the
trace form. -/
noncomputable def codiff (α : L) : Submodule ℤ L :=
  (Algebra.traceForm ℚ L).dualSubmodule
    (Subalgebra.toSubmodule (Algebra.adjoin ℤ ({α} : Set L)))

/-- `γ` lies in the codifferent exactly when its whole trace ladder is integral: `ℤ[α]` is
spanned by the powers of `α`. -/
theorem mem_codiff_iff {lam : L} :
    lam ∈ codiff α ↔ ∀ k, ladder α lam k ∈ (1 : Submodule ℤ ℚ) := by
  rw [codiff, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro h k
    have hmem : α ^ k ∈ Subalgebra.toSubmodule (Algebra.adjoin ℤ ({α} : Set L)) := by
      rw [Subalgebra.mem_toSubmodule]
      exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton α)) k
    have hk := h _ hmem
    rwa [Algebra.traceForm_apply] at hk
  · intro h y hy
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    have hp : (aeval α).toRingHom p = aeval α p := rfl
    rw [Algebra.traceForm_apply, hp, trace_mul_aeval]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)

/-- **Euler's identity**: the codifferent of `ℤ[α]` is `f'(α)⁻¹ ℤ[α]`.  This is Mathlib's
`traceForm_dualSubmodule_adjoin`, recorded here in the notation of this file. -/
theorem codiff_eq_smul_adjoin (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) :
    codiff α = (aeval α (derivative (minpoly ℚ α)))⁻¹ •
      Subalgebra.toSubmodule (Algebra.adjoin ℤ ({α} : Set L)) :=
  traceForm_dualSubmodule_adjoin ℤ ℚ hgen hint

/-! ## The ladder determines `λ`, and every initial datum occurs -/

/-- `λ ↦ (Tr(λ αᵏ))` is injective: the trace form is nondegenerate and the powers of `α`
span `L`. -/
theorem ladderMap_injective (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤) :
    Function.Injective (ladderMap α) := by
  rw [injective_iff_map_eq_zero]
  intro lam hlam
  refine (traceForm_nondegenerate ℚ L).1 lam fun y => ?_
  have hy : y ∈ Algebra.adjoin ℚ ({α} : Set L) := hgen ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := hy
  have hp : (aeval α).toRingHom p = aeval α p := rfl
  rw [Algebra.traceForm_apply, hp, trace_mul_aeval]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show ladder α lam i = ladderMap α lam i from rfl, hlam]
  simp

/-! ## Prescribing the first `d` terms -/

/-- `[L : ℚ]` is the degree of `α`'s minimal polynomial over `ℤ`. -/
theorem finrank_eq_natDegree (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤) (hint : IsIntegral ℤ α) :
    Module.finrank ℚ L = (minpoly ℤ α).natDegree := by
  have hKα : IsIntegral ℚ α := hint.tower_top
  let pb : PowerBasis ℚ L :=
    (Algebra.adjoin.powerBasis hKα).map
      ((Subalgebra.equivOfEq _ _ hgen).trans Subalgebra.topEquiv)
  have h1 : Module.finrank ℚ L = pb.dim := pb.finrank
  have h2 : pb.dim = (minpoly ℚ α).natDegree := rfl
  rw [h1, h2, minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) hint,
    (minpoly.monic hint).natDegree_map]

/-- **Every initial datum occurs**: `λ ↦ (Tr(λ αⁱ))_{i < d}` is onto `ℚ^d`.  The map is
injective by `ladderMap_injective` together with `IsRecSeq.ext`, and both sides have
dimension `d`. -/
theorem exists_ladder_eq_init (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤) (hint : IsIntegral ℤ α)
    (v : Fin (minpoly ℤ α).natDegree → ℚ) :
    ∃ lam : L, ∀ i : Fin (minpoly ℤ α).natDegree, ladder α lam (i : ℕ) = v i := by
  let Φ : L →ₗ[ℚ] (Fin (minpoly ℤ α).natDegree → ℚ) :=
    { toFun := fun lam i => ladder α lam (i : ℕ)
      map_add' := fun lam mu => by funext i; simp [ladder, add_mul]
      map_smul' := fun c lam => by funext i; simp [ladder] }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro lam hlam
    refine ladderMap_injective hgen ?_
    have hz : ladder α lam = fun _ : ℕ => (0 : ℚ) := by
      refine (isRecSeq_ladder lam).ext (minpoly.monic hint) isRecSeq_zero fun i hi => ?_
      exact congrFun hlam ⟨i, hi⟩
    show ladder α lam = ladder α 0
    rw [hz]
    funext k
    simp [ladder]
  have hdim : Module.finrank ℚ L = Module.finrank ℚ (Fin (minpoly ℤ α).natDegree → ℚ) := by
    rw [finrank_eq_natDegree hgen hint, Module.finrank_fin_fun]
  obtain ⟨lam, hlam⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj v
  exact ⟨lam, fun i => congrFun hlam i⟩

/-! ## Proposition 15 -/

/-- **The integer solutions of `α`'s recurrence are exactly the trace ladders over the
codifferent.**  Forward: match the first `d` terms by `exists_ladder_eq_init`, then the two
sequences obey the same monic recurrence, so they agree everywhere; integrality of the ladder
then *is* membership in the codifferent.  Backward: the trace ladder obeys the recurrence for
every `λ`. -/
theorem isRecSeq_iff_exists_codiff (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) (h : ℕ → ℤ) :
    IsRecSeq (minpoly ℤ α) h ↔ ∃ lam ∈ codiff α, ∀ k, ladder α lam k = (h k : ℚ) := by
  constructor
  · intro hh
    obtain ⟨lam, hlam⟩ := exists_ladder_eq_init hgen hint fun i => ((h (i : ℕ) : ℤ) : ℚ)
    have hq : IsRecSeq (minpoly ℤ α) (fun k => ((h k : ℤ) : ℚ)) := hh.map (Int.castAddHom ℚ)
    have heq : ladder α lam = fun k => ((h k : ℤ) : ℚ) :=
      (isRecSeq_ladder lam).ext (minpoly.monic hint) hq fun i hi => hlam ⟨i, hi⟩
    refine ⟨lam, mem_codiff_iff.mpr fun k => ?_, fun k => congrFun heq k⟩
    rw [congrFun heq k]
    exact Submodule.mem_one.mpr ⟨h k, by simp⟩
  · rintro ⟨lam, _, heq⟩
    refine IsRecSeq.of_map (g := Int.castAddHom ℚ) Int.cast_injective ?_
    have hr := isRecSeq_ladder (α := α) lam
    rwa [funext heq] at hr

/-! ## The `ℤ`-module isomorphisms `𝔡⁻¹ ≃ 𝓡 ≃ ℤ^d` -/

/-- The integer sequence underlying an integer-valued rational sequence.  Canonical, so no
choice is involved: an integer-valued rational is its own numerator. -/
def numSeq (u : ℕ → ℚ) : ℕ → ℤ := fun k => (u k).num

theorem cast_numSeq {u : ℕ → ℚ} (hu : ∀ k, u k ∈ (1 : Submodule ℤ ℚ)) (k : ℕ) :
    ((numSeq u k : ℤ) : ℚ) = u k := by
  obtain ⟨m, hm⟩ := Submodule.mem_one.mp (hu k)
  rw [numSeq, ← hm]
  simp

theorem numSeq_eq_of_cast {u : ℕ → ℚ} {h : ℕ → ℤ} (hu : ∀ k, u k = (h k : ℚ)) :
    numSeq u = h := by
  funext k
  rw [numSeq, hu k]
  simp

theorem numSeq_add {u v : ℕ → ℚ} (hu : ∀ k, u k ∈ (1 : Submodule ℤ ℚ))
    (hv : ∀ k, v k ∈ (1 : Submodule ℤ ℚ)) : numSeq (u + v) = numSeq u + numSeq v := by
  refine numSeq_eq_of_cast fun k => ?_
  simp only [Pi.add_apply]
  push_cast
  rw [cast_numSeq hu k, cast_numSeq hv k]

theorem numSeq_zsmul {u : ℕ → ℚ} (hu : ∀ k, u k ∈ (1 : Submodule ℤ ℚ)) (c : ℤ) :
    numSeq (c • u) = c • numSeq u := by
  refine numSeq_eq_of_cast fun k => ?_
  simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
  push_cast
  rw [cast_numSeq hu k]

theorem ladder_add (α lam mu : L) : ladder α (lam + mu) = ladder α lam + ladder α mu :=
  (ladderMap α).map_add lam mu

/-- `λ ↦ (Tr(λ αᵏ))_k`, from the codifferent to the integer solutions. -/
noncomputable def codiffToRec : codiff α →ₗ[ℤ] recModule (minpoly ℤ α) where
  toFun lam := ⟨numSeq (ladder α lam.1), by
    refine IsRecSeq.of_map (g := Int.castAddHom ℚ) Int.cast_injective ?_
    have hc : (fun k => (Int.castAddHom ℚ) (numSeq (ladder α lam.1) k)) = ladder α lam.1 :=
      funext fun k => cast_numSeq (mem_codiff_iff.mp lam.2) k
    rw [hc]
    exact isRecSeq_ladder lam.1⟩
  map_add' lam mu := by
    refine Subtype.ext ?_
    show numSeq (ladder α ((lam : L) + (mu : L)))
        = numSeq (ladder α lam.1) + numSeq (ladder α mu.1)
    rw [ladder_add]
    exact numSeq_add (mem_codiff_iff.mp lam.2) (mem_codiff_iff.mp mu.2)
  map_smul' c lam := by
    refine Subtype.ext ?_
    show numSeq (ladder α (c • (lam : L))) = c • numSeq (ladder α lam.1)
    rw [show ladder α (c • (lam : L)) = c • ladder α lam.1 from map_zsmul (ladderMap α) c lam.1]
    exact numSeq_zsmul (mem_codiff_iff.mp lam.2) c

theorem codiffToRec_bijective (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) : Function.Bijective (codiffToRec (α := α)) := by
  constructor
  · intro lam mu hlm
    refine Subtype.ext (ladderMap_injective hgen (funext fun k => ?_))
    have h1 := cast_numSeq (mem_codiff_iff.mp lam.2) k
    have h2 := cast_numSeq (mem_codiff_iff.mp mu.2) k
    have hk : numSeq (ladder α lam.1) k = numSeq (ladder α mu.1) k :=
      congrFun (congrArg Subtype.val hlm) k
    show ladder α lam.1 k = ladder α mu.1 k
    rw [← h1, ← h2, hk]
  · rintro ⟨h, hh⟩
    obtain ⟨lam, hlam, heq⟩ := (isRecSeq_iff_exists_codiff hgen hint h).mp hh
    refine ⟨⟨lam, hlam⟩, Subtype.ext ?_⟩
    show numSeq (ladder α lam) = h
    exact numSeq_eq_of_cast heq

/-- **Proposition 15, first isomorphism**: `λ ↦ (Tr(λ αᵏ))` is a `ℤ`-module isomorphism from
the codifferent onto the integer solutions of `α`'s recurrence. -/
noncomputable def codiffEquivRec (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) : codiff α ≃ₗ[ℤ] recModule (minpoly ℤ α) :=
  LinearEquiv.ofBijective (codiffToRec (α := α)) (codiffToRec_bijective hgen hint)

/-- Reading off the first `deg f` terms of a solution. -/
def recToInit (f : ℤ[X]) : recModule f →ₗ[ℤ] (Fin f.natDegree → ℤ) where
  toFun u i := u.1 (i : ℕ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem recToInit_bijective (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) : Function.Bijective (recToInit (minpoly ℤ α)) := by
  constructor
  · intro u v huv
    refine Subtype.ext ((mem_recModule.mp u.2).ext (minpoly.monic hint)
      (mem_recModule.mp v.2) fun i hi => ?_)
    exact congrFun huv ⟨i, hi⟩
  · intro v
    obtain ⟨lam, hlam⟩ := exists_ladder_eq_init hgen hint fun i => ((v i : ℤ) : ℚ)
    have hcodiff : lam ∈ codiff α := by
      refine mem_codiff_iff.mpr fun k => ?_
      refine (isRecSeq_ladder lam).mem_of_init_mem (minpoly.monic hint) _ ?_ k
      intro i hi
      rw [hlam ⟨i, hi⟩]
      exact Submodule.mem_one.mpr ⟨v ⟨i, hi⟩, by simp⟩
    have hc := cast_numSeq (mem_codiff_iff.mp hcodiff)
    refine ⟨⟨numSeq (ladder α lam), ?_⟩, ?_⟩
    · refine IsRecSeq.of_map (g := Int.castAddHom ℚ) Int.cast_injective ?_
      have hc' : (fun k => (Int.castAddHom ℚ) (numSeq (ladder α lam) k)) = ladder α lam :=
        funext hc
      rw [hc']
      exact isRecSeq_ladder lam
    · funext i
      show numSeq (ladder α lam) (i : ℕ) = v i
      have hi := hc (i : ℕ)
      rw [hlam i] at hi
      exact_mod_cast hi

/-- **Proposition 15, second isomorphism**: an integer solution is determined by, and
determines, its first `d` terms — so `𝓡 ≅ ℤ^d`. -/
noncomputable def recEquivInit (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) :
    recModule (minpoly ℤ α) ≃ₗ[ℤ] (Fin (minpoly ℤ α).natDegree → ℤ) :=
  LinearEquiv.ofBijective (recToInit (minpoly ℤ α)) (recToInit_bijective hgen hint)

end TraceLadder
