/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Power sums of the conjugates of an algebraic integer

For a real algebraic integer `θ` and every `n`, the sum `∑ βⁿ` over the roots `β ∈ ℂ` of the
minimal polynomial of `θ` over `ℚ` — i.e. the `n`-th power sum of the conjugates of `θ` — is a
*rational integer*.  It equals the field trace `Tr_{ℚ(θ)/ℚ}(θⁿ)`, and the trace of an algebraic
integer is again an algebraic integer, hence (living in `ℚ`) an ordinary integer.

This is the elementary trace input to the study of the fractional parts of powers of Pisot and Salem
numbers: writing `θⁿ` as (an integer) minus the sum of the non-dominant conjugate powers reduces the
distribution of `(θⁿ)` modulo one to that of the oscillatory conjugate sum.

## Main results

* `conj_powerSum_isInt` — the `n`-th power sum of the conjugates of an algebraic integer is a
  rational integer;
* `conj_shiftedPowerSum_isInt` — so is `∑_β (β-1)βᵐ = Tr((θ-1)θᵐ)`, the difference of two
  consecutive power sums;
* `self_mem_aroots_minpoly`, `nodup_aroots_minpoly`, `conj_erase_sum_add` — `θ` occurs exactly
  once among its conjugates, and a conjugate sum splits as (dominant term) + (the rest);
* `exists_int_sub_le_of_conj` — the quantitative consequence: if the full conjugate sum of `f`
  is a rational integer and `‖f z‖ ≤ B` at every non-dominant conjugate, then `f θ` is within
  `(d-1)B` of a rational integer.  At a Pisot number `B` decays geometrically; see
  `ForMathlib/NumberTheory/PisotFractionalParts.lean`.
-/

open Polynomial IntermediateField in
/-- **Power sum of the conjugates of an algebraic integer is a rational integer.** For an algebraic
integer `θ` and every `n`, the sum `∑ βⁿ` over the roots `β ∈ ℂ` of `minpoly ℚ θ` is a rational
integer.  With `K = ℚ(θ)` (a `PowerBasis`), `PowerBasis.liftEquiv` matches the embeddings
`σ : K →ₐ[ℚ] ℂ` with the (distinct, by separability) roots, so `∑ βⁿ = ∑_σ (σ θ)ⁿ =
algebraMap ℚ ℂ (Tr_{K/ℚ}(θⁿ))` (`trace_eq_sum_embeddings`); the trace of the algebraic integer `θⁿ`
is an algebraic integer in `ℚ` (`Algebra.isIntegral_trace`), hence in `ℤ`
(`IsIntegrallyClosed.isIntegral_iff`). -/
theorem conj_powerSum_isInt (θ : ℝ) (hθ : IsIntegral ℤ θ) (n : ℕ) :
    ∃ m : ℤ, (((minpoly ℚ θ).aroots ℂ).map (· ^ n)).sum = (m : ℂ) := by
  have hintℚ : IsIntegral ℚ θ := hθ.tower_top
  have hfd : FiniteDimensional ℚ ℚ⟮θ⟯ := adjoin.finiteDimensional hintℚ
  let pb : PowerBasis ℚ ℚ⟮θ⟯ := adjoin.powerBasis hintℚ
  have hgenθ : pb.gen = AdjoinSimple.gen ℚ θ := adjoin.powerBasis_gen hintℚ
  have hgenInt : IsIntegral ℤ pb.gen := by
    have hf : Function.Injective ((IntermediateField.val ℚ⟮θ⟯).restrictScalars ℤ) :=
      (IntermediateField.val ℚ⟮θ⟯).injective
    rw [← isIntegral_algHom_iff _ hf]
    have hv : (IntermediateField.val ℚ⟮θ⟯).restrictScalars ℤ pb.gen = θ := by rw [hgenθ]; rfl
    rw [hv]; exact hθ
  have htrInt : IsIntegral ℤ (Algebra.trace ℚ ℚ⟮θ⟯ (pb.gen ^ n)) :=
    Algebra.isIntegral_trace (hgenInt.pow n)
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrInt
  refine ⟨m, ?_⟩
  have hemb := trace_eq_sum_embeddings (K := ℚ) (L := ℚ⟮θ⟯) ℂ (x := pb.gen ^ n)
  have hbridge : ∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, (σ pb.gen) ^ n
      = (((minpoly ℚ θ).aroots ℂ).map (· ^ n)).sum := by
    have hgI : IsIntegral ℚ pb.gen := hgenInt.tower_top
    have hpne : minpoly ℚ pb.gen ≠ 0 := minpoly.ne_zero hgI
    have hsep : (minpoly ℚ pb.gen).Separable := (minpoly.irreducible hgI).separable
    have hnodup : ((minpoly ℚ pb.gen).aroots ℂ).Nodup := by
      rw [Polynomial.aroots]; exact Polynomial.nodup_roots hsep.map
    have hmp : minpoly ℚ pb.gen = minpoly ℚ θ := by rw [hgenθ]; exact minpoly_gen ℚ θ
    have : Fintype {y : ℂ // (aeval y) (minpoly ℚ pb.gen) = 0} := Fintype.ofEquiv _ pb.liftEquiv
    rw [Fintype.sum_equiv pb.liftEquiv (fun σ => (σ pb.gen) ^ n) (fun y => ((y : ℂ)) ^ n)
        (fun σ => by rw [pb.liftEquiv_apply_coe])]
    rw [← Finset.sum_subtype ((minpoly ℚ pb.gen).aroots ℂ).toFinset
        (fun x => by
          rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
          exact ⟨fun h => h.2, fun h => ⟨hpne, h⟩⟩)
        (fun y => y ^ n)]
    rw [hmp] at hnodup ⊢
    rw [Finset.sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  calc (((minpoly ℚ θ).aroots ℂ).map (· ^ n)).sum
      = ∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, (σ pb.gen) ^ n := hbridge.symm
    _ = ∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, σ (pb.gen ^ n) := by simp_rw [map_pow]
    _ = (algebraMap ℚ ℂ) (Algebra.trace ℚ ℚ⟮θ⟯ (pb.gen ^ n)) := hemb.symm
    _ = (algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) m) := by rw [hm]
    _ = (m : ℂ) := by rw [← IsScalarTower.algebraMap_apply]; simp

/-! ## Splitting off the dominant conjugate -/

open Polynomial in
/-- The conjugates of an algebraic integer are pairwise distinct: `minpoly ℚ θ` is irreducible
over a field of characteristic zero, hence separable, hence has no repeated root. -/
theorem nodup_aroots_minpoly (θ : ℝ) (hθ : IsIntegral ℤ θ) : ((minpoly ℚ θ).aroots ℂ).Nodup := by
  have hintℚ : IsIntegral ℚ θ := hθ.tower_top
  have hsep : (minpoly ℚ θ).Separable := (minpoly.irreducible hintℚ).separable
  rw [Polynomial.aroots]
  exact Polynomial.nodup_roots hsep.map

open Polynomial in
/-- `θ` is one of its own conjugates. -/
theorem self_mem_aroots_minpoly (θ : ℝ) (hθ : IsIntegral ℤ θ) :
    (θ : ℂ) ∈ (minpoly ℚ θ).aroots ℂ := by
  have hintℚ : IsIntegral ℚ θ := hθ.tower_top
  rw [Polynomial.mem_aroots]
  refine ⟨minpoly.ne_zero hintℚ, ?_⟩
  have h0 : (aeval θ) (minpoly ℚ θ) = 0 := minpoly.aeval ℚ θ
  have h1 : (aeval ((θ : ℝ) : ℂ)) (minpoly ℚ θ)
      = Complex.ofRealAm ((aeval θ) (minpoly ℚ θ)) :=
    Polynomial.aeval_algHom_apply (Complex.ofRealAm.restrictScalars ℚ) θ (minpoly ℚ θ)
  rw [h1, h0]
  simp

open Polynomial in
/-- **The trace ladder of `θ - 1` is integral.**  For an algebraic integer `θ` and every `m`,
`∑_β (β - 1)βᵐ = Tr((θ-1)θᵐ)` is a rational integer, being the difference `s_{m+1} - s_m` of two
power sums. -/
theorem conj_shiftedPowerSum_isInt (θ : ℝ) (hθ : IsIntegral ℤ θ) (m : ℕ) :
    ∃ T : ℤ, (((minpoly ℚ θ).aroots ℂ).map (fun z => (z - 1) * z ^ m)).sum = (T : ℂ) := by
  obtain ⟨a, ha⟩ := conj_powerSum_isInt θ hθ (m + 1)
  obtain ⟨b, hb⟩ := conj_powerSum_isInt θ hθ m
  refine ⟨a - b, ?_⟩
  have hfun : (fun z : ℂ => (z - 1) * z ^ m) = fun z : ℂ => z ^ (m + 1) - z ^ m := by
    funext z; ring
  rw [hfun, Multiset.sum_map_sub, ha, hb]
  push_cast; ring

open Polynomial in
/-- Splitting the dominant conjugate off a conjugate sum. -/
theorem conj_erase_sum_add (θ : ℝ) (hθ : IsIntegral ℤ θ) (f : ℂ → ℂ) :
    ((((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ)).map f).sum + f (θ : ℂ)
      = (((minpoly ℚ θ).aroots ℂ).map f).sum := by
  conv_rhs => rw [← Multiset.cons_erase (self_mem_aroots_minpoly θ hθ)]
  rw [Multiset.map_cons, Multiset.sum_cons]
  ring

open Polynomial in
/-- **The distance from `f θ` to `ℤ`, from the conjugate sum.**  If the full conjugate sum of `f`
is the rational integer `T`, `f θ` is the real number `r`, and every *non-dominant* conjugate
satisfies `‖f z‖ ≤ B`, then `r` is within `(number of non-dominant conjugates) · B` of `T`.

Applied to `f z = zᵐ` and `f z = (z-1)zᵐ` at a Pisot number, where `B` decays geometrically, this
is the statement that the fractional parts in question tend to zero exponentially fast. -/
theorem exists_int_sub_le_of_conj (θ : ℝ) (hθ : IsIntegral ℤ θ) {f : ℂ → ℂ} {T : ℤ}
    (hT : (((minpoly ℚ θ).aroots ℂ).map f).sum = (T : ℂ)) {r B : ℝ} (hr : f (θ : ℂ) = (r : ℂ))
    (hB : ∀ z ∈ ((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ), ‖f z‖ ≤ B) :
    |r - (T : ℝ)| ≤ (Multiset.card (((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ)) : ℝ) * B := by
  set s : Multiset ℂ := ((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ) with hs
  have hsum : (s.map f).sum = (T : ℂ) - (r : ℂ) := by
    have h := conj_erase_sum_add θ hθ f
    rw [hr, hT] at h
    linear_combination h
  have habs : |r - (T : ℝ)| = ‖(s.map f).sum‖ := by
    rw [hsum, ← Real.norm_eq_abs, ← Complex.norm_real, ← norm_neg]
    congr 1
    push_cast
    ring
  rw [habs]
  calc ‖(s.map f).sum‖ ≤ ((s.map f).map norm).sum := norm_multiset_sum_le _
    _ = (s.map (fun z => ‖f z‖)).sum := by rw [Multiset.map_map]; rfl
    _ ≤ Multiset.card (s.map (fun z => ‖f z‖)) • B :=
        Multiset.sum_le_card_nsmul _ _ (by
          intro x hx
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
          exact hB z hz)
    _ = (Multiset.card s : ℝ) * B := by rw [Multiset.card_map, nsmul_eq_mul]
