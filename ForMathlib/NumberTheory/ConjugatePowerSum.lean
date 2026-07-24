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
  rational integer.
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
    haveI : Fintype {y : ℂ // (aeval y) (minpoly ℚ pb.gen) = 0} := Fintype.ofEquiv _ pb.liftEquiv
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
