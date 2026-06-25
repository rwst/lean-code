/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Ostrowski
public import ForMathlib.Analysis.AbsoluteValue.Equivalence
public import ForMathlib.NumberTheory.RatPadicValuationNorm

@[expose] public section
/-!
# Finite places of `ℚ` are the `p`-adic absolute values

For a prime `p`, the finite place of `ℚ` attached to the height-one prime `(p) ⊂ 𝓞 ℚ` — the place of
the embedding of `ℚ` into the `(p)`-adic completion — is exactly the standard `p`-adic absolute value
`Rat.AbsoluteValue.padic p`. Consequently `Rat.AbsoluteValue.padic p` is a finite place of `ℚ`.

Mathlib's `Rat.HeightOneSpectrum.valuation_equiv_padicValuation` only records that the underlying
*valuations* are equivalent; here the normalisations are pinned down so that the two *absolute values*
are equal, by matching their common value `1/p` at `p` (via `AbsoluteValue.IsEquiv.eq_of_apply_eq`).
The value `1/p` on the place side comes from `absNorm (p) = p` (the residue field has `p` elements).

## Main statements

* `Rat.HeightOneSpectrum.place_embedding_primeSpectrum`:
  `place (embedding (primeSpectrum p)) = Rat.AbsoluteValue.padic p`.
* `Rat.HeightOneSpectrum.isFinitePlace_padic`: `IsFinitePlace (Rat.AbsoluteValue.padic p)`.
-/

open NumberField IsDedekindDomain

namespace Rat.HeightOneSpectrum

variable (p : ℕ) [Fact p.Prime]

/-- The height-one prime of `𝓞 ℚ` corresponding to the rational prime `p`, via the equivalence
`Rat.HeightOneSpectrum.primesEquiv : HeightOneSpectrum (𝓞 ℚ) ≃ Nat.Primes`. -/
noncomputable def primeSpectrum : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv).symm ⟨p, Fact.out⟩

/-- **The finite place of `ℚ` at the prime `(p)` is the `p`-adic absolute value.** The place of the
embedding of `ℚ` into the `(p)`-adic completion of `𝓞 ℚ` equals `Rat.AbsoluteValue.padic p`. *Proof:*
both are nonarchimedean and equivalent — the adic absolute value's closed unit ball matches that of
`Rat.padicValuation p` (`valuation_equiv_padicValuation`), which matches `padicNorm p`'s
(`padicValuation_le_one_iff_padicNorm`) — and they agree at `p` (both equal `1/p`: on the place side
via `embedding_mul_absNorm` with `absNorm (p) = p`, on the norm side `padicNorm p p = 1/p`), so the
equivalence exponent is forced to `1`. -/
theorem place_embedding_primeSpectrum :
    NumberField.place (FinitePlace.embedding (primeSpectrum p)) = Rat.AbsoluteValue.padic p := by
  have hpℝ : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : 𝓞 ℚ) ≠ 0 := by simpa using (Fact.out : p.Prime).pos.ne'
  -- the value at `p` is `1/p` on both sides
  have hf : NumberField.place (FinitePlace.embedding (primeSpectrum p)) (p : ℚ) = 1 / p := by
    rw [NumberField.place_apply]
    have key := NumberField.HeightOneSpectrum.embedding_mul_absNorm ℚ (primeSpectrum p)
      (x := (p : 𝓞 ℚ)) hp0
    rw [show (algebraMap (𝓞 ℚ) ℚ (p : 𝓞 ℚ)) = (p : ℚ) by rw [map_natCast]] at key
    have hasIdeal : (primeSpectrum p).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
      have hng : Rat.HeightOneSpectrum.natGenerator (primeSpectrum p) = p := by
        unfold primeSpectrum
        rw [show (Rat.HeightOneSpectrum.natGenerator :
              IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → ℕ)
              = fun w => ((Rat.HeightOneSpectrum.primesEquiv) w).1 from rfl]
        simp
      have hspan := Rat.HeightOneSpectrum.span_natGenerator (primeSpectrum p)
      rw [hng] at hspan
      have h1 : (primeSpectrum p).asIdeal
          = Ideal.comap (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (Ideal.span {(p : ℤ)}) := by
        rw [hspan, Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective]
      rw [h1, ← Ideal.map_symm, Ideal.map_span]; simp
    have habs : Ideal.absNorm ((primeSpectrum p).maxPowDividing (Ideal.span {(p : 𝓞 ℚ)})) = p := by
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity
            (by simpa using hp0 : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥) (primeSpectrum p),
          show multiplicity (primeSpectrum p).asIdeal (Ideal.span {(p : 𝓞 ℚ)}) = 1 by
            rw [← hasIdeal]; exact multiplicity_self,
          pow_one, hasIdeal, Ideal.absNorm_span_singleton,
          show (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) p by rw [map_natCast], Algebra.norm_algebraMap]
      simp [NumberField.RingOfIntegers.rank]
    rw [habs] at key
    field_simp at key ⊢
    linarith [key]
  have hg : (Rat.AbsoluteValue.padic p) (p : ℚ) = 1 / p := by
    rw [Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p (Fact.out : p.Prime).one_lt]
    simp
  -- the two absolute values are equivalent
  have hequiv : (NumberField.place (FinitePlace.embedding (primeSpectrum p))).IsEquiv
      (Rat.AbsoluteValue.padic p) := by
    have hpe : NumberField.place (FinitePlace.embedding (primeSpectrum p))
        = NumberField.HeightOneSpectrum.adicAbv ℚ (primeSpectrum p) := by
      ext x; rw [NumberField.place_apply, FinitePlace.norm_embedding]
    rw [hpe, AbsoluteValue.isEquiv_iff_le_one_iff]
    intro x
    rw [NumberField.HeightOneSpectrum.adicAbv_def, ← NNReal.coe_one, NNReal.coe_le_coe,
        WithZeroMulInt.toNNReal_le_one_iff
          (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (primeSpectrum p))]
    have hprimes : Rat.HeightOneSpectrum.primesEquiv (primeSpectrum p) = ⟨p, Fact.out⟩ := by
      unfold primeSpectrum; rw [Equiv.apply_symm_apply]
    rw [Valuation.isEquiv_iff_val_le_one.mp
          (hprimes ▸ Rat.HeightOneSpectrum.valuation_equiv_padicValuation (primeSpectrum p))]
    rw [Rat.padicValuation_le_one_iff_padicNorm, Rat.AbsoluteValue.padic_eq_padicNorm]
    norm_num
  -- pin the equivalence exponent to `1` via the shared value at `p`, then conclude
  refine hequiv.eq_of_apply_eq (a := (p : ℚ)) (by exact_mod_cast (Fact.out : p.Prime).pos.ne') ?_ ?_
  · rw [hf]
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by positivity)]; exact hpℝ
    exact ne_of_lt this
  · rw [hf, hg]

/-- **`Rat.AbsoluteValue.padic p` is a finite place of `ℚ`.** Witnessed by the height-one prime
`primeSpectrum p` over `p`, via `place_embedding_primeSpectrum`. -/
theorem isFinitePlace_padic : NumberField.IsFinitePlace (Rat.AbsoluteValue.padic p) :=
  ⟨primeSpectrum p, place_embedding_primeSpectrum p⟩

end Rat.HeightOneSpectrum
