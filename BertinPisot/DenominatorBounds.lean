/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.RingTheory.PowerSeries.Rationality
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Integrality of denominators for ℤ-rational series (Bertin, Lemma 2.1.1)

Bertin §2.1, Lemma 2.1.1: if a formal power series `F = ∑ aₙ Xⁿ ∈ ℚ⟦X⟧` is the quotient `S/T` of two
integer power series `S, T ∈ ℤ⟦X⟧` whose denominator has constant term `t₀ = q ∈ ℕ*`, then the
`q`-power denominators of `F` are controlled:

* i) `q^{n+1} aₙ ∈ ℤ` for every `n` (`qpow_coeff_isInt_of_isIntegerQuotient`);
* ii) `q^{2n+1} Dₙ(F) ∈ ℤ` for every `n` (`qpow_kroneckerDet_isInt_of_isIntegerQuotient`), where
  `Dₙ(F) = kroneckerDet F n` is the order-`(n+1)` Hankel/Kronecker determinant `det (aᵢ₊ⱼ)₀≤ᵢ,ⱼ≤ₙ`.

The hypothesis — `F` is the quotient of two integer series with denominator constant term `q` — is
the predicate `IsIntegerQuotient F q`; since `q ≠ 0` makes the denominator a unit in `ℚ⟦X⟧`, the
relation `F = S/T` is recorded as the cleared identity `T · F = S`.

Part i) is **proved** here, by strong induction on the coefficient recurrence
`q aₙ = sₙ - ∑_{k=1}^n tₖ aₙ₋ₖ` read off from `T · F = S` (multiply through by `qⁿ` and apply the
induction hypothesis to each earlier coefficient). Part ii) is recorded as a **literature axiom** on
the authority of [Ber92]: it follows from i) by clearing the `q`-power denominators of the Hankel
matrix `(aᵢ₊ⱼ)` through column operations driven by the recurrence — factoring a `q^{i+j+1}` out of
each entry only gives the naive bound `q^{(n+1)²} Dₙ ∈ ℤ`, and the column operations sharpen it to the
linear `q^{2n+1}`. That determinant manipulation is not yet formalized, so part ii) is asserted
rather than left as `sorry`, keeping the development sorry-free. The supporting Kronecker determinant
`kroneckerDet` is from `ForMathlib`.

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open scoped PowerSeries

/-- `F : ℚ⟦X⟧` is an **integer quotient with denominator constant term `q`**: it equals `S / T` for
some integer power series `S, T ∈ ℤ⟦X⟧` whose denominator `T` has constant term `t₀ = q ∈ ℕ*`. Since
`q ≠ 0` makes `T` a unit in `ℚ⟦X⟧`, the relation `F = S/T` is recorded as the cleared identity
`T · F = S` (with `S, T` mapped into `ℚ⟦X⟧` by `Int.castRingHom ℚ`). This is the standing hypothesis
of Bertin's Lemma 2.1.1. -/
@[category API, AMS 11 13, ref "Ber92"]
def IsIntegerQuotient (F : ℚ⟦X⟧) (q : ℕ) : Prop :=
  0 < q ∧ ∃ S T : ℤ⟦X⟧, PowerSeries.coeff 0 T = (q : ℤ) ∧
    PowerSeries.map (Int.castRingHom ℚ) T * F = PowerSeries.map (Int.castRingHom ℚ) S

/-- **Lemma 2.1.1 i)** (Bertin). If `F = ∑ aₙ Xⁿ ∈ ℚ⟦X⟧` is an integer quotient with denominator
constant term `q` (`IsIntegerQuotient F q`), then `q^{n+1} aₙ ∈ ℤ` for every `n`.

Proved by strong induction on the coefficient recurrence `q aₙ = sₙ - ∑_{k=1}^n tₖ aₙ₋ₖ` (apply
`PowerSeries.coeff_mul` to `T · F = S` and peel the `k = 0` term `t₀ aₙ = q aₙ`). Multiplying by
`qⁿ`, each summand is an integer: `qⁿ aₙ₋ₖ = q^{k-1} · (q^{(n-k)+1} aₙ₋ₖ)`, whose second factor is an
integer by the induction hypothesis (`n - k < n`). Integrality is tracked as membership in the
subring `(Int.castRingHom ℚ).range ⊆ ℚ`. -/
@[category research solved, AMS 11 13, ref "Ber92"]
theorem qpow_coeff_isInt_of_isIntegerQuotient {F : ℚ⟦X⟧} {q : ℕ} (h : IsIntegerQuotient F q)
    (n : ℕ) : ∃ m : ℤ, (q : ℚ) ^ (n + 1) * PowerSeries.coeff n F = (m : ℚ) := by
  obtain ⟨-, S, T, hT0, hST⟩ := h
  have hint : ∀ z : ℤ, (z : ℚ) ∈ (Int.castRingHom ℚ).range :=
    fun z => RingHom.mem_range.mpr ⟨z, rfl⟩
  have hqmem : (q : ℚ) ∈ (Int.castRingHom ℚ).range :=
    RingHom.mem_range.mpr ⟨(q : ℤ), by simp⟩
  -- `q^{n+1} aₙ ∈ ℤ`, by strong induction on `n`.
  have key : ∀ n : ℕ,
      (q : ℚ) ^ (n + 1) * PowerSeries.coeff n F ∈ (Int.castRingHom ℚ).range := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      -- `qⁿ aⱼ ∈ ℤ` for `j < n`, since `qⁿ aⱼ = q^{n-(j+1)} · (q^{j+1} aⱼ)` and the IH bounds the tail.
      have hpow : ∀ j, j < n →
          (q : ℚ) ^ n * PowerSeries.coeff j F ∈ (Int.castRingHom ℚ).range := by
        intro j hj
        have hsplit : (q : ℚ) ^ n = (q : ℚ) ^ (n - (j + 1)) * (q : ℚ) ^ (j + 1) := by
          rw [← pow_add, Nat.sub_add_cancel hj]
        rw [hsplit, mul_assoc]
        exact mul_mem (pow_mem hqmem _) (ih j hj)
      -- The recurrence: peel the `k = 0` term off `coeff n (T · F) = coeff n S`.
      have hcoeff : PowerSeries.coeff n (PowerSeries.map (Int.castRingHom ℚ) T * F)
          = PowerSeries.coeff n (PowerSeries.map (Int.castRingHom ℚ) S) := by rw [hST]
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ'] at hcoeff
      simp only [PowerSeries.coeff_map, Int.coe_castRingHom, Nat.sub_zero, hT0,
        Int.cast_natCast] at hcoeff
      have hcf := eq_sub_of_add_eq' hcoeff
      -- `q^{n+1} aₙ = qⁿ·sₙ - ∑ₖ tₖ₊₁·(qⁿ aₙ₋ₖ₋₁)`, each summand in `ℤ` by `hpow`.
      rw [pow_succ, mul_assoc, hcf, mul_sub]
      refine sub_mem (mul_mem (pow_mem hqmem n) (hint _)) ?_
      rw [Finset.mul_sum]
      refine sum_mem fun k hk => ?_
      rw [mul_left_comm]
      exact mul_mem (hint _) (hpow (n - (k + 1)) (by rw [Finset.mem_range] at hk; omega))
  obtain ⟨m, hm⟩ := RingHom.mem_range.mp (key n)
  exact ⟨m, by simpa using hm.symm⟩

/-- **Lemma 2.1.1 ii)** (Bertin). For `F` an integer quotient with denominator constant term `q`
(`IsIntegerQuotient F q`), the order-`(n+1)` Hankel/Kronecker determinant `Dₙ(F) = kroneckerDet F n`
satisfies `q^{2n+1} Dₙ(F) ∈ ℤ` for every `n`.

Deduced from part i) by clearing the `q`-power denominators of the Hankel matrix `(aᵢ₊ⱼ)` via column
operations, which sharpen the naive `q^{(n+1)²}` bound to the linear `q^{2n+1}`; recorded as a
literature axiom on the authority of [Ber92]. -/
@[category research solved, AMS 11 15, ref "Ber92",
  formal_uses qpow_coeff_isInt_of_isIntegerQuotient kroneckerDet]
axiom qpow_kroneckerDet_isInt_of_isIntegerQuotient {F : ℚ⟦X⟧} {q : ℕ} (h : IsIntegerQuotient F q)
    (n : ℕ) : ∃ m : ℤ, (q : ℚ) ^ (2 * n + 1) * kroneckerDet F n = (m : ℚ)
