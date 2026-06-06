/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.LaurentSeries
import BertinPisot.DenominatorBounds
import ForMathlib.RingTheory.PowerSeries.OrderConvergence
import ForMathlib.RingTheory.Polynomial.CoprimeFractionMap
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# The families `Φ_q` of integer rational fractions (Bertin §2.1)

Bertin's notation for the chapter on compact families of rational functions
(*Pisot and Salem Numbers*, [Ber92]): for `q ∈ ℕ*`, `Φ_q` is the set of rational fractions `F` with
coefficients in `ℚ` (`F : RatFunc ℚ`) admitting a representation `F = A / B` with integer polynomials
`A, B ∈ ℤ[X]` whose denominator has constant term `B(0) = q`.

`Phi q` is the rational-*function* counterpart of `IsIntegerQuotient`
(`BertinPisot/DenominatorBounds`), which is the same condition one level up, on formal power *series*
(`F ∈ ℚ⟦X⟧`, `A, B ∈ ℤ⟦X⟧`): the `X`-adic expansion `S(F)` of an `F ∈ Φ_q` is an `IsIntegerQuotient`
with the same `q`, since `ℤ[X] ⊆ ℤ⟦X⟧`. These `Φ_q` are the families Bertin proves compact (for the
topology of uniform convergence on the compacts of `D(0,1)`), the route to closed families of
algebraic numbers.

`mem_Phi_of_tendsto` is **Theorem 2.1**: `Φ_q` is closed under formal convergence (`ord(F - Fₙ) → +∞`).
It is recorded as a literature axiom; its proof combines Lemma 2.1.1's `q`-power denominator bounds
(`BertinPisot/DenominatorBounds`), the coefficient stabilisation of order convergence
(`PowerSeries.coeff_eventuallyEq_of_order_tendsto_top`), and the Kronecker rationality criterion,
closing with the integer-denominator reconstruction `rational-denominator-reconstruction` — the one
step not yet in Mathlib.

`exists_coprime_repr_constantCoeff` is **Lemma 2.1.2**: every integer-polynomial representation
`F = A / B` (`B(0) ≠ 0`) reduces to a coprime one `A₁ / B₁` with the *same* denominator constant
term `B₁(0) = B(0)` (Gauss's lemma). Specialised to `B(0) = q`, it gives every `F ∈ Φ q` a reduced
representative with the same `q`. Proved here, using the Gauss-descent lemma
`Polynomial.isCoprime_map_of_isUnit_gcd` (in `ForMathlib`).

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open scoped Polynomial

/-- **Bertin's family `Φ_q`** (`q ∈ ℕ*`): the set of rational fractions `F` over `ℚ`
(`F : RatFunc ℚ`) that can be written `F = A / B` with integer polynomials `A, B ∈ ℤ[X]` whose
denominator has constant term `B(0) = q`. The integer polynomials are sent into `RatFunc ℚ` along
`ℤ[X] → ℚ[X] → RatFunc ℚ` (`Polynomial.map (Int.castRingHom ℚ)`, then the polynomial-to-fraction
coercion). The guard `0 < q` reflects `q ∈ ℕ*` (so `B(0) ≠ 0` and `B` is a genuine denominator;
`Φ_0 = ∅`). This is the rational-function analogue of the power-series predicate `IsIntegerQuotient`,
and is the central object of Bertin's compact-families chapter. -/
@[category API, AMS 11 12, ref "Ber92"]
def Phi (q : ℕ) : Set (RatFunc ℚ) :=
  { F | 0 < q ∧ ∃ A B : ℤ[X], B.coeff 0 = (q : ℤ) ∧
      F = (A.map (Int.castRingHom ℚ) : RatFunc ℚ) / (B.map (Int.castRingHom ℚ) : RatFunc ℚ) }

/-! ## Informal-result registry

The one step of Theorem 2.1's proof that is not yet in Mathlib, recorded as a canonical node so the
`informal_uses` edge below points at it. -/

informal_result "rational-denominator-reconstruction"
  latex "Reconstruction of an integer-polynomial denominator with prescribed constant term: if a rational fraction F over ℚ has Taylor coefficients aₘ and Kronecker–Hankel determinants Dₘ obeying the q-power integrality bounds q^{m+1} aₘ ∈ ℤ and q^{2m+1} Dₘ ∈ ℤ, with Dₘ = 0 for m large (F rational), then F admits a representation F = A/B with A, B ∈ ℤ[X] and B(0) = q. The denominator B is recovered from the linear recurrence governing the (aₘ): its coefficients solve a Hankel/Cramer system whose determinants carry exactly the q-power denominators the bounds control, and the normalisation B(0) = q clears them to integers. This is the closure step in Bertin's Theorem 2.1; not yet formalised in Mathlib."
  refs "Ber92"

/-- **Theorem 2.1** (Bertin). The family `Φ_q` is closed under formal convergence: if every term of a
sequence `(Fₙ)` of rational fractions lies in `Φ_q`, and `(Fₙ)` converges to a rational fraction `F`
over `ℚ` — `ord (F - Fₙ) → +∞`, the order of the difference of the Laurent expansions tending to
`+∞` — then `F ∈ Φ_q`.

This is the closure step of Bertin's compact-families program. Proof sketch: each `Fₙ ∈ Φ_q` has
Taylor coefficients and Kronecker determinants obeying the `q`-power integrality bounds of
**Lemma 2.1.1** (`qpow_coeff_isInt_of_isIntegerQuotient`,
`qpow_kroneckerDet_isInt_of_isIntegerQuotient`); formal convergence makes each coefficient — hence
each determinant `Dₘ`, which reads only `a₀…a₂ₘ` — eventually equal to that of `F`
(`PowerSeries.coeff_eventuallyEq_of_order_tendsto_top`), so the bounds pass to `F` (ℤ is discrete).
As `F` is rational, `Dₘ(S F) = 0` eventually (`isRationalSeries_iff_kroneckerDet_eventually_zero`); the
surviving bounds then let one reconstruct an integer-polynomial denominator with constant term exactly
`q` — the step `rational-denominator-reconstruction`, not yet in Mathlib. Recorded as a literature
axiom on the authority of [Ber92].

The convergence hypothesis uses the canonical Laurent expansion `RatFunc ℚ → LaurentSeries ℚ` and its
order `HahnSeries.orderTop`; for elements of `Φ_q` (denominator constant term `q ≠ 0`) this expansion
is a power series and `orderTop` agrees with `PowerSeries.order`. -/
@[category research solved, AMS 11 12, ref "Ber92",
  formal_uses qpow_coeff_isInt_of_isIntegerQuotient qpow_kroneckerDet_isInt_of_isIntegerQuotient
    isRationalSeries_iff_kroneckerDet_eventually_zero
    PowerSeries.coeff_eventuallyEq_of_order_tendsto_top,
  informal_uses "rational-denominator-reconstruction"]
axiom mem_Phi_of_tendsto {q : ℕ} {Fs : ℕ → RatFunc ℚ} {F : RatFunc ℚ}
    (hmem : ∀ n, Fs n ∈ Phi q)
    (hconv : ∀ M : ℤ, ∀ᶠ n in Filter.atTop,
      (M : WithTop ℤ) < ((F : LaurentSeries ℚ) - (Fs n : LaurentSeries ℚ)).orderTop) :
    F ∈ Phi q

section
open Polynomial

/-- **Lemma 2.1.2** (Bertin). Every integer-polynomial representation of a rational fraction reduces
to a coprime one with the *same* denominator constant term. If `F = A / B` with `A, B ∈ ℤ[X]` and
`B(0) ≠ 0`, then there are `A₁, B₁ ∈ ℤ[X]`, relatively prime, with `F = A₁ / B₁` and `B₁(0) = B(0)`.

"Relatively prime" is the `ℚ[X]` notion `IsCoprime` on the images (no common factor of positive
degree — equivalently `A₁`, `B₁` share no root); the integer notion would be too strong, since e.g.
`X = (2·X)/2` must keep the common content `2` to preserve the denominator constant term `B(0) = 2`.
Specialised to `B(0) = q`, this gives every `F ∈ Φ q` (`Phi`) a reduced representative with the same
`q`.

Proof (Bertin's "easy, uses Gauss's lemma", here fully formalised): take `g = gcd A B` in `ℤ[X]` and
write `A = g · A'`, `B = g · B'`; cancelling `g` gives `gcd A' B' = 1`. Setting `A₁ = C (g 0) · A'`
and `B₁ = C (g 0) · B'` keeps both in `ℤ[X]`, preserves `F = A₁ / B₁` (cancel the common factor `g`,
resp. `C (g 0)`, in the field `RatFunc ℚ`), and gives `B₁(0) = g(0) · B'(0) = (g · B')(0) = B(0)`.
Coprimality of the images over `ℚ[X]` is Gauss's lemma `Polynomial.isCoprime_map_of_isUnit_gcd`
applied to `gcd A' B' = 1` (the unit `C (g 0)` does not affect `ℚ[X]`-coprimality). -/
@[category research solved, AMS 11 12, ref "Ber92",
  formal_uses Polynomial.isCoprime_map_of_isUnit_gcd]
theorem exists_coprime_repr_constantCoeff {F : RatFunc ℚ} {A B : ℤ[X]} (hB : B.coeff 0 ≠ 0)
    (hF : F = (A.map (Int.castRingHom ℚ) : RatFunc ℚ) / (B.map (Int.castRingHom ℚ) : RatFunc ℚ)) :
    ∃ A₁ B₁ : ℤ[X], IsCoprime (A₁.map (Int.castRingHom ℚ)) (B₁.map (Int.castRingHom ℚ)) ∧
      F = (A₁.map (Int.castRingHom ℚ) : RatFunc ℚ) / (B₁.map (Int.castRingHom ℚ) : RatFunc ℚ) ∧
      B₁.coeff 0 = B.coeff 0 := by
  have hBne : B ≠ 0 := fun hh => hB (by rw [hh]; simp)
  set g := gcd A B with hg
  have hgne : g ≠ 0 := by
    rw [hg, Ne, gcd_eq_zero_iff]; rintro ⟨-, hb⟩; exact hBne hb
  obtain ⟨A', hA'⟩ := gcd_dvd_left A B
  obtain ⟨B', hB'⟩ := gcd_dvd_right A B
  rw [← hg] at hA' hB'
  have hcop : IsUnit (gcd A' B') := by
    have e1 : gcd (g * A') (g * B') = normalize g * gcd A' B' := gcd_mul_left g A' B'
    have e2 : gcd (g * A') (g * B') = g := by rw [← hA', ← hB', ← hg]
    have e3 : normalize g = g := by rw [hg]; exact normalize_gcd A B
    rw [e2, e3] at e1
    have e4 : g * 1 = g * gcd A' B' := by rw [mul_one]; exact e1
    have e5 : (1 : ℤ[X]) = gcd A' B' := mul_left_cancel₀ hgne e4
    rw [← e5]; exact isUnit_one
  have hc0 : g.coeff 0 ≠ 0 := fun hh => hB (by rw [hB', mul_coeff_zero, hh, zero_mul])
  have hc0ℚ : (Int.castRingHom ℚ) (g.coeff 0) ≠ 0 := by simpa using hc0
  have hgm : g.map (Int.castRingHom ℚ) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff (Int.cast_injective)]; exact hgne
  have hφinj := RatFunc.algebraMap_injective (K := ℚ)
  have h1 : (algebraMap ℚ[X] (RatFunc ℚ)) (g.map (Int.castRingHom ℚ)) ≠ 0 := fun hh =>
    hgm (hφinj (hh.trans (map_zero _).symm))
  have h2 : (algebraMap ℚ[X] (RatFunc ℚ)) (C ((Int.castRingHom ℚ) (g.coeff 0))) ≠ 0 := fun hh =>
    (by simpa using hc0ℚ : (C ((Int.castRingHom ℚ) (g.coeff 0)) : ℚ[X]) ≠ 0)
      (hφinj (hh.trans (map_zero _).symm))
  refine ⟨C (g.coeff 0) * A', C (g.coeff 0) * B', ?_, ?_, ?_⟩
  · simp only [Polynomial.map_mul, Polynomial.map_C]
    rw [← gcd_isUnit_iff, gcd_mul_left]
    have hcc : IsUnit (C ((Int.castRingHom ℚ) (g.coeff 0)) : ℚ[X]) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0ℚ)
    rw [normalize_eq_one.mpr hcc, one_mul]
    exact (gcd_isUnit_iff _ _).mpr (isCoprime_map_of_isUnit_gcd hcop)
  · rw [hF, hA', hB']
    simp only [Polynomial.map_mul, Polynomial.map_C, RatFunc.coePolynomial_eq_algebraMap, map_mul]
    rw [mul_div_mul_left _ _ h1, mul_div_mul_left _ _ h2]
  · rw [hB', mul_coeff_zero, mul_coeff_zero, coeff_C_zero]

end
