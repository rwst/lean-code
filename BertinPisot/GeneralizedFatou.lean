/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.RingTheory.PowerSeries.Rationality
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Divisibility.Units
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# The generalized Fatou theorem (Bertin, Theorem 1.3) — a literature axiom

`IsRationalSeries.exists_coprime_quotient` is **Bertin, Theorem 1.3** [Ber92]: the *generalized Fatou
theorem*. Classical Fatou (over `ℤ`) says an integer power series that represents a rational function
can be written `P/Q` with `P, Q ∈ ℤ[X]` relatively prime and `Q(0) = 1`; Bertin generalizes the
coefficient ring `ℤ` to an arbitrary **Dedekind ring** `A`.

Concretely: if `F ∈ A⟦X⟧` is a rational series (`IsRationalSeries F`, i.e. `Q' · F = P'` for *some*
polynomials with `Q' ≠ 0`), then the fraction can be put in **reduced, normalized** form — there are
`P, Q ∈ A[X]` that are relatively prime, with `Q(0) = 1`, and `F = P/Q`.

Formalization notes.
* `F = P/Q` with `Q(0) = 1` is rendered faithfully as the formal identity `(Q : A⟦X⟧) * F = P`:
  the constant term `Q(0) = 1` makes `Q` a unit in `A⟦X⟧`, so this genuinely says `F = P · Q⁻¹`.
* "relatively prime" is `IsRelPrime P Q` — *every common divisor is a unit* — which is the correct
  notion in the non-Bézout ring `A[X]` (it is the gcd-coprimality `gcd(P,Q) = 1`, strictly weaker
  than Mathlib's Bézout `IsCoprime`, which would assert `u·P + v·Q = 1` and already fails for, e.g.,
  `X` and a nonunit constant).

The proof (content/Gauss-lemma arguments over a Dedekind ring) is not yet formalized here, so the
result is recorded as an `axiom` on the authority of its citation rather than left as a `sorry`. This
keeps `ForMathlib/` under strict QA: the supporting notion `IsRationalSeries` lives there as a clean,
upstreamable definition; only the asserted theorem lives here.

## References
* [Fat06] Fatou, Pierre. *Séries trigonométriques et séries de Taylor.* Acta Math. 30 (1906), 335–400.
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open scoped Polynomial PowerSeries

/-! ## Informal-result registry

The classical result the (published) proof relies on but that is **not** in Mathlib, recorded at the
level of "what notion the proof needs", so the `informal_uses` edge below points at a canonical
node. -/

informal_result "fatou-rational-series"
  latex "Fatou's theorem on rational power series (Fatou 1906; distinct from Fatou's lemma in measure theory, MeasureTheory.lintegral_liminf_le): a formal power series over an integral domain A whose coefficients satisfy a linear recurrence over the fraction field (equivalently, it represents a rational function) admits a reduced normalized representation F = P/Q with P, Q in A[X] relatively prime and Q(0) = 1 — a rational series that is integral over A has a reduced, normalized polynomial denominator over A. The classical case is A = ℤ; Bertin's Theorem 1.3 generalizes A to an arbitrary Dedekind ring, its proof reducing to this statement over the discrete valuation rings obtained by localizing at the height-one primes."
  refs "Fat06" "Ber92"

/-- **Theorem 1.3 (Bertin; generalized Fatou).** Let `A` be a Dedekind ring and `F ∈ A⟦X⟧` a rational
series. Then there exist `P, Q ∈ A[X]` that are relatively prime (`IsRelPrime`), with `Q(0) = 1`,
such that `F = P/Q` — formally `(Q : A⟦X⟧) * F = P` (the normalization `Q(0) = 1` makes `Q` a unit in
`A⟦X⟧`, so this is honestly `F = P · Q⁻¹`).

This generalizes the classical Fatou theorem from `A = ℤ` to an arbitrary Dedekind ring. Proof (via
content/Gauss-lemma arguments over `A`) not yet formalized; asserted on the authority of [Ber92]. -/
@[category research solved, AMS 11 13, ref "Ber92", informal_uses "fatou-rational-series"]
axiom IsRationalSeries.exists_coprime_quotient {A : Type*} [CommRing A] [IsDomain A]
    [IsDedekindDomain A] {F : A⟦X⟧} (hF : IsRationalSeries F) :
    ∃ P Q : A[X], IsRelPrime P Q ∧ Q.coeff 0 = 1 ∧ (Q : A⟦X⟧) * F = (P : A⟦X⟧)
