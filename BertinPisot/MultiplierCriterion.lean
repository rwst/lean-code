/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.RingTheory.PowerSeries.Rationality
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Bertin's multiplier criterion (Theorem 1.1.2) — a literature axiom

`isRationalSeries_of_multiplierMatrix_det_lt_one` is **Bertin, Theorem 1.1.2** [Ber92]: a multiplier
refinement of Kronecker's rationality criterion for integer power series. Its published proof
(integrality of the Kronecker determinant `D_r(F)` together with the finite-rank/Hankel argument
over the index sequences `ℒ_r`) is not yet formalized here, so the result is recorded as an `axiom`
on the authority of its citation rather than left as a `sorry`.

This keeps `ForMathlib/` under the usual strict QA (no `sorry`, no axioms): the supporting
constructions `multiplierCoeff` / `multiplierMatrix` / `multiplierMatrix_apply` remain there as
clean, upstreamable definitions; only the asserted criterion lives here.

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open scoped Polynomial PowerSeries

/-- **Theorem 1.1.2 (Bertin).** Let `F = ∑ aₙ Xⁿ ∈ ℤ⟦X⟧` with `a₀ ≠ 0`. Suppose there exist a
multiplier polynomial `T = ∑ tₙ Xⁿ ∈ ℂ[X]` with `t₀ = 1` and an integer `r > 0` such that
`|det A(T, L_r, F)| < 1` for *every* strictly increasing index sequence `L_r ∈ ℒ_r` (every
`L : Fin (r + 1) → ℕ` with `StrictMono L`). Then `F` is a rational series.

A refinement of Kronecker's criterion (`isRationalSeries_iff_kroneckerDet_eventually_zero`): for the
sequence `L = (0, 1, …, r)` and any admissible `T`, `det A(T, L_r, F) = D_r(F)` is an *integer*, so
the modulus bound `< 1` forces it to vanish; the multiplier `T` and the freedom in `L_r` propagate
this to the rationality conclusion. Proof not yet formalized; asserted on the authority of [Ber92]. -/
@[category API, AMS 11, ref "Ber92"]
axiom isRationalSeries_of_multiplierMatrix_det_lt_one
    (F : ℤ⟦X⟧) (h0 : PowerSeries.coeff 0 F ≠ 0)
    (T : ℂ[X]) (hT : T.coeff 0 = 1) (r : ℕ) (hr : 0 < r)
    (hbound : ∀ L : Fin (r + 1) → ℕ, StrictMono L → ‖(multiplierMatrix T F L).det‖ < 1) :
    IsRationalSeries F
