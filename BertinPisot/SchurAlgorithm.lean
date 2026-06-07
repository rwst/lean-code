/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Schur determinants `δₙ(F)` and the reciprocal polynomial (Bertin §3)

Opening notions of Bertin's Chapter 3, *Meromorphic functions on `D(0,1)`. Generalised Schur
algorithm* (*Pisot and Salem Numbers*, [Ber92]). For a formal power series
`F = ∑_{n ∈ ℕ} aₙ zⁿ ∈ ℂ⟦z⟧` and `n ∈ ℕ` one forms two square matrices of order `n + 1`:

* `schurToeplitz F n` (`Fₙ`): the **lower-triangular Toeplitz matrix** of the first `n + 1` Taylor
  coefficients, `(Fₙ)ᵢⱼ = a_{i-j}` for `j ≤ i` and `0` otherwise — constant `a₀` down the diagonal,
  `a₁, …, aₙ` filling the sub-diagonals.
* `schurToeplitzStar F n` (`F*ₙ`): the **conjugate upper-triangular** companion, `(F*ₙ)ᵢⱼ = ā_{j-i}`
  for `i ≤ j` and `0` otherwise. Equivalently `F*ₙ = (Fₙ)ᴴ`, the conjugate transpose of `Fₙ`; so the
  block matrix below is Hermitian.

`schurDelta F n` (`δₙ(F)`) is then the **Schur determinant**
`δₙ(F) = det [ Iₙ₊₁  F*ₙ ; Fₙ  Iₙ₊₁ ]` of the `2(n+1) × 2(n+1)` block matrix. These determinants
were introduced by Schur; they drive the generalised Schur algorithm of the chapter (a function `F`
is bounded by `1` on `D(0,1)` — of Schur class — exactly when all `δₙ(F) ≥ 0`). The base case is the
worked example `schurDelta_zero`: `δ₀(F) = 1 − |a₀|²`, recorded here with a full proof.

`reciprocalC P` (`P*`) is the **reciprocal polynomial** of `P = p₀ + p₁z + ⋯ + pₙzⁿ ∈ ℂ[z]`
(`pₙ ≠ 0`): `P* = p̄ₙ + p̄ₙ₋₁z + ⋯ + p̄₀zⁿ`, the coefficients reversed *and conjugated*. It is the
conjugating refinement, over `ℂ`, of `Polynomial.reverse` — the real/integer-coefficient `Q*` used in
§2.2 (`BertinPisot.CompactFamily`); for real coefficients conjugation is trivial and the two agree.

## Lemma 3.1.1

The algebraic properties of the Schur determinants (Bertin's **Lemma 3.1.1**), all elementary linear
algebra and proved here in full:

* **a)** `schurToeplitz_mul`, `schurToeplitz_inv`: `F ↦ Fₙ` is a (commutative) ring homomorphism —
  `(FG)ₙ = Fₙ Gₙ = Gₙ Fₙ`, and if `G(0) ≠ 0` then `(F G⁻¹)ₙ = Fₙ Gₙ⁻¹ = Gₙ⁻¹ Fₙ`.
* **b)** `exchangeMatrix_schurToeplitzStar`: the exchange matrix `J = Jₙ₊₁` intertwines the two
  Toeplitz forms — `J F*ₙ = F̄ₙ J` and `J F̄ₙ = F*ₙ J`.
* **c)** `schurDelta_eq_det`: the block determinant collapses by Schur complement to
  `δₙ(F) = det(Iₙ₊₁ − Fₙ F*ₙ) = det(Iₙ₊₁ − F*ₙ Fₙ)`.
* **d)** `schurDelta_real`: for real `F`, `δₙ(F) = det(Iₙ₊₁ + J Fₙ) · det(Iₙ₊₁ − J Fₙ)` (from b) and
  c), via `(I + J Fₙ)(I − J Fₙ) = I − F*ₙ Fₙ`).
* **e)** `schurDelta_inv`: the inversion law `δₙ(1/F) = (−1)^{n+1} |F(0)|^{−2(n+1)} δₙ(F)` for
  `F(0) ≠ 0` (from c), the inverse half of a), and `det Fₙ = F(0)^{n+1}`).

Supporting identities (`schurToeplitz_one`, `schurToeplitzStar_eq_conjTranspose`,
`exchangeMatrix_mul_self` for `J² = I`, `det_schurToeplitz` for `det Fₙ = F(0)^{n+1}`,
`schurToeplitz_inv_eq` for `(G⁻¹)ₙ = Gₙ⁻¹`) are recorded as `API` lemmas feeding the five parts.

## Lemma 3.1.2 — the Schur transform and the determinant recurrence

`schurTransform F` (`F¹`) is the **Schur transform** of `F` (Bertin's **Lemma 3.1.2**, originally due
to I. Schur [Sch17]), meaningful when
`|a₀| ≠ 1`: `F¹ = (F − a₀) / (z (1 − ā₀ F))`. The numerator `F − a₀` has zero constant term, so it is
divisible by `z`, and `1 − ā₀ F` is invertible (constant term `1 − |a₀|² ≠ 0`); hence `F¹` is again a
power series — encoded as the coefficient shift `coeff k F¹ = coeff (k+1) ((F − a₀)(1 − ā₀ F)⁻¹)`.
`schurTransform_spec` proves the defining relation `z (1 − ā₀ F) · F¹ = F − a₀`, the formal content of
Bertin's "`F¹` belongs to `ℂ[[z]]`".

`schurDelta_recurrence` is the **Schur determinant recurrence** `δₙ(F) = δ₀(F)^{n+1} δ_{n-1}(F¹)`
(`n ≥ 1`), the engine of the generalised Schur algorithm — iterating it computes every `δₙ` from the
Schur parameters `δ₀(F), δ₀(F¹), …`. **Proved here in full**, following Bertin: the Hermitian matrix
`Iₙ₊₁ − Fₙ F*ₙ` factors as `(1 − |a₀|²)⁻¹ (Iₙ₊₁ − ā₀Fₙ)(Iₙ₊₁ − Gₙ G*ₙ)(Iₙ₊₁ − a₀F*ₙ)` with
`Gₙ = (Iₙ₊₁ − ā₀Fₙ)⁻¹(Fₙ − a₀Iₙ₊₁)`; since `Gₙ = (z F¹)ₙ` has a vanishing top row, its
`(Iₙ₊₁ − Gₙ G*ₙ)` determinant collapses by one row/column to `δ_{n-1}(F¹)`, while
`det(Iₙ₊₁ − ā₀Fₙ) = det(Iₙ₊₁ − a₀F*ₙ) = (1 − |a₀|²)^{n+1}` are lower/upper-triangular. Taking
determinants and using `δₙ(F) = det(Iₙ₊₁ − Fₙ F*ₙ)` (Lemma 3.1.1 c) and `δ₀(F) = 1 − |a₀|²` gives the
recurrence. The key algebraic identity `(Iₙ₊₁−ā₀Fₙ)(Iₙ₊₁−a₀F*ₙ) − (Fₙ−a₀Iₙ₊₁)(F*ₙ−ā₀Iₙ₊₁) =
(1−|a₀|²)(Iₙ₊₁−FₙF*ₙ)` is verified by `module`, and the row-collapse of `det(Iₙ₊₁ − Gₙ G*ₙ)` is the
helper `det_one_sub_schurToeplitz_X_mul`.

`schurDelta_X_pow_mul` is **Remark 3.1.1**: if `F = zˢ R` then `δₙ(F) = δ_{n-s}(R)` for `n ≥ s` —
proved by iterating the recurrence at `a₀ = 0` (`schurDelta_recurrence_zero`, where `δ₀ = 1` and
`schurTransform (z·G) = G`).

## Lemma 3.1.3 — the vanishing criterion

`schurDelta_eq_zero_iff` is **Lemma 3.1.3**: for `F(0) ≠ 0`, `δₙ(F) = 0` holds **iff** there are a
polynomial `P ∈ ℂ[z]` and `r ∈ ℕ` with `d°(P) = n − 2r ≥ 0`, `ord(F·P − P*) ≥ n + 1 − r`, and
`P(0) ≠ 0` — i.e. the near-self-inversive relation `F·P ≡ P* (mod z^{n+1−r})` is solvable by a
degree-`(n − 2r)` polynomial of nonzero constant term, with the slack `r` measuring the rank drop of
the Schur block matrix `[Iₙ₊₁ F*ₙ; Fₙ Iₙ₊₁]`. This is where the reciprocal polynomial
`P* = reciprocalC P` of the opener first enters. It is a proved theorem of Bertin (not an open
statement); it is recorded here as a `cited` axiom (`ref "Ber92"`) — the rank/kernel argument linking
the vanishing block determinant to the polynomial `P` is not yet formalised in this corpus.

## Lemma 3.1.4 — coprimality from a run of vanishing determinants

`exists_poly_of_schurDelta_run` is **Lemma 3.1.4**: if `F(0) ≠ 0`, `δ_{n−1}(F) ≠ 0`, and a run of
`k ≥ 1` consecutive Schur determinants vanishes, `δₙ(F) = δ_{n+1}(F) = ⋯ = δ_{n+k−1}(F) = 0`, then
there is a polynomial `P ∈ ℂ[z]` with `d°(P) = n`, `P(0) ≠ 0`, with `P` and `P*` relatively prime
(when `n ≠ 0`), and `ord(F·P − P*) ≥ n + 1 + ⌊k/2⌋`. It refines Lemma 3.1.3 along a maximal vanishing
block: the run length `k` raises the contact order by `⌊k/2⌋`, while the leading `δ_{n−1} ≠ 0` pins the
degree to exactly `n` (the `r = 0` case) and forces `P, P*` coprime. The `k = 1` case is precisely
Lemma 3.1.3 at `r = 0`. Recorded as a `cited` axiom (`ref "Ber92"`); the proof is not yet formalised.

## Theorem 3.1.1 — rational functions `zʳ P*/P` and the determinant pattern

`eq_X_pow_mul_reciprocalC_div_iff` is **Theorem 3.1.1**, the capstone of §3.1: `F ∈ ℂ⟦z⟧` has the form
`F = zʳ · P*/P` (`r ∈ ℕ`, `P ∈ ℂ[z]`, `P(0) ≠ 0`, `P` and `P*` coprime, `d°(P) = n₀`) **iff**
`δₙ(F) = 0` for all `n ≥ n₀ + r` and `δ_{n₀+r−1}(F) ≠ 0`. So the `zʳ`-times-self-inversive rational
functions are exactly those `F` whose Schur determinants vanish from a sharp index `n₀ + r` onward. Via
Remark 3.1.1 (`schurDelta_X_pow_mul`) the `zʳ` factor reduces this to the `F(0) ≠ 0` case, which rests
on Lemmas 3.1.3/3.1.4. Recorded as a `cited` axiom (`ref "Ber92"`) pending a full formalization.

## Lemma 3.2.1 — iterated Schur transforms and the continued-fraction convergents

For `F ∈ ℂ⟦z⟧` with `δ₀(F), …, δₙ(F)` all nonzero, write `Fⁱ = schurTransform^[i] F` for the iterated
Schur transform (`F⁰ = F`) and `γₖ = Fᵏ(0)` for the Schur parameters. `schurOmega F i` is
`ωᵢ = ∏_{k=0}^{i} δ₀(Fᵏ) = ∏_{k=0}^{i}(1 − |γₖ|²)`. The rank-`i` reciprocal-conjugate
`Ã(z) = zⁱ Ā(1/z)` is `reciprocalAt i A = (A.reflect i).map (starRingEnd ℂ)` — the degree-`i` version
of `reciprocalC` (`reciprocalAt_natDegree`: `reciprocalAt (d°P) P = P*`). The bridge
`schurDelta_zero_ne_zero_iff` is `δ₀(F) ≠ 0 ↔ |a₀|² ≠ 1`, converting the determinant hypotheses to the
`normSq … ≠ 1` form that `schurTransform_spec`/`schurDelta_recurrence` consume.

* **a)** `schurDelta_zero_iterate_ne_zero`: the transforms are defined up to rank `n + 1`, i.e.
  `δ₀(Fᵏ) ≠ 0` (equivalently `|γₖ| ≠ 1`) for every `k ≤ n`, so each of `F¹, …, F^{n+1}` is a genuine
  power series. **Proved here**: induction on `n`, using `δ_{j+1}(F) = δ₀(F)^{j+2} δ_j(F¹)`
  (`schurDelta_recurrence`) to pass the hypothesis down to `F¹`.
* **b)** `exists_convergents`: for each `i ≤ n` there are convergent polynomials `Aᵢ, Qᵢ ∈ ℂ[z]` with
  `d°Aᵢ, d°Qᵢ ≤ i` and `Qᵢ(0) = 1`, satisfying the continued-fraction relation
  `F·(Qᵢ + z Ãᵢ F^{i+1}) = Aᵢ + z Q̃ᵢ F^{i+1}` (`~` is `reciprocalAt i`), the Wronskian identity
  `Qᵢ Q̃ᵢ − Aᵢ Ãᵢ = ωᵢ zⁱ`, and the approximation order `ord(F·Qᵢ − Aᵢ) ≥ i + 1` with `(i+1)`-th
  coefficient `ωᵢ γᵢ₊₁`. The Schur–Wall convergent construction is recorded as a `cited` axiom
  (`ref "Ber92"`), existential form, pending formalization.
* **c)** `schurDelta_add_eq_iterate_prod`: the iterated determinant formula
  `δ_{n+k}(F) = ∏_{j=0}^{n-1} δ₀(Fʲ)^{(n−j)+(k+1)} · δₖ(Fⁿ)` for all `k`. **Proved here** by iterating
  `schurDelta_recurrence` `n` times (nonvanishing derived inline as in a). The exponent
  `(n−j)+(k+1) = n+k+1−j` runs `n+k+1, n+k, …, k+2`; Bertin's text prints the final exponent as `k+1`,
  but iterating the recurrence forces `k+2` (already at `n = 1` the first and last factor coincide,
  both `δ₀(F)^{k+2}`).

The Schur-parameter products `ωᵢ = schurOmega F i` satisfy `schurOmega_zero` (`ω₀ = δ₀(F)`),
`schurOmega_succ` (`ωₙ₊₁ = ωₙ·δ₀(Fⁿ⁺¹)`), `schurOmega_succ'` (`ωₙ₊₁ = ωₙ(F¹)·δ₀(F)`), and the **ratio
identity** `schurDelta_succ_eq_schurOmega_mul`: `δₙ₊₁(F) = ωₙ₊₁·δₙ(F)` (so `ωₙ₊₁ = δₙ₊₁/δₙ` when
`δₙ ≠ 0`) — the determinant computation behind Bertin's **Corollary 3.2.1** (formalised in
`BertinPisot.SchurClass`).

## Notation

Bertin fixes companion matrix/polynomial notation in this section; the ones with a direct Mathlib
primitive are used inline rather than re-aliased:

* `Ā` (entrywise conjugate of a complex matrix `A = (aᵢⱼ)`, i.e. `(āᵢⱼ)`) is `A.map (starRingEnd ℂ)`
  (Mathlib's `Matrix.conjTranspose Aᴴ` is this *composed with transpose*);
* `Iₙ₊₁` (identity of order `n + 1`) is `(1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)`;
* `Oᵢⱼ` (the `i × j` zero matrix) is `(0 : Matrix (Fin i) (Fin j) ℂ)`;
* `Jₙ₊₁` (the **exchange matrix**: `1` on the anti-diagonal `i + j = n`, `0` elsewhere) has no single
  Mathlib primitive, so it is the explicit definition `exchangeMatrix n` (used in parts b) and d) of
  Lemma 3.1.1 below; `exchangeMatrix_mul_self` records `J² = I`).

## Encoding

* `F ∈ ℂ⟦z⟧` is `F : PowerSeries ℂ`, with coefficient `aₘ = PowerSeries.coeff m F`.
* The matrices are indexed by `Fin (n + 1)`; entries `a_{i-j}`, `ā_{j-i}` use natural-number index
  subtraction (well-defined under the triangularity guards `j ≤ i`, resp. `i ≤ j`). Conjugation is
  `starRingEnd ℂ`.
* `δₙ(F)` is `(Matrix.fromBlocks 1 (F*ₙ) (Fₙ) 1).det`. The example `δ₀(F) = 1 − |a₀|²` writes
  `|a₀|²` as `Complex.normSq a₀` (cast to `ℂ`); it falls out of the `1×1` Schur-complement reduction
  `det [1, F*₀; F₀, 1] = det (1 − F₀ · F*₀) = 1 − a₀ ā₀`.
* `P*` is `P.reverse.map (starRingEnd ℂ)` (`Polynomial.reverse`, reindexing `pₖ ↦ p_{n-k}`, then
  entrywise conjugation).

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
* [Sch17] Schur, Issai. *Über Potenzreihen, die im Innern des Einheitskreises beschränkt sind.*
  J. Reine Angew. Math. **147** (1917), 205–232; **148** (1918), 122–145. (Origin of the Schur
  algorithm: the Schur transform `F¹` and the determinant recurrence of Lemma 3.1.2.)
-/

open scoped Polynomial Matrix

/-- **Bertin's matrix `Fₙ`** (§3): the lower-triangular Toeplitz matrix of order `n + 1` built from
the first `n + 1` Taylor coefficients of `F = ∑ aₘ zᵐ ∈ ℂ⟦z⟧`. Its `(i, j)` entry is `a_{i-j}` when
`j ≤ i` (constant `a₀` on the diagonal, `a₁, …, aₙ` on the successive sub-diagonals) and `0` above the
diagonal. Index subtraction is on `ℕ`, well-defined under the guard `j ≤ i`. -/
@[category API, AMS 15 30, ref "Ber92"]
noncomputable def schurToeplitz (F : PowerSeries ℂ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if j ≤ i then PowerSeries.coeff ((i : ℕ) - (j : ℕ)) F else 0

/-- **Bertin's matrix `F*ₙ`** (§3): the conjugate upper-triangular companion of `Fₙ`, of order
`n + 1`. Its `(i, j)` entry is `ā_{j-i}` (the conjugate of the `(j-i)`-th Taylor coefficient of `F`)
when `i ≤ j`, and `0` below the diagonal. Equivalently `F*ₙ = (Fₙ)ᴴ = (schurToeplitz F n)ᴴ`, the
conjugate transpose of `Fₙ`. -/
@[category API, AMS 15 30, ref "Ber92"]
noncomputable def schurToeplitzStar (F : PowerSeries ℂ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if i ≤ j then starRingEnd ℂ (PowerSeries.coeff ((j : ℕ) - (i : ℕ)) F) else 0

/-- **Schur determinant `δₙ(F)`** (Bertin §3): the determinant of the `2(n+1) × 2(n+1)` block matrix
`[ Iₙ₊₁  F*ₙ ; Fₙ  Iₙ₊₁ ]`, with `Fₙ = schurToeplitz F n` and `F*ₙ = schurToeplitzStar F n`. These
determinants were introduced by Schur and are the engine of the generalised Schur algorithm: `F` is
of Schur class (`|F| ≤ 1` on `D(0,1)`) iff `δₙ(F) ≥ 0` for all `n`. See `schurDelta_zero` for the base
case `δ₀(F) = 1 − |a₀|²`. -/
@[category API, AMS 15 30, ref "Ber92", formal_uses schurToeplitz schurToeplitzStar]
noncomputable def schurDelta (F : PowerSeries ℂ) (n : ℕ) : ℂ :=
  (Matrix.fromBlocks (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (schurToeplitzStar F n)
    (schurToeplitz F n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det

/-- **Bertin's exchange matrix `Jₙ₊₁`** (§3 notation): the `(n+1) × (n+1)` matrix with `1` on the
anti-diagonal (`i + j = n`) and `0` elsewhere; equivalently the permutation matrix of the reversal
`Fin.rev`. It satisfies `J² = I` (`exchangeMatrix_mul_self`) and conjugates `Fₙ`/`F*ₙ` into each
other (Lemma 3.1.1 b), `exchangeMatrix_schurToeplitzStar`). -/
@[category API, AMS 15, ref "Ber92"]
def exchangeMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if (i : ℕ) + (j : ℕ) = n then 1 else 0

/-- **Reciprocal polynomial `P*`** (Bertin §3): for `P = p₀ + p₁z + ⋯ + pₙzⁿ ∈ ℂ[z]` (`pₙ ≠ 0`),
`P* = p̄ₙ + p̄ₙ₋₁z + ⋯ + p̄₀zⁿ` — the coefficients reversed and conjugated. Implemented as
`P.reverse.map (starRingEnd ℂ)` (`Polynomial.reverse` reverses `pₖ ↦ p_{n-k}` up to the degree, then
the coefficients are conjugated). It refines, over `ℂ`, the real-coefficient `Q* = Q.reverse` of §2.2
(`BertinPisot.CompactFamily`): the two coincide when the coefficients are real. -/
@[category API, AMS 12 30, ref "Ber92"]
noncomputable def reciprocalC (P : ℂ[X]) : ℂ[X] := P.reverse.map (starRingEnd ℂ)

/-- **Base case of the Schur determinants** (Bertin §3, worked example): `δ₀(F) = 1 − |a₀|²`, where
`a₀ = PowerSeries.coeff 0 F` is the constant term and `|a₀|² = Complex.normSq a₀`. The `0`-th Schur
matrix is the `1×1` block matrix `[1, ā₀; a₀, 1]`, whose determinant `1 − a₀ ā₀ = 1 − |a₀|²` is the
first Schur parameter. -/
@[category API, AMS 15 30, ref "Ber92", formal_uses schurDelta schurToeplitz schurToeplitzStar]
theorem schurDelta_zero (F : PowerSeries ℂ) :
    schurDelta F 0 = 1 - (Complex.normSq (PowerSeries.coeff 0 F) : ℂ) := by
  rw [schurDelta, Matrix.det_fromBlocks_one₁₁, Matrix.det_fin_one]
  simp [schurToeplitz, schurToeplitzStar, Matrix.mul_apply, Matrix.sub_apply, Complex.mul_conj]

/-! ## Lemma 3.1.1 — algebraic properties of the Schur determinants

Bertin's **Lemma 3.1.1**, proved here in full (elementary linear algebra). Parts a)–e) are the
`research solved` nodes; the preceding identities are `API` lemmas supporting them. -/

/-- `1ₙ = Iₙ₊₁`: the Toeplitz matrix of the unit power series is the identity (supporting identity for
Lemma 3.1.1 a)). -/
@[category API, AMS 15, formal_uses schurToeplitz]
theorem schurToeplitz_one (n : ℕ) : schurToeplitz (1 : PowerSeries ℂ) n = 1 := by
  ext i j
  simp only [schurToeplitz, PowerSeries.coeff_one, Matrix.one_apply, Fin.le_def, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- `F*ₙ = (Fₙ)ᴴ`: the conjugate upper-triangular matrix is the conjugate transpose of the
lower-triangular Toeplitz matrix (supporting identity, used in Lemma 3.1.1 e)). -/
@[category API, AMS 15, formal_uses schurToeplitzStar schurToeplitz]
theorem schurToeplitzStar_eq_conjTranspose (F : PowerSeries ℂ) (n : ℕ) :
    schurToeplitzStar F n = (schurToeplitz F n)ᴴ := by
  ext i j
  simp only [schurToeplitzStar, schurToeplitz, Matrix.conjTranspose_apply]
  split_ifs with h <;> simp

/-- `J² = Iₙ₊₁`: the exchange matrix is an involution (supporting identity for Lemma 3.1.1 b), d)). -/
@[category API, AMS 15, formal_uses exchangeMatrix]
theorem exchangeMatrix_mul_self (n : ℕ) : exchangeMatrix n * exchangeMatrix n = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [exchangeMatrix]
  rw [Finset.sum_eq_single (⟨n - (k:ℕ), by omega⟩ : Fin (n+1))]
  · rw [if_pos (show (n - (k:ℕ)) + (k:ℕ) = n by omega), mul_one]
    by_cases hik : i = k
    · subst hik; rw [if_pos (show (i:ℕ) + (n - (i:ℕ)) = n by omega), if_pos rfl]
    · rw [if_neg (show ¬ (i:ℕ) + (n - (k:ℕ)) = n by intro h; exact hik (Fin.ext (by omega))),
        if_neg hik]
  · intro b _ hb
    rw [if_neg (show ¬ (b:ℕ) + (k:ℕ) = n by
      intro h; exact hb (Fin.ext (by omega : (b:ℕ) = n - (k:ℕ)))), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `det Fₙ = F(0)^{n+1}`: the determinant of a lower-triangular Toeplitz matrix is the `(n+1)`-th
power of its constant diagonal entry `F(0)` (supporting identity for Lemma 3.1.1 e)). -/
@[category API, AMS 15 30, formal_uses schurToeplitz]
theorem det_schurToeplitz (F : PowerSeries ℂ) (n : ℕ) :
    (schurToeplitz F n).det = (PowerSeries.coeff 0 F) ^ (n + 1) := by
  rw [Matrix.det_of_lowerTriangular]
  · simp only [schurToeplitz, le_refl, if_true, Nat.sub_self, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  · intro i j hij
    simp only [schurToeplitz]
    exact if_neg (not_le.mpr (OrderDual.toDual_lt_toDual.mp hij))

/-- **Lemma 3.1.1 a)** (Bertin), product law: `F ↦ Fₙ` is multiplicative — `(FG)ₙ = Fₙ Gₙ`. The
`(i,j)` entry of `Fₙ Gₙ` is the convolution `∑_{j ≤ l ≤ i} a_{i-l} b_{l-j}`, which is the `(i-j)`-th
coefficient of `FG`. Commutativity `Fₙ Gₙ = Gₙ Fₙ` follows since `FG = GF`. -/
@[category research solved, AMS 15 30, ref "Ber92", formal_uses schurToeplitz]
theorem schurToeplitz_mul (F G : PowerSeries ℂ) (n : ℕ) :
    schurToeplitz (F * G) n = schurToeplitz F n * schurToeplitz G n := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [schurToeplitz, Fin.le_def]
  rw [Fin.sum_univ_eq_sum_range (fun m =>
    (if m ≤ (i:ℕ) then PowerSeries.coeff ((i:ℕ) - m) F else 0) *
    (if (j:ℕ) ≤ m then PowerSeries.coeff (m - (j:ℕ)) G else 0)) (n+1)]
  split_ifs with hji
  · rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hsub : Finset.Icc (j:ℕ) (i:ℕ) ⊆ Finset.range (n+1) := by
      intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    have hzero : ∀ m ∈ Finset.range (n+1), m ∉ Finset.Icc (j:ℕ) (i:ℕ) →
        (if m ≤ (i:ℕ) then PowerSeries.coeff ((i:ℕ)-m) F else 0) *
        (if (j:ℕ) ≤ m then PowerSeries.coeff (m-(j:ℕ)) G else 0) = 0 := by
      intro m _ hm
      simp only [Finset.mem_Icc, not_and, not_le] at hm
      by_cases hjm : (j:ℕ) ≤ m
      · rw [if_neg (show ¬ m ≤ (i:ℕ) by omega), zero_mul]
      · rw [if_neg hjm, mul_zero]
    rw [← Finset.sum_subset hsub hzero]
    apply Finset.sum_nbij' (fun x => (i:ℕ) - x) (fun m => (i:ℕ) - m)
    · intro x hx; simp only [Finset.mem_range] at hx; simp only [Finset.mem_Icc]; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    · intro x hx; simp only [Finset.mem_range] at hx; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; omega
    · intro x hx; simp only [Finset.mem_range] at hx
      have hxi : x ≤ (i:ℕ) := by omega
      rw [if_pos (Nat.sub_le _ _), if_pos (show (j:ℕ) ≤ (i:ℕ) - x by omega),
        show (i:ℕ) - ((i:ℕ) - x) = x by omega,
        show ((i:ℕ) - x) - (j:ℕ) = (i:ℕ) - (j:ℕ) - x by omega]
  · symm
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_range] at hm
    by_cases hmi : m ≤ (i:ℕ)
    · rw [if_neg (show ¬ (j:ℕ) ≤ m by omega), mul_zero]
    · rw [if_neg hmi, zero_mul]

/-- `(G⁻¹)ₙ = (Gₙ)⁻¹` for `G(0) ≠ 0`: the Toeplitz matrix of the power-series inverse is the matrix
inverse (supporting identity, the inverse half of Lemma 3.1.1 a)). -/
@[category API, AMS 15 30, formal_uses schurToeplitz schurToeplitz_mul schurToeplitz_one]
theorem schurToeplitz_inv_eq (G : PowerSeries ℂ) (n : ℕ)
    (hG : PowerSeries.constantCoeff G ≠ 0) :
    schurToeplitz G⁻¹ n = (schurToeplitz G n)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← schurToeplitz_mul, PowerSeries.mul_inv_cancel G hG, schurToeplitz_one]

/-- **Lemma 3.1.1 a)** (Bertin), inverse law: if `G(0) ≠ 0` then `(F G⁻¹)ₙ = Fₙ Gₙ⁻¹`. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurToeplitz schurToeplitz_mul schurToeplitz_inv_eq]
theorem schurToeplitz_inv (F G : PowerSeries ℂ) (n : ℕ)
    (hG : PowerSeries.constantCoeff G ≠ 0) :
    schurToeplitz (F * G⁻¹) n = schurToeplitz F n * (schurToeplitz G n)⁻¹ := by
  rw [schurToeplitz_mul, schurToeplitz_inv_eq G n hG]

/-- **Lemma 3.1.1 b)** (Bertin). The exchange matrix `J = Jₙ₊₁` intertwines the two Toeplitz forms:
`J F*ₙ = F̄ₙ J` and `J F̄ₙ = F*ₙ J`, where `F̄ₙ = (Fₙ).map (starRingEnd ℂ)` is the entrywise
conjugate. The first equation is an entry computation; the second follows from it and `J² = I`. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses exchangeMatrix schurToeplitzStar schurToeplitz exchangeMatrix_mul_self]
theorem exchangeMatrix_schurToeplitzStar (F : PowerSeries ℂ) (n : ℕ) :
    exchangeMatrix n * schurToeplitzStar F n
        = (schurToeplitz F n).map (starRingEnd ℂ) * exchangeMatrix n
    ∧ exchangeMatrix n * (schurToeplitz F n).map (starRingEnd ℂ)
        = schurToeplitzStar F n * exchangeMatrix n := by
  have h1 : exchangeMatrix n * schurToeplitzStar F n
      = (schurToeplitz F n).map (starRingEnd ℂ) * exchangeMatrix n := by
    ext i j
    have hL : (exchangeMatrix n * schurToeplitzStar F n) i j
        = if n ≤ (i:ℕ)+(j:ℕ) then starRingEnd ℂ (PowerSeries.coeff ((i:ℕ)+(j:ℕ)-n) F) else 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (⟨n - (i:ℕ), by omega⟩ : Fin (n+1))]
      · simp only [exchangeMatrix, schurToeplitzStar, Fin.le_def]
        rw [if_pos (show (i:ℕ) + (n - (i:ℕ)) = n by omega), one_mul]
        by_cases hij : n ≤ (i:ℕ) + (j:ℕ)
        · rw [if_pos (show n - (i:ℕ) ≤ (j:ℕ) by omega), if_pos hij,
            show (j:ℕ) - (n - (i:ℕ)) = (i:ℕ)+(j:ℕ)-n by omega]
        · rw [if_neg (show ¬ n - (i:ℕ) ≤ (j:ℕ) by omega), if_neg hij]
      · intro b _ hb
        simp only [exchangeMatrix]
        rw [if_neg (show ¬ (i:ℕ) + (b:ℕ) = n by
          intro h; exact hb (Fin.ext (by omega : (b:ℕ) = n - (i:ℕ)))), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR : ((schurToeplitz F n).map (starRingEnd ℂ) * exchangeMatrix n) i j
        = if n ≤ (i:ℕ)+(j:ℕ) then starRingEnd ℂ (PowerSeries.coeff ((i:ℕ)+(j:ℕ)-n) F) else 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (⟨n - (j:ℕ), by omega⟩ : Fin (n+1))]
      · simp only [exchangeMatrix, schurToeplitz, Matrix.map_apply, Fin.le_def]
        rw [if_pos (show (n - (j:ℕ)) + (j:ℕ) = n by omega), mul_one]
        by_cases hij : n ≤ (i:ℕ) + (j:ℕ)
        · rw [if_pos (show n - (j:ℕ) ≤ (i:ℕ) by omega), if_pos hij,
            show (i:ℕ) - (n - (j:ℕ)) = (i:ℕ)+(j:ℕ)-n by omega]
        · rw [if_neg (show ¬ n - (j:ℕ) ≤ (i:ℕ) by omega), if_neg hij, map_zero]
      · intro b _ hb
        simp only [exchangeMatrix]
        rw [if_neg (show ¬ (b:ℕ) + (j:ℕ) = n by
          intro h; exact hb (Fin.ext (by omega : (b:ℕ) = n - (j:ℕ)))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hL, hR]
  have hJ := exchangeMatrix_mul_self n
  refine ⟨h1, ?_⟩
  have hABA : exchangeMatrix n * (schurToeplitz F n).map (starRingEnd ℂ) * exchangeMatrix n
      = schurToeplitzStar F n := by rw [mul_assoc, ← h1, ← mul_assoc, hJ, one_mul]
  rw [← hABA, mul_assoc, hJ, mul_one]

/-- **Lemma 3.1.1 c)** (Bertin). The Schur determinant collapses by the Schur-complement reduction of
its defining block matrix: `δₙ(F) = det(Iₙ₊₁ − Fₙ F*ₙ) = det(Iₙ₊₁ − F*ₙ Fₙ)`. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurDelta schurToeplitz schurToeplitzStar]
theorem schurDelta_eq_det (F : PowerSeries ℂ) (n : ℕ) :
    schurDelta F n = (1 - schurToeplitz F n * schurToeplitzStar F n).det ∧
    schurDelta F n = (1 - schurToeplitzStar F n * schurToeplitz F n).det :=
  ⟨by rw [schurDelta, Matrix.det_fromBlocks_one₁₁], by rw [schurDelta, Matrix.det_fromBlocks_one₂₂]⟩

/-- **Lemma 3.1.1 d)** (Bertin). For a real power series `F ∈ ℝ⟦z⟧` (every coefficient fixed by
conjugation), the Schur determinant factors as
`δₙ(F) = det(Iₙ₊₁ + J Fₙ) · det(Iₙ₊₁ − J Fₙ)`. Proof: from b) (real ⇒ `F̄ₙ = Fₙ`) and `J² = I` one
gets `J Fₙ J = F*ₙ`, so `(I + J Fₙ)(I − J Fₙ) = I − F*ₙ Fₙ`; take determinants and apply c). -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurDelta exchangeMatrix schurToeplitz schurDelta_eq_det
    exchangeMatrix_schurToeplitzStar exchangeMatrix_mul_self]
theorem schurDelta_real (F : PowerSeries ℂ) (n : ℕ)
    (hF : ∀ m, starRingEnd ℂ (PowerSeries.coeff m F) = PowerSeries.coeff m F) :
    schurDelta F n = (1 + exchangeMatrix n * schurToeplitz F n).det
      * (1 - exchangeMatrix n * schurToeplitz F n).det := by
  have hreal : (schurToeplitz F n).map (starRingEnd ℂ) = schurToeplitz F n := by
    ext i j; simp only [Matrix.map_apply, schurToeplitz]; split_ifs <;> simp [hF]
  have hb := (exchangeMatrix_schurToeplitzStar F n).1
  rw [hreal] at hb
  have hJ := exchangeMatrix_mul_self n
  have hJFJ : exchangeMatrix n * schurToeplitz F n * exchangeMatrix n = schurToeplitzStar F n := by
    rw [mul_assoc, ← hb, ← mul_assoc, hJ, one_mul]
  have hsq : (exchangeMatrix n * schurToeplitz F n) * (exchangeMatrix n * schurToeplitz F n)
      = schurToeplitzStar F n * schurToeplitz F n := by rw [← mul_assoc, hJFJ]
  rw [(schurDelta_eq_det F n).2, ← hsq, ← Matrix.det_mul]
  congr 1
  noncomm_ring

/-- **Lemma 3.1.1 e)** (Bertin). The Schur determinants transform under inversion `F ↦ 1/F`
(`F(0) ≠ 0`) by `δₙ(1/F) = (−1)^{n+1} |F(0)|^{−2(n+1)} δₙ(F)`, with `|F(0)|² = Complex.normSq (F 0)`.
Proof: by c), `δₙ(1/F) = det(I − (F*ₙ Fₙ)⁻¹)`; pulling out `(F*ₙ Fₙ)⁻¹` and using
`det(F*ₙ Fₙ) = |det Fₙ|² = |F(0)|^{2(n+1)}` (`det_schurToeplitz`, `det_conjTranspose`) and
`det(−A) = (−1)^{n+1} det A` gives the formula. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurDelta schurToeplitz schurToeplitzStar schurDelta_eq_det schurToeplitz_inv_eq
    schurToeplitzStar_eq_conjTranspose det_schurToeplitz]
theorem schurDelta_inv (F : PowerSeries ℂ) (n : ℕ) (hF : PowerSeries.constantCoeff F ≠ 0) :
    schurDelta F⁻¹ n
      = (-1)^(n+1) * ((Complex.normSq (PowerSeries.coeff 0 F) : ℂ)^(n+1))⁻¹ * schurDelta F n := by
  have hc0 : PowerSeries.coeff 0 F ≠ 0 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff]
  have hinv : schurToeplitz F⁻¹ n = (schurToeplitz F n)⁻¹ := schurToeplitz_inv_eq F n hF
  have hstar : schurToeplitzStar F⁻¹ n = (schurToeplitzStar F n)⁻¹ := by
    rw [schurToeplitzStar_eq_conjTranspose, schurToeplitzStar_eq_conjTranspose, hinv,
      Matrix.conjTranspose_nonsing_inv]
  have hMdet : (schurToeplitzStar F n * schurToeplitz F n).det
      = (Complex.normSq (PowerSeries.coeff 0 F) : ℂ)^(n+1) := by
    rw [Matrix.det_mul, schurToeplitzStar_eq_conjTranspose, Matrix.det_conjTranspose]
    simp only [det_schurToeplitz]
    rw [star_pow, ← mul_pow]
    congr 1
    rw [Complex.star_def, mul_comm, Complex.mul_conj]
  have hMunit : IsUnit (schurToeplitzStar F n * schurToeplitz F n).det := by
    rw [hMdet]
    refine (pow_ne_zero _ ?_).isUnit
    simp only [ne_eq, Complex.ofReal_eq_zero, Complex.normSq_eq_zero]
    exact hc0
  have hcM : (1 - schurToeplitzStar F n * schurToeplitz F n).det = schurDelta F n :=
    ((schurDelta_eq_det F n).2).symm
  rw [(schurDelta_eq_det F⁻¹ n).1, hinv, hstar, ← Matrix.mul_inv_rev,
    show (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - (schurToeplitzStar F n * schurToeplitz F n)⁻¹
      = (schurToeplitzStar F n * schurToeplitz F n)⁻¹
        * ((schurToeplitzStar F n * schurToeplitz F n) - 1) by
      rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hMunit, mul_one],
    Matrix.det_mul, Matrix.det_nonsing_inv,
    show (schurToeplitzStar F n * schurToeplitz F n) - 1
       = -(1 - schurToeplitzStar F n * schurToeplitz F n) by abel,
    Matrix.det_neg, Fintype.card_fin, hcM, hMdet, Ring.inverse_eq_inv']
  ring

/-! ## Lemma 3.1.2 — the Schur transform `F¹` and the determinant recurrence -/

section SchurTransform
open PowerSeries

/-- Additivity of the Toeplitz map: `(F − G)ₙ = Fₙ − Gₙ` (supporting identity for Lemma 3.1.2). -/
@[category API, AMS 15, formal_uses schurToeplitz]
theorem schurToeplitz_sub (F G : PowerSeries ℂ) (n : ℕ) :
    schurToeplitz (F - G) n = schurToeplitz F n - schurToeplitz G n := by
  ext i j
  simp only [schurToeplitz, Matrix.sub_apply, map_sub]
  split_ifs <;> simp

/-- The Toeplitz matrix of a constant series is the scalar matrix: `(C c)ₙ = c • Iₙ₊₁` (supporting
identity for Lemma 3.1.2). -/
@[category API, AMS 15, formal_uses schurToeplitz]
theorem schurToeplitz_C (c : ℂ) (n : ℕ) : schurToeplitz (C c) n = c • 1 := by
  ext i j
  simp only [schurToeplitz, coeff_C, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Fin.le_def, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- Scalar multiplication through the Toeplitz map: `(C c * F)ₙ = c • Fₙ` (supporting identity for
Lemma 3.1.2). -/
@[category API, AMS 15, formal_uses schurToeplitz schurToeplitz_mul schurToeplitz_C]
theorem schurToeplitz_C_mul (c : ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    schurToeplitz (C c * F) n = c • schurToeplitz F n := by
  rw [schurToeplitz_mul, schurToeplitz_C, Matrix.smul_mul, one_mul]

/-- **Schur transform `F¹`** (Bertin §3, Lemma 3.1.2): for `F = ∑ aₘ zᵐ` with `|a₀| ≠ 1`,
`F¹ = (F − a₀) / (z (1 − ā₀ F))`. The numerator `F − a₀` has zero constant term, hence is divisible by
`z`, and `1 − ā₀ F` is invertible (constant term `1 − |a₀|² ≠ 0`), so `F¹` is again a power series —
here the coefficient shift `coeff k F¹ = coeff (k+1) ((F − a₀)(1 − ā₀ F)⁻¹)`, with `a₀ = constantCoeff F`.
Defined as a total function (junk for `|a₀| = 1`); the defining relation is `schurTransform_spec`. -/
@[category API, AMS 30 13, ref "Ber92" "Sch17"]
noncomputable def schurTransform (F : PowerSeries ℂ) : PowerSeries ℂ :=
  mk fun k => coeff (k + 1)
    ((F - C (constantCoeff F)) * (1 - C (starRingEnd ℂ (constantCoeff F)) * F)⁻¹)

/-- **Lemma 3.1.2** (Bertin), well-definedness ("`F¹` belongs to `ℂ[[z]]`"): the Schur transform
`F¹ = schurTransform F` satisfies the defining relation `z (1 − ā₀ F) · F¹ = F − a₀` whenever
`|a₀| ≠ 1` (here `Complex.normSq a₀ ≠ 1`). So the formal division `(F − a₀)/(z(1 − ā₀ F))` does yield a
genuine power series. Proof: `F¹` is the `z`-shift of `H = (F − a₀)(1 − ā₀ F)⁻¹`, which has zero
constant term, so `z · F¹ = H`; and `(1 − ā₀ F) · H = F − a₀` since `1 − ā₀ F` is invertible. -/
@[category research solved, AMS 30 13, ref "Ber92" "Sch17", formal_uses schurTransform]
theorem schurTransform_spec (F : PowerSeries ℂ) (hF : Complex.normSq (constantCoeff F) ≠ 1) :
    X * (1 - C (starRingEnd ℂ (constantCoeff F)) * F) * schurTransform F
      = F - C (constantCoeff F) := by
  have hH0 : constantCoeff ((F - C (constantCoeff F))
      * (1 - C (starRingEnd ℂ (constantCoeff F)) * F)⁻¹) = 0 := by
    rw [map_mul, map_sub, constantCoeff_C, sub_self, zero_mul]
  have hXsT : X * schurTransform F
      = (F - C (constantCoeff F)) * (1 - C (starRingEnd ℂ (constantCoeff F)) * F)⁻¹ := by
    ext k
    cases k with
    | zero =>
      rw [coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul]
      exact hH0.symm
    | succ k => rw [coeff_succ_X_mul]; simp only [schurTransform, coeff_mk]
  have hDinv : (1 - C (starRingEnd ℂ (constantCoeff F)) * F)
      * (1 - C (starRingEnd ℂ (constantCoeff F)) * F)⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    rw [map_sub, map_one, map_mul, constantCoeff_C, mul_comm, Complex.mul_conj, sub_ne_zero]
    exact fun h => hF (by exact_mod_cast h.symm)
  calc X * (1 - C (starRingEnd ℂ (constantCoeff F)) * F) * schurTransform F
      = (1 - C (starRingEnd ℂ (constantCoeff F)) * F) * (X * schurTransform F) := by ring
    _ = (1 - C (starRingEnd ℂ (constantCoeff F)) * F)
        * ((F - C (constantCoeff F)) * (1 - C (starRingEnd ℂ (constantCoeff F)) * F)⁻¹) := by
          rw [hXsT]
    _ = (F - C (constantCoeff F)) * ((1 - C (starRingEnd ℂ (constantCoeff F)) * F)
        * (1 - C (starRingEnd ℂ (constantCoeff F)) * F)⁻¹) := by ring
    _ = F - C (constantCoeff F) := by rw [hDinv, mul_one]

/-- The Schur transform satisfies `z · F¹ = (F − a₀)(1 − ā₀ F)⁻¹`: the `z`-multiple of `F¹` is the
product whose `z`-shift defines it (the unconditional core of `schurTransform_spec`; used in the
determinant recurrence). -/
@[category API, AMS 30 13, formal_uses schurTransform]
theorem schurTransform_X_mul (F : PowerSeries ℂ) :
    X * schurTransform F
      = (F - C (constantCoeff F)) * (1 - C (starRingEnd ℂ (constantCoeff F)) * F)⁻¹ := by
  have hH0 : constantCoeff ((F - C (constantCoeff F))
      * (1 - C (starRingEnd ℂ (constantCoeff F)) * F)⁻¹) = 0 := by
    rw [map_mul, map_sub, constantCoeff_C, sub_self, zero_mul]
  ext k
  cases k with
  | zero => rw [coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul]; exact hH0.symm
  | succ k => rw [coeff_succ_X_mul]; simp only [schurTransform, coeff_mk]

/-- **Row-collapse for the Schur step.** For any `G ∈ ℂ⟦z⟧`, the order-`(m+2)` determinant
`det(Iₘ₊₂ − (z G)ₘ₊₁ (z G)*ₘ₊₁)` equals the order-`(m+1)` determinant `det(Iₘ₊₁ − Gₘ Gₘ*)`:
multiplying by `z` shifts the lower-triangular Toeplitz matrix down one row, so its top row vanishes;
expanding the determinant along that row (`Matrix.det_succ_row_zero`) drops the dimension by one and
leaves exactly the `G`-determinant. This is the key dimension-reducing step of the Schur determinant
recurrence (Lemma 3.1.2). -/
@[category API, AMS 15 30, formal_uses schurToeplitz]
theorem det_one_sub_schurToeplitz_X_mul (G : PowerSeries ℂ) (m : ℕ) :
    (1 - schurToeplitz (X * G) (m + 1) * (schurToeplitz (X * G) (m + 1))ᴴ).det
      = (1 - schurToeplitz G m * (schurToeplitz G m)ᴴ).det := by
  have hXG0 : constantCoeff (X * G) = 0 := by rw [map_mul, constantCoeff_X, zero_mul]
  have hrow0 : ∀ k, schurToeplitz (X * G) (m + 1) 0 k = 0 := by
    intro k
    simp only [schurToeplitz, Fin.le_def, Fin.val_zero]
    by_cases hk : (k : ℕ) ≤ 0
    · rw [if_pos hk, show (0 : ℕ) - (k : ℕ) = 0 by omega, coeff_zero_eq_constantCoeff, hXG0]
    · rw [if_neg hk]
  have hentry : ∀ (i k : Fin (m + 1)),
      schurToeplitz (X * G) (m + 1) i.succ k.castSucc = schurToeplitz G m i k := by
    intro i k
    simp only [schurToeplitz, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    by_cases hki : (k : ℕ) ≤ (i : ℕ)
    · rw [if_pos (by omega), if_pos hki,
        show (i : ℕ) + 1 - (k : ℕ) = ((i : ℕ) - (k : ℕ)) + 1 by omega, coeff_succ_X_mul]
    · rw [if_neg hki]
      by_cases hki2 : (k : ℕ) ≤ (i : ℕ) + 1
      · rw [if_pos hki2, show (i : ℕ) + 1 - (k : ℕ) = 0 by omega, coeff_zero_eq_constantCoeff, hXG0]
      · rw [if_neg hki2]
  have hlast : ∀ (i : Fin (m + 1)),
      schurToeplitz (X * G) (m + 1) i.succ (Fin.last (m + 1)) = 0 := by
    intro i
    simp only [schurToeplitz, Fin.le_def, Fin.val_succ, Fin.val_last]
    by_cases hi : m + 1 ≤ (i : ℕ) + 1
    · rw [if_pos hi, show (i : ℕ) + 1 - (m + 1) = 0 by omega, coeff_zero_eq_constantCoeff, hXG0]
    · rw [if_neg hi]
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · have h00 : (1 - schurToeplitz (X * G) (m + 1) * (schurToeplitz (X * G) (m + 1))ᴴ) 0 0 = 1 := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply,
        Finset.sum_eq_zero (fun k _ => by rw [hrow0 k, zero_mul]), sub_zero]
    rw [Fin.succAbove_zero]
    simp only [Fin.val_zero, pow_zero, one_mul, h00]
    congr 1
    ext i j
    rw [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.one_apply]
    congr 1
    · simp [Fin.succ_inj]
    · rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hlast i, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, hentry i k, hentry j k]
  · intro j _ hj
    have hMj : (1 - schurToeplitz (X * G) (m + 1) * (schurToeplitz (X * G) (m + 1))ᴴ) 0 j = 0 := by
      rw [Matrix.sub_apply, Matrix.one_apply, if_neg (Ne.symm hj), Matrix.mul_apply,
        Finset.sum_eq_zero (fun k _ => by rw [hrow0 k, zero_mul]), sub_zero]
    rw [hMj, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- **Lemma 3.1.2** (Bertin), the **Schur determinant recurrence**: for `n ≥ 1` and `|a₀| ≠ 1`,
`δₙ(F) = δ₀(F)^{n+1} δ_{n-1}(F¹)` — the order-`n` Schur determinant of `F` reduces to the order-`(n−1)`
determinant of its Schur transform `F¹`. Iterating this is the generalised Schur algorithm: every `δₙ`
is computed from the Schur parameters `δ₀(F), δ₀(F¹), …`.

Proved here in full (Bertin's argument). Writing `Fₙ = schurToeplitz F (m+1)`, `a₀ = F(0)`: the
algebraic identity `(Iₙ₊₁ − ā₀Fₙ)(Iₙ₊₁ − a₀F*ₙ) − (Fₙ − a₀Iₙ₊₁)(F*ₙ − ā₀Iₙ₊₁) =
(1−|a₀|²)(Iₙ₊₁ − FₙF*ₙ)` (verified by `module`) factors, via `Gₙ := (Iₙ₊₁−ā₀Fₙ)⁻¹(Fₙ−a₀Iₙ₊₁)`, into
`(Iₙ₊₁−ā₀Fₙ)(Iₙ₊₁−GₙG*ₙ)(Iₙ₊₁−a₀F*ₙ) = (1−|a₀|²)(Iₙ₊₁−FₙF*ₙ)`. Taking determinants and using
`det(Iₙ₊₁−ā₀Fₙ) = det(Iₙ₊₁−a₀F*ₙ) = (1−|a₀|²)^{n+1}` (`det_schurToeplitz`, lower/upper triangular)
gives `det(Iₙ₊₁−FₙF*ₙ) = (1−|a₀|²)^{n+1} det(Iₙ₊₁−GₙG*ₙ)`. Now `Gₙ = (z F¹)ₙ` (Lemma 3.1.1 a) +
`schurTransform_X_mul`), so `det(Iₙ₊₁−GₙG*ₙ) = δ_{n-1}(F¹)` by `det_one_sub_schurToeplitz_X_mul`; with
`det(Iₙ₊₁−FₙF*ₙ) = δₙ(F)` (Lemma 3.1.1 c) and `δ₀(F) = 1−|a₀|²` (`schurDelta_zero`) the recurrence
follows. -/
@[category research solved, AMS 15 30, ref "Ber92" "Sch17",
  formal_uses schurDelta schurTransform schurToeplitz schurToeplitz_mul schurToeplitz_sub
    schurToeplitz_C schurToeplitz_C_mul schurToeplitz_one schurToeplitzStar_eq_conjTranspose
    schurDelta_eq_det schurDelta_zero det_schurToeplitz schurTransform_X_mul
    det_one_sub_schurToeplitz_X_mul]
theorem schurDelta_recurrence (F : PowerSeries ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hF : Complex.normSq (constantCoeff F) ≠ 1) :
    schurDelta F n = schurDelta F 0 ^ (n + 1) * schurDelta (schurTransform F) (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set a : ℂ := constantCoeff F with ha
  set A : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ := schurToeplitz F (m + 1) with hA
  have hsne : (1 : ℂ) - a * starRingEnd ℂ a ≠ 0 := by
    rw [Complex.mul_conj, sub_ne_zero]; exact fun h => hF (by exact_mod_cast h.symm)
  have hsreal : star ((1 : ℂ) - a * starRingEnd ℂ a) = 1 - a * starRingEnd ℂ a := by
    rw [Complex.mul_conj, star_sub, star_one, Complex.star_def, Complex.conj_ofReal]
  have hs0 : schurDelta F 0 = 1 - a * starRingEnd ℂ a := by
    rw [schurDelta_zero, coeff_zero_eq_constantCoeff, ← ha, ← Complex.mul_conj]
  have hstarA : schurToeplitzStar F (m + 1) = Aᴴ := by rw [hA, schurToeplitzStar_eq_conjTranspose]
  set G : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ :=
    schurToeplitz (X * schurTransform F) (m + 1) with hG
  have hinv : constantCoeff (1 - C (starRingEnd ℂ a) * F) ≠ 0 := by
    rw [map_sub, map_one, map_mul, constantCoeff_C, ← ha, mul_comm, Complex.mul_conj, sub_ne_zero]
    exact fun h => hF (by exact_mod_cast h.symm)
  have hseries : (1 - C (starRingEnd ℂ a) * F) * (X * schurTransform F) = F - C a := by
    rw [schurTransform_X_mul, ← mul_assoc, mul_comm (1 - C (starRingEnd ℂ a) * F) (F - C a),
      mul_assoc, PowerSeries.mul_inv_cancel _ hinv, mul_one]
  have hP : schurToeplitz (1 - C (starRingEnd ℂ a) * F) (m + 1) = 1 - starRingEnd ℂ a • A := by
    rw [schurToeplitz_sub, schurToeplitz_one, schurToeplitz_C_mul, ← hA]
  have hR : schurToeplitz (F - C a) (m + 1) = A - a • 1 := by
    rw [schurToeplitz_sub, schurToeplitz_C, ← hA]
  have hPG : (1 - starRingEnd ℂ a • A) * G = A - a • 1 := by
    rw [← hP, hG, ← schurToeplitz_mul, hseries, hR]
  set X : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ := 1 - starRingEnd ℂ a • A with hX
  set Y : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ := 1 - a • Aᴴ with hY
  have hid : X * Y - (A - a • 1) * (Aᴴ - starRingEnd ℂ a • 1)
      = (1 - a * starRingEnd ℂ a) • (1 - A * Aᴴ) := by
    rw [hX, hY]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  have hYX : Y = Xᴴ := by
    rw [hX, hY, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
      starRingEnd_apply, star_star]
  have hRH : Aᴴ - starRingEnd ℂ a • 1 = Gᴴ * Y := by
    rw [hYX, ← Matrix.conjTranspose_mul, hPG, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, starRingEnd_apply]
  have hfact : X * (1 - G * Gᴴ) * Y = (1 - a * starRingEnd ℂ a) • (1 - A * Aᴴ) := by
    rw [← hid, ← hPG, hRH]; noncomm_ring
  have hdetX : X.det = (1 - a * starRingEnd ℂ a) ^ (m + 1 + 1) := by
    rw [← hP, det_schurToeplitz, coeff_zero_eq_constantCoeff, map_sub, map_one, map_mul,
      constantCoeff_C, ← ha, mul_comm]
  have hdetY : Y.det = (1 - a * starRingEnd ℂ a) ^ (m + 1 + 1) := by
    rw [hYX, Matrix.det_conjTranspose, hdetX, star_pow, hsreal]
  have hδF : schurDelta F (m + 1) = (1 - A * Aᴴ).det := by
    rw [(schurDelta_eq_det F (m + 1)).1, hstarA, ← hA]
  have hδF1 : schurDelta (schurTransform F) m = (1 - G * Gᴴ).det := by
    rw [(schurDelta_eq_det (schurTransform F) m).1, schurToeplitzStar_eq_conjTranspose, hG,
      ← det_one_sub_schurToeplitz_X_mul]
  have hdetfact : (1 - A * Aᴴ).det
      = (1 - a * starRingEnd ℂ a) ^ (m + 1 + 1) * (1 - G * Gᴴ).det := by
    have key := congrArg Matrix.det hfact
    rw [Matrix.det_mul, Matrix.det_mul, hdetX, hdetY, Matrix.det_smul, Fintype.card_fin] at key
    apply mul_left_cancel₀ (pow_ne_zero (m + 1 + 1) hsne)
    rw [← key]; ring
  rw [hδF, hdetfact, hs0, hδF1]

/-! ### Remark 3.1.1 — Schur determinants of `zˢ R` -/

/-- When `F(0) = 0` the Schur transform inverts multiplication by `z`: `schurTransform (z · G) = G`.
This is the `a₀ = 0` case (there `F¹ = F / z`), and the engine of Remark 3.1.1. -/
@[category API, AMS 30 13, formal_uses schurTransform]
theorem schurTransform_X_mul_cancel (G : PowerSeries ℂ) : schurTransform (X * G) = G := by
  have h0 : constantCoeff (X * G) = 0 := by rw [map_mul, constantCoeff_X, zero_mul]
  ext n
  simp only [schurTransform, coeff_mk, h0, map_zero, sub_zero, zero_mul, inv_one, mul_one,
    coeff_succ_X_mul]

/-- The Schur determinant recurrence at `a₀ = 0`: if `F(0) = 0` then `δₙ(F) = δ_{n-1}(F¹)` for `n ≥ 1`
(a single Schur step, with `δ₀(F) = 1`). -/
@[category API, AMS 15 30,
  formal_uses schurDelta schurTransform schurDelta_zero schurDelta_recurrence]
theorem schurDelta_recurrence_zero (F : PowerSeries ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hc : constantCoeff F = 0) :
    schurDelta F n = schurDelta (schurTransform F) (n - 1) := by
  have hF : Complex.normSq (constantCoeff F) ≠ 1 := by rw [hc, Complex.normSq_zero]; norm_num
  rw [schurDelta_recurrence F n hn hF, schurDelta_zero, coeff_zero_eq_constantCoeff, hc,
    Complex.normSq_zero, Complex.ofReal_zero, sub_zero, one_pow, one_mul]

/-- **Remark 3.1.1** (Bertin). If `F = zˢ R` for some `s ∈ ℕ` and `R ∈ ℂ⟦z⟧`, then
`δₙ(F) = δ_{n-s}(R)` for all `n ≥ s`. Proof: apply Lemma 3.1.2 `s` times with `a₀ = 0`
(`schurDelta_recurrence_zero`) — each step strips one factor of `z` (`schurTransform (z·G) = G`,
`schurTransform_X_mul_cancel`) and lowers the order by one. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurDelta schurTransform schurTransform_X_mul_cancel schurDelta_recurrence_zero]
theorem schurDelta_X_pow_mul {F : PowerSeries ℂ} (R : PowerSeries ℂ) (s n : ℕ)
    (hF : F = X ^ s * R) (hns : s ≤ n) :
    schurDelta F n = schurDelta R (n - s) := by
  subst hF
  induction s generalizing n with
  | zero => rw [pow_zero, one_mul, Nat.sub_zero]
  | succ s ih =>
    have hc : constantCoeff (X ^ (s + 1) * R) = 0 := by
      rw [map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul]
    have htr : schurTransform (X ^ (s + 1) * R) = X ^ s * R := by
      rw [pow_succ', mul_assoc, schurTransform_X_mul_cancel]
    rw [schurDelta_recurrence_zero _ n (by omega) hc, htr, ih (n - 1) (by omega)]
    congr 1
    omega

end SchurTransform

/-! ## Lemma 3.1.3 — vanishing of `δₙ(F)` and the reciprocal-polynomial criterion -/

/-- **Lemma 3.1.3** (Bertin). For `F ∈ ℂ⟦z⟧` with `F(0) ≠ 0`, the Schur determinant vanishes,
`δₙ(F) = 0`, **iff** there exist a polynomial `P ∈ ℂ[z]` and `r ∈ ℕ` such that

* **i)** `d°(P) = n − 2r ≥ 0` — encoded as `2 * r ≤ n` (the `≥ 0`) together with
  `P.natDegree = n − 2 * r`;
* **ii)** `ord(F·P − P*) ≥ n + 1 − r` — the power series `F·P − P*` is divisible by `z^{n+1−r}`,
  where `P* = reciprocalC P` is the reciprocal polynomial and `ord = PowerSeries.order`;
* **iii)** `P(0) ≠ 0`.

So the degeneracy `δₙ(F) = 0` is precisely the solvability of the near-self-inversive relation
`F·P ≡ P* (mod z^{n+1−r})` by a polynomial `P` of degree `n − 2r` with nonzero constant term; the
slack `r` measures the rank drop of the `2(n+1)`-block Schur matrix `[Iₙ₊₁ F*ₙ; Fₙ Iₙ₊₁]`.

Bertin proves this — it is **not** an open statement. It is recorded here as a `cited` axiom
(`ref "Ber92"`); the rank/kernel argument relating the vanishing block determinant to the polynomial
`P` is not yet formalised in this corpus. -/
@[category research solved, AMS 15 30 13, ref "Ber92", formal_uses schurDelta reciprocalC]
axiom schurDelta_eq_zero_iff (F : PowerSeries ℂ) (n : ℕ) (hF : PowerSeries.constantCoeff F ≠ 0) :
    schurDelta F n = 0 ↔
      ∃ (P : ℂ[X]) (r : ℕ),
        (2 * r ≤ n ∧ P.natDegree = n - 2 * r) ∧
          ((n + 1 - r : ℕ) : ℕ∞) ≤
              (F * (P : PowerSeries ℂ) - (reciprocalC P : PowerSeries ℂ)).order ∧
          P.eval 0 ≠ 0

/-! ## Lemma 3.1.4 — coprimality of `P, P*` from a run of vanishing Schur determinants -/

/-- **Lemma 3.1.4** (Bertin). Let `F ∈ ℂ⟦z⟧` with `F(0) ≠ 0`. Suppose `δ_{n−1}(F) ≠ 0` and a run of
`k ≥ 1` consecutive Schur determinants vanishes,
`δₙ(F) = δ_{n+1}(F) = ⋯ = δ_{n+k−1}(F) = 0`. Then there is a polynomial `P ∈ ℂ[z]` with

* **i)** `d°(P) = n` and `P(0) ≠ 0`;
* **ii)** `P` and `P* = reciprocalC P` relatively prime (`IsCoprime`), when `n ≠ 0`;
* **iii)** `ord(F·P − P*) ≥ n + 1 + ⌊k/2⌋`.

This refines Lemma 3.1.3 (`schurDelta_eq_zero_iff`) along a maximal vanishing block: the run length
`k` lifts the contact order by `⌊k/2⌋ = k / 2`, while `δ_{n−1} ≠ 0` pins the degree to exactly `n`
(the `r = 0` case of 3.1.3) and yields the coprimality of `P` and `P*`. At `k = 1` it is precisely
Lemma 3.1.3 with `r = 0`.

Encoding notes: the equality chain `δₙ = ⋯ = δ_{n+k−1}` is the run of zeros `∀ j < k, δ_{n+j}(F) = 0`
— forced to terminate in `= 0`, since the `k = 1` instance must reduce to 3.1.3's `δₙ(F) = 0`. The
hypothesis `δ_{n−1}(F) ≠ 0` is guarded as `1 ≤ n → δ_{n−1}(F) ≠ 0`: for `n = 0` Bertin reads `δ_{−1}`
as the empty determinant `1 ≠ 0` (consistent with the `n ≠ 0` guard on ii). `⌊k/2⌋` is natural-number
division `k / 2`.

Bertin proves this; it is recorded here as a `cited` axiom (`ref "Ber92"`) — the proof (continuing the
rank analysis of 3.1.3 across the vanishing block) is not yet formalised in this corpus. -/
@[category research solved, AMS 12 15 30 13, ref "Ber92", formal_uses schurDelta reciprocalC]
axiom exists_poly_of_schurDelta_run
    (F : PowerSeries ℂ) (n k : ℕ) (hk : 1 ≤ k)
    (hF : PowerSeries.constantCoeff F ≠ 0)
    (hprev : 1 ≤ n → schurDelta F (n - 1) ≠ 0)
    (hrun : ∀ j : ℕ, j < k → schurDelta F (n + j) = 0) :
    ∃ P : ℂ[X],
      (P.natDegree = n ∧ P.eval 0 ≠ 0) ∧
        (n ≠ 0 → IsCoprime P (reciprocalC P)) ∧
          ((n + 1 + k / 2 : ℕ) : ℕ∞) ≤
            (F * (P : PowerSeries ℂ) - (reciprocalC P : PowerSeries ℂ)).order

/-! ## Theorem 3.1.1 — `F = zʳ P*/P` and the Schur-determinant vanishing pattern

The proof follows Bertin. By Remark 3.1.1 (`schurDelta_X_pow_mul`) one reduces to `F(0) ≠ 0`; the
two directions are then Lemmas 3.1.4 (sufficient) and 3.1.3 (necessary). The supporting algebra of the
reciprocal polynomial and the degree-padding device `Qᵢ = (1+z)ⁱP` is developed first. -/

section Theorem311
open PowerSeries

/-- `reciprocalC` sends `1` to `1` (`reverse` and conjugation both fix constants). -/
@[category API, AMS 12, formal_uses reciprocalC]
theorem reciprocalC_one : reciprocalC (1 : ℂ[X]) = 1 := by
  rw [reciprocalC, ← Polynomial.C_1, Polynomial.reverse_C, Polynomial.map_C]; simp

/-- `reciprocalC` is multiplicative on `ℂ[z]` (a domain): `(P·Q)* = P*·Q*`. -/
@[category API, AMS 12, formal_uses reciprocalC]
theorem reciprocalC_mul (P Q : ℂ[X]) : reciprocalC (P * Q) = reciprocalC P * reciprocalC Q := by
  rw [reciprocalC, reciprocalC, reciprocalC, Polynomial.reverse_mul_of_domain, Polynomial.map_mul]

/-- `reciprocalC` commutes with powers: `(Pⁱ)* = (P*)ⁱ`. -/
@[category API, AMS 12, formal_uses reciprocalC]
theorem reciprocalC_pow (P : ℂ[X]) (i : ℕ) : reciprocalC (P ^ i) = reciprocalC P ^ i := by
  induction i with
  | zero => rw [pow_zero, pow_zero, reciprocalC_one]
  | succ k ih => rw [pow_succ, pow_succ, reciprocalC_mul, ih]

/-- `1 + z` is self-reciprocal: `(1+z)* = 1+z`. The degree-padding multiplier in Bertin's proof. -/
@[category API, AMS 12, formal_uses reciprocalC]
theorem reciprocalC_X_add_one : reciprocalC (1 + Polynomial.X) = 1 + Polynomial.X := by
  have hrev : (1 + Polynomial.X : ℂ[X]).reverse = 1 + Polynomial.X := by
    ext i
    rw [Polynomial.coeff_reverse]
    have hdeg : (1 + Polynomial.X : ℂ[X]).natDegree = 1 := by
      rw [show (1 + Polynomial.X : ℂ[X]) = Polynomial.X + Polynomial.C 1 by rw [Polynomial.C_1]; ring]
      exact Polynomial.natDegree_X_add_C _
    rw [hdeg]
    match i with
    | 0 => simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
    | 1 => simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
    | (k + 2) => simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
  rw [reciprocalC, hrev]; simp

/-- **Heart of Theorem 3.1.1, necessary direction** (Bertin's `Qᵢ` device). If `G(0) ≠ 0`,
`P(0) ≠ 0` and `G·P = P*` (i.e. `G = P*/P`), then `δₘ(G) = 0` for every `m ≥ d°(P)`. For `m = n₀ + i`
the padded polynomial `Qᵢ = (1+z)ⁱP` has degree `m`, `Qᵢ(0) ≠ 0`, and `G·Qᵢ − Qᵢ* = (1+z)ⁱ(G·P − P*)
= 0`, so the `r = 0` instance of Lemma 3.1.3 (`schurDelta_eq_zero_iff`) forces `δₘ(G) = 0`. -/
@[category API, AMS 15 30, formal_uses schurDelta reciprocalC schurDelta_eq_zero_iff]
theorem schurDelta_eq_zero_of_mul_eq_reciprocalC {G : PowerSeries ℂ} {P : ℂ[X]}
    (hG : PowerSeries.constantCoeff G ≠ 0) (hP0 : P.eval 0 ≠ 0)
    (hGP : G * (P : PowerSeries ℂ) = (reciprocalC P : PowerSeries ℂ))
    {m : ℕ} (hm : P.natDegree ≤ m) : schurDelta G m = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, m = P.natDegree + i := ⟨m - P.natDegree, by omega⟩
  have hdegX1 : (1 + Polynomial.X : ℂ[X]).natDegree = 1 := by
    rw [show (1 + Polynomial.X : ℂ[X]) = Polynomial.X + Polynomial.C 1 by rw [Polynomial.C_1]; ring]
    exact Polynomial.natDegree_X_add_C _
  have hX1 : (1 + Polynomial.X : ℂ[X]) ≠ 0 := by intro h; rw [h] at hdegX1; simp at hdegX1
  have hPne : P ≠ 0 := fun h => hP0 (by rw [h, Polynomial.eval_zero])
  have hQstar : reciprocalC ((1 + Polynomial.X) ^ i * P) = (1 + Polynomial.X) ^ i * reciprocalC P := by
    rw [reciprocalC_mul, reciprocalC_pow, reciprocalC_X_add_one]
  have key : G * (((1 + Polynomial.X) ^ i * P : ℂ[X]) : PowerSeries ℂ)
      - (reciprocalC ((1 + Polynomial.X) ^ i * P) : PowerSeries ℂ) = 0 := by
    rw [hQstar]
    simp only [Polynomial.coe_mul, Polynomial.coe_pow]
    set u : PowerSeries ℂ := ((1 + Polynomial.X : ℂ[X]) : PowerSeries ℂ)
    rw [show G * (u ^ i * (P : PowerSeries ℂ)) - u ^ i * (reciprocalC P : PowerSeries ℂ)
          = u ^ i * (G * (P : PowerSeries ℂ) - (reciprocalC P : PowerSeries ℂ)) from by ring,
        hGP, sub_self, mul_zero]
  rw [schurDelta_eq_zero_iff G (P.natDegree + i) hG]
  refine ⟨(1 + Polynomial.X) ^ i * P, 0, ⟨by omega, ?_⟩, ?_, ?_⟩
  · rw [Polynomial.natDegree_mul (pow_ne_zero i hX1) hPne, Polynomial.natDegree_pow, hdegX1]; omega
  · rw [key, PowerSeries.order_zero]; exact le_top
  · rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_X, add_zero, one_pow, one_mul]
    exact hP0

/-- Order extraction: a nonzero power series factors as `F = zʳ · R` with `R(0) ≠ 0` and
`r = ord F`. -/
@[category API, AMS 13]
theorem exists_eq_X_pow_mul (F : PowerSeries ℂ) (hF : F ≠ 0) :
    ∃ (r : ℕ) (R : PowerSeries ℂ), F = X ^ r * R ∧ PowerSeries.constantCoeff R ≠ 0 := by
  have hord : F.order ≠ ⊤ := fun h => hF (PowerSeries.order_eq_top.mp h)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hord
  obtain ⟨hco, hlt⟩ := PowerSeries.order_eq_nat.mp hn.symm
  refine ⟨n, mk fun k => PowerSeries.coeff (n + k) F, ?_, ?_⟩
  · ext m
    rw [PowerSeries.coeff_X_pow_mul']
    by_cases h : n ≤ m
    · rw [if_pos h, coeff_mk, Nat.add_sub_cancel' h]
    · rw [if_neg h]; exact hlt m (by omega)
  · rw [← coeff_zero_eq_constantCoeff, coeff_mk]; simpa using hco

/-- If the first `m + 1` coefficients of `F` vanish, both Schur–Toeplitz matrices of order `m + 1` are
zero, so `δₘ(F) = det [I 0; 0 I] = 1`. Handles the `n₀ = 0` edge of Theorem 3.1.1 (`F = zʳ·const`). -/
@[category API, AMS 15, formal_uses schurDelta schurToeplitz schurToeplitzStar]
theorem schurDelta_eq_one_of_coeff_eq_zero (F : PowerSeries ℂ) (m : ℕ)
    (h : ∀ k ≤ m, PowerSeries.coeff k F = 0) : schurDelta F m = 1 := by
  have hT : schurToeplitz F m = 0 := by
    ext i j
    simp only [schurToeplitz, Matrix.zero_apply]
    split
    · exact h _ (le_trans (Nat.sub_le _ _) i.is_le)
    · rfl
  have hTs : schurToeplitzStar F m = 0 := by
    ext i j
    simp only [schurToeplitzStar, Matrix.zero_apply]
    split
    · rw [h _ (le_trans (Nat.sub_le _ _) j.is_le), map_zero]
    · rfl
  rw [schurDelta, hT, hTs, Matrix.fromBlocks_one, Matrix.det_one]

/-- **Infinite-run form of Lemma 3.1.4** (Bertin's "by Lemma 3.1.4" in the proof of Theorem 3.1.1a).
If `G(0) ≠ 0`, `δ_{n₀−1}(G) ≠ 0` (guarded) and `δₘ(G) = 0` for all `m ≥ n₀`, there is `P ∈ ℂ[z]` of
degree `n₀`, `P(0) ≠ 0`, `P` and `P*` coprime, with `G · P = P*` (i.e. `G = P*/P`). This is Lemma
3.1.4 in the limit `k → ∞`: the contact order `n₀ + 1 + ⌊k/2⌋ → ∞` forces `G · P = P*`. Recorded as a
`cited` axiom alongside 3.1.4, whose stabilization step it makes precise. -/
@[category research solved, AMS 15 30 12, ref "Ber92",
  formal_uses schurDelta reciprocalC exists_poly_of_schurDelta_run]
axiom exists_poly_mul_eq_reciprocalC_of_schurDelta_eventually_zero
    (G : PowerSeries ℂ) (n₀ : ℕ) (hG : PowerSeries.constantCoeff G ≠ 0)
    (hprev : 1 ≤ n₀ → schurDelta G (n₀ - 1) ≠ 0)
    (hrun : ∀ m, n₀ ≤ m → schurDelta G m = 0) :
    ∃ P : ℂ[X], P.natDegree = n₀ ∧ P.eval 0 ≠ 0 ∧ IsCoprime P (reciprocalC P) ∧
      G * (P : PowerSeries ℂ) = (reciprocalC P : PowerSeries ℂ)

/-- **Sharpness for Theorem 3.1.1, necessary direction.** If `G(0) ≠ 0`, `G·P = P*` with `P(0) ≠ 0`,
`P, P*` coprime, and `d°(P) = n₀ ≥ 1`, then `δ_{n₀−1}(G) ≠ 0`. By contradiction: were it zero, then
(with `δₘ(G) = 0 ∀ m ≥ n₀`) the determinants vanish from a sharp index `thr ≤ n₀−1`, so the
infinite-run lemma yields `G = S*/S` with `d°S = thr < n₀`; cross-multiplying `P*·S = S*·P` and using
coprimality of `P, P*` forces `P ∣ S`, impossible for `0 ≠ S` of smaller degree. -/
@[category API, AMS 15 30 12,
  formal_uses schurDelta reciprocalC schurDelta_eq_zero_of_mul_eq_reciprocalC
    exists_poly_mul_eq_reciprocalC_of_schurDelta_eventually_zero]
theorem schurDelta_ne_zero_of_mul_eq_reciprocalC {G : PowerSeries ℂ} {P : ℂ[X]}
    (hG : PowerSeries.constantCoeff G ≠ 0) (hP0 : P.eval 0 ≠ 0)
    (hcop : IsCoprime P (reciprocalC P))
    (hGP : G * (P : PowerSeries ℂ) = (reciprocalC P : PowerSeries ℂ))
    (hn₀ : 1 ≤ P.natDegree) : schurDelta G (P.natDegree - 1) ≠ 0 := by
  intro hzero
  classical
  have hrun_all : ∀ m, P.natDegree - 1 ≤ m → schurDelta G m = 0 := by
    intro m hm
    rcases eq_or_lt_of_le hm with h | h
    · rw [← h]; exact hzero
    · exact schurDelta_eq_zero_of_mul_eq_reciprocalC hG hP0 hGP (by omega)
  have hex : ∃ t, ∀ m, t ≤ m → schurDelta G m = 0 := ⟨P.natDegree - 1, hrun_all⟩
  have hthr_spec : ∀ m, Nat.find hex ≤ m → schurDelta G m = 0 := Nat.find_spec hex
  have hthr_le : Nat.find hex ≤ P.natDegree - 1 := Nat.find_le hrun_all
  have hprev : 1 ≤ Nat.find hex → schurDelta G (Nat.find hex - 1) ≠ 0 := by
    intro h1 hc
    refine Nat.find_min hex (m := Nat.find hex - 1) (by omega) (fun m hm => ?_)
    rcases eq_or_lt_of_le hm with h | h
    · rw [← h]; exact hc
    · exact hthr_spec m (by omega)
  obtain ⟨S, hSdeg, hS0, _, hGS⟩ :=
    exists_poly_mul_eq_reciprocalC_of_schurDelta_eventually_zero G (Nat.find hex) hG hprev hthr_spec
  have hSne : S ≠ 0 := fun h => hS0 (by rw [h, Polynomial.eval_zero])
  have hcross : reciprocalC P * S = reciprocalC S * P := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hGP, ← hGS]; ring
  have hPdvd : P ∣ S :=
    hcop.dvd_of_dvd_mul_left ⟨reciprocalC S, by rw [hcross]; ring⟩
  have := Polynomial.natDegree_le_of_dvd hPdvd hSne
  omega

/-- **Theorem 3.1.1 for `F(0) ≠ 0`** (the `r = 0` core): `G = P*/P` with `P(0) ≠ 0` and `P, P*`
coprime, iff the Schur determinants vanish from a sharp index `n₀ = d°(P)` onward. The forward
direction is `schurDelta_eq_zero_of_mul_eq_reciprocalC` (the `Qᵢ` device) and
`schurDelta_ne_zero_of_mul_eq_reciprocalC` (sharpness); the converse is the cited infinite-run lemma. -/
@[category research solved, AMS 15 30 12, ref "Ber92",
  formal_uses schurDelta reciprocalC schurDelta_eq_zero_of_mul_eq_reciprocalC
    schurDelta_ne_zero_of_mul_eq_reciprocalC
    exists_poly_mul_eq_reciprocalC_of_schurDelta_eventually_zero]
theorem schurDelta_core_iff {G : PowerSeries ℂ} (hG : PowerSeries.constantCoeff G ≠ 0) :
    (∃ P : ℂ[X], G * (P : PowerSeries ℂ) = (reciprocalC P : PowerSeries ℂ) ∧
        P.eval 0 ≠ 0 ∧ IsCoprime P (reciprocalC P)) ↔
      (∃ n₀ : ℕ, (∀ m, n₀ ≤ m → schurDelta G m = 0) ∧ (1 ≤ n₀ → schurDelta G (n₀ - 1) ≠ 0)) := by
  constructor
  · rintro ⟨P, hGP, hP0, hcop⟩
    exact ⟨P.natDegree, fun m hm => schurDelta_eq_zero_of_mul_eq_reciprocalC hG hP0 hGP hm,
      fun _ => schurDelta_ne_zero_of_mul_eq_reciprocalC hG hP0 hcop hGP ‹_›⟩
  · rintro ⟨n₀, hrun, hprev⟩
    obtain ⟨P, _, hP0, hcop, hGP⟩ :=
      exists_poly_mul_eq_reciprocalC_of_schurDelta_eventually_zero G n₀ hG hprev hrun
    exact ⟨P, hGP, hP0, hcop⟩

/-! ## Theorem 3.1.1 — `F = zʳ P*/P` and the Schur-determinant vanishing pattern -/

/-- **Theorem 3.1.1** (Bertin), the capstone of §3.1. For `F ∈ ℂ⟦z⟧` the following are equivalent:

* `F = zʳ · P*/P` for some `r ∈ ℕ` and `P ∈ ℂ[z]` with `P(0) ≠ 0`, `P` and `P* = reciprocalC P`
  relatively prime, and `d°(P) = n₀` — i.e. `F` is `zʳ` times a self-inversive rational function;
* the Schur determinants vanish from a sharp index onward: `δₙ(F) = 0` for all `n ≥ n₀ + r`, and
  `δ_{n₀+r−1}(F) ≠ 0`.

Via Remark 3.1.1 (`schurDelta_X_pow_mul`) the `zʳ` factor strips off (`δₙ(F) = δ_{n−r}(P*/P)`),
reducing the statement to the `F(0) ≠ 0` case — the content of Lemmas 3.1.3 (`schurDelta_eq_zero_iff`)
and 3.1.4 (`exists_poly_of_schurDelta_run`): the infinite vanishing run `δ_{n₀+r} = δ_{n₀+r+1} = ⋯ = 0`
produces, in the limit, a polynomial `P` with `F·P = P*` exactly, while `δ_{n₀+r−1} ≠ 0` pins the degree
and forces coprimality.

Encoding notes: both sides are existentials over `r, n₀` (with `n₀ = d°(P)` on the left); the iff
relates their solvability — the math makes the witnesses coincide (`r = ord F`, `n₀ = d°(P)`). `P*/P`
is `(reciprocalC P : ℂ⟦z⟧) * (P : ℂ⟦z⟧)⁻¹`, a genuine power series since `P(0) ≠ 0`. The edge
hypothesis `δ_{n₀+r−1}(F) ≠ 0` is guarded by `1 ≤ n₀ + r`, as at `n₀ = r = 0` Bertin reads `δ_{−1}` as
the empty determinant `1 ≠ 0`.

Proved here, following Bertin: by Remark 3.1.1 the `zʳ` factor reduces to the `F(0) ≠ 0` core
(`schurDelta_core_iff`), whose forward direction is the `Qᵢ = (1+z)ⁱP` device
(`schurDelta_eq_zero_of_mul_eq_reciprocalC`) together with the sharpness lemma
(`schurDelta_ne_zero_of_mul_eq_reciprocalC`), and whose converse is the (cited) infinite-run form of
Lemma 3.1.4. The theorem is thus proved *modulo* Lemma 3.1.3 (`schurDelta_eq_zero_iff`) and the cited
infinite-run lemma — `#print axioms` lists exactly those two alongside the standard
`propext`/`Classical.choice`/`Quot.sound`. -/
@[category research solved, AMS 12 15 30 13, ref "Ber92",
  formal_uses schurDelta reciprocalC schurDelta_core_iff schurDelta_eq_zero_of_mul_eq_reciprocalC
    schurDelta_ne_zero_of_mul_eq_reciprocalC schurDelta_X_pow_mul exists_eq_X_pow_mul
    schurDelta_eq_one_of_coeff_eq_zero]
theorem eq_X_pow_mul_reciprocalC_div_iff (F : PowerSeries ℂ) :
    (∃ (r n₀ : ℕ) (P : ℂ[X]),
        F = PowerSeries.X ^ r * (reciprocalC P : PowerSeries ℂ) * (P : PowerSeries ℂ)⁻¹ ∧
          P.eval 0 ≠ 0 ∧ IsCoprime P (reciprocalC P) ∧ P.natDegree = n₀) ↔
      (∃ (r n₀ : ℕ),
        (∀ n, n₀ + r ≤ n → schurDelta F n = 0) ∧
          (1 ≤ n₀ + r → schurDelta F (n₀ + r - 1) ≠ 0)) := by
  constructor
  · rintro ⟨r, n₀, P, hF, hP0, hcop, rfl⟩
    have hPc : PowerSeries.constantCoeff (P : PowerSeries ℂ) ≠ 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe,
        Polynomial.coeff_zero_eq_eval_zero]
      exact hP0
    set G : PowerSeries ℂ := (reciprocalC P : PowerSeries ℂ) * (P : PowerSeries ℂ)⁻¹ with hGdef
    have hFG : F = PowerSeries.X ^ r * G := by rw [hF, hGdef]; ring
    have hGP : G * (P : PowerSeries ℂ) = (reciprocalC P : PowerSeries ℂ) := by
      rw [hGdef, mul_assoc, PowerSeries.inv_mul_cancel _ hPc, mul_one]
    have hPstar : PowerSeries.constantCoeff (reciprocalC P : PowerSeries ℂ) ≠ 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe]
      have hc0 : (reciprocalC P).coeff 0 = starRingEnd ℂ P.leadingCoeff := by
        rw [reciprocalC, Polynomial.coeff_map, Polynomial.coeff_reverse,
          Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero, Polynomial.leadingCoeff]
      rw [hc0, ne_eq, starRingEnd_apply, star_eq_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => hP0 (by rw [h, Polynomial.eval_zero]))
    have hGc : PowerSeries.constantCoeff G ≠ 0 := by
      intro h; apply hPstar; rw [← hGP, map_mul, h, zero_mul]
    refine ⟨r, P.natDegree, ?_, ?_⟩
    · intro n hn
      rw [schurDelta_X_pow_mul G r n hFG (by omega)]
      exact schurDelta_eq_zero_of_mul_eq_reciprocalC hGc hP0 hGP (by omega)
    · intro h1
      by_cases hd : 1 ≤ P.natDegree
      · rw [schurDelta_X_pow_mul G r (P.natDegree + r - 1) hFG (by omega),
          show P.natDegree + r - 1 - r = P.natDegree - 1 from by omega]
        exact schurDelta_ne_zero_of_mul_eq_reciprocalC hGc hP0 hcop hGP hd
      · have hn0 : P.natDegree = 0 := by omega
        have hco : ∀ k ≤ P.natDegree + r - 1, PowerSeries.coeff k F = 0 := by
          intro k hk
          rw [hFG, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [schurDelta_eq_one_of_coeff_eq_zero F (P.natDegree + r - 1) hco]
        exact one_ne_zero
  · rintro ⟨r, n₀, hrun, hprev⟩
    have hFne : F ≠ 0 := by
      intro h
      have h0 := hrun (n₀ + r) le_rfl
      rw [h, schurDelta_eq_one_of_coeff_eq_zero 0 (n₀ + r) (fun k _ => by simp)] at h0
      exact one_ne_zero h0
    obtain ⟨r', R, hFR, hR0⟩ := exists_eq_X_pow_mul F hFne
    have hr'le : r' ≤ n₀ + r := by
      by_contra hlt
      push Not at hlt
      have h1 : schurDelta F (n₀ + r) = 1 := by
        apply schurDelta_eq_one_of_coeff_eq_zero
        intro k hk
        rw [hFR, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
      rw [hrun (n₀ + r) le_rfl] at h1
      exact zero_ne_one h1
    have hrunR : ∀ m, n₀ + r - r' ≤ m → schurDelta R m = 0 := by
      intro m hm
      have hh := hrun (m + r') (by omega)
      rwa [schurDelta_X_pow_mul R r' (m + r') hFR (by omega), Nat.add_sub_cancel] at hh
    have hprevR : 1 ≤ n₀ + r - r' → schurDelta R (n₀ + r - r' - 1) ≠ 0 := by
      intro hge
      have hne := hprev (by omega)
      rw [schurDelta_X_pow_mul R r' (n₀ + r - 1) hFR (by omega),
        show n₀ + r - 1 - r' = n₀ + r - r' - 1 from by omega] at hne
      exact hne
    obtain ⟨P, hRP, hP0, hcop⟩ := (schurDelta_core_iff hR0).mpr ⟨n₀ + r - r', hrunR, hprevR⟩
    have hPc : PowerSeries.constantCoeff (P : PowerSeries ℂ) ≠ 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe,
        Polynomial.coeff_zero_eq_eval_zero]
      exact hP0
    refine ⟨r', P.natDegree, P, ?_, hP0, hcop, rfl⟩
    have hR : R = (reciprocalC P : PowerSeries ℂ) * (P : PowerSeries ℂ)⁻¹ := by
      rw [← hRP, mul_assoc, PowerSeries.mul_inv_cancel _ hPc, mul_one]
    rw [hFR, hR]; ring

end Theorem311

/-! ## Lemma 3.2.1 — iterated transforms, convergents, and the iterated determinant formula

Bertin's **Lemma 3.2.1** for `F` with `δ₀(F), …, δₙ(F)` nonzero. Parts a) and c) are proved here by
iterating §3.1's `schurDelta_recurrence`; part b) (the Schur–Wall continued-fraction convergents) is a
`cited` axiom. See the module docstring for the statement breakdown. -/

section Lemma321
open PowerSeries

/-- The **rank-`i` reciprocal-conjugate** `Ã(z) = zⁱ Ā(1/z)` of `A ∈ ℂ[z]`: reverse the coefficients
around rank `i` (`Polynomial.reflect i`, zero-padding when `d°A < i`) and conjugate. The degree-`i`
refinement of `reciprocalC`, used for the convergents `Aᵢ, Qᵢ` of Bertin's **Lemma 3.2.1**. -/
@[category API, AMS 12 30, ref "Ber92"]
noncomputable def reciprocalAt (i : ℕ) (P : ℂ[X]) : ℂ[X] := (P.reflect i).map (starRingEnd ℂ)

/-- `reciprocalAt (d°P) P = P*`: at rank `natDegree` the rank-`i` reciprocal-conjugate is the
reciprocal polynomial `reciprocalC` of §3.1 (since `Polynomial.reverse = reflect natDegree`). -/
@[category API, AMS 12, ref "Ber92", formal_uses reciprocalAt reciprocalC]
theorem reciprocalAt_natDegree (P : ℂ[X]) : reciprocalAt P.natDegree P = reciprocalC P := by
  rw [reciprocalAt, reciprocalC, Polynomial.reverse]

/-- The first Schur parameter is nonzero iff `|a₀| ≠ 1`: `δ₀(F) = 1 − |a₀|² ≠ 0 ↔ |a₀|² ≠ 1`. Bridges
the determinant hypotheses of Lemma 3.2.1 to the `Complex.normSq … ≠ 1` form consumed by
`schurTransform_spec`/`schurDelta_recurrence`. -/
@[category API, AMS 30, ref "Ber92", formal_uses schurDelta]
theorem schurDelta_zero_ne_zero_iff (F : PowerSeries ℂ) :
    schurDelta F 0 ≠ 0 ↔ Complex.normSq (constantCoeff F) ≠ 1 := by
  rw [schurDelta_zero, coeff_zero_eq_constantCoeff, sub_ne_zero, ne_comm, ne_eq, ne_eq,
    Complex.ofReal_eq_one]

/-- `ωᵢ = ∏_{k=0}^{i} δ₀(Fᵏ) = ∏_{k=0}^{i}(1 − |γₖ|²)`, the product of the first `i + 1` Schur
parameters (`γₖ = Fᵏ(0)`); the leading factor of the Wronskian identity in Lemma 3.2.1 b). -/
@[category API, AMS 30, ref "Ber92", formal_uses schurDelta schurTransform]
noncomputable def schurOmega (F : PowerSeries ℂ) (i : ℕ) : ℂ :=
  ∏ k ∈ Finset.range (i + 1), schurDelta (schurTransform^[k] F) 0

/-- **Lemma 3.2.1 a)** (Bertin): if `δ₀(F), …, δₙ(F)` are all nonzero, the Schur transforms are
defined up to rank `n + 1` — `δ₀(Fᵏ) ≠ 0` for every `k ≤ n`, so each of `F¹, …, F^{n+1}` is a genuine
power series. **Proved**: induction on `n`, passing `δ_{j+1}(F) = δ₀(F)^{j+2} δ_j(F¹)` down to `F¹`. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurDelta schurTransform schurDelta_recurrence schurDelta_zero_ne_zero_iff]
theorem schurDelta_zero_iterate_ne_zero (F : PowerSeries ℂ) (n : ℕ)
    (hδ : ∀ i ≤ n, schurDelta F i ≠ 0) : ∀ k ≤ n, schurDelta (schurTransform^[k] F) 0 ≠ 0 := by
  induction n generalizing F with
  | zero => intro k hk; obtain rfl : k = 0 := Nat.le_zero.mp hk; simpa using hδ 0 le_rfl
  | succ m ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simpa using hδ 0 (by omega)
    · have hF0 : Complex.normSq (constantCoeff F) ≠ 1 :=
        (schurDelta_zero_ne_zero_iff F).mp (hδ 0 (by omega))
      have hδ' : ∀ j ≤ m, schurDelta (schurTransform F) j ≠ 0 := by
        intro j hj
        have hrec := schurDelta_recurrence F (j + 1) (by omega) hF0
        have hne := hδ (j + 1) (by omega)
        rw [hrec, Nat.add_sub_cancel] at hne
        exact right_ne_zero_of_mul hne
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have := ih (schurTransform F) hδ' k' (by omega)
      rwa [← Function.iterate_succ_apply] at this

/-- **Lemma 3.2.1 b)** (Bertin): the continued-fraction **convergents**. For `F` with
`δ₀(F), …, δₙ(F)` nonzero and each `i ≤ n`, there exist `Aᵢ, Qᵢ ∈ ℂ[z]` with `d°Aᵢ, d°Qᵢ ≤ i`,
`Qᵢ(0) = 1`, the continued-fraction relation `F·(Qᵢ + z Ãᵢ F^{i+1}) = Aᵢ + z Q̃ᵢ F^{i+1}`
(`~ = reciprocalAt i`), the Wronskian identity `Qᵢ Q̃ᵢ − Aᵢ Ãᵢ = ωᵢ zⁱ` (`ωᵢ = schurOmega F i`), and
the approximation order `ord(F·Qᵢ − Aᵢ) ≥ i + 1` with `(i+1)`-th coefficient `ωᵢ γᵢ₊₁`. The Schur–Wall
convergent/Wronskian construction is recorded as a `cited` axiom (`ref "Ber92"`) pending a full
formalization. -/
@[category research solved, AMS 12 15 30 13, ref "Ber92",
  formal_uses schurDelta schurTransform reciprocalAt schurOmega]
axiom exists_convergents (F : PowerSeries ℂ) (n : ℕ) (hδ : ∀ i ≤ n, schurDelta F i ≠ 0) :
    ∀ i ≤ n, ∃ A Q : ℂ[X],
      (A.natDegree ≤ i ∧ Q.natDegree ≤ i ∧ Q.eval 0 = 1) ∧
      F * ((Q : PowerSeries ℂ) + X * (reciprocalAt i A : PowerSeries ℂ) * schurTransform^[i + 1] F)
          = (A : PowerSeries ℂ) + X * (reciprocalAt i Q : PowerSeries ℂ) * schurTransform^[i + 1] F ∧
      Q * reciprocalAt i Q - A * reciprocalAt i A = Polynomial.C (schurOmega F i) * Polynomial.X ^ i ∧
      ((i + 1 : ℕ) : ℕ∞) ≤ (F * (Q : PowerSeries ℂ) - (A : PowerSeries ℂ)).order ∧
      coeff (i + 1) (F * (Q : PowerSeries ℂ) - (A : PowerSeries ℂ))
          = schurOmega F i * constantCoeff (schurTransform^[i + 1] F)

/-- **Lemma 3.2.1 c)** (Bertin): the **iterated Schur-determinant formula**. For `F` with
`δ₀(F), …, δₙ(F)` nonzero, `δ_{n+k}(F) = ∏_{j<n} δ₀(Fʲ)^{(n−j)+(k+1)} · δₖ(Fⁿ)` for every `k`.
**Proved** by iterating `schurDelta_recurrence` `n` times. The exponent `(n−j)+(k+1) = n+k+1−j` runs
`n+k+1, …, k+2` (Bertin prints the final one as `k+1`; the recurrence forces `k+2`). -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurDelta schurTransform schurDelta_recurrence schurDelta_zero_ne_zero_iff]
theorem schurDelta_add_eq_iterate_prod (F : PowerSeries ℂ) (n : ℕ)
    (hδ : ∀ i ≤ n, schurDelta F i ≠ 0) (k : ℕ) :
    schurDelta F (n + k)
      = (∏ j ∈ Finset.range n, schurDelta (schurTransform^[j] F) 0 ^ ((n - j) + (k + 1)))
          * schurDelta (schurTransform^[n] F) k := by
  induction n generalizing F k with
  | zero => simp
  | succ m ih =>
    have hF0 : Complex.normSq (constantCoeff F) ≠ 1 :=
      (schurDelta_zero_ne_zero_iff F).mp (hδ 0 (by omega))
    have hδ' : ∀ i ≤ m, schurDelta (schurTransform F) i ≠ 0 := by
      intro i hi
      have hrec := schurDelta_recurrence F (i + 1) (by omega) hF0
      have hne := hδ (i + 1) (by omega)
      rw [hrec, Nat.add_sub_cancel] at hne
      exact right_ne_zero_of_mul hne
    rw [schurDelta_recurrence F (m + 1 + k) (by omega) hF0,
      show m + 1 + k - 1 = m + k from by omega, ih (schurTransform F) hδ' k,
      Finset.prod_range_succ']
    simp only [← Function.iterate_succ_apply, Function.iterate_zero_apply, Nat.add_sub_add_right,
      Nat.sub_zero]
    ring

/-- `ω₀ = δ₀(F)`: the one-factor Schur-parameter product is the first parameter. -/
@[category API, AMS 30 13, ref "Ber92", formal_uses schurOmega schurDelta]
theorem schurOmega_zero (F : PowerSeries ℂ) : schurOmega F 0 = schurDelta F 0 := by
  unfold schurOmega; rw [Finset.prod_range_one, Function.iterate_zero_apply]

/-- `ωₙ₊₁ = ωₙ · δ₀(Fⁿ⁺¹)`: peel the **last** Schur parameter (drives the monotonicity of `ωₙ`). -/
@[category API, AMS 30 13, ref "Ber92", formal_uses schurOmega schurDelta schurTransform]
theorem schurOmega_succ (F : PowerSeries ℂ) (n : ℕ) :
    schurOmega F (n + 1) = schurOmega F n * schurDelta (schurTransform^[n + 1] F) 0 := by
  unfold schurOmega; rw [Finset.prod_range_succ]

/-- `ωₙ₊₁ = ωₙ(F¹) · δ₀(F)`: peel the **first** Schur parameter (drives the ratio identity). -/
@[category API, AMS 30 13, ref "Ber92", formal_uses schurOmega schurDelta schurTransform]
theorem schurOmega_succ' (F : PowerSeries ℂ) (n : ℕ) :
    schurOmega F (n + 1) = schurOmega (schurTransform F) n * schurDelta F 0 := by
  unfold schurOmega; rw [Finset.prod_range_succ']
  simp only [← Function.iterate_succ_apply, Function.iterate_zero_apply]

/-- The **ratio identity** behind Bertin's Corollary 3.2.1: `δₙ₊₁(F) = ωₙ₊₁ · δₙ(F)`, where
`ωₙ₊₁ = schurOmega F (n+1) = ∏_{k≤n+1} δ₀(Fᵏ)`. So when `δₙ(F) ≠ 0`, `ωₙ₊₁ = δₙ₊₁(F)/δₙ(F)` —
Bertin's `ωₙ = δₙ(f)/δ_{n-1}(f)`. **Proved** by induction, from `schurDelta_recurrence` (Lemma 3.1.2)
and `schurOmega_succ'`. -/
@[category research solved, AMS 15 30 13, ref "Ber92",
  formal_uses schurDelta schurOmega schurTransform schurDelta_recurrence schurDelta_zero_ne_zero_iff
    schurOmega_succ' schurOmega_zero]
theorem schurDelta_succ_eq_schurOmega_mul (F : PowerSeries ℂ) (n : ℕ)
    (hδ : ∀ i ≤ n + 1, schurDelta F i ≠ 0) :
    schurDelta F (n + 1) = schurOmega F (n + 1) * schurDelta F n := by
  induction n generalizing F with
  | zero =>
    have hF0 : Complex.normSq (constantCoeff F) ≠ 1 :=
      (schurDelta_zero_ne_zero_iff F).mp (hδ 0 (by omega))
    rw [schurDelta_recurrence F (0 + 1) (by omega) hF0, schurOmega_succ' F 0, schurOmega_zero]
    simp only [Nat.add_sub_cancel]; ring
  | succ n ih =>
    have hF0 : Complex.normSq (constantCoeff F) ≠ 1 :=
      (schurDelta_zero_ne_zero_iff F).mp (hδ 0 (by omega))
    have hδ' : ∀ i ≤ n + 1, schurDelta (schurTransform F) i ≠ 0 := by
      intro i hi
      have hrec := schurDelta_recurrence F (i + 1) (by omega) hF0
      have hne := hδ (i + 1) (by omega)
      rw [hrec, Nat.add_sub_cancel] at hne; exact right_ne_zero_of_mul hne
    rw [schurDelta_recurrence F (n + 1 + 1) (by omega) hF0, Nat.add_sub_cancel,
      ih (schurTransform F) hδ', schurOmega_succ' F (n + 1),
      schurDelta_recurrence F (n + 1) (by omega) hF0, Nat.add_sub_cancel]; ring

end Lemma321
