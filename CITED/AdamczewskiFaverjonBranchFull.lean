/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonMahlerAmbient
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] Lemma 2.8, with everything it owes the assembly

plan-formalize-AF17's **WP20**, and the **second cited axiom of Stage 2**.

`CITED/AdamczewskiFaverjonBranchExistence.lean` states the interface `AF.IsAnalyticBranch` and
derives Step (UB) from it; this file states the existence.  The statement being cited is unchanged:

*«**Lemma 2.8.** Let `φ(z) ∈ GLₘ(A)` be a relation matrix.  Then the three following properties
hold for `k ≫ 1`: (a) the point `α^{q^k}` belongs to the disc of convergence of each of the
functions `f₁(z), …, f_m(z)`; (b) each coordinate of `φ(z)` defines an analytic function on some
neighborhood of `α^{q^k}`; (c) the matrix `φ(α^{q^k})` is invertible.»*

What has changed since rev. 20 is how much of it the corpus needs.  rev. 20 cited (b) and (c) only,
because Step (UB) was the consumer; the assembly of gap (6) consumes the *same object* four more
times, and rev. 21, 24 and 26 each pinned one of those uses.  Every one of them is a property
[AF22]'s realization — «an algebraic function, or a convergent series, goes to its analytic branch
at `ξ`» — has by construction, so folding them in keeps Stage 2 at **two** cited axioms rather than
five.  This is the decision recorded at rev. 21 for the evaluation homomorphism and extended at
rev. 24 and rev. 26.

## The five clauses, and what each is for

1. `AF.IsAnalyticBranch` — (b) and (c), the original citation.  Step (UB).
2. `IsPreconnected U` — the identity principle of WP16 needs a *connected* domain to spread «zero
   near `ξ`» to «zero on `U`».  [AF22] take a disc; any connected neighbourhood will do.
3. `AF.IsSolutionRealization` — item **(a)**.  The Mahler solutions lie in the same subring `R` and
   are realized by the analytic functions `fs` they sum to.  Without this the reverse transport of
   WP16 cannot identify the two sides: `AF.IsBranchRealization` carries `K[z]` and the relation
   matrix and nothing else.
4. `AF.IsAnalyticRealization` and injectivity of `real` — also WP16.  Injectivity is *not* free:
   `AF.not_isField_of_mem` shows that `R` is never a field, so the usual «a ring map out of a field
   is injective» is unavailable.  It is true of [AF22]'s realization for the honest reason that a
   non-zero algebraic function has a non-zero branch.
5. A branch of the **twisted** matrix `φ(z^{q^{k₀}})` at `φ(α)`, with the *same* `Φ₀`.  This is
   gap (5): §2.4 never evaluates `φ` at `ξ`, it evaluates `φ(z^{q^{k₀}})` at `α`, and those are the
   same numbers, `Ψ'(φ α) = Ψ((φ α)^{q^{k₀}}) = Ψ(ξ) = φ(Φ₀)`.  Sharing `Φ₀` is therefore not an
   extra assumption but the content of the identity — which is why the clause is stated for *every*
   `s` implementing the substitution on `K(z)` rather than for one chosen `s`: the axiom needs no
   hypothesis about `s` at all.

## The hypotheses, audited

* **`[IsAlgClosed K]`** is used for exactly one thing: the conclusion `Φ₀.map φ = Ψ ξ` with `Φ₀` a
  matrix over `K`.  The value at an algebraic point of a function algebraic over `K(z)` is algebraic
  over `K`, so it lies in `φ(K)` *when `K` is algebraically closed* — [AF22]'s `K` is `ℚ̄`.  Without
  it Lemma 2.8(c)'s normalizing matrix `a = A_{k₀}(α)φ(ξ)⁻¹` would not be defined over `K`, which is
  what Step (AF)'s substitution `Y ↦ MY` needs.

* **The algebraicity hypothesis is on the entries of `Φalg`, not on `Ω`** — the difference between a
  true statement and a false one.  If `Ω` is relatively algebraically closed in a field of Puiseux
  series then for *every* `ξ` it contains `√(z-ξ)`, which has no analytic branch at `ξ`; no
  realization of all of `Ω` exists anywhere.  Only finitely many elements may be realized at once,
  which is why the interface is a `Subring` and the hypothesis reads
  `∀ i j, IsIntegral (RatFunc K) (Φalg i j)` — exactly the extra conclusion
  `AF.exists_relationMatrix_algebraic` carries.

* **`α ≠ 0`, `‖φ α‖ < 1` and `2 ≤ q`** are what make «for `k ≫ 1`» meaningful: the points
  `ξ_k = φ(α)^{q^k}` then have strictly decreasing moduli, so they are pairwise distinct, all but
  finitely many of them avoid any fixed finite bad set, and all but finitely many lie in the disc of
  convergence — which is item (a).  With `q = 1` the sequence is constant and the statement is false
  at a bad `ξ`.

* **`Φalg.det ≠ 0`** is the `GLₘ(A)` of the quoted statement, half of `AF.IsRelationMatrix`.  The
  relation ideal is *not* a hypothesis: Lemma 2.8 knows nothing about `𝓘`.

* **The solutions enter only through `hr0` and `hsum`.**  The system itself is not assumed: item (a)
  is a statement about the radius of convergence, and `AF.IsSeriesSumOn r φ (f i) (fs i)` is that
  radius, named.  `Ω` is asked to be a `K⸨z⸩`-algebra so that the solutions have a home in it
  (`AF.toAmbientSeries`); this is [AF22]'s own §2.2, where `A` contains the Puiseux series.

## Why this is still an axiom

Mathlib has none of the three ingredients of the four-line literature proof: no vanishing criterion
for the resultant (`Polynomial.resultant` exists with its formal API only), hence no «finitely many
singularities»; no field of convergent power series and no Newton–Puiseux theorem, hence no way to
*produce* a branch; and no analytic implicit function theorem for algebraic function elements —
WP8's `AF.exists_analytic_branch` gives a branch through one non-critical root of one bivariate
polynomial, which is the local half, but not the global «all but finitely many `ξ`» statement that
makes «for `k ≫ 1`» true.  This is plan risk **R14**.

`AF.exists_isAnalyticBranch_one` exhibits a model of clause 1, so the interface is satisfiable and
the axiom is not contradictory in shape.

## Contents

* **`AF.lemma_2_8`** — the axiom;
* `AF.lemma_2_8_branch` — its first clause alone, in the shape
  `AF.eventually_exists_isAnalyticBranch` consumes.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.2.3 (Lemma 2.8), §2.3.2, §2.4.
* [AF17f] `plans/plan-formalize-AF17.html`: §2.17, risk R14, WP20, milestone M4.
-/

open Filter Topology

open scoped Polynomial LaurentSeries RatFunc

namespace AF

/-! ## The cited axiom -/

section Axiom

/-- **[AF22] Lemma 2.8 — the branch-existence axiom, with the four clauses the assembly needs.**
*«Let `φ(z) ∈ GLₘ(A)` be a relation matrix.  Then for `k ≫ 1`: (a) `α^{q^k}` belongs to the disc of
convergence of each `f_i`; (b) each coordinate of `φ(z)` defines an analytic function on some
neighborhood of `α^{q^k}`; (c) the matrix `φ(α^{q^k})` is invertible.»*

The abstract ambient field of the corpus has no functions in it, so «defines an analytic function
near `ξ`» becomes: the subring generated by `K[z]`, the entries and the solutions admits a
homomorphism into the germs of complex functions along `𝓟 U`, realizing polynomials by polynomial
functions, the entries by an analytic `Ψ` and the solutions by their sums.  The five clauses of the
conclusion are taken apart in the module doc, as are the hypotheses; the two that are easy to get
wrong are `[IsAlgClosed K]` and the algebraicity being required of the *entries* rather than of `Ω`.

The last clause is stated for an arbitrary `s` implementing the substitution `z ↦ z^{q^{k₀}}` on
`K(z)`, so that the axiom assumes nothing about `s`: the twisted matrix `φ(z^{q^{k₀}})` takes at
`α` the value `φ` takes at `ξ`, which is why `Φ₀` is shared. -/
@[category research solved, AMS 11 12 14 30, ref "AF22", group "af_mahler_alternative"]
axiom lemma_2_8 {K : Type*} [Field K] [IsAlgClosed K] {Ω : Type*} [Field Ω]
    [Algebra (LaurentSeries K) Ω] [Algebra (RatFunc K) Ω]
    [IsScalarTower (RatFunc K) (LaurentSeries K) Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* ℂ) {α : K}
    (hα0 : α ≠ 0) (hα1 : ‖φ α‖ < 1) {q : ℕ} (hq : 2 ≤ q) {Φalg : Matrix ι ι Ω}
    (halg : ∀ i j, IsIntegral (RatFunc K) (Φalg i j)) (hdet : Φalg.det ≠ 0)
    {r : ℝ} (hr0 : 0 < r) {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ}
    (hsum : ∀ i, IsSeriesSumOn r φ (f i) (fs i)) :
    ∀ᶠ k₀ in atTop, ∃ (U : Set ℂ) (R : Subring Ω) (real : R →+* Germ (𝓟 U) ℂ)
      (Ψ : ℂ → Matrix ι ι ℂ) (Φ₀ : Matrix ι ι K),
      IsAnalyticBranch φ Φalg (φ α ^ q ^ k₀) U R real Ψ Φ₀ ∧ IsPreconnected U ∧
      IsSolutionRealization (𝓟 U) (fun i => toAmbientSeries K Ω (f i)) R real fs ∧
      IsAnalyticRealization U R real ∧ Function.Injective real ∧
      ∀ s : Ω →+* Ω, (∀ (hn : 0 < q ^ k₀) (c : RatFunc K),
          s (algebraMap (RatFunc K) Ω c) = algebraMap (RatFunc K) Ω (substPowRat K hn c)) →
        ∃ (V : Set ℂ) (R' : Subring Ω) (real' : R' →+* Germ (𝓟 V) ℂ) (Ψ' : ℂ → Matrix ι ι ℂ),
          IsAnalyticBranch φ (Matrix.of fun l j => s (Φalg l j)) (φ α) V R' real' Ψ' Φ₀

end Axiom

/-! ## The first clause, alone -/

section Branch

variable {K : Type*} [Field K] [IsAlgClosed K] {Ω : Type*} [Field Ω]
  [Algebra (LaurentSeries K) Ω] [Algebra (RatFunc K) Ω]
  [IsScalarTower (RatFunc K) (LaurentSeries K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma 2.8(b,c) alone — the hypothesis `hax` of `AF.eventually_exists_isAnalyticBranch`, which is
how Step (UB) sees the axiom. -/
@[category research solved, AMS 11 12 30, ref "AF22", group "af_mahler_alternative"]
theorem lemma_2_8_branch (φ : K →+* ℂ) {α : K} (hα0 : α ≠ 0) (hα1 : ‖φ α‖ < 1) {q : ℕ}
    (hq : 2 ≤ q) {Φalg : Matrix ι ι Ω} (halg : ∀ i j, IsIntegral (RatFunc K) (Φalg i j))
    (hdet : Φalg.det ≠ 0) {r : ℝ} (hr0 : 0 < r) {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ}
    (hsum : ∀ i, IsSeriesSumOn r φ (f i) (fs i)) :
    ∀ᶠ k₀ in atTop, ∃ (U : Set ℂ) (R : Subring Ω) (real : R →+* Germ (𝓟 U) ℂ)
      (Ψ : ℂ → Matrix ι ι ℂ) (Φ₀ : Matrix ι ι K),
      IsAnalyticBranch φ Φalg (φ α ^ q ^ k₀) U R real Ψ Φ₀ :=
  (lemma_2_8 φ hα0 hα1 hq halg hdet hr0 hsum).mono fun _ h => by
    obtain ⟨U, R, real, Ψ, Φ₀, hb, -⟩ := h
    exact ⟨U, R, real, Ψ, Φ₀, hb⟩

end Branch

end AF
