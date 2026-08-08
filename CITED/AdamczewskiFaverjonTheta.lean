/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonAssembly
import CITED.AdamczewskiFaverjonUpperBound
import Mathlib.Analysis.Analytic.Polynomial
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] §2.3.1–§2.3.2: the matrices `Θ_k(z)` and the analytic reading of (2.6)

The first half of plan-formalize-AF17's **WP11**, the *analytic instantiation layer*: everything
in `CITED/AdamczewskiFaverjonAssembly` and below lives at the level of **values** in a number
field and of **abstract** extensions of `K(z)`, and what is missing between it and [AF22] Theorem
2.1 is the layer that reads those objects as **functions** on a disc.  This file builds that
layer's matrix half.

## What is here

* the evaluation of a matrix of polynomials at a point (`AF.evalMat`) and its behaviour under a
  ring homomorphism of the coefficients (`AF.mapMat`) — the passage `K → ℂ` along an embedding,
  which is what lets the analytic estimates of Step (UB) and the height estimates of Step (LB)
  speak about the same number;
* the **iterated Mahler relation** `f(z) = A_k(z)f(z^{q^k})` (`AF.isMahlerSolution_iterMatrix`),
  and with it [AF22]'s **(2.6)** — `F(Y A_k(z), z^{q^k}) = F(Y,z)` — as an identity of analytic
  functions (`AF.formVal_mul_evalMat_iterMatrix`);
* **the matrices `Θ_k(z)`** of [AF22] (2.9) (`AF.theta`), their analyticity on any disc where the
  relation matrix is analytic (`AF.analyticAt_theta`), and the identity `Θ_k(ξ) = A_k(α)`
  (`AF.theta_center`) that makes the whole scheme work;
* the **growth bound** `‖A_k(z)‖ ≤ C^k` on a disc of radius `≤ 1` (`AF.norm_evalMat_iterMatrix_le`)
  — the fact behind the remark in `CITED/AdamczewskiFaverjonUpperBound` that `Θ_k` grows like
  `C^k` and not like `e^{γq^k}`, which is what makes the maximum-modulus route to Step (UB) work;
* the **value bridge** `𝔈_k(ξ) = E(A_k(α), α^{q^k})` (`AF.eval_theta_center`), the identity that
  lets Step (UB)'s analytic bound and Step (LB)'s Liouville bound be applied to one and the same
  algebraic number;
* the **evaluation at `α`** (`AF.hspec_of_evalHom`): what a homomorphism «evaluate at `α`» on the
  subring of the ambient field where it makes sense has to satisfy in order to discharge the one
  analytic hypothesis `hspec` of the endgame `AF.exists_lift`, and the derivation from it.

## Two simplifications over the printed proof

**No shrinking discs.**  [AF22]'s Remark 2.10 has to shrink `D(ξ,r₂)` to `D(ξ,r_k)` as `k` grows,
because their Mahler matrix has entries in `Q̄(z)` and `A(z^{q^j})` acquires poles.  Every Mahler
matrix in this corpus is *polynomial* — see `AF.lemme_4_1_of_polynomial` for why that costs
nothing — so `A_{k-k₀}(z)` is entire and `Θ_k` is analytic on the *fixed* disc where the relation
matrix is.  The bound `‖A_k(z)‖ ≤ C^k` is the quantitative form of the same remark.

**No matrix inverse.**  [AF22] define `Θ_k(z) := A_{k₀}(α)φ(α^{q^{k₀}})^{-1}φ(z)A_{k-k₀}(z)`, so
that `Θ_k(ξ) = A_k(α)` uses `φ(ξ)^{-1}φ(ξ) = 1`.  Here the left factor is an arbitrary matrix `a`
subject to the hypothesis `a·Φ(ξ) = A_{k₀}(α)`, which is all the proof ever uses; invertibility of
`Φ(ξ)` — [AF22] Lemma 2.8(c) — is what *provides* such an `a`, and is not needed again.  This is
the same economy as `AF.relation_subst` in the assembly, which needs only a left inverse.

## What this file does not do

The identity `E_p(Θ_k(z), z^{q^{k-k₀}}) = 0` of [AF22] Lemma 2.12 — the vanishing of the truncated
auxiliary function along the analytic branch — is *not* proved here.  It is the transport of
Lemma 2.7, an identity in the ambient field of algebraic functions, along the realization of that
field as germs of analytic functions at `ξ`; the corpus's ambient field is abstract (see
`CITED/AdamczewskiFaverjonPrimitive`), so the transport is an interface, not a theorem.  It is
carried as a hypothesis in `CITED/AdamczewskiFaverjonAnalyticUB`, together with the choice of a
non-critical `k₀` (plan risk **R14**: Mathlib has no vanishing criterion for the resultant, so
[AF22]'s «for `k ≫ 1`» in Lemma 2.8 cannot be proved, and is used — as they use it — as a
hypothesis on one good `k₀`).

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3.1 ((2.6), (2.7)) and §2.3.2 ((2.8), (2.9), Remark 2.10).
* [AF17f] `plans/plan-formalize-AF17.html`: WP11, risk R14, milestone M4.
-/

open Filter Metric Topology MvPolynomial
open scoped Polynomial

namespace AF

/-! ## Matrices of polynomials, evaluated and transported -/

section EvalMat

variable {R S : Type*} [CommRing R] [CommRing S] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Entrywise evaluation of a matrix of polynomials.**  `A_k(z)` of [AF22], as a matrix of
numbers.  Packaged as the image of a ring homomorphism so that `evalMat z (M*N)` splits without
further ado. -/
@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def evalMat (z : R) (M : Matrix ι ι R[X]) : Matrix ι ι R :=
  (Polynomial.evalRingHom z).mapMatrix M

@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem evalMat_apply (z : R) (M : Matrix ι ι R[X]) (i j : ι) :
    evalMat z M i j = (M i j).eval z := rfl

@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem evalMat_one (z : R) : evalMat z (1 : Matrix ι ι R[X]) = 1 := map_one _

@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem evalMat_mul (z : R) (M N : Matrix ι ι R[X]) :
    evalMat z (M * N) = evalMat z M * evalMat z N := map_mul _ _ _

/-- **Transport of a matrix of polynomials along a ring homomorphism of the coefficients.**  The
embedding `K → ℂ` of Step (UB) applied to the Mahler matrix. -/
@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def mapMat (φ : R →+* S) (M : Matrix ι ι R[X]) : Matrix ι ι S[X] :=
  (Polynomial.mapRingHom φ).mapMatrix M

@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem mapMat_apply (φ : R →+* S) (M : Matrix ι ι R[X]) (i j : ι) :
    mapMat φ M i j = (M i j).map φ := rfl

/-- Evaluating the transported matrix at the transported point is transporting the value. -/
@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem evalMat_mapMat (φ : R →+* S) (z : R) (M : Matrix ι ι R[X]) :
    evalMat (φ z) (mapMat φ M) = (evalMat z M).map φ := by
  ext i j
  rw [evalMat_apply, mapMat_apply, Matrix.map_apply, evalMat_apply, Polynomial.eval_map,
    Polynomial.eval₂_hom]

end EvalMat

/-! ## The iterated matrix, at a point -/

section IterMat

variable {K L : Type*} [Field K] [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem evalMat_map_substPow (q : ℕ) (z : K) (M : Matrix ι ι K[X]) :
    evalMat z (M.map (substPow K q)) = evalMat (z ^ q) M := by
  ext i j
  rw [evalMat_apply, Matrix.map_apply, substPow_eval, evalMat_apply]

/-- **The cocycle identity at a point**: `A_{k+l}(α) = A_l(α)·A_k(α^{q^l})`.  With `l = k₀` this is
what makes `Θ_k(ξ) = A_k(α)` in [AF22] (2.9). -/
@[category research solved, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem evalMat_iterMatrix_add (q : ℕ) (A : Matrix ι ι K[X]) (α : K) (k l : ℕ) :
    evalMat α (iterMatrix q A (k + l)) =
      evalMat α (iterMatrix q A l) * evalMat (α ^ q ^ l) (iterMatrix q A k) := by
  rw [iterMatrix_add, evalMat_mul, evalMat_map_substPow]

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem map_substPow (φ : K →+* L) (q : ℕ) (p : K[X]) :
    (substPow K q p).map φ = substPow L q (p.map φ) := by
  simp only [substPow_eq_expand]
  exact Polynomial.map_expand

/-- The iterated matrix commutes with a coefficient homomorphism: `A_k` computed over `ℂ` from the
transported `A` is the transport of `A_k`. -/
@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem mapMat_iterMatrix (φ : K →+* L) (q : ℕ) (A : Matrix ι ι K[X]) (k : ℕ) :
    mapMat φ (iterMatrix q A k) = iterMatrix q (mapMat φ A) k := by
  induction k with
  | zero =>
      ext i j
      rw [iterMatrix_zero, iterMatrix_zero, mapMat_apply]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ n ih =>
      ext i j
      rw [iterMatrix_succ, iterMatrix_succ, ← ih]
      simp only [mapMat_apply, Matrix.mul_apply, Matrix.map_apply, Polynomial.map_sum,
        Polynomial.map_mul, map_substPow]

end IterMat

/-! ## The Mahler relation, iterated -/

section Mahler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] (2.1) iterated**: a solution of `f(z) = A(z)f(z^q)` on a set stable under `z ↦ z^q`
satisfies `f(z) = A_k(z)f(z^{q^k})` for every `k`. -/
@[category research solved, AMS 11 39, ref "AF22", group "af_mahler_alternative"]
theorem isMahlerSolution_iterMatrix {q : ℕ} {A : Matrix ι ι ℂ[X]} {f : ι → ℂ → ℂ} {S : Set ℂ}
    (hS : ∀ z ∈ S, z ^ q ∈ S) (hf : IsMahlerSolution q A f S) (k : ℕ) :
    ∀ z ∈ S, ∀ i, f i z = ∑ j, (iterMatrix q A k i j).eval z * f j (z ^ q ^ k) := by
  induction k with
  | zero =>
      intro z _ i
      simp [iterMatrix_zero, Matrix.one_apply, apply_ite (Polynomial.eval z), Finset.sum_ite_eq]
  | succ n ih =>
      intro z hz i
      have h1 : f i z = ∑ l, (A i l).eval z * f l (z ^ q) := by
        have := hf z hz i
        simpa using this
      rw [h1]
      have h2 : ∀ l, f l (z ^ q) = ∑ j, (iterMatrix q A n l j).eval (z ^ q) * f j (z ^ q ^ (n + 1)) := by
        intro l
        have := ih (z ^ q) (hS z hz) l
        rwa [← pow_mul, ← pow_succ'] at this
      calc ∑ l, (A i l).eval z * f l (z ^ q)
          = ∑ l, ∑ j, (A i l).eval z * ((iterMatrix q A n l j).eval (z ^ q) *
              f j (z ^ q ^ (n + 1))) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [h2 l, Finset.mul_sum]
        _ = ∑ j, (iterMatrix q A (n + 1) i j).eval z * f j (z ^ q ^ (n + 1)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [iterMatrix_succ, Matrix.mul_apply, Polynomial.eval_finsetSum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Polynomial.eval_mul, Matrix.map_apply, substPow_eval]
            ring

/-- **The linear form `F(Y,z) = τ Y f(z)` of [AF22] §2.3**, as a function of a complex matrix and
a complex point. -/
@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def formVal (τ : ι → ℂ) (f : ι → ℂ → ℂ) (M : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  ∑ i, ∑ j, τ i * M i j * f j z

/-- **[AF22] (2.6), analytically**: `F(Y·A_k(z), z^{q^k}) = F(Y,z)`.

This is the identity that makes the whole scheme run: the auxiliary function is built from powers
of `F`, and (2.6) is what turns a statement about `F(Θ_k(z), z^{q^{k-k₀}})` into one about the
`k`-independent function `F(Θ_{k₀}(z), z)`. -/
@[category research solved, AMS 11 39, ref "AF22", group "af_mahler_alternative"]
theorem formVal_mul_evalMat_iterMatrix {q : ℕ} {A : Matrix ι ι ℂ[X]} {f : ι → ℂ → ℂ} {S : Set ℂ}
    (hS : ∀ z ∈ S, z ^ q ∈ S) (hf : IsMahlerSolution q A f S) (τ : ι → ℂ) (M : Matrix ι ι ℂ)
    (k : ℕ) {z : ℂ} (hz : z ∈ S) :
    formVal τ f (M * evalMat z (iterMatrix q A k)) (z ^ q ^ k) = formVal τ f M z := by
  have hiter := isMahlerSolution_iterMatrix hS hf k z hz
  simp only [formVal, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hiter l, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [evalMat_apply]
  ring

end Mahler

/-! ## The matrices `Θ_k(z)` -/

section Theta

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] (2.9)**: `Θ_k(z) := a·Φ(z)·A_{k-k₀}(z)`, where `Φ` is a relation matrix read as a
matrix of analytic functions near `ξ = α^{q^{k₀}}` and `a` is any matrix with `a·Φ(ξ) = A_{k₀}(α)`
— [AF22] take `a = A_{k₀}(α)Φ(ξ)^{-1}`, which exists by their Lemma 2.8(c). -/
@[category API, AMS 11 15 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def theta (q k₀ : ℕ) (A : Matrix ι ι ℂ[X]) (a : Matrix ι ι ℂ)
    (Φ : ℂ → Matrix ι ι ℂ) (k : ℕ) (z : ℂ) : Matrix ι ι ℂ :=
  a * Φ z * evalMat z (iterMatrix q A (k - k₀))

/-- **`Θ_k(ξ) = A_k(α)`** — [AF22] (2.9).  The one place where the choice of `a` is used, and the
reason the whole analytic construction is about the *algebraic* numbers `A_k(α)`. -/
@[category research solved, AMS 11 15 30, ref "AF22", group "af_mahler_alternative"]
theorem theta_center {q k₀ k : ℕ} (hk : k₀ ≤ k) {A : Matrix ι ι ℂ[X]} {a : Matrix ι ι ℂ}
    {Φ : ℂ → Matrix ι ι ℂ} {α ξ : ℂ} (hξ : ξ = α ^ q ^ k₀)
    (ha : a * Φ ξ = evalMat α (iterMatrix q A k₀)) :
    theta q k₀ A a Φ k ξ = evalMat α (iterMatrix q A k) := by
  rw [theta, ha, hξ, ← evalMat_iterMatrix_add, Nat.sub_add_cancel hk]

/-- Every entry of `Θ_k` is analytic wherever the entries of the relation matrix are: the other
two factors are constant and polynomial.  This is [AF22]'s Remark 2.10, *without* the shrinking
discs — their `A(z^{q^j})` has poles, ours is a polynomial. -/
@[category research solved, AMS 15 30, ref "AF22", group "af_mahler_alternative"]
theorem analyticAt_theta {q k₀ k : ℕ} {A : Matrix ι ι ℂ[X]} {a : Matrix ι ι ℂ}
    {Φ : ℂ → Matrix ι ι ℂ} {z₀ : ℂ} (hΦ : ∀ i j, AnalyticAt ℂ (fun z => Φ z i j) z₀) (i j : ι) :
    AnalyticAt ℂ (fun z => theta q k₀ A a Φ k z i j) z₀ := by
  have hpoly : ∀ p : ℂ[X], AnalyticAt ℂ (fun z : ℂ => p.eval z) z₀ := by
    intro p
    simpa using (analyticAt_id : AnalyticAt ℂ id z₀).aeval_polynomial p
  have hentry : ∀ l : ι, AnalyticAt ℂ (fun z => ∑ m, a i m * Φ z m l) z₀ := fun l =>
    Finset.analyticAt_fun_sum _ fun m _ => analyticAt_const.mul (hΦ m l)
  simp only [theta, Matrix.mul_apply, evalMat_apply]
  exact Finset.analyticAt_fun_sum _ fun l _ => (hentry l).mul (hpoly _)

end Theta

/-! ## Growth of the iterated matrix on a disc of radius `≤ 1` -/

section Growth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`‖A_k(z)‖ ≤ C^k` on a disc of radius `≤ 1`.**

[AF22] bound the Taylor coefficients of `Θ_k` by `e^{γ q^k}` — their (2.30) — and that estimate is
an artefact of expanding in powers of `z - ξ`.  The *values* of `A_k(z)` on a disc of radius `≤ 1`
grow only geometrically, because `A_k(z) = A(z)A(z^q)⋯A(z^{q^{k-1}})` is a product of `k` factors
each evaluated **inside the same disc**: `|z| ≤ t ≤ 1` implies `|z^{q^j}| ≤ t`.  This is what makes
the maximum-modulus route of `CITED/AdamczewskiFaverjonUpperBound` work, and it is why no Taylor
coefficient of `Θ_k` ever has to be estimated. -/
@[category research solved, AMS 15 30, ref "AF22", group "af_mahler_alternative"]
theorem norm_evalMat_iterMatrix_le {q : ℕ} (hq : 1 ≤ q) {A : Matrix ι ι ℂ[X]} {t C : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hC1 : 1 ≤ C)
    (hA : ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(A i j).eval z‖ ≤ C) (k : ℕ) :
    ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(iterMatrix q A k i j).eval z‖ ≤ ((Fintype.card ι : ℝ) * C) ^ k := by
  have hstable : ∀ z : ℂ, ‖z‖ ≤ t → ‖z ^ q‖ ≤ t := by
    intro z hz
    rw [norm_pow]
    calc ‖z‖ ^ q ≤ t ^ q := by gcongr
      _ ≤ t ^ 1 := pow_le_pow_of_le_one ht0 ht1 hq
      _ = t := pow_one t
  induction k with
  | zero =>
      intro z _ i j
      rw [iterMatrix_zero]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ n ih =>
      intro z hz i j
      rw [iterMatrix_succ, Matrix.mul_apply, Polynomial.eval_finsetSum]
      calc ‖∑ l, ((A i l) * ((iterMatrix q A n).map (substPow ℂ q) l j)).eval z‖
          ≤ ∑ l : ι, ‖((A i l) * ((iterMatrix q A n).map (substPow ℂ q) l j)).eval z‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _l : ι, C * ((Fintype.card ι : ℝ) * C) ^ n := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [Polynomial.eval_mul, norm_mul, Matrix.map_apply, substPow_eval]
            exact mul_le_mul (hA z hz i l) (ih (z ^ q) (hstable z hz) l j) (norm_nonneg _)
              (le_trans zero_le_one hC1)
        _ = (Fintype.card ι : ℝ) * (C * ((Fintype.card ι : ℝ) * C) ^ n) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ((Fintype.card ι : ℝ) * C) ^ (n + 1) := by ring

end Growth

/-! ## The value bridge: `𝔈_k(ξ) = E(A_k(α), α^{q^k})` -/

section Bridge

variable {K L : Type*} [Field K] [Field L] {σ : Type*}

/-- Evaluation at the `n`-th point commutes with a homomorphism of the coefficient field. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem map_evalAt (φ : K →+* L) (pt : ℕ → K) (Yval : ℕ → σ → K) (n : ℕ)
    (P : MvPolynomial σ K[X]) :
    φ (evalAt pt Yval n P) =
      evalAt (fun n => φ (pt n)) (fun n s => φ (Yval n s)) n
        (MvPolynomial.map (Polynomial.mapRingHom φ) P) := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      rw [MvPolynomial.map_C, evalAt, evalAt, eval₂Hom_C, eval₂Hom_C]
      show φ (p.eval (pt n)) = (p.map φ).eval (φ (pt n))
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p s hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.map_X]; simp [evalAt]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The value bridge.**  At the centre `ξ = φ(α)^{q^{k₀}}` the analytic evaluation of a
polynomial at `(Θ_k(z), z^{q^{k-k₀}})` is the image under `φ` of its value at the algebraic point
`(A_k(α), α^{q^k})`.

This is the identity `𝔈_k(ξ) = E(A_k(α),α^{q^k})` on which the whole proof of Lemma 2.11 turns:
the left-hand side is what Step (UB) bounds above by the maximum-modulus principle, the right-hand
side is what Step (LB) bounds below by Liouville's inequality, and `AF.key_lemma_of_auxiliary`
puts the two together. -/
@[category research solved, AMS 11 15 30, ref "AF22", group "af_mahler_alternative"]
theorem eval_theta_center {q k₀ k : ℕ} (hk : k₀ ≤ k) {A : Matrix ι ι K[X]} {α : K}
    (φ : K →+* ℂ) {a : Matrix ι ι ℂ} {Φ : ℂ → Matrix ι ι ℂ} {ξ : ℂ} (hξ : ξ = φ α ^ q ^ k₀)
    (ha : a * Φ ξ = evalMat (φ α) (iterMatrix q (mapMat φ A) k₀))
    (P : MvPolynomial (ι × ι) K[X]) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom (ξ ^ q ^ (k - k₀)))
        (fun s => theta q k₀ (mapMat φ A) a Φ k ξ s.1 s.2)
        (MvPolynomial.map (Polynomial.mapRingHom φ) P) =
      φ (evalAt (fun k => α ^ q ^ k) (fun k s => (iterMatrix q A k s.1 s.2).eval α) k P) := by
  have hpt : ξ ^ q ^ (k - k₀) = φ (α ^ q ^ k) := by
    rw [hξ, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hk, map_pow]
  have hY : theta q k₀ (mapMat φ A) a Φ k ξ =
      (evalMat α (iterMatrix q A k)).map φ := by
    rw [theta_center hk hξ ha, ← mapMat_iterMatrix, evalMat_mapMat]
  rw [map_evalAt φ]
  rw [evalAt]
  rw [hpt, hY]
  rfl

end Bridge

/-! ## The evaluation at `α`, and the hypothesis `hspec` of the endgame -/

section EvalHom

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω] {ι : Type*}

/-- **The evaluation homomorphism at `α` discharges `hspec`.**

`AF.exists_lift` — the last step of [AF22] §2.4 — takes as its one analytic hypothesis the
*specialization* `hspec`: that the decomposition (2.36) of the coefficient row, evaluated at `α`,
returns the coefficients of the original linear form up to the factor `d(α)`.  Here is what has
to be supplied for it, and the derivation from it.

Suppose some subring `R` of the ambient field carries a ring homomorphism `ev : R → K` — this is
[AF22]'s «`ϕ(z^{q^{k₀}})` is analytic at `α`, and `d(α)q(α) ≠ 0`», i.e. evaluation at `α` of the
functions that survive the clearing of denominators — such that `ev` is evaluation at `α` on
polynomials, sends the primitive element `x` to the number `xα`, and sends the coefficient row
`c` to `τ`.  Then applying `ev` to the decomposition gives `hspec` with `e = d(α)`.

`ev` cannot be constructed inside the corpus: the ambient field is an abstract extension of `K(z)`
(`CITED/AdamczewskiFaverjonPrimitive`), and a *field* of functions admits no evaluation
homomorphism — only its subring of functions regular at `α` does.  Making `ev` a theorem is the
same task as making `hEp` of `CITED/AdamczewskiFaverjonAnalyticUB` one: realizing the ambient
field by germs of analytic functions at `ξ`. -/
@[category research solved, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem hspec_of_evalHom {R : Subring Ω} (ev : R →+* K) {α xα : K} {x : Ω} (hxR : x ∈ R)
    (hevx : ev ⟨x, hxR⟩ = xα) (hpolyR : ∀ w : K[X], toAmbient K Ω w ∈ R)
    (hevpoly : ∀ w : K[X], ev ⟨toAmbient K Ω w, hpolyR w⟩ = w.eval α) {δ : ℕ}
    {p : ι → ℕ → K[X]} {d : K[X]} {c : ι → Ω} (hcR : ∀ i, c i ∈ R) {τ : ι → K}
    (hevc : ∀ i, ev ⟨c i, hcR i⟩ = τ i)
    (hdec : ∀ i, toAmbient K Ω d * c i = ∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j)
    (i : ι) :
    ∑ j ∈ Finset.range δ, (p i j).eval α * xα ^ j = d.eval α * τ i := by
  have hu : (⟨toAmbient K Ω d, hpolyR d⟩ : R) * ⟨c i, hcR i⟩
      = ∑ j ∈ Finset.range δ, (⟨toAmbient K Ω (p i j), hpolyR _⟩ : R) * ⟨x, hxR⟩ ^ j := by
    apply Subtype.ext
    push_cast
    exact hdec i
  have h := congrArg ev hu
  simp only [map_mul, map_sum, map_pow, hevpoly, hevc, hevx] at h
  exact h.symm

end EvalHom

end AF
