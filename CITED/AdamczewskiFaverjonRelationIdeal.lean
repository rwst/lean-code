/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import CITED.AdamczewskiFaverjonBidegree

/-!
# [AF22] §2.2: the relation ideal `𝓘` of a Mahler system, and its radicality

The second half of plan-formalize-AF17's **WP7**.  [AF22] attach to a `q`-Mahler system
`f(z) = A(z)f(z^q)` and a regular algebraic point `α` with `0 < |α| < 1` the ideal

  `𝓘 := {P ∈ ℚ̄(z)[Y] : P(A_k(α), α^{q^k}) = 0 for all k ≫ 1}`,

where `Y = (y_{i,j})` is a matrix of indeterminates and `A_k(z) = A(z)A(z^q)⋯A(z^{q^{k-1}})`.
They then observe that `𝓘` is an ideal (their Lemma 2.4) and that it is *radical*, which is what
makes the weak Nullstellensatz produce a relation matrix in §2.2.2 (= WP8).

## «well-defined for `k ≫ 1`», honestly

The coefficients of `P` are *rational* functions, so `P(A_k(α), α^{q^k})` need not be defined for
every `k`; [AF22] note that it is defined for `k ≫ 1` because a rational function has finitely
many poles while the points `α^{q^k}` are pairwise distinct.  A partial evaluation is awkward to
carry around in Lean.  The device used here is that "a sequence defined for `k ≫ 1`, up to what
happens for small `k`" is exactly an element of the ring of **germs** `Filter.Germ atTop K`: the
finitely many undefined values do not change the germ.  So evaluation becomes a genuine, total
**ring homomorphism**

  `AF.germEval : K(z)[Y] →+* Filter.Germ atTop K`,

built from `Polynomial.evalRingHom` by inverting the nonzero polynomials (which are eventually
nonzero at pairwise distinct points, hence units in the germ ring), and

  `AF.relationIdeal = RingHom.ker AF.germEval`.

That `𝓘` is an ideal is then automatic, and radicality (**Lemma 2.4**) is the statement that the
germ ring of a reduced ring is reduced — a five-line proof rather than the two-paragraph
verification in [AF22].  The only hypothesis needed is that the points are **pairwise distinct**;
regularity of `α` is not used here (it enters in §2.2.2, with the relation matrices).

## Contents

* `AF.germEval`, `AF.relationIdeal` — the ideal `𝓘`;
* `AF.relationIdeal_ne_top` — `1 ∉ 𝓘`, the hypothesis of the dimension lemmas of
  `CITED/AdamczewskiFaverjonBidegree`;
* `AF.lemma_2_4` — `𝓘` is radical;
* `AF.mem_relationIdeal_map_iff` — for a polynomial with *polynomial* coefficients, membership is
  literally «vanishes at `(A_k(α), α^{q^k})` for all `k ≫ 1`»;
* `AF.iterMatrix` and `AF.iterMatrix_add` — `A_k(z)` and the cocycle identity
  `A_{k+l}(z) = A_l(z)·A_k(z^{q^l})` of [AF22] (2.1), the shape used in their Lemma 2.7;
* `AF.injective_iterPow` — `k ↦ α^{q^k}` is injective when `0 < |α| < 1`, the hypothesis above;
* `AF.mahlerRelationIdeal` and `AF.lemma_2_2_mahler`, `AF.lemma_2_3_mahler` — the relation ideal
  of an actual Mahler system, and the two dimension lemmas for it.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.2 ((2.1), `𝓘`, Lemma 2.4).
* [AF17f] `plans/plan-formalize-AF17.html`: WP7, milestone M4 (Stage 2).
-/

open Filter MvPolynomial
open scoped Polynomial

namespace AF

/-! ## Germ evaluation -/

section GermEval

variable {K : Type*} [Field K]

/-- Evaluation of polynomials along a sequence of points, as a ring homomorphism into the ring of
germs at infinity. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def germPolyEval (pt : ℕ → K) : K[X] →+* Germ (atTop : Filter ℕ) K :=
  (Germ.coeRingHom (atTop : Filter ℕ)).comp (RingHom.pi fun n => Polynomial.evalRingHom (pt n))

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem germPolyEval_apply (pt : ℕ → K) (p : K[X]) :
    germPolyEval pt p = ((fun n => p.eval (pt n) : ℕ → K) : Germ (atTop : Filter ℕ) K) := rfl

/-- A nonzero polynomial is eventually nonzero along a sequence of pairwise distinct points: it
has only finitely many roots, and each is hit at most once. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem eventually_eval_ne_zero {pt : ℕ → K} (hpt : Function.Injective pt) {p : K[X]}
    (hp : p ≠ 0) : ∀ᶠ n in atTop, p.eval (pt n) ≠ 0 := by
  have hfin : {x : K | p.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hp
  rw [Filter.eventually_iff, ← Nat.cofinite_eq_atTop, Filter.mem_cofinite]
  refine Set.Finite.subset (hfin.preimage hpt.injOn) fun n hn => ?_
  simpa [Polynomial.IsRoot, Set.mem_preimage] using not_not.mp hn

/-- Hence a nonzero polynomial becomes a **unit** in the germ ring. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem isUnit_germPolyEval {pt : ℕ → K} (hpt : Function.Injective pt) {p : K[X]} (hp : p ≠ 0) :
    IsUnit (germPolyEval pt p) := by
  refine isUnit_iff_exists_inv.mpr
    ⟨((fun n => (p.eval (pt n))⁻¹ : ℕ → K) : Germ (atTop : Filter ℕ) K), ?_⟩
  rw [germPolyEval_apply, ← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
  filter_upwards [eventually_eval_ne_zero hpt hp] with n hn
  simp [mul_inv_cancel₀ hn]

/-- **Evaluation of rational functions along pairwise distinct points**, as a total ring
homomorphism into germs.  This is [AF22]'s «`P(A_k(α), α^{q^k})` is well-defined for `k ≫ 1`». -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def germRatFuncEval {pt : ℕ → K} (hpt : Function.Injective pt) :
    RatFunc K →+* Germ (atTop : Filter ℕ) K :=
  IsLocalization.lift (S := RatFunc K) (g := germPolyEval pt)
    (fun y => isUnit_germPolyEval hpt (nonZeroDivisors.ne_zero y.2))

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem germRatFuncEval_algebraMap {pt : ℕ → K} (hpt : Function.Injective pt) (p : K[X]) :
    germRatFuncEval hpt (algebraMap K[X] (RatFunc K) p) = germPolyEval pt p :=
  IsLocalization.lift_eq _ _

variable {σ : Type*}

/-- **Evaluation at `(A_k(α), α^{q^k})`**, as a ring homomorphism `K(z)[Y] →+* Germ atTop K`: the
indeterminates `Y` go to the germ of the matrix entries, the coefficients to the germ of their
values at the points. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def germEval {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → σ → K) :
    MvPolynomial σ (RatFunc K) →+* Germ (atTop : Filter ℕ) K :=
  eval₂Hom (germRatFuncEval hpt) fun s =>
    ((fun n => Yval n s : ℕ → K) : Germ (atTop : Filter ℕ) K)

/-- **The relation ideal `𝓘`** ([AF22] §2.2): the polynomials over `K(z)` in the matrix of
indeterminates that vanish at `(A_k(α), α^{q^k})` for all large `k`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def relationIdeal {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → σ → K) :
    Ideal (MvPolynomial σ (RatFunc K)) :=
  RingHom.ker (germEval hpt Yval)

/-- The germ ring of a reduced ring is reduced: a germ is nilpotent iff it is eventually
nilpotent, hence eventually zero. -/
@[category API, AMS 13, ref "AF22", group "af_mahler_alternative"]
theorem isReduced_germ {α : Type*} {l : Filter α} {R : Type*} [MonoidWithZero R] [IsReduced R] :
    IsReduced (Germ l R) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  induction x using Germ.inductionOn with
  | _ f =>
      rw [← Germ.coe_pow, ← Germ.coe_zero, Germ.coe_eq] at hn
      rw [← Germ.coe_zero, Germ.coe_eq]
      filter_upwards [hn] with i hi
      exact IsReduced.eq_zero (f i) ⟨n, hi⟩

/-- **[AF22] Lemma 2.4.**  *«The set `𝓘` is a radical ideal of `ℚ̄(z)[Y]`.»*

It is an ideal because it is the kernel of a ring homomorphism, and radical because the germ ring
of a field is reduced. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem lemma_2_4 {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → σ → K) :
    (relationIdeal hpt Yval).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  haveI : IsReduced (Germ (atTop : Filter ℕ) K) := isReduced_germ
  have hx0 : germEval hpt Yval x ^ n = 0 := by
    rw [← map_pow]
    exact hn
  exact IsReduced.eq_zero _ ⟨n, hx0⟩

/-- `𝓘` is a **proper** ideal: `1` does not vanish anywhere.  This is the hypothesis `I ≠ ⊤` of
the dimension lemmas, i.e. [AF22]'s «`𝓘(δ₁)` does not contain any non-zero element of `ℚ̄`». -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem relationIdeal_ne_top {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → σ → K) :
    relationIdeal hpt Yval ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one]
  intro h
  have h1 : (1 : Germ (atTop : Filter ℕ) K) = 0 := by
    rw [← map_one (germEval hpt Yval)]
    exact h
  exact one_ne_zero h1

/-! ### Membership, read at the points -/

/-- Evaluation of a polynomial with *polynomial* coefficients at the `n`-th point — a total map,
no germs needed. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def evalAt (pt : ℕ → K) (Yval : ℕ → σ → K) (n : ℕ) : MvPolynomial σ K[X] →+* K :=
  eval₂Hom (Polynomial.evalRingHom (pt n)) (Yval n)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem germEval_map {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → σ → K)
    (P : MvPolynomial σ K[X]) :
    germEval hpt Yval (MvPolynomial.map (algebraMap K[X] (RatFunc K)) P) =
      ((fun n => evalAt pt Yval n P : ℕ → K) : Germ (atTop : Filter ℕ) K) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.map_C, germEval, eval₂Hom_C, germRatFuncEval_algebraMap,
        germPolyEval_apply]
      exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun n => by simp [evalAt])
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, ← Germ.coe_add]
      exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun n => by simp [map_add])
  | mul_X p s hp =>
      rw [map_mul, map_mul, hp, MvPolynomial.map_X, germEval, eval₂Hom_X', ← Germ.coe_mul]
      exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun n => by simp [evalAt])

/-- **Membership in `𝓘`, spelled out.**  A polynomial with polynomial coefficients lies in the
relation ideal exactly when it vanishes at the points `(A_k(α), α^{q^k})` for all large `k`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem mem_relationIdeal_map_iff {pt : ℕ → K} (hpt : Function.Injective pt) (Yval : ℕ → σ → K)
    (P : MvPolynomial σ K[X]) :
    MvPolynomial.map (algebraMap K[X] (RatFunc K)) P ∈ relationIdeal hpt Yval ↔
      ∀ᶠ n in atTop, evalAt pt Yval n P = 0 := by
  rw [relationIdeal, RingHom.mem_ker, germEval_map, ← Germ.coe_zero, Germ.coe_eq]
  rfl

end GermEval

/-! ## The iterated matrix `A_k(z)` -/

section IterMatrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Substitution `z ↦ z^q` on polynomials. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def substPow (K : Type*) [Field K] (q : ℕ) : K[X] →+* K[X] :=
  (Polynomial.aeval ((Polynomial.X : K[X]) ^ q)).toRingHom

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem substPow_one : substPow K 1 = RingHom.id K[X] := by
  refine RingHom.ext fun p => ?_
  simp [substPow]

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem substPow_comp (q l : ℕ) :
    (substPow K q).comp (substPow K (q ^ l)) = substPow K (q ^ (l + 1)) := by
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, substPow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← Polynomial.aeval_algHom_apply]
  congr 1
  rw [map_pow, Polynomial.aeval_X, ← pow_mul, ← pow_succ']

/-- **`A_k(z) = A(z)A(z^q)⋯A(z^{q^{k-1}})`** ([AF22] (2.1)). -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def iterMatrix (q : ℕ) (A : Matrix ι ι K[X]) : ℕ → Matrix ι ι K[X]
  | 0 => 1
  | k + 1 => A * (iterMatrix q A k).map (substPow K q)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem iterMatrix_zero (q : ℕ) (A : Matrix ι ι K[X]) : iterMatrix q A 0 = 1 := rfl

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem iterMatrix_succ (q : ℕ) (A : Matrix ι ι K[X]) (k : ℕ) :
    iterMatrix q A (k + 1) = A * (iterMatrix q A k).map (substPow K q) := rfl

/-- **The cocycle identity `A_{k+l}(z) = A_l(z)·A_k(z^{q^l})`** — [AF22] use it in the form
`A_ℓ(α)A_k(α^{q^ℓ}) = A_{k+ℓ}(α)` in the proof of their Lemma 2.7. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem iterMatrix_add (q : ℕ) (A : Matrix ι ι K[X]) (k l : ℕ) :
    iterMatrix q A (k + l) = iterMatrix q A l * (iterMatrix q A k).map (substPow K (q ^ l)) := by
  induction l with
  | zero => simp [iterMatrix_zero, substPow_one]
  | succ n ih =>
      rw [show k + (n + 1) = (k + n) + 1 from by omega, iterMatrix_succ, ih, iterMatrix_succ,
        Matrix.map_mul, Matrix.mul_assoc, Matrix.map_map, ← RingHom.coe_comp, substPow_comp]

end IterMatrix

/-! ## The relation ideal of a Mahler system at an algebraic point -/

section Mahler

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The points `α^{q^k}` are pairwise distinct as soon as `0 < |α| < 1` in some embedding: their
absolute values are strictly decreasing. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem injective_iterPow (f : K →+* ℂ) {α : K} {q : ℕ} (hq : 2 ≤ q) (h0 : α ≠ 0)
    (h1 : ‖f α‖ < 1) : Function.Injective fun k : ℕ => α ^ q ^ k := by
  have hfα : f α ≠ 0 := fun h => h0 (f.injective (by simpa using h))
  have hpos : 0 < ‖f α‖ := norm_pos_iff.mpr hfα
  have hmono : StrictAnti fun k : ℕ => ‖f α‖ ^ q ^ k := by
    refine strictAnti_nat_of_succ_lt fun k => ?_
    refine pow_lt_pow_right_of_lt_one₀ hpos h1 ?_
    have hqk : 0 < q ^ k := pow_pos (by omega) k
    calc q ^ k < 2 * q ^ k := by omega
      _ ≤ q * q ^ k := Nat.mul_le_mul_right _ hq
      _ = q ^ (k + 1) := (pow_succ' q k).symm
  intro m n hmn
  by_contra hne
  have : ‖f α‖ ^ q ^ m = ‖f α‖ ^ q ^ n := by
    have := congrArg (fun x : K => ‖f x‖) hmn
    simpa [map_pow, norm_pow] using this
  exact hne (hmono.injective this)

variable {q : ℕ} {A : Matrix ι ι K[X]} {α : K}

/-- **The relation ideal of a Mahler system** at an algebraic point `α` with `0 < |α| < 1`:
[AF22]'s `𝓘`, with `Y` evaluated at the entries of `A_k(α)` and `z` at `α^{q^k}`. -/
@[category research solved, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def mahlerRelationIdeal (f : K →+* ℂ) (hq : 2 ≤ q) (h0 : α ≠ 0) (h1 : ‖f α‖ < 1)
    (A : Matrix ι ι K[X]) : Ideal (MvPolynomial (ι × ι) (RatFunc K)) :=
  relationIdeal (injective_iterPow f hq h0 h1)
    fun k s => ((iterMatrix q A k) s.1 s.2).eval α

@[category research solved, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem mahlerRelationIdeal_ne_top (f : K →+* ℂ) (hq : 2 ≤ q) (h0 : α ≠ 0) (h1 : ‖f α‖ < 1)
    (A : Matrix ι ι K[X]) : mahlerRelationIdeal f hq h0 h1 A ≠ ⊤ :=
  relationIdeal_ne_top _ _

@[category research solved, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem isRadical_mahlerRelationIdeal (f : K →+* ℂ) (hq : 2 ≤ q) (h0 : α ≠ 0) (h1 : ‖f α‖ < 1)
    (A : Matrix ι ι K[X]) : (mahlerRelationIdeal f hq h0 h1 A).IsRadical :=
  lemma_2_4 _ _

/-- **[AF22] Lemma 2.2 for the relation ideal of a Mahler system**: `d(δ₁,δ₂) ∼ c₁(δ₁)δ₂`. -/
@[category research solved, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem lemma_2_2_mahler (f : K →+* ℂ) (hq : 2 ≤ q) (h0 : α ≠ 0) (h1 : ‖f α‖ < 1)
    (A : Matrix ι ι K[X]) (δ₁ : ℕ) :
    ∃ c : ℕ, 1 ≤ c ∧ Filter.Tendsto
      (fun δ₂ : ℕ => (relDim (mahlerRelationIdeal f hq h0 h1 A) δ₁ δ₂ : ℝ) / δ₂)
      atTop (nhds (c : ℝ)) :=
  lemma_2_2 _ (mahlerRelationIdeal_ne_top f hq h0 h1 A) δ₁

/-- **[AF22] Lemma 2.3 for the relation ideal of a Mahler system**:
`d(2δ₁,δ₂) ≤ 2^{m²}·d(δ₁,δ₂)`, where `m` is the size of the system. -/
@[category research solved, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem lemma_2_3_mahler (f : K →+* ℂ) (hq : 2 ≤ q) (h0 : α ≠ 0) (h1 : ‖f α‖ < 1)
    (A : Matrix ι ι K[X]) (δ₁ δ₂ : ℕ) :
    relDim (mahlerRelationIdeal f hq h0 h1 A) (2 * δ₁) δ₂ ≤
      2 ^ (Fintype.card ι) ^ 2 * relDim (mahlerRelationIdeal f hq h0 h1 A) δ₁ δ₂ := by
  have h := lemma_2_3 (mahlerRelationIdeal f hq h0 h1 A) δ₁ δ₂
  rwa [Fintype.card_prod, ← pow_two] at h

end Mahler

end AF
