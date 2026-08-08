/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonLowerBound
import CITED.AdamczewskiFaverjonPrimitive
import ForMathlib.Algebra.MvPolynomial.OptionEquiv
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] §2.3–§2.4: the key lemma assembled, and the endgame of Theorem 2.1

The last work package of plan-formalize-AF17's **WP10**.  The four steps of [AF22]'s key lemma are
formalized elsewhere — (AF) and (NV) in `CITED/AdamczewskiFaverjonAuxiliary`, (UB) in
`CITED/AdamczewskiFaverjonUpperBound`, (LB) in `CITED/AdamczewskiFaverjonLowerBound` — and this
file does the three things that remain:

1. **the bridge** between the two ways WP10 writes the auxiliary function's value: `AF.evalAt`,
   which evaluates a polynomial in `Y` with coefficients in `K[z]` at `(A_k(α), α^{q^k})`, and the
   point `AF.evalPoint` over `Option (ι × ι)` at which Step (LB)'s height bound is stated;
2. **the contradiction** of Lemma 2.11: Step (UB)'s `e^{-c₂q^kδ₁δ₂}`, Step (NV)'s infinite set of
   good `k`, and Step (LB)'s `e^{-(C+c₃q^kδ₂)}` are incompatible once `δ₁ > c₃/c₂`;
3. **[AF22] §2.4**, the passage from the key lemma to Theorem 2.1: the substitution
   `z ↦ z^{q^{k₀}}` that turns `F(Θ_{k₀}(z), z) = 0` into (2.37), and the splitting of the
   resulting linear form into one with coefficients in `K[z]`.

## Why `z` has to become a variable

Step (LB) bounds `h(P(β))` by [Wal00] Lemma 3.7 (`Height.logHeight₁_eval_le_of_degreeOf`), in
which each degree is charged **once**.  Mathlib's `Height.logHeight₁_eval_le` charges them once
per monomial, which for [AF22]'s auxiliary polynomial — support of size `≍ (δ₁+1)^{m²}(δ₂+1)` —
is exponential in `δ₁` and destroys the contradiction, whose whole content is that `c₃` does not
depend on `δ₁`.  Applying the sharp bound means the `z`-degree must be visible as the degree in a
*variable*, not hidden inside coefficients: hence `MvPolynomial (Option (ι × ι)) K` rather than
`MvPolynomial (ι × ι) K[X]`, and hence the translation
`AF.evalAt_eq_eval_evalPoint`, which is Mathlib's `MvPolynomial.optionEquivRight` in disguise.
The degree bookkeeping across it — `deg_{y_{ij}}` is unchanged, `deg_z` becomes the degree of the
coefficients — is `ForMathlib/Algebra/MvPolynomial/OptionEquiv.lean`.

## What §2.4 needs, and what it is given

The endgame is algebra with one analytic hypothesis, and the two are separated here.  The algebra:

* `AF.relation_subst` — [AF22] (2.6)/(2.37).  If the solutions satisfy `f = M · σ(f)` for a
  substitution `σ` of the ambient field and an invertible `M` (this is `A_{k₀}(z)`), then a
  relation `∑ᵢ rᵢfᵢ = 0` yields another one with coefficient row `σ(r)·M⁻¹`.  Applied to
  `r = τΘ_{k₀}(z)` this is exactly [AF22]'s (2.37);
* `AF.exists_polynomial_relation` — the coefficients of that new row are algebraic over `K(z)`,
  hence, after clearing one denominator `d(z)`, polynomials in `z` and in a single primitive
  element `ϕ` (this is (2.36), from `CITED/AdamczewskiFaverjonPrimitive`);
* `AF.exists_lift` — the splitting and the re-summation.  The powers of `ϕ` are independent over
  the solution field because that field is a *regular* extension of `K(z)`, so each
  `ϕ`-component of the relation vanishes separately (`AF.linearForm_split_solField`); summing the
  components back with the **numerical** coefficients `ϕ(ξ)ʲ` gives a relation whose coefficients
  are polynomials in `z` alone and which specializes at `α` to the given linear form.  That last
  swap — `ϕ(z^{q^{k₀}})ʲ ↦ ϕ(ξ)ʲ` — is [AF22]'s final `L(z, X) := ∑ⱼ Qⱼ(z, X)ϕ(ξ)ʲ`.

The analytic hypothesis is the specialization `hspec`: that the decomposition, evaluated at `α`,
returns the coefficients `τ` of the original form (up to the factor `d(α)`).  In [AF22] this is
`Θ_{k₀}(ξ) = A_{k₀}(α)` together with the choice of `k₀` making `ϕ` analytic at `ξ` and
`d(ξ)q(α) ≠ 0`; it is the one place where the ambient field has to be a field of *functions* and
not merely an abstract extension of `K(z)`, and it is carried as a hypothesis for exactly the
reason the regularity of the solution field is (see `CITED/AdamczewskiFaverjonPrimitive`).

## Contents

* `AF.evalAt_eq_eval`, **`AF.evalAt_eq_eval_evalPoint`** — the bridge;
* `AF.exists_logHeight₁_evalAt_le`, `AF.exists_exp_le_norm_evalAt` — [AF22] (2.33) and (2.35)
  restated for the auxiliary polynomial as WP10 builds it;
* `AF.le_of_steps`, `AF.key_lemma_contradiction`, **`AF.key_lemma_of_auxiliary`** — the end of
  the proof of Lemma 2.11, the last in the form that takes only Steps (AF), (NV) and (UB) as
  hypotheses and supplies Step (LB) itself;
* `AF.relation_subst` — [AF22] (2.6) and (2.37);
* `AF.exists_polynomial_relation` — (2.36) with denominators cleared;
* `AF.liftForm`, `AF.relation_liftForm`, `AF.eval_liftForm`, **`AF.exists_lift`** — the splitting
  and the final linear form;
* **`AF.exists_lift_of_subst`** — the three assembled: Lemma 2.11's conclusion in, Theorem 2.1's
  conclusion out.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3.3 (Lemma 2.11) and §2.4 ((2.36), (2.37), the final `L(z,X)`).
* [Wal00] M. Waldschmidt. *Diophantine Approximation on Linear Algebraic Groups.* Springer 2000,
  Lemma 3.7 (the sharp evaluation bound, `Height.logHeight₁_eval_le_of_degreeOf`).
* [AF17f] `plans/plan-formalize-AF17.html`: WP10, §2.11–§2.13, milestone M4.
-/

open Height Finset MvPolynomial
open scoped Polynomial

namespace AF

/-! ## The bridge: the coefficient variable `z` as one more indeterminate -/

section Bridge

variable {K : Type*} [Field K] {σ : Type*}

/-- **The bridge.**  Evaluating a polynomial in `Y` with coefficients in `K[z]` at the `n`-th
point is evaluating its `Option σ`-avatar — `z` promoted to an indeterminate — at the point
extended by the value of `z`.

This is what lets Step (LB)'s height bound, stated at `AF.evalPoint`, be applied to the auxiliary
function of Step (AF), which lives in `MvPolynomial σ K[X]`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem evalAt_eq_eval (pt : ℕ → K) (Yval : ℕ → σ → K) (n : ℕ) (P : MvPolynomial σ K[X]) :
    evalAt pt Yval n P =
      MvPolynomial.eval (fun o : Option σ ↦ o.elim (pt n) (Yval n))
        ((optionEquivRight K σ).symm P) := by
  rw [MvPolynomial.eval_optionEquivRight_symm]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bridge at the Mahler iterates: `AF.evalAt` at the `k`-th point is `MvPolynomial.eval` at
`AF.evalPoint q A α k`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem evalAt_eq_eval_evalPoint (q : ℕ) (A : Matrix ι ι K[X]) (α : K) (k : ℕ)
    (P : MvPolynomial (ι × ι) K[X]) :
    evalAt (fun j ↦ α ^ q ^ j) (fun n s ↦ (iterMatrix q A n s.1 s.2).eval α) k P =
      MvPolynomial.eval (evalPoint q A α k) ((optionEquivRight K (ι × ι)).symm P) :=
  evalAt_eq_eval _ _ k P

end Bridge

/-! ## [AF22] (2.33) and (2.35) for the auxiliary function as WP10 builds it -/

section Height

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] (2.33), transported across the bridge.**  For a polynomial `P` of degree at most `dY`
in each `y_{i,j}` whose coefficients have degree at most `dZ` in `z`, the height of its value at
`(A_k(α), α^{q^k})` grows like `q^k` with a rate **linear in both degrees**.  The `k`-free
constant `C` is left unnamed: the contradiction of Lemma 2.11 washes it out. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem exists_logHeight₁_evalAt_le {q : ℕ} {A : Matrix ι ι K[X]} {α : K}
    (P : MvPolynomial (ι × ι) K[X]) {dY dZ : ℕ}
    (hdY : ∀ s, P.degreeOf s ≤ dY) (hdZ : ∀ ν, (P.coeff ν).natDegree ≤ dZ)
    {γ : ℝ} (hγ : ∀ (k : ℕ) (i j : ι), logHeight₁ ((iterMatrix q A k i j).eval α) ≤ γ * q ^ k) :
    ∃ C : ℝ, ∀ k : ℕ,
      logHeight₁ (evalAt (fun j ↦ α ^ q ^ j) (fun n s ↦ (iterMatrix q A n s.1 s.2).eval α) k P)
        ≤ C + ((Fintype.card (ι × ι) : ℝ) * dY * γ + dZ * logHeight₁ α) * q ^ k := by
  classical
  set Q := (optionEquivRight K (ι × ι)).symm P with hQ
  refine ⟨totalWeight K * Real.log ((#Q.support + 1 : ℕ) : ℝ)
    + ∑ ν ∈ Q.support, logHeight₁ (Q.coeff ν), fun k ↦ ?_⟩
  rw [evalAt_eq_eval_evalPoint]
  exact logHeight₁_eval_evalPoint_le Q
    (fun s ↦ (MvPolynomial.degreeOf_some_optionEquivRight_symm_le P s).trans (hdY s))
    (MvPolynomial.degreeOf_none_optionEquivRight_symm_le hdZ) hγ k

/-- **[AF22] (2.35), transported across the bridge**: Liouville's inequality applied to the value
of the auxiliary function, whenever that value is non-zero — which Step (NV) guarantees for
infinitely many `k`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem exists_exp_le_norm_evalAt {q : ℕ} {A : Matrix ι ι K[X]} {α : K} (φ : K →+* ℂ)
    (P : MvPolynomial (ι × ι) K[X]) {dY dZ : ℕ}
    (hdY : ∀ s, P.degreeOf s ≤ dY) (hdZ : ∀ ν, (P.coeff ν).natDegree ≤ dZ)
    {γ : ℝ} (hγ : ∀ (k : ℕ) (i j : ι), logHeight₁ ((iterMatrix q A k i j).eval α) ≤ γ * q ^ k) :
    ∃ C : ℝ, ∀ k : ℕ,
      evalAt (fun j ↦ α ^ q ^ j) (fun n s ↦ (iterMatrix q A n s.1 s.2).eval α) k P ≠ 0 →
      Real.exp (-(C + ((Fintype.card (ι × ι) : ℝ) * dY * γ + dZ * logHeight₁ α) * q ^ k))
        ≤ ‖φ (evalAt (fun j ↦ α ^ q ^ j)
            (fun n s ↦ (iterMatrix q A n s.1 s.2).eval α) k P)‖ := by
  obtain ⟨C, hC⟩ := exists_logHeight₁_evalAt_le P hdY hdZ hγ
  exact ⟨C, fun k hne ↦ exp_neg_le_norm φ hne (hC k)⟩

end Height

/-! ## The end of the proof of Lemma 2.11 -/

section KeyLemma

/-- **The three steps meet.**  Step (UB) bounds the value above by `e^{-bq^k}` for all large `k`,
Step (NV) makes it non-zero for infinitely many `k`, and Step (LB) bounds it below by
`e^{-(C+aq^k)}` whenever it is non-zero.  Then `b ≤ a`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem le_of_steps {q : ℕ} (hq : 2 ≤ q) {E : ℕ → ℂ} {C a b : ℝ}
    (hUB : ∀ᶠ k in Filter.atTop, ‖E k‖ ≤ Real.exp (-(b * q ^ k)))
    (hNV : ∃ᶠ k in Filter.atTop, E k ≠ 0)
    (hLB : ∀ k, E k ≠ 0 → Real.exp (-(C + a * q ^ k)) ≤ ‖E k‖) :
    b ≤ a :=
  le_of_frequently_exp_le hq <|
    (hNV.and_eventually hUB).mono fun k hk ↦ (hLB k hk.1).trans hk.2

/-- **[AF22] Lemma 2.11, the contradiction.**  *«By Inequalities (2.14) and (2.35) we obtain
`e^{-c₃q^kδ₂} ≤ |E(A_k(α),α^{q^k})| ≤ e^{-c₂q^kδ₁δ₂}`.  We deduce that `c₃ ≥ c₂δ₁`.  Since `c₂` and
`c₃` are positive numbers which do not depend on `δ₁`, this provides a contradiction, as soon as
`δ₁` is large enough.»*

The hypothesis is the whole of Steps (AF), (UB), (NV), (LB) as [AF22] use them: for **every**
`δ₁` there is an auxiliary function whose value at the iterates obeys the two bounds, with `c₂`
and `c₃` fixed once and for all.  The conclusion is that the assumption `F(Θ_{k₀}(z),z) ≠ 0` that
produced them is untenable. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem key_lemma_contradiction {q : ℕ} (hq : 2 ≤ q) {c₂ c₃ : ℝ} (hc₂ : 0 < c₂)
    (h : ∀ δ₁ : ℕ, ∃ (δ₂ : ℕ) (C : ℝ) (E : ℕ → ℂ), 0 < δ₂ ∧
      (∀ᶠ k in Filter.atTop, ‖E k‖ ≤ Real.exp (-(c₂ * δ₁ * δ₂ * q ^ k))) ∧
      (∃ᶠ k in Filter.atTop, E k ≠ 0) ∧
      (∀ k, E k ≠ 0 → Real.exp (-(C + c₃ * δ₂ * q ^ k)) ≤ ‖E k‖)) :
    False := by
  obtain ⟨δ₁, hδ₁⟩ := exists_nat_gt (c₃ / c₂)
  obtain ⟨δ₂, C, E, hδ₂, hUB, hNV, hLB⟩ := h δ₁
  have hle : c₂ * δ₁ * δ₂ ≤ c₃ * δ₂ := le_of_steps hq hUB hNV hLB
  have hδ₂pos : (0 : ℝ) < δ₂ := by exact_mod_cast hδ₂
  have hle' : c₂ * δ₁ ≤ c₃ := le_of_mul_le_mul_right (by linarith) hδ₂pos
  have : c₃ / c₂ * c₂ < (δ₁ : ℝ) * c₂ := mul_lt_mul_of_pos_right hδ₁ hc₂
  rw [div_mul_cancel₀ _ hc₂.ne'] at this
  nlinarith

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] Lemma 2.11, assembled from Steps (AF), (NV) and (UB)** — Step (LB) is supplied here
rather than assumed.

The hypothesis is what §2.3 delivers for every `δ₁`: an auxiliary polynomial `P` (Step (AF)),
whose degrees are bounded by fixed multiples of `δ₂` — `deg_Y ≍ δ₁ ≤ δ₂` and `deg_z ≍ δ₂` in
[AF22]'s regime `δ₂ ≫ δ₁` — which is non-zero at the iterates for infinitely many `k` (Step (NV))
and whose value there is at most `e^{-c₂δ₁δ₂q^k}` (Step (UB)).  The lower bound
`e^{-(C+c₃δ₂q^k)}` is then a consequence of the height machinery, with

`c₃ = m²·b₁·γ + b₂·h(α)`

visibly independent of `δ₁` and `δ₂` — *«some constant `c` that does not depend on `δ₁`, `δ₂` and
`k`»* — and that is the whole content of the contradiction. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem key_lemma_of_auxiliary {q : ℕ} (hq : 2 ≤ q) {A : Matrix ι ι K[X]} {α : K} (φ : K →+* ℂ)
    {γ : ℝ} (hγ : ∀ (k : ℕ) (i j : ι), logHeight₁ ((iterMatrix q A k i j).eval α) ≤ γ * q ^ k)
    {c₂ : ℝ} (hc₂ : 0 < c₂) {b₁ b₂ : ℕ}
    (h : ∀ δ₁ : ℕ, ∃ (δ₂ : ℕ) (P : MvPolynomial (ι × ι) K[X]), 0 < δ₂ ∧
      (∀ s, P.degreeOf s ≤ b₁ * δ₂) ∧ (∀ ν, (P.coeff ν).natDegree ≤ b₂ * δ₂) ∧
      (∃ᶠ k in Filter.atTop,
        evalAt (fun j ↦ α ^ q ^ j) (fun n s ↦ (iterMatrix q A n s.1 s.2).eval α) k P ≠ 0) ∧
      (∀ᶠ k in Filter.atTop,
        ‖φ (evalAt (fun j ↦ α ^ q ^ j) (fun n s ↦ (iterMatrix q A n s.1 s.2).eval α) k P)‖
          ≤ Real.exp (-(c₂ * δ₁ * δ₂ * q ^ k)))) :
    False := by
  refine key_lemma_contradiction (c₃ := (Fintype.card (ι × ι) : ℝ) * b₁ * γ + b₂ * logHeight₁ α)
    hq hc₂ fun δ₁ ↦ ?_
  obtain ⟨δ₂, P, hδ₂, hdY, hdZ, hNV, hUB⟩ := h δ₁
  obtain ⟨C, hC⟩ := exists_exp_le_norm_evalAt φ P hdY hdZ hγ
  refine ⟨δ₂, C, fun k ↦ φ (evalAt (fun j ↦ α ^ q ^ j)
    (fun n s ↦ (iterMatrix q A n s.1 s.2).eval α) k P), hδ₂, ?_, ?_, ?_⟩
  · exact hUB
  · exact hNV.mono fun k hk hz ↦ hk ((map_eq_zero_iff φ φ.injective).1 hz)
  · intro k hk
    have hne : evalAt (fun j ↦ α ^ q ^ j)
        (fun n s ↦ (iterMatrix q A n s.1 s.2).eval α) k P ≠ 0 := fun hz ↦ hk (by simp [hz])
    have heq : ((Fintype.card (ι × ι) : ℝ) * b₁ * γ + b₂ * logHeight₁ α) * (δ₂ : ℝ)
        = (Fintype.card (ι × ι) : ℝ) * ((b₁ * δ₂ : ℕ) : ℝ) * γ
          + ((b₂ * δ₂ : ℕ) : ℝ) * logHeight₁ α := by
      push_cast; ring
    rw [heq]
    exact hC k hne

end KeyLemma

/-! ## [AF22] §2.4: from the key lemma to Theorem 2.1 -/

section Endgame

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficients of a linear form in `K[z]`, read in the ambient field. -/
@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def toAmbient (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra (RatFunc K) Ω] :
    K[X] →+* Ω :=
  (algebraMap (RatFunc K) Ω).comp (algebraMap K[X] (RatFunc K))

@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem toAmbient_apply (p : K[X]) :
    toAmbient K Ω p = algebraMap (RatFunc K) Ω (algebraMap K[X] (RatFunc K) p) := rfl

/-- **[AF22] (2.6) and (2.37).**  *«Writing `Θ_{k₀}(z^{q^{k₀}}) = Θ_{k₀}(z^{q^{k₀}})A_{k₀}(z)^{-1}
A_{k₀}(z)` and using (2.6), we get `F(…Θ_{k₀}(z^{q^{k₀}})A_{k₀}(z)^{-1}, z) = 0`.»*

A relation `∑ᵢ rᵢfᵢ = 0` between the solutions survives the Mahler substitution `s` — `z ↦
z^{q^{k₀}}` on the ambient field — as a relation with coefficient row `s(r)·M⁻¹`, where `M` is the
matrix of the system, `f = M·s(f)`.  The inverse is given as a left inverse `N`, so no
invertibility API and no `DecidableEq` is needed. -/
@[category research solved, AMS 11 12 15 39, ref "AF22", group "af_mahler_alternative"]
theorem relation_subst (s : Ω →+* Ω) {M N : Matrix ι ι Ω} (hMN : N * M = 1)
    {f : ι → Ω} (hf : ∀ i, f i = ∑ j, M i j * s (f j))
    {r : ι → Ω} (hr : ∑ i, r i * f i = 0) :
    ∑ i, (∑ j, s (r j) * N j i) * f i = 0 := by
  classical
  have hsf : ∀ i, ∑ j, N i j * f j = s (f i) := by
    intro i
    calc ∑ j, N i j * f j
        = ∑ j, ∑ l, N i j * M j l * s (f l) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [hf j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ ↦ by ring
      _ = ∑ l, (N * M) i l * s (f l) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ ↦ by rw [Matrix.mul_apply, Finset.sum_mul]
      _ = s (f i) := by
          rw [hMN]
          simp [Matrix.one_apply]
  have h0 : ∑ i, s (r i) * s (f i) = 0 := by
    have h := congrArg s hr
    rw [map_sum, map_zero] at h
    simpa only [map_mul] using h
  calc ∑ i, (∑ j, s (r j) * N j i) * f i
      = ∑ i, ∑ j, s (r j) * (N j i * f i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ∑ j, s (r j) * s (f j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [← Finset.mul_sum, hsf j]
    _ = 0 := h0

section Decomposition

variable [CharZero K]

omit [DecidableEq ι] in
/-- **[AF22] (2.36) with the denominators cleared**, in the form §2.4 uses it: the coefficients of
a relation being algebraic over `K(z)`, one polynomial `d(z) ≠ 0` makes them polynomials in `z`
and in a single primitive element `ϕ`, and the relation is transported along. -/
@[category research solved, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem exists_polynomial_relation {f c : ι → Ω} (hint : ∀ i, IsIntegral (RatFunc K) (c i))
    (hr : ∑ i, c i * f i = 0) :
    ∃ (x : Ω) (δ : ℕ) (d : K[X]) (p : ι → ℕ → K[X]),
      IsIntegral (RatFunc K) x ∧ (minpoly (RatFunc K) x).natDegree = δ ∧ d ≠ 0 ∧
      (∀ i, toAmbient K Ω d * c i = ∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j) ∧
      ∑ i, (∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j) * f i = 0 := by
  obtain ⟨x, δ, d, p, hx, hδ, hd, hdec⟩ := exists_polynomial_decomposition c hint
  simp only [← toAmbient_apply] at hdec
  refine ⟨x, δ, d, p, hx, hδ, hd, hdec, ?_⟩
  calc ∑ i, (∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j) * f i
      = ∑ i, toAmbient K Ω d * (c i * f i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← hdec i, mul_assoc]
    _ = toAmbient K Ω d * ∑ i, c i * f i := by rw [Finset.mul_sum]
    _ = 0 := by rw [hr, mul_zero]

end Decomposition

/-- **[AF22]'s final linear form** `L(z,X) := ∑ⱼ Qⱼ(z,X)ϕ(ξ)ʲ`, up to the normalizing scalar `c`:
the `ϕ`-components of the split relation, summed back with the *numerical* powers of `ϕ(ξ)`. -/
@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def liftForm (δ : ℕ) (c xα : K) (p : ι → ℕ → K[X]) (i : ι) : K[X] :=
  Polynomial.C c * ∑ j ∈ Finset.range δ, Polynomial.C (xα ^ j) * p i j

omit [Fintype ι] [DecidableEq ι] in
@[category API, AMS 11 12 13, ref "AF22", group "af_mahler_alternative"]
theorem eval_liftForm (δ : ℕ) (c xα : K) (p : ι → ℕ → K[X]) (i : ι) (α : K) :
    (liftForm δ c xα p i).eval α = c * ∑ j ∈ Finset.range δ, (p i j).eval α * xα ^ j := by
  rw [liftForm, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]

omit [DecidableEq ι] in
/-- **The splitting, applied.**  A relation whose coefficients are polynomials in `z` and in `ϕ`
gives, for every scalar `xα`, a relation whose coefficients are polynomials in `z` alone: the
`ϕ`-components vanish one by one, by the regularity of the solution field. -/
@[category research solved, AMS 11 12 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem relation_liftForm {f : ι → Ω} (hreg : IsRegularSolField K f)
    {x : Ω} (hx : IsIntegral (RatFunc K) x) {δ : ℕ}
    (hδ : δ ≤ (minpoly (RatFunc K) x).natDegree) (p : ι → ℕ → K[X])
    (hrel : ∑ i, (∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j) * f i = 0) (c xα : K) :
    ∑ i, toAmbient K Ω (liftForm δ c xα p i) * f i = 0 := by
  have hsplit := linearForm_split_solField K hreg hx hδ
    (fun i j ↦ algebraMap K[X] (RatFunc K) (p i j))
    (by simpa only [toAmbient_apply] using hrel)
  simp only [← toAmbient_apply] at hsplit
  calc ∑ i, toAmbient K Ω (liftForm δ c xα p i) * f i
      = ∑ i, ∑ j ∈ Finset.range δ,
          toAmbient K Ω (Polynomial.C c * Polynomial.C (xα ^ j)) *
            (toAmbient K Ω (p i j) * f i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [liftForm, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [map_mul, map_mul]; ring
    _ = ∑ j ∈ Finset.range δ, toAmbient K Ω (Polynomial.C c * Polynomial.C (xα ^ j)) *
          ∑ i, toAmbient K Ω (p i j) * f i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]
    _ = 0 := Finset.sum_eq_zero fun j hj ↦ by rw [hsplit j hj, mul_zero]

omit [DecidableEq ι] in
/-- **[AF22] §2.4, the last paragraph.**  *«Setting `L(z,X) := ∑ⱼ Qⱼ(z,X)ϕ(α^{q^{k₀}})ʲ`, we
obtain `L(z,f(z)) = 0` and `L(α,X) = L(X)`, as wanted.»*

The hypothesis `hspec` is the analytic input: evaluating the decomposition at `α` returns the
coefficients `τ` of the original linear form, up to the value `e = d(α)` of the denominator, which
[AF22]'s choice of `k₀` makes non-zero. -/
@[category research solved, AMS 11 12 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem exists_lift {f : ι → Ω} (hreg : IsRegularSolField K f)
    {x : Ω} (hx : IsIntegral (RatFunc K) x) {δ : ℕ}
    (hδ : δ ≤ (minpoly (RatFunc K) x).natDegree) (p : ι → ℕ → K[X])
    (hrel : ∑ i, (∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j) * f i = 0)
    {α xα e : K} (he : e ≠ 0) {τ : ι → K}
    (hspec : ∀ i, ∑ j ∈ Finset.range δ, (p i j).eval α * xα ^ j = e * τ i) :
    ∃ L : ι → K[X], (∑ i, toAmbient K Ω (L i) * f i = 0) ∧ ∀ i, (L i).eval α = τ i := by
  refine ⟨liftForm δ e⁻¹ xα p, relation_liftForm hreg hx hδ p hrel _ _, fun i ↦ ?_⟩
  rw [eval_liftForm, hspec i, ← mul_assoc, inv_mul_cancel₀ he, one_mul]

/-- **[AF22] Theorem 2.1, the algebraic endgame in one statement.**  Lemma 2.11's conclusion goes
in — a relation `∑ᵢ rᵢfᵢ = 0` whose coefficient row is `τΘ_{k₀}(z)` — and Theorem 2.1's conclusion
comes out: a linear form with coefficients in `K[z]`, vanishing on the solutions, and
specializing at `α` to the given form `τ`.

Between them: the Mahler substitution (`relation_subst`, [AF22] (2.37)), the decomposition
`(2.36)` with its denominator, and the splitting.  The decomposition and its specialization at `α`
are hypotheses — the first exists by `AF.exists_polynomial_relation`, the second is the analytic
input `Θ_{k₀}(ξ) = A_{k₀}(α)` discussed in the module doc. -/
@[category research solved, AMS 11 12 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem exists_lift_of_subst {f : ι → Ω} (hreg : IsRegularSolField K f)
    (s : Ω →+* Ω) {M N : Matrix ι ι Ω} (hMN : N * M = 1)
    (hf : ∀ i, f i = ∑ j, M i j * s (f j))
    {r : ι → Ω} (hr : ∑ i, r i * f i = 0)
    {x : Ω} (hx : IsIntegral (RatFunc K) x) {δ : ℕ}
    (hδ : δ ≤ (minpoly (RatFunc K) x).natDegree) {d : K[X]} (p : ι → ℕ → K[X])
    (hdec : ∀ i, toAmbient K Ω d * (∑ j, s (r j) * N j i) =
      ∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j)
    {α xα e : K} (he : e ≠ 0) {τ : ι → K}
    (hspec : ∀ i, ∑ j ∈ Finset.range δ, (p i j).eval α * xα ^ j = e * τ i) :
    ∃ L : ι → K[X], (∑ i, toAmbient K Ω (L i) * f i = 0) ∧ ∀ i, (L i).eval α = τ i := by
  have h237 : ∑ i, (∑ j, s (r j) * N j i) * f i = 0 := relation_subst s hMN hf hr
  have hrel : ∑ i, (∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j) * f i = 0 := by
    calc ∑ i, (∑ j ∈ Finset.range δ, toAmbient K Ω (p i j) * x ^ j) * f i
        = toAmbient K Ω d * ∑ i, (∑ j, s (r j) * N j i) * f i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [← hdec i, mul_assoc]
      _ = 0 := by rw [h237, mul_zero]
  exact exists_lift hreg hx hδ p hrel he hspec

end Endgame

end AF
