/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonKeyLemma
import Mathlib.Analysis.Analytic.Uniqueness
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The reverse transport: from the analytic identity back to a relation in `Ω`

plan-formalize-AF17's **WP16**, finding **F2** of gap (6).

`AF.key_lemma` ([AF22] Lemma 2.11) concludes that the linear form `F(Θ_{k₀}(z),z)` vanishes
identically near `ξ` — an identity of *complex functions*.  [AF22] §2.4 then substitutes into it,
clears denominators and splits it along a primitive element; the corpus's entry point for all that,
`AF.exists_lift_of_subst`, wants a relation **in the ambient field** `Ω`:

  `∑ᵢ rᵢfᵢ = 0`,  `rⱼ = ∑ᵢ τᵢ(MΦ)ᵢⱼ`.

So the germ realization, which WP12(b) built to carry algebra *into* analysis, has to be run
backwards.  This file does that, and the price is exactly one property that the interface does not
have and cannot be given for free.

## The realization subring is never a field

The natural hope is that `real` is injective because a ring homomorphism out of a field into a
non-trivial ring is.  **It is not available**: `AF.not_isField_of_mem` proves that `R` is never a
field, for the same reason the source of `real` had to be a subring in the first place.  If `ξ`
is the image of a point `c` of `K` — and it is, `ξ = φ(α^{q^{k₀}})` — then `X - C c` lies in `R` by
`poly_mem`, is realized by a function vanishing at `ξ ∈ U`, and so cannot be a unit; a field would
make it one.

Injectivity is therefore a genuine *hypothesis*, and it is the honest one: [AF22]'s realization is
the correspondence «algebraic function ↦ its analytic branch», which is injective by construction —
a non-zero algebraic function has a non-zero branch.  It is the third clause the branch-existence
axiom will have to deliver, next to the solutions being realized and every element of `R` being
realized by a function analytic on `U`.

## What has to be added to the interface, and what does not

* `AF.IsSolutionRealization` — the **solutions** lie in `R` and are realized by `fs`.
  `AF.IsBranchRealization` carries the polynomials and the relation matrix and nothing else, which
  was enough for Step (UB) (there the solutions enter analytically, through `AF.formVal`) but is
  not enough here, where they must be the same objects on both sides.
* `AF.IsAnalyticRealization` — every element of `R` is realized by a function analytic on `U`.
  Needed because the identity principle is what turns «vanishes near `ξ`» into «vanishes on `U`»,
  and germ equality along `𝓟 U` is equality on the whole of `U`.
* Injectivity of `real`, as above.

Nothing here needs a new *axiom*: all three are properties of the same object [AF22] Lemma 2.8
produces, and folding them into `AF.lemma_2_8` keeps Stage 2 at two cited axioms — the same
decision already recorded for the evaluation homomorphism `ev` of gap (5).

## Contents

* `AF.germ_coe_finsetSum` — the coercion `(α → β) → Germ l β` commutes with finite sums;
* `AF.not_isField_of_mem` — the realization subring is not a field;
* `AF.IsSolutionRealization`, `AF.IsAnalyticRealization` — the two interface extensions;
* `AF.eq_zero_of_eventually_eq_zero` — the identity principle, read through `real`;
* `AF.formR`, `AF.real_formR` — the linear form as an element of `R`, and its realization;
* **`AF.relation_of_eventually_formVal_eq_zero`** — the reverse transport: Lemma 2.11's conclusion
  in, `AF.exists_lift_of_subst`'s hypothesis out.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3.1 (Lemma 2.8), §2.4.
* [AF17f] `plans/plan-formalize-AF17.html`: WP16, finding F2 of gap (6), milestone M4.
-/

open Filter Metric Topology MvPolynomial

open scoped Polynomial

namespace AF

/-! ## Germs of finite sums -/

section GermSum

/-- The coercion of functions into germs commutes with finite sums.  Mathlib has the `simp` lemmas
for `+`, `*`, `0` and `1`; this is the `Finset.sum` case, which the transport needs constantly. -/
@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem germ_coe_finsetSum {α β ι : Type*} [CommSemiring β] (l : Filter α) (s : Finset ι)
    (g : ι → α → β) :
    ((∑ i ∈ s, g i : α → β) : Germ l β) = ∑ i ∈ s, ((g i : α → β) : Germ l β) :=
  map_sum (Filter.Germ.coeRingHom l) g s

end GermSum

/-! ## The realization subring is not a field -/

section NotField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω] {ι : Type*}
variable {φ : K →+* ℂ} {U : Set ℂ} {Φalg : Matrix ι ι Ω} {R : Subring Ω}
  {real : R →+* Germ (𝓟 U) ℂ} {Ψ : ℂ → Matrix ι ι ℂ}

/-- **The realization subring is never a field.**  Hence the injectivity of `real` cannot be had
from «a homomorphism out of a field is injective», and has to be assumed.

`X - C c` lies in `R` by `poly_mem` and is realized by `z ↦ z - φ(c)`, which vanishes at `φ(c)`;
in a field it would be a unit, and a unit of `Germ (𝓟 U) ℂ` — germs along a principal filter being
honest functions on `U` — cannot vanish anywhere on `U`. -/
@[category research solved, AMS 11 12 30, ref "AF22", group "af_mahler_alternative"]
theorem not_isField_of_mem (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ) {c : K}
    (hc : φ c ∈ U) : ¬ IsField R := by
  intro hfield
  set w : K[X] := Polynomial.X - Polynomial.C c with hw
  set x : R := ⟨toAmbient K Ω w, hbr.poly_mem w⟩ with hx
  -- `x` is not zero, because `K[z] → Ω` is injective
  have hinj : Function.Injective (toAmbient K Ω) := fun a b hab =>
    RatFunc.algebraMap_injective K ((algebraMap (RatFunc K) Ω).injective hab)
  have hw0 : w ≠ 0 := by
    rw [hw]
    intro h
    have := congrArg Polynomial.natDegree h
    simp at this
  have hx0 : x ≠ 0 := by
    rw [hx]
    intro h
    exact hw0 (hinj (by simpa using congrArg (Subring.subtype R) h))
  -- so it has an inverse, and `real` sends the identity `x·y = 1` to functions on `U`
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx0
  have hxy : real x * real y = 1 := by rw [← map_mul, hy, map_one]
  rw [hx, hbr.real_poly w] at hxy
  -- a germ along `𝓟 U` that vanishes at a point of `U` is not invertible
  have key : ∀ G : Germ (𝓟 U) ℂ,
      ((fun z : ℂ => (Polynomial.eval z (w.map φ)) : ℂ → ℂ) : Germ (𝓟 U) ℂ) * G ≠ 1 := by
    intro G
    induction G using Filter.Germ.inductionOn with
    | _ g =>
      rw [← Filter.Germ.coe_mul, show (1 : Germ (𝓟 U) ℂ) = ((1 : ℂ → ℂ) : Germ (𝓟 U) ℂ) from rfl,
        Ne, Filter.Germ.coe_eq, Filter.eventuallyEq_principal]
      intro h
      have h1 := h hc
      rw [hw] at h1
      simp at h1
  exact key _ hxy

end NotField

/-! ## The two interface extensions -/

section Interface

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω] {ι : Type*}

/-- **The solutions are realized too.**  `AF.IsBranchRealization` carries `K[z]` and the relation
matrix; the reverse transport needs the Mahler solutions `f : ι → Ω` to be the same objects as the
analytic `fs`, which is what this says. -/
@[category API, AMS 11 12 30, ref "AF22", group "af_mahler_alternative"]
structure IsSolutionRealization (l : Filter ℂ) (f : ι → Ω) (R : Subring Ω)
    (real : R →+* Germ l ℂ) (fs : ι → ℂ → ℂ) : Prop where
  /-- Every solution lies in the realization subring. -/
  sol_mem : ∀ i, f i ∈ R
  /-- …and is realized by the corresponding analytic solution. -/
  real_sol : ∀ i, real ⟨f i, sol_mem i⟩ = ((fs i : ℂ → ℂ) : Germ l ℂ)

/-- **Every element of the realization subring is an analytic function on `U`.**  This is what
makes the identity principle applicable to `real x` for an arbitrary `x`, and it is true of
[AF22]'s realization by construction: `R` consists of algebraic functions analytic on `U`. -/
@[category API, AMS 11 12 30, ref "AF22", group "af_mahler_alternative"]
def IsAnalyticRealization (U : Set ℂ) (R : Subring Ω) (real : R →+* Germ (𝓟 U) ℂ) : Prop :=
  ∀ x : R, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ real x = ((g : ℂ → ℂ) : Germ (𝓟 U) ℂ)

end Interface

/-! ## The identity principle, read through the realization -/

section Identity

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {U : Set ℂ} {R : Subring Ω} {real : R →+* Germ (𝓟 U) ℂ}

/-- **The identity principle for the realization.**  An element of `R` whose realizing function
vanishes on a neighbourhood of one point of `U` is zero — `U` being open and connected.

This is the whole of the reverse transport: everything else is bookkeeping. -/
@[category research solved, AMS 11 12 30, ref "AF22", group "af_mahler_alternative"]
theorem eq_zero_of_eventually_eq_zero (han : IsAnalyticRealization U R real)
    (hinj : Function.Injective real) (hUo : IsOpen U) (hconn : IsPreconnected U) {ξ : ℂ}
    (hξU : ξ ∈ U) {x : R} {g : ℂ → ℂ} (hx : real x = ((g : ℂ → ℂ) : Germ (𝓟 U) ℂ))
    (h0 : ∀ᶠ z in 𝓝 ξ, g z = 0) : (x : Ω) = 0 := by
  obtain ⟨G, hGan, hG⟩ := han x
  -- the analytic representative agrees with `g` on `U`
  have hEq : Set.EqOn G g U := by
    have h : ((G : ℂ → ℂ) : Germ (𝓟 U) ℂ) = ((g : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by rw [← hG, hx]
    exact Filter.eventuallyEq_principal.1 (Filter.Germ.coe_eq.1 h)
  -- hence it too vanishes near `ξ`
  have hG0 : G =ᶠ[𝓝 ξ] 0 := by
    filter_upwards [h0, hUo.mem_nhds hξU] with z hz hzU
    rw [hEq hzU, hz, Pi.zero_apply]
  -- the identity principle spreads that to the whole of `U`
  have hzero : Set.EqOn G 0 U :=
    hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hξU hG0
  have hreal0 : real x = 0 := by
    rw [hG, show (0 : Germ (𝓟 U) ℂ) = ((0 : ℂ → ℂ) : Germ (𝓟 U) ℂ) from rfl, Filter.Germ.coe_eq,
      Filter.eventuallyEq_principal]
    exact hzero
  have : x = 0 := hinj (by rw [hreal0, map_zero])
  exact congrArg (Subring.subtype R) this

end Identity

/-! ## The linear form, transported -/

section Transport

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι]
variable {φ : K →+* ℂ} {U : Set ℂ} {Φalg : Matrix ι ι Ω} {R : Subring Ω}
  {real : R →+* Germ (𝓟 U) ℂ} {Ψ : ℂ → Matrix ι ι ℂ} {f : ι → Ω} {fs : ι → ℂ → ℂ}

/-- The constants of `K`, read in the ambient field. -/
@[category API, AMS 11 12, ref "AF22", group "af_mahler_alternative"]
noncomputable def ambC (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra (RatFunc K) Ω] :
    K →+* Ω :=
  (toAmbient K Ω).comp (Polynomial.C : K →+* K[X])

/-- A constant of `K`, as an element of the realization subring. -/
@[category API, AMS 11 12, ref "AF22", group "af_mahler_alternative"]
noncomputable def constR (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ) (a : K) : R :=
  ⟨toAmbient K Ω (Polynomial.C a), hbr.poly_mem (Polynomial.C a)⟩

omit [Fintype ι] in
@[category API, AMS 11 12 30, ref "AF22", group "af_mahler_alternative"]
theorem real_constR (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ) (a : K) :
    real (constR hbr a) = ((fun _ : ℂ => φ a : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
  have h := hbr.real_poly (Polynomial.C a)
  simp only [Polynomial.map_C, Polynomial.eval_C] at h
  exact h

/-- **[AF22]'s linear form `F(Θ_{k₀}(z),z)`, as an element of the realization subring**: the
coefficient row `τ` times the normalized relation matrix `MΦ`, applied to the solutions. -/
@[category API, AMS 11 12 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def formR (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ)
    (hsr : IsSolutionRealization (𝓟 U) f R real fs) (τ : ι → K) (M : Matrix ι ι K) : R :=
  ∑ j, (∑ i, constR hbr (τ i) * ∑ l, constR hbr (M i l) * ⟨Φalg l j, hbr.mat_mem l j⟩) *
    ⟨f j, hsr.sol_mem j⟩

/-- **The transport**: the realization of `AF.formR` is [AF22]'s analytic `F(Θ_{k₀}(z),z)`. -/
@[category research solved, AMS 11 12 15 30, ref "AF22", group "af_mahler_alternative"]
theorem real_formR (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ)
    (hsr : IsSolutionRealization (𝓟 U) f R real fs) (τ : ι → K) (M : Matrix ι ι K) :
    real (formR hbr hsr τ M) =
      ((fun z => formVal (fun i => φ (τ i)) fs (M.map φ * Ψ z) z : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
  have hfun : (fun z => formVal (fun i => φ (τ i)) fs (M.map φ * Ψ z) z : ℂ → ℂ)
      = ∑ j, (∑ i, (fun _ : ℂ => φ (τ i)) * ∑ l, (fun _ : ℂ => φ (M i l)) * (fun z => Ψ z l j)) *
          fs j := by
    funext z
    simp only [Finset.sum_apply, Pi.mul_apply, formVal, Matrix.mul_apply, Matrix.map_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [formR, map_sum, hfun, germ_coe_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hsr.real_sol j, Filter.Germ.coe_mul]
  congr 1
  rw [map_sum, germ_coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, real_constR, Filter.Germ.coe_mul]
  congr 1
  rw [map_sum, germ_coe_finsetSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, real_constR, hbr.real_mat, Filter.Germ.coe_mul]

/-- The value of `AF.formR` in the ambient field: the coefficient row `τ(MΦ)` against the
solutions, which is the shape `AF.exists_lift_of_subst` consumes. -/
@[category API, AMS 11 12 15, ref "AF22", group "af_mahler_alternative"]
theorem coe_formR (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ)
    (hsr : IsSolutionRealization (𝓟 U) f R real fs) (τ : ι → K) (M : Matrix ι ι K) :
    ((formR hbr hsr τ M : R) : Ω)
      = ∑ j, (∑ i, ambC K Ω (τ i) * ∑ l, ambC K Ω (M i l) * Φalg l j) * f j := by
  push_cast [formR, constR, ambC]
  rfl

/-- **The reverse transport.**  [AF22] Lemma 2.11's conclusion — the linear form vanishes near `ξ`
as an analytic function — becomes the relation in `Ω` that [AF22] §2.4 substitutes into, i.e. the
hypothesis `hr` of `AF.exists_lift_of_subst`. -/
@[category research solved, AMS 11 12 15 30 39, ref "AF22", group "af_mahler_alternative"]
theorem relation_of_eventually_formVal_eq_zero
    (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ)
    (hsr : IsSolutionRealization (𝓟 U) f R real fs) (han : IsAnalyticRealization U R real)
    (hinj : Function.Injective real) (hUo : IsOpen U) (hconn : IsPreconnected U) {ξ : ℂ}
    (hξU : ξ ∈ U) (τ : ι → K) (M : Matrix ι ι K)
    (h0 : ∀ᶠ z in 𝓝 ξ, formVal (fun i => φ (τ i)) fs (M.map φ * Ψ z) z = 0) :
    ∑ j, (∑ i, ambC K Ω (τ i) * ∑ l, ambC K Ω (M i l) * Φalg l j) * f j = 0 := by
  have h := eq_zero_of_eventually_eq_zero han hinj hUo hconn hξU
    (real_formR hbr hsr τ M) h0
  rwa [coe_formR] at h

end Transport

end AF
