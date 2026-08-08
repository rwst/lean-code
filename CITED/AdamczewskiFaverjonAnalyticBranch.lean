/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] Lemma 2.8(b): an algebraic function has an analytic branch

The analytic half of plan-formalize-AF17's **WP8**, and the only place in [AF22] §2 where the
Puiseux realization of the ambient field `A` is used for anything but algebra (gate **G3**):

> *«Each coordinate of `φ(z)` defines an analytic function on some neighborhood of `α^{q^k}`.»*

Because the coordinates of `φ(z)` are algebraic over `ℚ̄(z)`, and (§2.4) are polynomials in one
primitive element `ϕ`, the whole statement reduces to producing an **analytic branch** of one
algebraic function at one non-critical point:

  given `P ∈ ℂ[z][T]`, `ξ, t₀ ∈ ℂ` with `P(ξ,t₀) = 0` and `∂P/∂T (ξ,t₀) ≠ 0`, there is a
  function `g`, analytic at `ξ`, with `g(ξ) = t₀` and `P(z, g(z)) = 0` near `ξ`.

This is `AF.exists_analytic_branch`.  Gate G3 costed it at 150–300 lines on top of Mathlib's
bivariate implicit function theorem, which is what it takes.

## Why the implicit function theorem is not enough by itself

`implicitFunctionOfBivariate` produces a function `g` with `P(z, g(z)) = P(ξ,t₀)` near `ξ`, and
differentiability **at the single point `ξ`** — a strict Fréchet derivative there.  Analyticity of
a function of a complex variable needs differentiability on a *neighbourhood*
(`Complex.analyticAt_iff_eventually_differentiableAt`).  The upgrade is the standard bootstrap,
and is the bulk of this file: at every `z'` near `ξ` the pair `(z', g(z'))` again satisfies the
hypotheses of the theorem — it is a root, and `∂P/∂T` is still non-zero there by continuity — so
the theorem applies again and produces a function `h` differentiable at `z'`; the *local
uniqueness* clause of the theorem (`eventually_apply_eq_iff_implicitFunctionOfBivariate`), applied
on an open set around `(ξ,t₀)` where it is valid, forces `g = h` near `z'`, so `g` is
differentiable at `z'` too.

## What is *not* here

[AF22]'s Lemma 2.8 asserts the conclusion «for `k ≫ 1`», which they get from *«an algebraic
function has only finitely many singularities and finitely many zeros»*.  Turning that into the
statement that all but finitely many `ξ` are non-critical needs a resultant/discriminant argument:
Mathlib has `Polynomial.resultant` but not the theorem that it vanishes exactly at the parameters
where the two polynomials share a root, so the finiteness half is *not* formalized here.  It is
not needed to state the branch lemma, and in [AF22]'s proof it is used only to *choose* the single
index `k₀` of (2.8), which WP10 may equally take as a hypothesis.

## Contents

* `AF.bipoly`, `AF.bipolyDZ`, `AF.bipolyDT` — a bivariate polynomial and its two partial
  derivatives, as functions `ℂ → ℂ → ℂ`, with their continuity and differentiability;
* `AF.exists_implicit_branch` — the raw output of the implicit function theorem at a point where
  `∂P/∂T ≠ 0`: value, local equation, local uniqueness, differentiability at the point;
* **`AF.exists_analytic_branch`** — [AF22] Lemma 2.8(b).

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.2.3 (Lemma 2.8).
* [AF17f] `plans/plan-formalize-AF17.html`: WP8, gate G3 (§2.8).
-/

open Filter Topology Polynomial
open scoped Polynomial

namespace AF

/-! ## A bivariate polynomial and its partial derivatives -/

section Bipoly

variable (p : Polynomial (Polynomial ℂ))

/-- The function `(z,t) ↦ P(z,t)` attached to `P ∈ ℂ[z][T]`. -/
@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def bipoly (z t : ℂ) : ℂ := Polynomial.eval₂ (Polynomial.evalRingHom z) t p

/-- The partial derivative `∂P/∂z`. -/
@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def bipolyDZ (z t : ℂ) : ℂ :=
  ∑ k ∈ p.support, (Polynomial.derivative (p.coeff k)).eval z * t ^ k

/-- The partial derivative `∂P/∂T`. -/
@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def bipolyDT (z t : ℂ) : ℂ := bipoly (Polynomial.derivative p) z t

@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem bipoly_eq_sum (z t : ℂ) :
    bipoly p z t = ∑ k ∈ p.support, (p.coeff k).eval z * t ^ k := by
  rw [bipoly, Polynomial.eval₂_eq_sum, Polynomial.sum]
  rfl

@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem continuous_bipoly : Continuous fun v : ℂ × ℂ => bipoly p v.1 v.2 := by
  simp only [bipoly_eq_sum]
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((p.coeff k).continuous.comp continuous_fst).mul (continuous_snd.pow k)

@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem continuous_bipolyDZ : Continuous fun v : ℂ × ℂ => bipolyDZ p v.1 v.2 := by
  simp only [bipolyDZ]
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((Polynomial.derivative (p.coeff k)).continuous.comp continuous_fst).mul
    (continuous_snd.pow k)

@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem continuous_bipolyDT : Continuous fun v : ℂ × ℂ => bipolyDT p v.1 v.2 :=
  continuous_bipoly _

/-- `∂P/∂z` really is the derivative in the first variable. -/
@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem hasDerivAt_bipoly_fst (z t : ℂ) :
    HasDerivAt (fun z => bipoly p z t) (bipolyDZ p z t) z := by
  simp only [bipoly_eq_sum, bipolyDZ]
  have hfun : (fun z => ∑ k ∈ p.support, (p.coeff k).eval z * t ^ k) =
      ∑ k ∈ p.support, fun z => (p.coeff k).eval z * t ^ k := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun]
  exact HasDerivAt.sum fun k _ => ((p.coeff k).hasDerivAt z).mul_const (t ^ k)

/-- `∂P/∂T` really is the derivative in the second variable. -/
@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem hasDerivAt_bipoly_snd (z t : ℂ) :
    HasDerivAt (fun t => bipoly p z t) (bipolyDT p z t) t := by
  have hmap : (fun t => bipoly p z t) = fun t => (p.map (Polynomial.evalRingHom z)).eval t := by
    funext t
    rw [bipoly, Polynomial.eval₂_eq_eval_map]
  rw [hmap]
  have h := (p.map (Polynomial.evalRingHom z)).hasDerivAt t
  rwa [Polynomial.derivative_map, ← Polynomial.eval₂_eq_eval_map] at h

/-- The first partial derivative as a continuous linear map. -/
@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def fderivZ (z t : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (bipolyDZ p z t)

/-- The second partial derivative as a continuous linear map. -/
@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def fderivT (z t : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (bipolyDT p z t)

@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem continuous_smulRight_one :
    Continuous fun c : ℂ => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c := by
  have h : (fun c : ℂ => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c) =
      fun c : ℂ => c • (ContinuousLinearMap.id ℂ ℂ) := by
    funext c
    refine ContinuousLinearMap.ext fun x => ?_
    simp [mul_comm]
  rw [h]
  exact continuous_id.smul continuous_const

@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem continuous_fderivZ : Continuous (Function.uncurry (fderivZ p)) :=
  continuous_smulRight_one.comp (continuous_bipolyDZ p)

@[category API, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem continuous_fderivT : Continuous (Function.uncurry (fderivT p)) :=
  continuous_smulRight_one.comp (continuous_bipolyDT p)

end Bipoly

/-! ## The implicit branch -/

section Branch

variable (p : Polynomial (Polynomial ℂ))

/-- **The implicit function theorem at a non-critical point of `P`.**  At any `(z₀,t₀)` with
`∂P/∂T (z₀,t₀) ≠ 0` there is a function `g` with `g(z₀) = t₀`, satisfying `P(z, g(z)) = P(z₀,t₀)`
near `z₀`, *characterizing* the solutions of that equation near `(z₀,t₀)`, and differentiable at
`z₀`.  No hypothesis that `(z₀,t₀)` is a root is needed. -/
@[category research solved, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem exists_implicit_branch {z₀ t₀ : ℂ} (hd : bipolyDT p z₀ t₀ ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = t₀ ∧ (∀ᶠ z in 𝓝 z₀, bipoly p z (g z) = bipoly p z₀ t₀) ∧
      (∀ᶠ v in 𝓝 ((z₀, t₀) : ℂ × ℂ),
        (bipoly p v.1 v.2 = bipoly p z₀ t₀ ↔ g v.1 = v.2)) ∧
      DifferentiableAt ℂ g z₀ := by
  have df₁ : ∀ᶠ v in 𝓝 ((z₀, t₀) : ℂ × ℂ),
      HasFDerivAt (fun z => bipoly p z v.2) (fderivZ p v.1 v.2) v.1 :=
    Filter.Eventually.of_forall fun v => (hasDerivAt_bipoly_fst p v.1 v.2).hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 ((z₀, t₀) : ℂ × ℂ),
      HasFDerivAt (fun t => bipoly p v.1 t) (fderivT p v.1 v.2) v.2 :=
    Filter.Eventually.of_forall fun v => (hasDerivAt_bipoly_snd p v.1 v.2).hasFDerivAt
  have cf₁ : ContinuousAt (Function.uncurry (fderivZ p)) ((z₀, t₀) : ℂ × ℂ) :=
    (continuous_fderivZ p).continuousAt
  have cf₂ : ContinuousAt (Function.uncurry (fderivT p)) ((z₀, t₀) : ℂ × ℂ) :=
    (continuous_fderivT p).continuousAt
  have hinv : (fderivT p ((z₀, t₀) : ℂ × ℂ).1 ((z₀, t₀) : ℂ × ℂ).2).IsInvertible :=
    ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hd), rfl⟩
  refine ⟨implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv, ?_, ?_, ?_, ?_⟩
  · have h := (eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂
      hinv).self_of_nhds
    exact h.1 rfl
  · exact eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv
  · exact eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv
  · exact (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂
      hinv).hasFDerivAt.differentiableAt

/-- **[AF22] Lemma 2.8(b).**  *«Each coordinate of `φ(z)` defines an analytic function on some
neighborhood of `α^{q^k}`.»*

An algebraic function has an **analytic branch** through every non-critical root: if
`P(ξ,t₀) = 0` and `∂P/∂T(ξ,t₀) ≠ 0`, some `g` analytic at `ξ` takes the value `t₀` there and
satisfies `P(z,g(z)) = 0` throughout a neighbourhood.

The implicit function theorem gives differentiability at `ξ` only; analyticity comes from
re-applying it at each nearby point of the graph and gluing with its local-uniqueness clause. -/
@[category research solved, AMS 12 30, ref "AF22", group "af_mahler_alternative"]
theorem exists_analytic_branch {ξ t₀ : ℂ} (hroot : bipoly p ξ t₀ = 0)
    (hd : bipolyDT p ξ t₀ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ξ ∧ g ξ = t₀ ∧ ∀ᶠ z in 𝓝 ξ, bipoly p z (g z) = 0 := by
  obtain ⟨g, hgval, hgroot, hgiff, hgdiff⟩ := exists_implicit_branch p hd
  rw [hroot] at hgroot hgiff
  refine ⟨g, ?_, hgval, hgroot⟩
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  -- an *open* set around `(ξ, t₀)` on which the implicit function characterizes the solutions
  obtain ⟨U, hU, hUopen, hUmem⟩ := mem_nhds_iff.1 hgiff
  have hcont : ContinuousAt (fun z => (z, g z)) ξ :=
    continuousAt_id.prodMk hgdiff.continuousAt
  have hgraph : (ξ, g ξ) ∈ U := by rw [hgval]; exact hUmem
  have hmemU : ∀ᶠ z in 𝓝 ξ, (z, g z) ∈ U :=
    hcont.preimage_mem_nhds (hUopen.mem_nhds hgraph)
  have hDT : ∀ᶠ z in 𝓝 ξ, bipolyDT p z (g z) ≠ 0 := by
    have hc : ContinuousAt (fun z => bipolyDT p z (g z)) ξ :=
      (continuous_bipolyDT p).continuousAt.comp hcont
    refine hc.eventually_ne ?_
    rw [hgval]
    exact hd
  filter_upwards [hmemU, hgroot, hDT] with z' hz'U hz'root hz'DT
  -- apply the implicit function theorem again, at the point `(z', g z')` of the graph
  obtain ⟨h, hval, hhroot, _, hhdiff⟩ := exists_implicit_branch p hz'DT
  have hEq : g =ᶠ[𝓝 z'] h := by
    have h1 : ∀ᶠ w in 𝓝 z', (w, h w) ∈ U := by
      have hc : ContinuousAt (fun w => (w, h w)) z' :=
        continuousAt_id.prodMk hhdiff.continuousAt
      refine hc.preimage_mem_nhds (hUopen.mem_nhds ?_)
      rw [hval]
      exact hz'U
    filter_upwards [h1, hhroot] with w hwU hwroot
    exact (hU hwU).1 (hwroot.trans hz'root)
  exact hhdiff.congr_of_eventuallyEq hEq

end Branch

end AF
