/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Realization
import BB61.ProductFormula
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.ZeroOne
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M5 Theorem 1: the limit law at a generic word

Formal companion of `note-1061-M5.html` (milestone M5 of `plans/plan-1061.html`), Theorem 1
and its corollaries, quadratic case.

`BB61/ProductFormula.lean` evaluates the Fourier coefficients of `F_*μ_p` — a statement about
a *measure*.  Theorem 1 is what turns it into a statement about the *points* of `C(α)`:

> Let `ν` be a shift-invariant measure on `{0,1}^ℕ`, `ν̂` its natural extension to `{0,1}^ℤ`,
> and let `ε` be `ν`-generic.  Then the orbit of `ξ = π(ε)` has limit law `F_*ν̂`; in
> particular it is u.d. mod one iff `F_*ν̂ = Leb`.

The note reads this as "M1 Prop. 8(i) with `μ`-a.e. `ω` is generic replaced by let `ε` be
generic — the proof never used more".  That is exactly the shape here: `BB61/Realization.lean`
produced *some* generic `ω` from Birkhoff and then padded; this file takes the genericity as a
hypothesis on the given `ε`, and must therefore do the one step Prop. 8(i) did not: transport
genericity from the one-sided space `{0,1}^ℕ` to the two-sided model.

## The transport, and why it costs nothing extra

The note's proof runs through "cylinders are a convergence-determining class on `{0,1}^ℤ`",
i.e. through `ν_N → ν̂` on the shift space.  That is the one form `BB61/Realization.lean`
explicitly declines to prove, because it needs a modulus of continuity for *every*
`φ ∈ C({0,1}^ℤ, ℝ)` and the product topology has no Mathlib support for that.  The route
taken here is the same one that file takes for `λ_N`: use `F`'s **own** modulus, which
`BB61/Factor.lean` already supplies.

Concretely, for a test function `G` on the circle and a window `L`, the composite

`gTest G L : {0,1}^ℕ → ℝ`,  `δ ↦ G(F(σ^{L+1} δ̃))`  (`δ̃ = padZ δ`)

is bounded continuous on the one-sided space, so genericity of `ε` applies to it verbatim.
Its values along the one-sided orbit differ from the values of `G ∘ F` along the two-sided
orbit of `ε̃` by at most `padErr L = (1+|β|)|β|^{L+1}/(1-|β|)` in the circle metric — this is
`abs_fRaw_sub_padZ_le`, the padding estimate of `BB61/Realization.lean`, applied at time
`L+1` instead of at time `n` — and the same estimate compares `∫ gTest dν` with `∫ G∘F dν̂`
once `ν = futures_*ν̂` and `ν̂` is shift-invariant.  Since `padErr L → 0` and `G` is uniformly
continuous on the compact circle, a `4ε` argument closes it.  Only two further bookkeeping
facts are needed: shifting a Cesàro average by `L+1` places costs `2(L+1)‖G‖/(N+1)`
(`abs_cesaro_shift_le`), and shift-invariance may be iterated (`integral_comp_shiftZ_iterate`).

So the whole of the note's §3 is here, with `IsNaturalExtension` in place of a construction of
`ν̂`: the hypotheses are that `μ` is `σ`-invariant and that its future marginal is `ν`, which
is precisely what a natural extension is and precisely what the proof uses.  Mathlib has no
natural-extension functor, but the case that matters — Bernoulli — is *given* by
`Measure.infinitePi`, and `isNaturalExtension_bern` verifies both axioms from
`Measure.map_infinitePi_infinitePi_of_inj`.

## What comes out

* `tendsto_emp_of_generic` — **Theorem 1**: `λ_N → F_*ν̂` weak-\*.
* `equidistributed_iff_map_eq_haarT` — its "in particular": u.d. iff `F_*ν̂ = Leb`.
* `tendsto_weylSum_of_generic` — the Fourier form, `N⁻¹∑ e(hξαⁿ) → \widehat{F_*ν̂}(h)`.
* `ae_isGenericFor_of_ergodic` — **Corollary 2**, the a.e. form, by Birkhoff.
* `isNaturalExtension_bern` — the Bernoulli natural extension.
* `ergodic_shiftN_bernN` — the one-sided Bernoulli shift is **ergodic**.
* `tendsto_weylSum_bern` — **Corollary 4 with the constant**: at a Bernoulli(`p`)-generic
  word the Weyl sums converge to `G_p(h)`, the product of M5 Theorem 2.
* `not_equidistributed_of_bern_half_generic` — **Corollary 4 at `p = 1/2`**: a fair-coin
  generic digit word gives a point of `C(α)` whose orbit is *not* u.d. mod one, for every
  quadratic Pisot `α > 2`; `…_twoAddSqrt3` is the instance at `α = 2+√3`.
* `ae_not_equidistributed_bern_half` and `measure_equidistributed_bern_half_eq_zero` —
  **Corollary 5**, i.e. [MF67] Th. II.2.2: the words whose orbit is u.d. form a
  `μ_{1/2}`-null set.  `…_twoAddSqrt3` is the instance.

Ergodicity of the Bernoulli shift is not in Mathlib and is proved here from what is: measure
preservation is one more reindexing, and pre-ergodicity is **Kolmogorov's 0–1 law**
(`measure_zero_or_one_of_measurableSet_limsup_atTop`) applied to the independent coordinate
σ-algebras of `Measure.infinitePi` — a strictly invariant `t` equals `(σⁿ)⁻¹ t` for every `n`,
hence lies in the tail field.  Besides Corollary 5 this is what makes the whole file
non-vacuous: `exists_isGenericFor_bern` says the hypothesis "`ε` is Bernoulli(`p`)-generic"
is satisfiable.

What is **not** here: Corollary 6 (the multiplier version, `λ ∈ ℤ[α]`), which needs the
second ladder `c^λ_m` and a second coding `F^λ`; and the discrepancy floor of Corollary 4,
which needs Koksma's inequality -- now recorded as a cited axiom in
`CITED/KoksmaInequality.lean` (with the star discrepancy, which Mathlib lacks), so what is left
between it and Corollary 4 is the total variation of the characters, `V(cos 2 pi h x) = 4h`.
-/

namespace BB61

open MeasureTheory Filter Topology BoundedContinuousFunction
open TopologicalSpace (SeparableSpace exists_countable_dense)

/-! ## The one-sided shift, and genericity -/

/-- The one-sided shift `(σ ε)_k = ε_{k+1}` on `{0,1}^ℕ`. -/
def shiftN (ε : ℕ → Bool) : ℕ → Bool := fun k => ε (k + 1)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_shiftN : Continuous shiftN :=
  continuous_pi fun k => continuous_apply (k + 1)

/-- Iterating the one-sided shift is `BB61/Defs.lean`'s indexed shift. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shiftN_iterate (ε : ℕ → Bool) (n : ℕ) : shiftN^[n] ε = shift ε n := by
  induction n generalizing ε with
  | zero => funext k; simp [shift]
  | succ n ih =>
      funext k
      rw [Function.iterate_succ_apply, ih]
      simp only [shift, shiftN]
      congr 1
      omega

/-- The future half `ω ↦ ω⁺` is continuous. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_futures : Continuous (futures : Shift → ℕ → Bool) :=
  continuous_pi fun _ => continuous_apply _

/-- Zero-padding `ε ↦ ε̃` is continuous. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_padZ : Continuous (padZ : (ℕ → Bool) → Shift) := by
  refine continuous_pi fun k => ?_
  simp only [padZ]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- The empirical measures of the *one-sided* orbit of `ε`. -/
noncomputable def orbitEmpN (ε : ℕ → Bool) (N : ℕ) : ProbabilityMeasure (ℕ → Bool) :=
  emp (fun n => shift ε n) N

/-- `ε` is **generic** for `ν`: the empirical measures of its one-sided orbit converge
weak-\* to `ν`.  This is the note's `N⁻¹∑_{n<N} δ_{σⁿ ε} → ν`. -/
def IsGenericFor (ν : ProbabilityMeasure (ℕ → Bool)) (ε : ℕ → Bool) : Prop :=
  Tendsto (fun N => orbitEmpN ε N) atTop (𝓝 ν)

/-- `μ` on `{0,1}^ℤ` is a **natural extension** of `ν` on `{0,1}^ℕ`: it is `σ`-invariant and
its future marginal is `ν`.  These are the two properties of `ν̂` that Theorem 1 uses; the
note defines `ν̂` by "`ν̂` of a cylinder = `ν` of the same word", which is the same thing. -/
structure IsNaturalExtension (ν : ProbabilityMeasure (ℕ → Bool))
    (μ : ProbabilityMeasure Shift) : Prop where
  /-- `μ` is invariant under the two-sided shift. -/
  invariant : pmap continuous_shiftZ.measurable μ = μ
  /-- The future marginal of `μ` is `ν`. -/
  marginal : pmap continuous_futures.measurable μ = ν

/-! ## Two pieces of bookkeeping -/

/-- Shift-invariance of `μ`, in integral form. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_comp_shiftZ {μ : ProbabilityMeasure Shift}
    (hinv : pmap continuous_shiftZ.measurable μ = μ) (φ : Shift →ᵇ ℝ) :
    ∫ ζ, φ (shiftZ ζ) ∂(μ : Measure Shift) = ∫ ζ, φ ζ ∂(μ : Measure Shift) := by
  have h := integral_pmap continuous_shiftZ μ φ
  rw [hinv] at h
  exact h.symm

/-- Shift-invariance of `μ`, iterated. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_comp_shiftZ_iterate {μ : ProbabilityMeasure Shift}
    (hinv : pmap continuous_shiftZ.measurable μ = μ) (m : ℕ) (φ : Shift →ᵇ ℝ) :
    ∫ ζ, φ (shiftZ^[m] ζ) ∂(μ : Measure Shift) = ∫ ζ, φ ζ ∂(μ : Measure Shift) := by
  induction m generalizing φ with
  | zero => simp
  | succ m ih =>
      set ψ : Shift →ᵇ ℝ := φ.compContinuous ⟨shiftZ, continuous_shiftZ⟩ with hψ
      have hstep : ∀ ζ : Shift, φ (shiftZ^[m + 1] ζ) = ψ (shiftZ^[m] ζ) := by
        intro ζ
        rw [Function.iterate_succ_apply']
        rfl
      simp only [hstep]
      rw [ih ψ]
      exact integral_comp_shiftZ hinv φ

/-- A finite block of a uniformly bounded sequence has a bounded sum. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_sum_range_le {u : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |u n| ≤ C) (a m : ℕ) :
    |∑ i ∈ Finset.range m, u (a + i)| ≤ m * C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range m, |u (a + i)|
      ≤ ∑ _i ∈ Finset.range m, C := Finset.sum_le_sum fun i _ => hC _
  _ = m * C := by simp [mul_comm]

/-- **Shifting a Cesàro average.**  Advancing a uniformly bounded sequence by `m` places
changes its Cesàro mean by at most `2mC/(N+1)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_cesaro_shift_le {u : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |u n| ≤ C) (m N : ℕ) :
    |(∑ n ∈ Finset.range (N + 1), u (m + n)) / (N + 1)
        - (∑ n ∈ Finset.range (N + 1), u n) / (N + 1)|
      ≤ 2 * m * C / (N + 1) := by
  have e1 : ∑ i ∈ Finset.range (m + (N + 1)), u i
      = (∑ i ∈ Finset.range m, u i) + ∑ i ∈ Finset.range (N + 1), u (m + i) :=
    Finset.sum_range_add u m (N + 1)
  have e2 : ∑ i ∈ Finset.range ((N + 1) + m), u i
      = (∑ i ∈ Finset.range (N + 1), u i) + ∑ i ∈ Finset.range m, u ((N + 1) + i) :=
    Finset.sum_range_add u (N + 1) m
  have e3 : m + (N + 1) = (N + 1) + m := by omega
  rw [e3] at e1
  have key : (∑ n ∈ Finset.range (N + 1), u (m + n)) - (∑ n ∈ Finset.range (N + 1), u n)
      = (∑ i ∈ Finset.range m, u ((N + 1) + i)) - ∑ i ∈ Finset.range m, u i := by
    rw [e2] at e1; linarith
  have hb1 := abs_sum_range_le hC (N + 1) m
  have hb2 := abs_sum_range_le hC 0 m
  simp only [Nat.zero_add] at hb2
  have hnum : |(∑ n ∈ Finset.range (N + 1), u (m + n)) - ∑ n ∈ Finset.range (N + 1), u n|
      ≤ 2 * m * C := by
    rw [key]
    exact (abs_sub _ _).trans (by linarith)
  rw [div_sub_div_same, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)]
  exact div_le_div_of_nonneg_right hnum (by positivity) |>.trans_eq rfl

/-! ## The Weyl sums of a weak-\* limit -/

/-- **The Fourier form of weak-\* convergence.**  If the empirical measures of `(s n mod 1)`
converge weak-\* to `lam`, then every Weyl sum converges to the matching Fourier coefficient
of `lam`.  `weylCriterion_of_tendsto_emp` is the case `lam = Leb`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_weylSum_of_tendsto_emp {s : ℕ → ℝ} {lam : ProbabilityMeasure (AddCircle (1 : ℝ))}
    (h : Tendsto (fun N => emp (fun n => ((s n : ℝ) : AddCircle (1 : ℝ))) N) atTop (𝓝 lam))
    (k : ℤ) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range (N + 1), cexp1 ((k : ℝ) * s n)) / ((N : ℂ) + 1))
      atTop (𝓝 (∫ z, fourier k z ∂(lam : Measure (AddCircle (1 : ℝ))))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
  have hint : Integrable (fun z : AddCircle (1 : ℝ) => fourier k z)
      (lam : Measure (AddCircle (1 : ℝ))) :=
    (map_continuous (fourier k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  set J : ℂ := ∫ z, fourier k z ∂(lam : Measure (AddCircle (1 : ℝ))) with hJ
  have hre : ∫ z, fourierRe k z ∂(lam : Measure (AddCircle (1 : ℝ))) = J.re := by
    show ∫ z, RCLike.re (fourier k z) ∂(lam : Measure (AddCircle (1 : ℝ))) = J.re
    rw [integral_re hint]
    rfl
  have him : ∫ z, fourierIm k z ∂(lam : Measure (AddCircle (1 : ℝ))) = J.im := by
    show ∫ z, RCLike.im (fourier k z) ∂(lam : Measure (AddCircle (1 : ℝ))) = J.im
    rw [integral_im hint]
    rfl
  set w : ℕ → ℂ := fun n => fourier k ((s n : ℝ) : AddCircle (1 : ℝ)) with hw
  have hA : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), (w n).re) / (N + 1))
      atTop (𝓝 J.re) := by
    have hlim := h (fourierRe k)
    rw [hre] at hlim
    exact hlim.congr fun N => integral_emp _ _ _
  have hB : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), (w n).im) / (N + 1))
      atTop (𝓝 J.im) := by
    have hlim := h (fourierIm k)
    rw [him] at hlim
    exact hlim.congr fun N => integral_emp _ _ _
  have hsplit : ∀ N : ℕ, (∑ n ∈ Finset.range (N + 1), w n)
      = ((∑ n ∈ Finset.range (N + 1), (w n).re : ℝ) : ℂ)
        + ((∑ n ∈ Finset.range (N + 1), (w n).im : ℝ) : ℂ) * Complex.I := by
    intro N
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => (Complex.re_add_im (w n)).symm
  have h1 : Tendsto (fun N : ℕ =>
      (((∑ n ∈ Finset.range (N + 1), (w n).re) / (N + 1) : ℝ) : ℂ)) atTop (𝓝 (J.re : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hA
  have h2 : Tendsto (fun N : ℕ =>
      (((∑ n ∈ Finset.range (N + 1), (w n).im) / (N + 1) : ℝ) : ℂ)) atTop (𝓝 (J.im : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hB
  have hlim := h1.add (h2.mul (tendsto_const_nhds (x := Complex.I)))
  rw [Complex.re_add_im] at hlim
  refine hlim.congr fun N => ?_
  have hcast : ∀ n : ℕ, w n = cexp1 ((k : ℝ) * s n) := by
    intro n
    show fourier k ((s n : ℝ) : AddCircle (1 : ℝ)) = cexp1 ((k : ℝ) * s n)
    rw [cexp1, fourier_coe_apply]
    congr 1
    push_cast
    ring
  simp only [hcast] at hsplit ⊢
  rw [hsplit N]
  push_cast
  ring

/-! ## Codings: the data Theorem 1 consumes

The proof of Theorem 1 uses only four things about the factor map `F` of
`BB61/Factor.lean`: that it is continuous, that its value at time `L+1` is insensitive to
replacing a two-sided word by its zero-padded future up to a null modulus `err L`, that
`err → 0`, and — as a hypothesis of the theorem, not of the map — that it computes the
orbit.  A `Coding` is exactly that data.  `F` is one (`QuadSetup.coding`); so is each
multiplier twist `F^λ` of `BB61/Multiplier.lean`, which is why Theorem 1 is proved once,
here, rather than once per coding. -/

/-- A **coding**: a continuous map `{0,1}^ℤ → 𝕋` together with a null padding modulus.  See
`Coding.tendsto_emp_of_generic`. -/
structure Coding where
  /-- the coding map -/
  toFun : Shift → AddCircle (1 : ℝ)
  /-- the coding map is continuous -/
  continuous : Continuous toFun
  /-- the padding modulus at window `L` -/
  err : ℕ → ℝ
  /-- the modulus is non-negative -/
  err_nonneg : ∀ L, 0 ≤ err L
  /-- the modulus is null -/
  tendsto_err : Tendsto err atTop (𝓝 0)
  /-- **the padding estimate**: read `L+1` steps out, zero-padding the past of `ω` moves the
  coding by at most `err L` -/
  dist_padZ_le : ∀ (ω : Shift) (L : ℕ),
    dist (toFun (shiftZ^[L + 1] (padZ (futures ω)))) (toFun (shiftZ^[L + 1] ω)) ≤ err L

namespace Coding

variable (C : Coding)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurable : Measurable C.toFun := C.continuous.measurable

/-- The test function on `{0,1}^ℕ` that Theorem 1 feeds to genericity: `δ ↦ G(F(σ^{L+1} δ̃))`,
the circle observable `G` read `L+1` steps into the future of the zero-padded word.  Pushing
the reading time out to `L+1` is what makes the padding invisible: at time `L+1` the coding
sees only coordinates `> 0`, where `δ̃` carries `δ` itself. -/
noncomputable def testFun (G : AddCircle (1 : ℝ) →ᵇ ℝ) (L : ℕ) : (ℕ → Bool) →ᵇ ℝ :=
  G.compContinuous ⟨fun δ => C.toFun (shiftZ^[L + 1] (padZ δ)),
    C.continuous.comp ((continuous_shiftZ.iterate _).comp continuous_padZ)⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem testFun_apply (G : AddCircle (1 : ℝ) →ᵇ ℝ) (L : ℕ) (δ : ℕ → Bool) :
    C.testFun G L δ = G (C.toFun (shiftZ^[L + 1] (padZ δ))) := rfl

/-- The one-sided orbit of `ε`, read by `testFun`, tracks the two-sided orbit of `ε̃` at time
`n + L + 1`, to within `err L`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dist_testFun_orbit (ε : ℕ → Bool) (L n : ℕ) :
    dist (C.toFun (shiftZ^[L + 1] (padZ (shift ε n))))
      (C.toFun (shiftZ^[(L + 1) + n] (padZ ε))) ≤ C.err L := by
  have h1 : shift ε n = futures (shiftZ^[n] (padZ ε)) := (futures_iterate_padZ ε n).symm
  have h2 : shiftZ^[(L + 1) + n] (padZ ε) = shiftZ^[L + 1] (shiftZ^[n] (padZ ε)) :=
    Function.iterate_add_apply shiftZ (L + 1) n (padZ ε)
  rw [h1, h2]
  exact C.dist_padZ_le (shiftZ^[n] (padZ ε)) L

/-! ### Theorem 1, for an arbitrary coding -/

/-- **M5 Theorem 1, the limit law at a generic word — abstract form.**  Let `μ` be a natural
extension of `ν`, let `ε` be `ν`-generic, and let the coding `C` compute the sequence `s`
along the padded orbit of `ε`.  Then the empirical measures of `(s n mod 1)` converge weak-\*
to `C_*μ`.

The note's proof runs through "cylinders are a convergence-determining class", i.e. through
`ν_N → ν̂` on the shift space; this proof never proves that.  It uses `C`'s own modulus
instead: `testFun G L` is bounded continuous on the one-sided space, so genericity applies to
it verbatim, and the padding estimate compares it with `G ∘ C` along the two-sided orbit and
`∫ testFun dν` with `∫ G∘C dμ`.  A `4ε` argument closes it. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_emp_of_generic {ν : ProbabilityMeasure (ℕ → Bool)}
    {μ : ProbabilityMeasure Shift} (hne : IsNaturalExtension ν μ)
    {ε : ℕ → Bool} (hgen : IsGenericFor ν ε) {s : ℕ → ℝ}
    (horb : ∀ n, C.toFun (shiftZ^[n] (padZ ε)) = ((s n : ℝ) : AddCircle (1 : ℝ))) :
    Tendsto (fun N => emp (fun n => ((s n : ℝ) : AddCircle (1 : ℝ))) N) atTop
      (𝓝 (pmap C.measurable μ)) := by
  refine tendsto_of_dense_of_tendsto_integral (D := Set.univ) dense_univ fun G _ => ?_
  set Φ : Shift →ᵇ ℝ := G.compContinuous ⟨C.toFun, C.continuous⟩ with hΦ
  set u : ℕ → ℝ := fun n => Φ (shiftZ^[n] (padZ ε)) with hu
  set I : ℝ := ∫ ζ, Φ ζ ∂(μ : Measure Shift) with hI
  have hgoalR : ∫ z, G z ∂(pmap C.measurable μ : Measure (AddCircle (1 : ℝ))) = I :=
    integral_pmap C.continuous μ G
  have hgoalL : ∀ N : ℕ,
      ∫ z, G z ∂(emp (fun n => ((s n : ℝ) : AddCircle (1 : ℝ))) N
          : Measure (AddCircle (1 : ℝ)))
        = (∑ n ∈ Finset.range (N + 1), u n) / (N + 1) := by
    intro N
    rw [integral_emp]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hu, hΦ]
    exact congrArg G (horb n).symm
  have hCu : ∀ n : ℕ, |u n| ≤ ‖Φ‖ := fun n => by
    simpa [Real.norm_eq_abs] using Φ.norm_coe_le_norm (shiftZ^[n] (padZ ε))
  have main : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), u n) / (N + 1))
      atTop (𝓝 I) := by
    refine Metric.tendsto_atTop.mpr fun η hη => ?_
    set η' : ℝ := η / 5 with hη'def
    have hη' : 0 < η' := by positivity
    -- the circle observable is uniformly continuous
    have hGuc : UniformContinuous (G : AddCircle (1 : ℝ) → ℝ) :=
      CompactSpace.uniformContinuous_of_continuous G.continuous
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp hGuc η' hη'
    -- a window at which the padding is invisible to `G`
    obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp C.tendsto_err δ hδ
    have hLδ : C.err L < δ := by
      have h := hL L le_rfl
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (C.err_nonneg L)] at h
    set g : (ℕ → Bool) →ᵇ ℝ := C.testFun G L with hg
    set J : ℝ := ∫ x, g x ∂(ν : Measure (ℕ → Bool)) with hJ
    -- (a) the one-sided orbit reads the two-sided one, shifted by `L+1`
    have hstep : ∀ n : ℕ, |g (shift ε n) - u ((L + 1) + n)| ≤ η' := by
      intro n
      have hd : dist (C.toFun (shiftZ^[L + 1] (padZ (shift ε n))))
          (C.toFun (shiftZ^[(L + 1) + n] (padZ ε))) < δ :=
        lt_of_le_of_lt (C.dist_testFun_orbit ε L n) hLδ
      have := hδ' hd
      rw [Real.dist_eq] at this
      exact this.le
    -- (b) the two limits are close
    have hJI : |J - I| ≤ η' := by
      set g' : Shift →ᵇ ℝ := g.compContinuous ⟨futures, continuous_futures⟩ with hg'
      set Ψ : Shift →ᵇ ℝ :=
        Φ.compContinuous ⟨fun ζ => shiftZ^[L + 1] ζ, continuous_shiftZ.iterate _⟩ with hΨ
      have hJ' : J = ∫ ζ, g' ζ ∂(μ : Measure Shift) := by
        rw [hJ, ← hne.marginal]
        exact integral_pmap continuous_futures μ g
      have hΨI : ∫ ζ, Ψ ζ ∂(μ : Measure Shift) = I :=
        integral_comp_shiftZ_iterate hne.invariant (L + 1) Φ
      have hdist : dist g' Ψ ≤ η' := by
        refine (BoundedContinuousFunction.dist_le hη'.le).mpr fun ζ => ?_
        have hd : dist (C.toFun (shiftZ^[L + 1] (padZ (futures ζ))))
            (C.toFun (shiftZ^[L + 1] ζ)) < δ :=
          lt_of_le_of_lt (C.dist_padZ_le ζ L) hLδ
        exact (hδ' hd).le
      have hab := abs_integral_sub_le_dist μ g' Ψ
      rw [← hJ', hΨI] at hab
      exact hab.trans hdist
    -- (c) genericity
    have hBlim : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), g (shift ε n)) / (N + 1))
        atTop (𝓝 J) := by
      have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hgen g
      exact h.congr fun N => integral_emp _ _ _
    -- (d) averaging (a)
    have hAB : ∀ N : ℕ,
        |(∑ n ∈ Finset.range (N + 1), u ((L + 1) + n)) / (N + 1)
            - (∑ n ∈ Finset.range (N + 1), g (shift ε n)) / (N + 1)| ≤ η' := by
      intro N
      have h1 : (∑ n ∈ Finset.range (N + 1), u ((L + 1) + n))
          - (∑ n ∈ Finset.range (N + 1), g (shift ε n))
          = ∑ n ∈ Finset.range (N + 1), (u ((L + 1) + n) - g (shift ε n)) := by
        rw [Finset.sum_sub_distrib]
      have h2 : |∑ n ∈ Finset.range (N + 1), (u ((L + 1) + n) - g (shift ε n))|
          ≤ ((N : ℝ) + 1) * η' := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ n ∈ Finset.range (N + 1), |u ((L + 1) + n) - g (shift ε n)|
            ≤ ∑ _n ∈ Finset.range (N + 1), η' :=
              Finset.sum_le_sum fun n _ => by rw [abs_sub_comm]; exact hstep n
        _ = ((N : ℝ) + 1) * η' := by simp
      rw [div_sub_div_same, h1, abs_div,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1),
        div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      linarith
    -- (e) the Cesàro shift
    have hCS : ∀ N : ℕ,
        |(∑ n ∈ Finset.range (N + 1), u ((L + 1) + n)) / (N + 1)
            - (∑ n ∈ Finset.range (N + 1), u n) / (N + 1)|
          ≤ 2 * ((L : ℝ) + 1) * ‖Φ‖ / ((N : ℝ) + 1) := by
      intro N
      have h := abs_cesaro_shift_le hCu (L + 1) N
      push_cast at h
      exact h
    have hzero : Tendsto (fun N : ℕ => 2 * ((L : ℝ) + 1) * ‖Φ‖ / ((N : ℝ) + 1))
        atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (2 * ((L : ℝ) + 1) * ‖Φ‖)).comp
        (tendsto_add_atTop_nat 1)
      refine h.congr fun N => ?_
      simp only [Function.comp_apply]
      push_cast
      ring
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hBlim η' hη'
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hzero η' hη'
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have hb := hN₁ N (le_of_max_le_left hN)
    have hz := hN₂ N (le_of_max_le_right hN)
    rw [Real.dist_eq] at hb hz ⊢
    rw [sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ((L : ℝ) + 1) * ‖Φ‖ / ((N : ℝ) + 1))]
      at hz
    have c1 := abs_sub_le ((∑ n ∈ Finset.range (N + 1), u n) / ((N : ℝ) + 1))
      ((∑ n ∈ Finset.range (N + 1), u ((L + 1) + n)) / ((N : ℝ) + 1)) I
    have c2 := abs_sub_le ((∑ n ∈ Finset.range (N + 1), u ((L + 1) + n)) / ((N : ℝ) + 1))
      ((∑ n ∈ Finset.range (N + 1), g (shift ε n)) / ((N : ℝ) + 1)) I
    have c3 := abs_sub_le ((∑ n ∈ Finset.range (N + 1), g (shift ε n)) / ((N : ℝ) + 1)) J I
    have c4 : |(∑ n ∈ Finset.range (N + 1), u n) / ((N : ℝ) + 1)
          - (∑ n ∈ Finset.range (N + 1), u ((L + 1) + n)) / ((N : ℝ) + 1)|
        = |(∑ n ∈ Finset.range (N + 1), u ((L + 1) + n)) / ((N : ℝ) + 1)
          - (∑ n ∈ Finset.range (N + 1), u n) / ((N : ℝ) + 1)| := abs_sub_comm _ _
    linarith [hCS N, hAB N, hJI]
  rw [hgoalR]
  exact main.congr fun N => (hgoalL N).symm

/-- **Theorem 1, the "in particular" — abstract form.**  A generic word gives an orbit that is
u.d. mod one exactly when the limit law is Lebesgue. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem equidistributed_iff_map_eq_haarT {ν : ProbabilityMeasure (ℕ → Bool)}
    {μ : ProbabilityMeasure Shift} (hne : IsNaturalExtension ν μ)
    {ε : ℕ → Bool} (hgen : IsGenericFor ν ε) {s : ℕ → ℝ}
    (horb : ∀ n, C.toFun (shiftZ^[n] (padZ ε)) = ((s n : ℝ) : AddCircle (1 : ℝ))) :
    IsEquidistributedModuloOne s ↔ pmap C.measurable μ = haarT := by
  constructor
  · intro hud
    exact tendsto_nhds_unique (C.tendsto_emp_of_generic hne hgen horb)
      (tendsto_emp_of_equidistributed hud)
  · intro hmap
    refine equidistributed_of_tendsto_emp ?_
    simpa [hmap] using C.tendsto_emp_of_generic hne hgen horb

/-- **Theorem 1, Fourier form — abstract form.**  At a `ν`-generic word the Weyl sums converge
to the Fourier coefficients of the limit law `C_*μ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_weylSum_of_generic {ν : ProbabilityMeasure (ℕ → Bool)}
    {μ : ProbabilityMeasure Shift} (hne : IsNaturalExtension ν μ)
    {ε : ℕ → Bool} (hgen : IsGenericFor ν ε) {s : ℕ → ℝ}
    (horb : ∀ n, C.toFun (shiftZ^[n] (padZ ε)) = ((s n : ℝ) : AddCircle (1 : ℝ))) (k : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), cexp1 ((k : ℝ) * s n)) / ((N : ℂ) + 1))
      atTop (𝓝 (∫ z, fourier k z ∂(Measure.map C.toFun (μ : Measure Shift)))) := by
  have h := tendsto_weylSum_of_tendsto_emp (C.tendsto_emp_of_generic hne hgen horb) k
  rwa [toMeasure_pmap] at h

end Coding


/-! ## The padding modulus -/

namespace QuadSetup

variable (P : QuadSetup)

/-- The factor map is `1`-Lipschitz for `fRaw`: reduction mod one does not increase
distances. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dist_fMap_le (a b : Shift) : dist (P.fMap a) (P.fMap b) ≤ |P.fRaw a - P.fRaw b| := by
  rw [dist_eq_norm]
  have h : P.fMap a - P.fMap b = ((P.fRaw a - P.fRaw b : ℝ) : AddCircle (1 : ℝ)) := by
    simp [QuadSetup.fMap]
  rw [h]
  simpa [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ))
      (m := P.fRaw a - P.fRaw b))

/-- The **padding error at window `L`**: `(1+|β|)|β|^{L+1}/(1-|β|)`, the note's `C_α ρ^{L+1}
/(1-ρ)`.  It is the price of replacing the two-sided word by its zero-padded future, read
`L+1` steps into the future. -/
noncomputable def padErr (L : ℕ) : ℝ := (1 + |P.β|) * |P.β| ^ (L + 1) / (1 - |P.β|)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem padErr_nonneg (L : ℕ) : 0 ≤ P.padErr L := by
  have hβ := P.abs_beta_lt_one
  have hd : (0 : ℝ) < 1 - |P.β| := by linarith
  unfold padErr
  exact div_nonneg (by positivity) hd.le

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_padErr : Tendsto P.padErr atTop (𝓝 0) := by
  have hβ := P.abs_beta_lt_one
  have hpow : Tendsto (fun L : ℕ => |P.β| ^ (L + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg P.β) hβ).comp (tendsto_add_atTop_nat 1)
  have h := (hpow.const_mul (1 + |P.β|)).div_const (1 - |P.β|)
  rw [mul_zero, zero_div] at h
  exact h

/-- **The padding estimate on the circle.**  Replacing `ω` by its zero-padded future moves
`F(σ^{L+1}·)` by at most `padErr L`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dist_fMap_padZ_futures (ω : Shift) (L : ℕ) :
    dist (P.fMap (shiftZ^[L + 1] (padZ (futures ω)))) (P.fMap (shiftZ^[L + 1] ω))
      ≤ P.padErr L :=
  (P.dist_fMap_le _ _).trans (P.abs_fRaw_sub_padZ_le ω L)

/-! ## `F` as a coding -/

/-- **The factor map, packaged as a `Coding`.**  Every field is already proved: continuity is
`BB61/Factor.lean`'s `continuous_fMap`, the modulus is `padErr`.  This is what lets Theorem 1
be quoted rather than re-run — for `F` here, and for the multiplier twists `F^λ` of
`BB61/Multiplier.lean`. -/
noncomputable def coding : Coding where
  toFun := P.fMap
  continuous := P.continuous_fMap
  err := P.padErr
  err_nonneg := P.padErr_nonneg
  tendsto_err := P.tendsto_padErr
  dist_padZ_le := P.dist_fMap_padZ_futures

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coding_toFun : P.coding.toFun = P.fMap := rfl

/-! ## Theorem 1 -/

/-- **M5 Theorem 1, the limit law at a generic word.**  Let `μ` be a natural extension of `ν`
and let `ε` be `ν`-generic.  Then the empirical measures of the orbit of `ξ = π(ε)` converge
weak-\* to `F_*μ`.

This is M1 Proposition 8(i) with "some `μ`-generic `ω` exists by Birkhoff" replaced by "let
`ε` be generic", and with the limit *named*: M1 Theorem 7 says every limit point is some
`F_*μ`; here the whole sequence converges and `μ` is `ν̂`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_emp_of_generic {ν : ProbabilityMeasure (ℕ → Bool)}
    {μ : ProbabilityMeasure Shift} (hne : IsNaturalExtension ν μ)
    {ε : ℕ → Bool} (hgen : IsGenericFor ν ε) :
    Tendsto (fun N => emp (fun n => ((piVal P.α ε * P.α ^ n : ℝ) : AddCircle (1 : ℝ))) N) atTop
      (𝓝 (pmap P.measurable_fMap μ)) :=
  P.coding.tendsto_emp_of_generic hne hgen (P.fMap_iterate_padZ ε)

/-- **Theorem 1, the "in particular".**  A generic word gives an orbit that is u.d. mod one
exactly when the limit law is Lebesgue. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem equidistributed_iff_map_eq_haarT {ν : ProbabilityMeasure (ℕ → Bool)}
    {μ : ProbabilityMeasure Shift} (hne : IsNaturalExtension ν μ)
    {ε : ℕ → Bool} (hgen : IsGenericFor ν ε) :
    IsEquidistributedModuloOne (fun n : ℕ => piVal P.α ε * P.α ^ n)
      ↔ pmap P.measurable_fMap μ = haarT :=
  P.coding.equidistributed_iff_map_eq_haarT hne hgen (P.fMap_iterate_padZ ε)

/-- **Theorem 1, Fourier form.**  At a `ν`-generic word the Weyl sums converge to the Fourier
coefficients of the limit law `F_*ν̂`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_weylSum_of_generic {ν : ProbabilityMeasure (ℕ → Bool)}
    {μ : ProbabilityMeasure Shift} (hne : IsNaturalExtension ν μ)
    {ε : ℕ → Bool} (hgen : IsGenericFor ν ε) (k : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1),
        cexp1 ((k : ℝ) * (piVal P.α ε * P.α ^ n))) / ((N : ℂ) + 1))
      atTop (𝓝 (∫ z, fourier k z ∂(Measure.map P.fMap (μ : Measure Shift)))) :=
  P.coding.tendsto_weylSum_of_generic hne hgen (P.fMap_iterate_padZ ε) k

end QuadSetup

/-! ## Corollary 2: the a.e. form -/

/-- **M5 Corollary 2.**  For an ergodic shift-invariant `ν` on `{0,1}^ℕ`, `ν`-a.e. word is
`ν`-generic.  This is Birkhoff, applied to a countable dense family of test functions so that
one `ν`-full set serves them all. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ae_isGenericFor_of_ergodic (ν : ProbabilityMeasure (ℕ → Bool))
    (hν : Ergodic shiftN (ν : Measure (ℕ → Bool))) :
    ∀ᵐ ε ∂(ν : Measure (ℕ → Bool)), IsGenericFor ν ε := by
  have : IsProbabilityMeasure (ν : Measure (ℕ → Bool)) := ν.2
  have : SeparableSpace ((ℕ → Bool) →ᵇ ℝ) := by
    have h := ContinuousMap.isometryEquivBoundedOfCompact (ℕ → Bool) ℝ
    exact h.surjective.denseRange.separableSpace h.continuous
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ((ℕ → Bool) →ᵇ ℝ)
  have hbirk : ∀ g ∈ D, ∀ᵐ ε ∂(ν : Measure (ℕ → Bool)),
      Tendsto (fun n => birkhoffAverage ℝ shiftN (g : (ℕ → Bool) → ℝ) n ε) atTop
        (𝓝 (∫ x, g x ∂(ν : Measure (ℕ → Bool)))) := fun g _ =>
    tendsto_birkhoffAverage_of_ergodic hν (g.integrable _)
  filter_upwards [(ae_ball_iff hDc).mpr hbirk] with ε hε
  refine tendsto_of_dense_of_tendsto_integral hDd fun g hg => ?_
  have h2 := (hε g hg).comp (tendsto_add_atTop_nat 1)
  refine h2.congr fun N => ?_
  rw [Function.comp_apply, birkhoffAverage_eq_div]
  simp only [orbitEmpN]
  rw [integral_emp]
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [shiftN_iterate]

/-! ## The Bernoulli natural extension -/

/-- The one-sided Bernoulli(`p`) product measure on `{0,1}^ℕ`. -/
noncomputable def bernN (p : ℝ) : Measure (ℕ → Bool) := Measure.infinitePi fun _ : ℕ => bern p

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isProbabilityMeasure_bernN {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (bernN p) := by
  have := isProbabilityMeasure_bern h0 h1
  unfold bernN
  infer_instance

/-- Bernoulli(`p`) on `{0,1}^ℕ`, bundled. -/
noncomputable def bernNP {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : ProbabilityMeasure (ℕ → Bool) :=
  ⟨bernN p, isProbabilityMeasure_bernN h0 h1⟩

/-- Bernoulli(`p`) on `{0,1}^ℤ`, bundled. -/
noncomputable def bernZP {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : ProbabilityMeasure Shift :=
  ⟨bernZ p, isProbabilityMeasure_bernZ h0 h1⟩

/-- **The two-sided Bernoulli measure is a natural extension of the one-sided one.**  Both
axioms are instances of `Measure.map_infinitePi_infinitePi_of_inj`: the shift is
reindexing by `k ↦ k+1` on `ℤ`, the future marginal is reindexing by `j ↦ j+1` from `ℕ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isNaturalExtension_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsNaturalExtension (bernNP h0 h1) (bernZP h0 h1) := by
  have := isProbabilityMeasure_bern h0 h1
  constructor
  · refine ProbabilityMeasure.toMeasure_injective ?_
    rw [toMeasure_pmap]
    show Measure.map shiftZ (bernZ p) = bernZ p
    have hinj : Function.Injective (fun k : ℤ => k + 1) := fun a b h => by simpa using h
    have h2 : (shiftZ : Shift → Shift)
        = fun (ω : Shift) (i : ℤ) => ω ((fun k : ℤ => k + 1) i) := rfl
    rw [bernZ, h2]
    exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℤ => bern p) hinj
  · refine ProbabilityMeasure.toMeasure_injective ?_
    rw [toMeasure_pmap]
    show Measure.map futures (bernZ p) = bernN p
    have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + 1) := by
      intro a b h
      have h' : (a : ℤ) + 1 = (b : ℤ) + 1 := h
      omega
    have h2 : (futures : Shift → ℕ → Bool)
        = fun (ω : Shift) (i : ℕ) => ω ((fun j : ℕ => (j : ℤ) + 1) i) := rfl
    rw [bernZ, bernN, h2]
    exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℤ => bern p) hinj

/-- **The one-sided Bernoulli shift is ergodic.**  Measure preservation is the reindexing
`k ↦ k+1` of `Measure.map_infinitePi_infinitePi_of_inj`; pre-ergodicity is Kolmogorov's 0–1
law, because a strictly invariant set is `(σⁿ)⁻¹` of itself for every `n` and therefore lies
in the tail field `limsup_n σ(ω_n, ω_{n+1}, …)` of the independent coordinate σ-algebras.

Mathlib has no ergodicity statement for a Bernoulli shift; this supplies the one input that
`ae_isGenericFor_of_ergodic` needs at the measures M5 is about. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ergodic_shiftN_bernN {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Ergodic shiftN (bernN p) := by
  have hbern := isProbabilityMeasure_bern h0 h1
  have hmp : MeasurePreserving shiftN (bernN p) (bernN p) := by
    refine ⟨continuous_shiftN.measurable, ?_⟩
    have hinj : Function.Injective (fun k : ℕ => k + 1) := fun a b h => by simpa using h
    have h2 : (shiftN : (ℕ → Bool) → ℕ → Bool)
        = fun (ω : ℕ → Bool) (i : ℕ) => ω ((fun k : ℕ => k + 1) i) := rfl
    rw [bernN, h2]
    exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => bern p) hinj
  refine ⟨hmp, ?_⟩
  set sig : ℕ → MeasurableSpace (ℕ → Bool) :=
    fun n => MeasurableSpace.comap (fun ω : ℕ → Bool => ω n) inferInstance with hsig
  have h_le : ∀ n, sig n ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
    fun n => (measurable_pi_apply n).comap_le
  have h_indep : ProbabilityTheory.iIndep sig (bernN p) := by
    have h := ProbabilityTheory.iIndepFun_infinitePi (Ω := fun _ : ℕ => Bool)
      (𝓧 := fun _ : ℕ => Bool) (P := fun _ : ℕ => bern p) (X := fun _ b => b)
      (fun _ => measurable_id)
    rw [ProbabilityTheory.iIndepFun_iff_iIndep] at h
    exact h
  refine ⟨fun t ht hinv => ?_⟩
  have htail : MeasurableSet[Filter.limsup sig atTop] t := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro n
    have hiter : (shiftN^[n]) ⁻¹' t = t := Function.IsFixedPt.preimage_iterate hinv n
    have hmeas : Measurable[⨆ i ≥ n, sig i] (shiftN^[n] : (ℕ → Bool) → ℕ → Bool) := by
      refine Measurable.of_comap_le ?_
      show MeasurableSpace.comap (shiftN^[n]) MeasurableSpace.pi ≤ ⨆ i ≥ n, sig i
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun a => ?_
      rw [MeasurableSpace.comap_comp]
      have heq : ((fun f : ℕ → Bool => f a) ∘ (shiftN^[n] : (ℕ → Bool) → ℕ → Bool))
          = fun ω : ℕ → Bool => ω (n + a) := by
        funext ω
        simp only [Function.comp_apply]
        rw [shiftN_iterate]
        rfl
      rw [heq]
      exact le_iSup₂ (f := fun i (_ : n ≤ i) => sig i) (n + a) (by omega)
    rw [← hiter]
    exact hmeas ht
  have hprob : IsProbabilityMeasure (bernN p) := isProbabilityMeasure_bernN h0 h1
  rcases ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop
    h_le h_indep htail with hz0 | hz1
  · exact eventuallyConst_set'.mpr (Or.inl (by simpa using hz0))
  · refine eventuallyConst_set'.mpr (Or.inr ?_)
    have hc : bernN p tᶜ = 0 := by
      rw [measure_compl ht (measure_ne_top _ _), hz1, measure_univ, tsub_self]
    simpa using hc

/-- **Bernoulli-a.e. word is generic** — Corollary 2 at the measures M5 is about. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ae_isGenericFor_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∀ᵐ ε ∂(bernN p), IsGenericFor (bernNP h0 h1) ε :=
  ae_isGenericFor_of_ergodic (bernNP h0 h1) (ergodic_shiftN_bernN h0 h1)

/-- Generic words exist.  This is what makes the Bernoulli corollaries below non-vacuous. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_isGenericFor_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ ε : ℕ → Bool, IsGenericFor (bernNP h0 h1) ε := by
  have : IsProbabilityMeasure (bernN p) := isProbabilityMeasure_bernN h0 h1
  exact (ae_isGenericFor_bern h0 h1).exists

namespace QuadSetup

variable (P : QuadSetup)

/-- **M5 Corollary 4, with the constant.**  At a Bernoulli(`p`)-generic digit word the Weyl
sums of the orbit converge to `G_p(h)`, the Erdős product of M5 Theorem 2.  This is the
`(α-1)`-adapted [BM86] Th. XIV.1 in the form the note proves it, with the limit *evaluated*
rather than merely shown to exist. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_weylSum_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {ε : ℕ → Bool} (hgen : IsGenericFor (bernNP h0 h1) ε) (k : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1),
        cexp1 ((k : ℝ) * (piVal P.α ε * P.α ^ n))) / ((N : ℂ) + 1))
      atTop (𝓝 (P.weylC p (k : ℝ))) := by
  have h := P.tendsto_weylSum_of_generic (isNaturalExtension_bern h0 h1) hgen k
  rwa [show ((bernZP h0 h1 : ProbabilityMeasure Shift) : Measure Shift) = bernZ p from rfl,
    P.integral_fourier_map_fMap h0 h1 k] at h

/-- **M5 Corollary 4 at the fair coin.**  For every quadratic Pisot `α > 2`, a digit word
generic for the fair coin gives a point `ξ = π(ε)` of `C(α)` whose orbit `(ξ αⁿ)` is **not**
uniformly distributed modulo one.

The limit law is `F_*μ_{1/2}`, whose first Fourier coefficient is `G_{1/2}(1) ≠ 0`
(`BB61/ProductFormula.lean`), so it is not Lebesgue; Theorem 1 transports that from the
measure to the point. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_bern_half_generic (h2 : 2 < P.α) (hirr : Irrational P.α)
    {ε : ℕ → Bool}
    (hgen : IsGenericFor (bernNP (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)) ε) :
    ¬ IsEquidistributedModuloOne (fun n : ℕ => piVal P.α ε * P.α ^ n) := by
  intro hud
  have hmap := (P.equidistributed_iff_map_eq_haarT
    (isNaturalExtension_bern (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1))
    hgen).mp hud
  have := congrArg (fun ρ : ProbabilityMeasure (AddCircle (1 : ℝ)) =>
    (ρ : Measure (AddCircle (1 : ℝ)))) hmap
  rw [toMeasure_pmap, toMeasure_haarT] at this
  exact P.map_fMap_bernZ_half_ne_volume h2 hirr this

/-- **M5 Corollary 5 — [MF67] Theorem II.2.2, reproved.**  For every quadratic Pisot `α > 2`
the set of digit words whose point of `C(α)` has an equidistributed orbit is `μ_{1/2}`-null.
At `p = 1/2` this is Mauduit–France's `σ(B ∩ C(α)) = 0`, the coin-flipping measure on the
Cantor set being the natural `σ` there.

The route is the note's: Birkhoff (`ae_isGenericFor_bern`) plus one Fourier coefficient
(`BB61/ProductFormula.lean`), rather than [MF67]'s density-point bootstrap. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ae_not_equidistributed_bern_half (h2 : 2 < P.α) (hirr : Irrational P.α) :
    ∀ᵐ ε ∂(bernN (1 / 2)),
      ¬ IsEquidistributedModuloOne (fun n : ℕ => piVal P.α ε * P.α ^ n) := by
  filter_upwards [ae_isGenericFor_bern (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 ≤ 1)] with ε hε
  exact P.not_equidistributed_of_bern_half_generic h2 hirr hε

/-- Corollary 5 as a null-set statement. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measure_equidistributed_bern_half_eq_zero (h2 : 2 < P.α) (hirr : Irrational P.α) :
    bernN (1 / 2)
      {ε : ℕ → Bool | IsEquidistributedModuloOne fun n : ℕ => piVal P.α ε * P.α ^ n} = 0 := by
  have h := P.ae_not_equidistributed_bern_half h2 hirr
  rw [ae_iff] at h
  simpa using h

/-- The instance of `BB61/Bernoulli.lean`: at `α = 2 + √3`, no fair-coin generic word gives an
equidistributed orbit. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_bern_half_generic_twoAddSqrt3 {ε : ℕ → Bool}
    (hgen : IsGenericFor (bernNP (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)) ε) :
    ¬ IsEquidistributedModuloOne (fun n : ℕ => piVal twoAddSqrt3.α ε * twoAddSqrt3.α ^ n) :=
  twoAddSqrt3.not_equidistributed_of_bern_half_generic two_lt_twoAddSqrt3
    irrational_twoAddSqrt3 hgen

/-- Corollary 5 at `α = 2 + √3`: `σ(B ∩ C(2+√3)) = 0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ae_not_equidistributed_bern_half_twoAddSqrt3 :
    ∀ᵐ ε ∂(bernN (1 / 2)), ¬ IsEquidistributedModuloOne
      (fun n : ℕ => piVal twoAddSqrt3.α ε * twoAddSqrt3.α ^ n) :=
  twoAddSqrt3.ae_not_equidistributed_bern_half two_lt_twoAddSqrt3 irrational_twoAddSqrt3

end QuadSetup

end BB61
