/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Invariant
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import BertinPisot.ModOneEquivalence
import ForMathlib.Analysis.Equidistribution.AddCircleWeyl
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Weak-\* toolbox for the realization converses

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Propositions 8 and 9.

Both halves of the realization converse — the ergodic one of `BB61/Realization.lean` and the
general one of `BB61/Saturation.lean` — read a statement about *orbits* as a statement about
*measures*, and then need to get back.  This file holds the three pieces of that traffic that
depend on neither ergodic theory nor the shift space:

* `tendsto_of_dense_of_tendsto_integral` — weak-\* convergence of probability measures may be
  tested on a **dense** set of bounded continuous functions (the usual `3ε`).  Together with
  separability of `C(𝕋, ℝ)` this replaces "for all test functions" by a countable condition.
* `tendsto_cesaro_sub_of_dist` — two orbits of a compact metric space that come together have
  the same Cesàro limits.  This is what makes the zero-padding of a one-sided word invisible.
* `equidistributed_of_tendsto_emp` — the **converse of `tendsto_emp_of_equidistributed`**:
  weak-\* convergence of the empirical measures to Haar measure *is* uniform distribution in
  the counting sense of `IsEquidistributedModuloOne`.  Weak-\* convergence contains the Weyl
  sums, and the converse half of Weyl's criterion is already proved in the repository
  (`Bertin.uniformlyDistributedModOne_of_weylCriterion`, whose `circBump` sandwich runs on
  `ForMathlib/Analysis/Equidistribution/AddCircleWeyl.lean`), so the bridge costs only the
  passage from a bounded-continuous test function to the two real characters.
-/

namespace BB61

open MeasureTheory Filter Topology BoundedContinuousFunction

/-! ## Weak-\* convergence tested on a dense family -/

section Dense

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- Two bounded continuous functions at distance `d` have integrals at distance at most `d`
against any probability measure. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_integral_sub_le_dist (ρ : ProbabilityMeasure Ω) (ψ φ : Ω →ᵇ ℝ) :
    |∫ x, ψ x ∂(ρ : Measure Ω) - ∫ x, φ x ∂(ρ : Measure Ω)| ≤ dist ψ φ := by
  have hbd : ∀ x, ‖(ψ : Ω → ℝ) x - (φ : Ω → ℝ) x‖ ≤ dist ψ φ := by
    intro x
    rw [dist_eq_norm]
    simpa using (ψ - φ).norm_coe_le_norm x
  rw [← integral_sub (ψ.integrable _) (φ.integrable _)]
  have := norm_integral_le_of_norm_le_const (μ := (ρ : Measure Ω))
    (f := fun x => (ψ : Ω → ℝ) x - (φ : Ω → ℝ) x) (C := dist ψ φ)
    (Eventually.of_forall hbd)
  simpa [Real.norm_eq_abs] using this

/-- Weak-\* convergence of probability measures may be tested on a **dense** family of
bounded continuous functions. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_of_dense_of_tendsto_integral {ν : ℕ → ProbabilityMeasure Ω}
    {lam : ProbabilityMeasure Ω} {D : Set (Ω →ᵇ ℝ)} (hD : Dense D)
    (h : ∀ φ ∈ D, Tendsto (fun N => ∫ x, φ x ∂(ν N : Measure Ω)) atTop
      (𝓝 (∫ x, φ x ∂(lam : Measure Ω)))) :
    Tendsto ν atTop (𝓝 lam) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro ψ
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨φ, hφD, hφ⟩ := Metric.mem_closure_iff.mp (hD.closure_eq ▸ Set.mem_univ ψ) (δ / 3)
    (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h φ hφD) (δ / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := abs_integral_sub_le_dist (ν n) ψ φ
  have h2 := abs_integral_sub_le_dist lam ψ φ
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have t1 : |∫ x, ψ x ∂(ν n : Measure Ω) - ∫ x, ψ x ∂(lam : Measure Ω)|
      ≤ |∫ x, ψ x ∂(ν n : Measure Ω) - ∫ x, φ x ∂(ν n : Measure Ω)|
        + |∫ x, φ x ∂(ν n : Measure Ω) - ∫ x, ψ x ∂(lam : Measure Ω)| := abs_sub_le _ _ _
  have t2 : |∫ x, φ x ∂(ν n : Measure Ω) - ∫ x, ψ x ∂(lam : Measure Ω)|
      ≤ |∫ x, φ x ∂(ν n : Measure Ω) - ∫ x, φ x ∂(lam : Measure Ω)|
        + |∫ x, φ x ∂(lam : Measure Ω) - ∫ x, ψ x ∂(lam : Measure Ω)| := abs_sub_le _ _ _
  have t3 : |∫ x, φ x ∂(lam : Measure Ω) - ∫ x, ψ x ∂(lam : Measure Ω)| ≤ dist ψ φ := by
    rw [abs_sub_comm]; exact h2
  linarith

end Dense

/-! ## Cesàro comparison of two nearby orbits -/

/-- If two sequences in a compact metric space come together, the Cesàro means of the
values of a bounded continuous function along them agree in the limit. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_cesaro_sub_of_dist {X : Type*} [MetricSpace X] [CompactSpace X] (G : X →ᵇ ℝ)
    {a b : ℕ → X} (h : Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), (G (a n) - G (b n))) / (N + 1))
      atTop (𝓝 0) := by
  have hu : Tendsto (fun n => G (a n) - G (b n)) atTop (𝓝 0) := by
    have hG : UniformContinuous (G : X → ℝ) :=
      CompactSpace.uniformContinuous_of_continuous G.continuous
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp hG ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have hab : dist (a n) (b n) < δ := by
      have := hN n hn
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at this
    have := hδ' hab
    rwa [Real.dist_eq, sub_zero, ← Real.dist_eq]
  have hces := hu.cesaro.comp (tendsto_add_atTop_nat 1)
  refine hces.congr fun N => ?_
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  ring

/-! ## The converse bridge: weak-\* convergence to Haar *is* uniform distribution -/

/-- The real part of the character `e(k ·)`, as a bounded continuous function on `𝕋`. -/
noncomputable def fourierRe (k : ℤ) : AddCircle (1 : ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => (fourier k z).re, Complex.continuous_re.comp (map_continuous (fourier k))⟩

/-- The imaginary part of the character `e(k ·)`, as a bounded continuous function on `𝕋`. -/
noncomputable def fourierIm (k : ℤ) : AddCircle (1 : ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => (fourier k z).im, Complex.continuous_im.comp (map_continuous (fourier k))⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integrable_fourier (k : ℤ) :
    Integrable (fun z : AddCircle (1 : ℝ) => fourier k z)
      (volume : Measure (AddCircle (1 : ℝ))) :=
  (map_continuous (fourier k)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourierRe_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ z, fourierRe k z ∂(haarT : Measure (AddCircle (1 : ℝ))) = 0 := by
  have hre : ∀ z : AddCircle (1 : ℝ), fourierRe k z = RCLike.re (fourier k z) := fun _ => rfl
  simp_rw [hre]
  rw [toMeasure_haarT, integral_re (integrable_fourier k), ← haarAddCircle_eq_volume,
    integral_fourier_eq_zero hk]
  simp

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourierIm_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ z, fourierIm k z ∂(haarT : Measure (AddCircle (1 : ℝ))) = 0 := by
  have him : ∀ z : AddCircle (1 : ℝ), fourierIm k z = RCLike.im (fourier k z) := fun _ => rfl
  simp_rw [him]
  rw [toMeasure_haarT, integral_im (integrable_fourier k), ← haarAddCircle_eq_volume,
    integral_fourier_eq_zero hk]
  simp

/-- Weak-\* convergence of the empirical measures to Haar measure contains, in particular, the
vanishing of every non-trivial Weyl sum. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem weylCriterion_of_tendsto_emp {s : ℕ → ℝ}
    (h : Tendsto (fun N => emp (fun n => ((s n : ℝ) : AddCircle (1 : ℝ))) N) atTop (𝓝 haarT)) :
    WeylCriterion s := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
  intro k hk
  set w : ℕ → ℂ := fun n => fourier k ((s n : ℝ) : AddCircle (1 : ℝ)) with hw
  have hA : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), (w n).re) / (N + 1))
      atTop (𝓝 0) := by
    have hlim := h (fourierRe k)
    rw [integral_fourierRe_eq_zero hk] at hlim
    exact hlim.congr fun N => integral_emp _ _ _
  have hB : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), (w n).im) / (N + 1))
      atTop (𝓝 0) := by
    have hlim := h (fourierIm k)
    rw [integral_fourierIm_eq_zero hk] at hlim
    exact hlim.congr fun N => integral_emp _ _ _
  have hsplit : ∀ N : ℕ, (∑ n ∈ Finset.range (N + 1), w n)
      = ((∑ n ∈ Finset.range (N + 1), (w n).re : ℝ) : ℂ)
        + ((∑ n ∈ Finset.range (N + 1), (w n).im : ℝ) : ℂ) * Complex.I := by
    intro N
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => (Complex.re_add_im (w n)).symm
  have hcplx : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), w n) / ((N : ℂ) + 1))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ =>
        (((∑ n ∈ Finset.range (N + 1), (w n).re) / (N + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have hc := (Complex.continuous_ofReal.tendsto 0).comp hA
      simp only [Function.comp_def, Complex.ofReal_zero] at hc
      exact hc
    have h2 : Tendsto (fun N : ℕ =>
        (((∑ n ∈ Finset.range (N + 1), (w n).im) / (N + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have hc := (Complex.continuous_ofReal.tendsto 0).comp hB
      simp only [Function.comp_def, Complex.ofReal_zero] at hc
      exact hc
    have hlim := h1.add (h2.mul (tendsto_const_nhds (x := Complex.I)))
    rw [zero_mul, add_zero] at hlim
    refine hlim.congr fun N => ?_
    rw [hsplit N]
    push_cast
    ring
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hcplx.congr fun N => ?_
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [hw]
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- **The converse of `tendsto_emp_of_equidistributed`.**  If the empirical measures of
`(s n mod 1)` converge weak-\* to Haar measure on `𝕋`, then `(s n)` is uniformly distributed
modulo one in the counting sense.

Weak-\* convergence contains the Weyl sums (`weylCriterion_of_tendsto_emp`), and the converse
half of Weyl's criterion — the `circBump` sandwich of
`ForMathlib/Analysis/Equidistribution/AddCircleWeyl.lean`, carried out in
`BertinPisot/UniformDistribution.lean` — turns those into the counting statement. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem equidistributed_of_tendsto_emp {s : ℕ → ℝ}
    (h : Tendsto (fun N => emp (fun n => ((s n : ℝ) : AddCircle (1 : ℝ))) N) atTop (𝓝 haarT)) :
    IsEquidistributedModuloOne s :=
  (Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne s).mp
    (Bertin.uniformlyDistributedModOne_of_weylCriterion s (weylCriterion_of_tendsto_emp h))

end BB61
