/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.PriceCompleteness
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Lower bounds for `E_H(α)` by linear programming

`BB61/Price.lean` and `BB61/PriceCompleteness.lean` proved the *price* of a certificate,

`⨅_{a ∈ ℂ^H} P(ψ_a) = E_H(α)`   (Theorem 3.4 of `paper.tex`, Theorem B(iii)),

and Corollary 3.5 turned it into a completeness statement: 10.61 holds at `α` **iff** some
`E_H(α)` falls below the entropy floor `½ log α`.  Read from the other side, that equality says a
*failed* certificate search is a theorem as soon as `E_H(α)` can be bounded from **below**, and
this file is the machine that produces such bounds — Theorem 9.1 of `paper.tex`, the dual of
Theorem 3.4:

> Let `ν_1, …, ν_m ∈ M(σ)` be any invariant measures.  Then
> `E_H(α) ≥ max { ∑_j λ_j h(ν_j) : λ ∈ Δ_m, ∑_j λ_j Φ_h(ν_j) = 0 for 1 ≤ h ≤ H }`,
> a linear program.  If the value exceeds `h_min(α)`, no trigonometric certificate of degree
> `≤ H` exists at `α`.  If the optimal mixture only satisfies `|Φ_h| ≤ ε`, the bound degrades by
> at most `ε‖a‖₁` for the optimiser's multiplier vector `a`.

Everything here is proved from Lean's three standard axioms.  In particular the consumer
`floor_lt_partitionPressure_of_le_priceEntropy` — "no certificate of this degree exists" — needs
neither the variational principle nor the Ledrappier–Young floor: it runs on
`BB61.priceEntropy_le_iInf_partitionPressure`, whose only ingredient is the *Jensen* half of the
variational principle, a theorem of `ForMathlib/Dynamics/TopologicalPressure.lean`.

## Main results

* `BB61.FlatPool` — the feasible point of the linear program: finitely many invariant measures,
  convex weights, and exact flatness `∑_j λ_j Φ_h(ν_j) = 0` on the mode set.
* `BB61.FlatPool.entropy_le_priceEntropy` — **Theorem 9.1**: `∑_j λ_j h(ν_j) ≤ E_H(α)`.
* `BB61.sub_le_measurePressure_of_approxFlat`, `BB61.sub_le_partitionPressure_of_approxFlat` —
  **the degradation clause**: a pool flat only to `ε` still gives
  `∑_j λ_j h(ν_j) − ε‖a‖₁ ≤ P(ψ_a)` for every `a`.
* `BB61.floor_lt_partitionPressure_of_le_priceEntropy` — the consumer: a lower bound on `E_H(α)`
  above the floor forbids every degree-`H` pressure certificate.
* `BB61.forall_le_floor_lt_partitionPressure`, `BB61.not_priceEntropy_lt_of_le`,
  `BB61.lt_entDegree_of_le_priceEntropy` — the same at every degree `≤ H₀`, since `E_H(α)` is
  non-increasing in `H`.
* `BB61.norm_one_lt_of_partitionPressure_lt` — the quantitative form of the degradation clause: a
  certificate that beats a pool of entropy `e` and defect `ε` must have `‖a‖₁ > (e − h_min)/ε`.

## What the three ingredients are

The proof is three lines of the dictionary, and each is an already-proved structural fact:

| step | ingredient |
| --- | --- |
| a convex combination of invariant measures is invariant | `Measure.map_add`, `Measure.map_smul` |
| the moments are affine in the measure | the integral is linear in the measure |
| the entropy is **concave** in the measure | `MeasureTheory.entropyRate_sum_smul_le` |

The third is the one with content, and it is the same concavity that
`ForMathlib/Dynamics/EntropySemicontinuity.lean` supplies to the separation argument behind
Theorem 3.4 — there in its binary form, here for a finite pool.  Note that no *ergodic
decomposition* is needed anywhere: the linear program lives entirely on the concave side.

## Reference

* `paper.tex`, Section 9 (`\ref{thm:lowerbound}`) and Theorem E of the introduction.
-/

namespace BB61

open MeasureTheory Dynamics BoundedContinuousFunction

/-! ## Finite mixtures of invariant measures -/

section Pool

variable {ι' : Type*} {s : Finset ι'} {lam : ι' → ℝ} {ν : ι' → ProbabilityMeasure Shift}

/-- Pushing forward commutes with a finite sum of measures. -/
@[category API, AMS 28, ref "Bug12", group "bugeaud_10_61"]
theorem map_finsetSum_measure {β : Type*} [MeasurableSpace β] {f : Shift → β} (hf : Measurable f)
    (s : Finset ι') (μ : ι' → Measure Shift) :
    Measure.map f (∑ j ∈ s, μ j) = ∑ j ∈ s, Measure.map f (μ j) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j t hj ih
  rw [Finset.sum_insert hj, Finset.sum_insert hj, Measure.map_add _ _ hf, ih]

/-- The convex combination `∑_j λ_j ν_j` of finitely many probability measures on the shift. -/
noncomputable def poolMix (s : Finset ι') (lam : ι' → ℝ) (ν : ι' → ProbabilityMeasure Shift)
    (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1) : ProbabilityMeasure Shift :=
  ⟨∑ j ∈ s, ENNReal.ofReal (lam j) • (ν j : Measure Shift),
    isProbabilityMeasure_sum_smul (μ := fun j => (ν j : Measure Shift)) hlam hsum⟩

@[simp, category API, AMS 28, ref "Bug12", group "bugeaud_10_61"]
theorem toMeasure_poolMix (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1) :
    ((poolMix s lam ν hlam hsum : ProbabilityMeasure Shift) : Measure Shift)
      = ∑ j ∈ s, ENNReal.ofReal (lam j) • (ν j : Measure Shift) := rfl

/-- **A convex combination of invariant measures is invariant.** -/
@[category API, AMS 37 28, ref "Bug12", group "bugeaud_10_61"]
theorem poolMix_mem_invMeasures (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1)
    (hν : ∀ j ∈ s, ν j ∈ invMeasures) : poolMix s lam ν hlam hsum ∈ invMeasures := by
  rw [mem_invMeasures]
  refine ProbabilityMeasure.toMeasure_injective ?_
  rw [toMeasure_pmap, toMeasure_poolMix,
    map_finsetSum_measure continuous_shiftZ.measurable]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjinv : Measure.map shiftZ ((ν j : Measure Shift)) = (ν j : Measure Shift) := by
    have h := congrArg (fun x : ProbabilityMeasure Shift => (x : Measure Shift))
      (mem_invMeasures.1 (hν j hj))
    rwa [toMeasure_pmap] at h
  rw [Measure.map_smul, hjinv]

/-- **The entropy of a mixture is at least the mixture of the entropies** — concavity, for a
finite pool.  This is the one inequality of Theorem 9.1 with content. -/
@[category API, AMS 37 28, ref "Bug12", group "bugeaud_10_61"]
theorem le_shiftEntropy_poolMix (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1) :
    ∑ j ∈ s, lam j * shiftEntropy (ν j) ≤ shiftEntropy (poolMix s lam ν hlam hsum) :=
  entropyRate_sum_smul_le (μ := fun j => (ν j : Measure Shift)) hlam hsum shiftZ coordPartition

/-- The integral against a mixture is the mixture of the integrals. -/
@[category API, AMS 28, ref "Bug12", group "bugeaud_10_61"]
theorem integral_poolMix {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1) (f : Shift → G)
    (hf : ∀ j ∈ s, Integrable f (ν j : Measure Shift)) :
    ∫ ω, f ω ∂(poolMix s lam ν hlam hsum : Measure Shift)
      = ∑ j ∈ s, lam j • ∫ ω, f ω ∂(ν j : Measure Shift) := by
  rw [toMeasure_poolMix,
    integral_finsetSum_measure fun j hj => (hf j hj).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hlam j hj)]

/-- **The moments are affine in the measure**: `Φ_h(∑_j λ_j ν_j) = ∑_j λ_j Φ_h(ν_j)`. -/
@[category API, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem fourierMoment_poolMix (P : QuadSetup) (h : ℤ) (hlam : ∀ j ∈ s, 0 ≤ lam j)
    (hsum : ∑ j ∈ s, lam j = 1) :
    fourierMoment P h (poolMix s lam ν hlam hsum)
      = ∑ j ∈ s, (lam j : ℂ) * fourierMoment P h (ν j) := by
  rw [fourierMoment, integral_poolMix hlam hsum _ fun j _ => integrable_fourier_comp P h (ν j)]
  exact Finset.sum_congr rfl fun j _ => Complex.real_smul

end Pool

/-! ## The pairing, in complex form -/

/-- `∫ ψ_a dμ = Re ∑_{h ∈ Hs} a_h Φ_h(μ)`.  (`BB61.integral_fourierPotential` is the same identity
after separating real and imaginary parts; this form is what the `ℓ¹` estimate needs.) -/
@[category API, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourierPotential_re (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ)
    (μ : ProbabilityMeasure Shift) :
    ∫ ω, fourierPotential P Hs a ω ∂(μ : Measure Shift)
      = (∑ h ∈ Hs, a h * fourierMoment P h μ).re := by
  have hint : ∀ h ∈ Hs, Integrable (fun ω => a h * fourier h (P.fMap ω)) (μ : Measure Shift) :=
    fun h _ => (integrable_fourier_comp P h μ).const_mul _
  have hsum : Integrable (fun ω => ∑ h ∈ Hs, a h * fourier h (P.fMap ω)) (μ : Measure Shift) :=
    integrable_finsetSum _ hint
  have hre : ∀ ω : Shift, fourierPotential P Hs a ω
      = RCLike.re (∑ h ∈ Hs, a h * fourier h (P.fMap ω)) := fun _ => rfl
  simp_rw [hre]
  rw [integral_re hsum, MeasureTheory.integral_finsetSum Hs hint, RCLike.re_to_complex]
  simp only [fourierMoment, integral_const_mul]

/-- **The `ℓ¹` estimate.**  A measure whose moments on `Hs` are at most `ε` in modulus pairs with
`ψ_a` to at most `ε‖a‖₁`.  This is the whole content of the degradation clause. -/
@[category API, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_integral_fourierPotential_le (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ)
    (μ : ProbabilityMeasure Shift) {ε : ℝ} (hε : ∀ h ∈ Hs, ‖fourierMoment P h μ‖ ≤ ε) :
    |∫ ω, fourierPotential P Hs a ω ∂(μ : Measure Shift)| ≤ ε * ∑ h ∈ Hs, ‖a h‖ := by
  rw [integral_fourierPotential_re, Finset.mul_sum]
  refine le_trans (Complex.abs_re_le_norm _) (le_trans (norm_sum_le _ _) ?_)
  refine Finset.sum_le_sum fun h hh => ?_
  rw [norm_mul, mul_comm ε]
  exact mul_le_mul_of_nonneg_left (hε h hh) (norm_nonneg _)

/-! ## Theorem 9.1 -/

/-- **A flat pool** — a feasible point of the linear program of Theorem 9.1: finitely many
`σ`-invariant measures, convex weights, and the exact flatness `∑_j λ_j Φ_h(ν_j) = 0` for every
mode `h` of `Hs`.  The paper's Theorem E exhibits such a pool with `129` atoms at `H = 64`. -/
structure FlatPool (P : QuadSetup) (Hs : Finset ℤ) where
  /-- the number of measures in the pool -/
  card : ℕ
  /-- the measures -/
  meas : Fin card → ProbabilityMeasure Shift
  /-- each is shift-invariant -/
  inv : ∀ j, meas j ∈ invMeasures
  /-- the convex weights -/
  weight : Fin card → ℝ
  /-- the weights are non-negative -/
  weight_nonneg : ∀ j, 0 ≤ weight j
  /-- the weights sum to one -/
  weight_sum : ∑ j, weight j = 1
  /-- the mixture is Fourier-flat on `Hs` -/
  flat : ∀ h ∈ Hs, ∑ j, (weight j : ℂ) * fourierMoment P h (meas j) = 0

namespace FlatPool

variable {P : QuadSetup} {Hs : Finset ℤ} (pool : FlatPool P Hs)

/-- The objective value `∑_j λ_j h(ν_j)` of the linear program at this feasible point. -/
noncomputable def entropy : ℝ := ∑ j, pool.weight j * shiftEntropy (pool.meas j)

/-- The mixture `∑_j λ_j ν_j` itself. -/
noncomputable def mixture : ProbabilityMeasure Shift :=
  poolMix Finset.univ pool.weight pool.meas (fun j _ => pool.weight_nonneg j) pool.weight_sum

@[category API, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem mixture_mem_flatSet : pool.mixture ∈ flatSet P Hs := by
  refine ⟨poolMix_mem_invMeasures _ _ fun j _ => pool.inv j, fun h hh => ?_⟩
  rw [mixture, fourierMoment_poolMix]
  exact pool.flat h hh

@[category API, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem entropy_le_shiftEntropy_mixture : pool.entropy ≤ shiftEntropy pool.mixture :=
  le_shiftEntropy_poolMix _ _

/-- **Theorem 9.1 of `paper.tex` — lower bounds by linear programming.**  Any convex combination
of invariant measures that is Fourier-flat to degree `H` certifies `E_H(α) ≥ ∑_j λ_j h(ν_j)`.

The three ingredients are that a convex combination of invariant measures is invariant, that the
moments are affine, and that the entropy is concave; the last is
`MeasureTheory.entropyRate_sum_smul_le`. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem entropy_le_priceEntropy : ((pool.entropy : ℝ) : EReal) ≤ priceEntropy P Hs :=
  le_trans (EReal.coe_le_coe pool.entropy_le_shiftEntropy_mixture)
    (le_priceEntropy P Hs pool.mixture_mem_flatSet)

end FlatPool

/-! ## The degradation clause -/

section Degradation

variable {ι' : Type*} {s : Finset ι'} {lam : ι' → ℝ} {ν : ι' → ProbabilityMeasure Shift}

/-- **Theorem 9.1, the degradation clause**, on the measure side.  A pool that is flat only up to
`ε` still prices every potential: `∑_j λ_j h(ν_j) − ε‖a‖₁ ≤ sup_μ (h(μ) + ∫ψ_a dμ)`. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem sub_le_measurePressure_of_approxFlat (P : QuadSetup) (Hs : Finset ℤ)
    (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1)
    (hν : ∀ j ∈ s, ν j ∈ invMeasures) {ε : ℝ}
    (hε : ∀ h ∈ Hs, ‖∑ j ∈ s, (lam j : ℂ) * fourierMoment P h (ν j)‖ ≤ ε) (a : ℤ → ℂ) :
    (((∑ j ∈ s, lam j * shiftEntropy (ν j)) - ε * ∑ h ∈ Hs, ‖a h‖ : ℝ) : EReal)
      ≤ measurePressure (fourierPotential P Hs a) := by
  have hmom : ∀ h ∈ Hs, ‖fourierMoment P h (poolMix s lam ν hlam hsum)‖ ≤ ε := by
    intro h hh
    rw [fourierMoment_poolMix]
    exact hε h hh
  have hpair := abs_integral_fourierPotential_le P Hs a (poolMix s lam ν hlam hsum) hmom
  have hent := le_shiftEntropy_poolMix (ν := ν) hlam hsum
  refine le_trans (EReal.coe_le_coe ?_)
    (le_measurePressure (ψ := fourierPotential P Hs a)
      (poolMix_mem_invMeasures hlam hsum hν))
  have := (abs_le.1 hpair).1
  linarith

/-- **Theorem 9.1, the degradation clause**, for the pressure over cylinders.  The passage from the
measure side is the *Jensen* half of the variational principle, a theorem. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem sub_le_partitionPressure_of_approxFlat (P : QuadSetup) (Hs : Finset ℤ)
    (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1)
    (hν : ∀ j ∈ s, ν j ∈ invMeasures) {ε : ℝ}
    (hε : ∀ h ∈ Hs, ‖∑ j ∈ s, (lam j : ℂ) * fourierMoment P h (ν j)‖ ≤ ε) (a : ℤ → ℂ) :
    (((∑ j ∈ s, lam j * shiftEntropy (ν j)) - ε * ∑ h ∈ Hs, ‖a h‖ : ℝ) : EReal)
      ≤ partitionPressure shiftZ (fourierPotential P Hs a) coordPartition :=
  le_trans (sub_le_measurePressure_of_approxFlat P Hs hlam hsum hν hε a)
    (measurePressure_le_partitionPressure (continuous_fourierPotential P Hs a)
      (fun ω => le_trans (le_abs_self _) (abs_fourierPotential_le P Hs a ω)))

end Degradation

/-! ## Consumers: a lower bound above the floor kills every certificate -/

/-- **No certificate of degree `Hs`.**  If `E_H(α) ≥ c` and the entropy floor `½ log α` is strictly
below `c`, then every potential `ψ_a` of degree `Hs` has pressure strictly above the floor — the
pressure criterion of Theorem 4.2 cannot fire at this degree.

Unconditional: no cited axiom, and in particular neither the variational principle nor the
Ledrappier–Young floor. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem floor_lt_partitionPressure_of_le_priceEntropy (P : QuadSetup) (Hs : Finset ℤ) {c : ℝ}
    (hc : Real.log P.α / 2 < c) (hE : ((c : ℝ) : EReal) ≤ priceEntropy P Hs) (a : ℤ → ℂ) :
    ((Real.log P.α / 2 : ℝ) : EReal)
      < partitionPressure shiftZ (fourierPotential P Hs a) coordPartition := by
  refine lt_of_lt_of_le (by exact_mod_cast hc) (le_trans hE ?_)
  exact le_trans (priceEntropy_le_iInf_partitionPressure P Hs) (iInf_le _ a)

/-- A lower bound on `E_{H₀}(α)` above the floor bounds every smaller degree too: `E_H(α)` is
non-increasing in `H`. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_priceEntropy_lt_of_le (P : QuadSetup) (H₀ : ℕ) {c : ℝ}
    (hc : Real.log P.α / 2 < c)
    (hE : ((c : ℝ) : EReal) ≤ priceEntropy P (Finset.Icc 1 (H₀ : ℤ))) {H : ℕ} (hH : H ≤ H₀) :
    ¬ priceEntropy P (Finset.Icc 1 (H : ℤ)) < ((Real.log P.α / 2 : ℝ) : EReal) := by
  refine not_lt.2 (le_trans (by exact_mod_cast hc.le) (le_trans hE ?_))
  exact priceEntropy_mono P (Finset.Icc_subset_Icc le_rfl (by exact_mod_cast hH))

/-- **No certificate of any degree `≤ H₀`** — the conclusion the paper's Theorem E draws from its
linear programs. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem forall_le_floor_lt_partitionPressure (P : QuadSetup) (H₀ : ℕ) {c : ℝ}
    (hc : Real.log P.α / 2 < c)
    (hE : ((c : ℝ) : EReal) ≤ priceEntropy P (Finset.Icc 1 (H₀ : ℤ)))
    (H : ℕ) (hH : H ≤ H₀) (a : ℤ → ℂ) :
    ((Real.log P.α / 2 : ℝ) : EReal)
      < partitionPressure shiftZ (fourierPotential P (Finset.Icc 1 (H : ℤ)) a) coordPartition := by
  refine floor_lt_partitionPressure_of_le_priceEntropy P _ hc (le_trans hE ?_) a
  exact priceEntropy_mono P (Finset.Icc_subset_Icc le_rfl (by exact_mod_cast hH))

/-- **`H₀ < H_ent(α)`.**  The entropy criterion of Corollary 3.5 cannot fire at any degree `≤ H₀`.

The hypothesis `hne` — that it fires at *some* degree — is what makes `H_ent(α)` the minimum it is
meant to be rather than `sInf ∅ = 0`; by Corollary 3.5 it is equivalent to 10.61 holding at `α`. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_entDegree_of_le_priceEntropy (P : QuadSetup) (H₀ : ℕ) {c : ℝ}
    (hc : Real.log P.α / 2 < c)
    (hE : ((c : ℝ) : EReal) ≤ priceEntropy P (Finset.Icc 1 (H₀ : ℤ)))
    (hne : ∃ H : ℕ, priceEntropy P (Finset.Icc 1 (H : ℤ)) < ((Real.log P.α / 2 : ℝ) : EReal)) :
    H₀ < entDegree P := by
  by_contra hcon
  push Not at hcon
  exact not_priceEntropy_lt_of_le P H₀ hc hE hcon (Nat.sInf_mem hne)

/-- **The quantitative form of the degradation clause.**  If a pool of entropy `e` has defect `ε`
on `Hs`, then any potential of degree `Hs` whose pressure falls below the floor must have
`‖a‖₁ > (e − ½ log α)/ε`.  This is what makes an *approximate* linear-programming solution a
theorem: the residual is charged against the multiplier's `ℓ¹` norm. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_norm_one_of_partitionPressure_lt {ι' : Type*} {s : Finset ι'} {lam : ι' → ℝ}
    {ν : ι' → ProbabilityMeasure Shift} (P : QuadSetup) (Hs : Finset ℤ)
    (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1)
    (hν : ∀ j ∈ s, ν j ∈ invMeasures) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ h ∈ Hs, ‖∑ j ∈ s, (lam j : ℂ) * fourierMoment P h (ν j)‖ ≤ ε) (a : ℤ → ℂ)
    (hpress : partitionPressure shiftZ (fourierPotential P Hs a) coordPartition
      < ((Real.log P.α / 2 : ℝ) : EReal)) :
    ((∑ j ∈ s, lam j * shiftEntropy (ν j)) - Real.log P.α / 2) / ε < ∑ h ∈ Hs, ‖a h‖ := by
  have h := (sub_le_measurePressure_of_approxFlat P Hs hlam hsum hν hε a).trans_lt
    (lt_of_le_of_lt (measurePressure_le_partitionPressure (continuous_fourierPotential P Hs a)
      (fun ω => le_trans (le_abs_self _) (abs_fourierPotential_le P Hs a ω))) hpress)
  rw [EReal.coe_lt_coe_iff] at h
  rw [div_lt_iff₀ hε0]
  linarith

/-- `E_H(α) ≤ log 2` — the pool bounds of Theorem E all sit below this ceiling. -/
@[category API, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem priceEntropy_le_log_two (P : QuadSetup) (Hs : Finset ℤ) :
    priceEntropy P Hs ≤ ((Real.log 2 : ℝ) : EReal) := by
  refine sSup_le ?_
  rintro _ ⟨μ, -, rfl⟩
  exact EReal.coe_le_coe (shiftEntropy_le_log_two μ)

end BB61
