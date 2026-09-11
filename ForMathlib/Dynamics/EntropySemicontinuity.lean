/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Algebra.Indicator
public import ForMathlib.Dynamics.KolmogorovSinai

@[expose] public section

/-!
# Concavity and upper semicontinuity of the entropy rate

`ForMathlib/Dynamics/KolmogorovSinai.lean` defines `MeasureTheory.entropyRate T μ f`, the entropy
`h_μ(T, P)` of `T` relative to the finite partition `P` given by the fibers of `f`, as the
*infimum* of `H_μ(⋁_{i<n} T^{-i}P) / n` over `n ≥ 1`.  That definition — rather than the equal
Fekete limit — is what this file exploits: an infimum of concave functions of `μ` is concave, and
an infimum of continuous functions of `μ` is upper semicontinuous.  Both statements are about the
dependence on the **measure**, with the map and the partition held fixed.

## Main results

* `MeasureTheory.partitionEntropy_smul_add_smul_le` — Shannon entropy is concave in the measure,
  for *any* finite-valued observable: `p·H_{μ₀}(P) + q·H_{μ₁}(P) ≤ H_{p μ₀ + q μ₁}(P)`.  No
  measurability is needed; concavity of `Real.negMulLog` does all the work.
* `MeasureTheory.entropyRate_smul_add_smul_le` — hence `μ ↦ h_μ(T, P)` is concave.
* `MeasureTheory.continuous_partitionEntropy` — if the cells of `P` are **clopen**, then
  `μ ↦ H_μ(P)` is weak-\* continuous on `ProbabilityMeasure α`.  The cell measures are integrals of
  bounded continuous indicator functions, so weak-\* convergence sees them exactly.
* `MeasureTheory.upperSemicontinuous_entropyRate` — for `T` continuous and `P` clopen,
  `μ ↦ h_μ(T, P)` is upper semicontinuous on `ProbabilityMeasure α`.

Upper semicontinuity of the entropy is the standard hypothesis under which a supremum of entropy
over a compact convex set of invariant measures is *attained*, and (with concavity) under which the
hypograph `{(v, t) : t ≤ h_μ(T,P), Φ(μ) = v}` of a moment map is closed and convex — the input to
every Lagrange-duality argument in ergodic optimization.  For a general partition it is false; the
usual sufficient conditions are expansiveness of `T`, or, as here, a partition whose cells have
empty boundary.

## References

* Walters, Peter. *An Introduction to Ergodic Theory.* GTM 79, Springer, 1982, Theorems 8.1, 8.2.
* Jenkinson, Oliver. *Ergodic optimization in dynamical systems.* Ergodic Theory Dynam. Systems
  **39** (2019), 2593–2618.
-/

open Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace MeasureTheory

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-! ## Concavity in the measure

A convex combination of measures is written `ENNReal.ofReal p • μ₀ + ENNReal.ofReal q • μ₁`; the
space of measures is an `ℝ≥0∞`-module, not an `ℝ`-vector space, so `Convex`/`ConcaveOn` do not
apply directly and the two inequalities are stated by hand. -/

section Mixture

variable {p q : ℝ} {μ₀ μ₁ : Measure α}

/-- A convex combination of two probability measures is a probability measure. -/
theorem isProbabilityMeasure_smul_add_smul (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] :
    IsProbabilityMeasure (ENNReal.ofReal p • μ₀ + ENNReal.ofReal q • μ₁) := by
  constructor
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add hp hq, hpq,
    ENNReal.ofReal_one]

/-- The mass a convex combination gives a set is the combination of the masses. -/
theorem toReal_smul_add_smul_apply (hp : 0 ≤ p) (hq : 0 ≤ q) [IsFiniteMeasure μ₀]
    [IsFiniteMeasure μ₁] (s : Set α) :
    ((ENNReal.ofReal p • μ₀ + ENNReal.ofReal q • μ₁) s).toReal
      = p * (μ₀ s).toReal + q * (μ₁ s).toReal := by
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]

/-- **Shannon entropy is concave in the measure.**  This is concavity of `Real.negMulLog` applied
cell by cell; no measurability of the cells is needed. -/
theorem partitionEntropy_smul_add_smul_le (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (f : α → ι) :
    p * partitionEntropy μ₀ f + q * partitionEntropy μ₁ f
      ≤ partitionEntropy (ENNReal.ofReal p • μ₀ + ENNReal.ofReal q • μ₁) f := by
  rw [partitionEntropy, partitionEntropy, partitionEntropy, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [toReal_smul_add_smul_apply hp hq]
  have := Real.concaveOn_negMulLog.2 (Set.mem_Ici.2 (ENNReal.toReal_nonneg (a := μ₀ (f ⁻¹' {i}))))
    (Set.mem_Ici.2 (ENNReal.toReal_nonneg (a := μ₁ (f ⁻¹' {i})))) hp hq hpq
  simpa using this

/-- The entropy rate is at most the `n`-th normalised join entropy, for every `n ≥ 1`.  (The
`entropyRate` is *defined* as the infimum of those, so this is `csInf_le`.) -/
theorem entropyRate_le_div {μ : Measure α} [IsProbabilityMeasure μ] (T : α → α) (f : α → ι) {n : ℕ}
    (hn : 1 ≤ n) : entropyRate T μ f ≤ partitionEntropy μ (joinIter T f n) / n := by
  refine csInf_le ⟨0, ?_⟩ ⟨n, hn, rfl⟩
  rintro _ ⟨m, -, rfl⟩
  exact div_nonneg (partitionEntropy_nonneg _) (Nat.cast_nonneg m)

/-- **The entropy rate is concave in the measure**: an infimum of concave functions. -/
theorem entropyRate_smul_add_smul_le (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (T : α → α) (f : α → ι) :
    p * entropyRate T μ₀ f + q * entropyRate T μ₁ f
      ≤ entropyRate T (ENNReal.ofReal p • μ₀ + ENNReal.ofReal q • μ₁) f := by
  have hmix : IsProbabilityMeasure (ENNReal.ofReal p • μ₀ + ENNReal.ofReal q • μ₁) :=
    isProbabilityMeasure_smul_add_smul hp hq hpq
  rw [entropyRate]
  refine le_csInf ⟨_, ⟨1, le_refl 1, rfl⟩⟩ ?_
  rintro _ ⟨n, hn, rfl⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have h0 := entropyRate_le_div (μ := μ₀) T f hn
  have h1 := entropyRate_le_div (μ := μ₁) T f hn
  have hc := partitionEntropy_smul_add_smul_le (μ₀ := μ₀) (μ₁ := μ₁) hp hq hpq (joinIter T f n)
  calc p * entropyRate T μ₀ f + q * entropyRate T μ₁ f
      ≤ p * (partitionEntropy μ₀ (joinIter T f n) / n)
        + q * (partitionEntropy μ₁ (joinIter T f n) / n) := by gcongr
    _ = (p * partitionEntropy μ₀ (joinIter T f n) + q * partitionEntropy μ₁ (joinIter T f n)) / n :=
        by ring
    _ ≤ partitionEntropy (ENNReal.ofReal p • μ₀ + ENNReal.ofReal q • μ₁) (joinIter T f n) / n := by
        gcongr

/-! ### Finite mixtures

The same two inequalities for a convex combination `∑_{i ∈ s} w i • μ i` of finitely many
measures.  They are what a *linear program* over a pool of invariant measures needs: the binary
case would give them only after an induction that renormalises the tail weights. -/

section FiniteMixture

variable {ι' : Type*} {s : Finset ι'} {w : ι' → ℝ} {μ : ι' → Measure α}

/-- A finite convex combination of probability measures is a probability measure. -/
theorem isProbabilityMeasure_sum_smul (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (∑ i ∈ s, ENNReal.ofReal (w i) • μ i) := by
  constructor
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg hw, hw1, ENNReal.ofReal_one]

/-- The mass a finite convex combination gives a set is the combination of the masses. -/
theorem toReal_sum_smul_apply (hw : ∀ i ∈ s, 0 ≤ w i) [∀ i, IsFiniteMeasure (μ i)] (t : Set α) :
    ((∑ i ∈ s, ENNReal.ofReal (w i) • μ i) t).toReal = ∑ i ∈ s, w i * (μ i t).toReal := by
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i hi)]

/-- **Shannon entropy is concave in the measure**, for a finite convex combination: concavity of
`Real.negMulLog` cell by cell, through Jensen's inequality. -/
theorem partitionEntropy_sum_smul_le (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    [∀ i, IsProbabilityMeasure (μ i)] (f : α → ι) :
    ∑ i ∈ s, w i * partitionEntropy (μ i) f
      ≤ partitionEntropy (∑ i ∈ s, ENNReal.ofReal (w i) • μ i) f := by
  have hswap : ∑ i ∈ s, w i * partitionEntropy (μ i) f
      = ∑ j : ι, ∑ i ∈ s, w i * Real.negMulLog ((μ i (f ⁻¹' {j})).toReal) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [partitionEntropy, Finset.mul_sum]
  rw [hswap, partitionEntropy]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [toReal_sum_smul_apply hw]
  have := Real.concaveOn_negMulLog.le_map_sum (t := s) (w := w)
    (p := fun i => (μ i (f ⁻¹' {j})).toReal) hw hw1
    (fun i _ => Set.mem_Ici.2 ENNReal.toReal_nonneg)
  simpa only [smul_eq_mul] using this

/-- **The entropy rate is concave in the measure**, for a finite convex combination. -/
theorem entropyRate_sum_smul_le (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    [∀ i, IsProbabilityMeasure (μ i)] (T : α → α) (f : α → ι) :
    ∑ i ∈ s, w i * entropyRate T (μ i) f
      ≤ entropyRate T (∑ i ∈ s, ENNReal.ofReal (w i) • μ i) f := by
  have hmix : IsProbabilityMeasure (∑ i ∈ s, ENNReal.ofReal (w i) • μ i) :=
    isProbabilityMeasure_sum_smul hw hw1
  rw [entropyRate]
  refine le_csInf ⟨_, ⟨1, le_refl 1, rfl⟩⟩ ?_
  rintro _ ⟨n, hn, rfl⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  calc ∑ i ∈ s, w i * entropyRate T (μ i) f
      ≤ ∑ i ∈ s, w i * (partitionEntropy (μ i) (joinIter T f n) / n) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul_of_nonneg_left (entropyRate_le_div T f hn) (hw i hi)
    _ = (∑ i ∈ s, w i * partitionEntropy (μ i) (joinIter T f n)) / n := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ partitionEntropy (∑ i ∈ s, ENNReal.ofReal (w i) • μ i) (joinIter T f n) / n := by
        gcongr
        exact partitionEntropy_sum_smul_le hw hw1 _

end FiniteMixture

end Mixture

/-! ## Continuity for a clopen partition -/

section Clopen

variable [TopologicalSpace α] [OpensMeasurableSpace α]

/-- The indicator of a clopen set, as a bounded continuous function. -/
noncomputable def clopenIndicator {s : Set α} (hs : IsClopen s) : α →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨s.indicator (1 : α → ℝ), hs.continuous_indicator continuous_const⟩ 1 <| by
      have hval : ∀ z : α, s.indicator (1 : α → ℝ) z = 0 ∨ s.indicator (1 : α → ℝ) z = 1 := by
        intro z
        by_cases hz : z ∈ s
        · exact Or.inr (by simp [hz])
        · exact Or.inl (by simp [hz])
      intro x y
      rcases hval x with hx | hx <;> rcases hval y with hy | hy <;>
        simp [ContinuousMap.coe_mk, Real.dist_eq, hx, hy]

omit [MeasurableSpace α] [OpensMeasurableSpace α] in
@[simp]
theorem clopenIndicator_apply {s : Set α} (hs : IsClopen s) (x : α) :
    clopenIndicator hs x = s.indicator (1 : α → ℝ) x := rfl

/-- The mass of a **clopen** set is weak-\* continuous in the measure: it is the integral of a
bounded continuous function. -/
theorem continuous_measure_toReal_of_isClopen {s : Set α} (hs : IsClopen s) :
    Continuous fun μ : ProbabilityMeasure α => ((μ : Measure α) s).toReal := by
  have h : (fun μ : ProbabilityMeasure α => ((μ : Measure α) s).toReal)
      = fun μ : ProbabilityMeasure α => ∫ x, clopenIndicator hs x ∂(μ : Measure α) := by
    funext μ
    simp only [clopenIndicator_apply]
    exact (integral_indicator_one hs.isOpen.measurableSet).symm
  rw [h]
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction _

/-- **Shannon entropy along a clopen partition is weak-\* continuous.** -/
theorem continuous_partitionEntropy {f : α → ι} (hf : ∀ i, IsClopen (f ⁻¹' {i})) :
    Continuous fun μ : ProbabilityMeasure α => partitionEntropy (μ : Measure α) f := by
  simp only [partitionEntropy]
  exact continuous_finsetSum _ fun i _ =>
    Real.continuous_negMulLog.comp (continuous_measure_toReal_of_isClopen (hf i))

omit [MeasurableSpace α] [Fintype ι] [OpensMeasurableSpace α] in
/-- The cells of the dynamical join of a clopen partition under a continuous map are clopen. -/
theorem isClopen_joinIter_fiber {T : α → α} (hT : Continuous T) {f : α → ι}
    (hf : ∀ i, IsClopen (f ⁻¹' {i})) (n : ℕ) (w : Fin n → ι) :
    IsClopen (joinIter T f n ⁻¹' {w}) := by
  have hset : joinIter T f n ⁻¹' {w} = ⋂ i : Fin n, T^[(i : ℕ)] ⁻¹' (f ⁻¹' {w i}) := by
    ext x
    simp [joinIter, Set.mem_iInter, funext_iff]
  rw [hset]
  exact isClopen_iInter_of_finite fun i => (hf (w i)).preimage (hT.iterate _)

/-- **The entropy rate along a clopen partition is upper semicontinuous** in the measure: it is an
infimum of the continuous functions `μ ↦ H_μ(⋁_{i<n} T^{-i}P) / n`. -/
theorem upperSemicontinuous_entropyRate {T : α → α} (hT : Continuous T) {f : α → ι}
    (hf : ∀ i, IsClopen (f ⁻¹' {i})) :
    UpperSemicontinuous fun μ : ProbabilityMeasure α => entropyRate T (μ : Measure α) f := by
  intro μ y hy
  obtain ⟨_, ⟨n, hn, rfl⟩, hxy⟩ :=
    exists_lt_of_csInf_lt (s := (fun n : ℕ =>
      partitionEntropy (μ : Measure α) (joinIter T f n) / n) '' Set.Ici 1)
      ⟨_, ⟨1, le_refl 1, rfl⟩⟩ hy
  have hcont : Continuous fun ν : ProbabilityMeasure α =>
      partitionEntropy (ν : Measure α) (joinIter T f n) / (n : ℝ) :=
    (continuous_partitionEntropy fun w => isClopen_joinIter_fiber hT hf n w).div_const _
  filter_upwards [(hcont.tendsto μ).eventually_lt_const hxy] with ν hν
  exact lt_of_le_of_lt (entropyRate_le_div T f hn) hν

end Clopen

end MeasureTheory
