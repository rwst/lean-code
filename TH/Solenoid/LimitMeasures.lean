/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.DiracProba
import TH.Solenoid.Dictionary
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Empirical measures of the `(3/2)ⁿ` orbit and their weak-∗ limit points

Work package W4 of plan-A1+ (§4, L4–L5): the measure-theoretic habitat in which the open inputs
of the bridge architecture (H-inv, H-ent) are stated.

For a real `ξ` the empirical measure of the orbit segment `x_ξ, T x_ξ, …, T^N x_ξ` of the winding
point `x_ξ = wind ξ` under the diagonal `T = ×(3/2)` is

`empirical ξ N = (N+1)⁻¹ ∑_{n ≤ N} δ_{T^n x_ξ}`,

a probability measure on the compact metrizable group `Σ₆` (W1, W2).  `limitMeasures ξ` is its set
of weak-∗ cluster points.  The four facts of this file are the ones the architecture consumes:

* **Existence** (`limitMeasures_nonempty`).  `Σ₆` is compact, so `ProbabilityMeasure Σ₆` is compact
  (Mathlib's Prokhorov instance), and a filter on a compact space has a cluster point.  This is
  the "Mathlib gap R-G" recorded in `Z32/BalanceVectors.lean`, now closed upstream.
* **Invariance** (`limitMeasures_T32_invariant`).  Every limit measure is `T`-invariant — the
  Krylov–Bogolyubov argument: the empirical measure and its `T`-pushforward differ by the two
  boundary Diracs, hence by `O(1/N)` on every bounded continuous test function.
* **The dictionary at the level of measures** (`equidistributed_iff_limitMeasures`).
  `Equidistributed ξ` (W3: weak-∗ convergence of the Birkhoff averages to Haar) holds **iff**
  `limitMeasures ξ = {haarProb}`.  Compactness is what makes "unique cluster point" equivalent to
  "converges": that is the whole reason to pass to measures.  Composed with W3's dictionary this
  says: the `ℤ[1/6]`-family `(r ξ (3/2)ⁿ)` is u.d. mod 1 for every `r ≠ 0` iff Haar is the only
  limit measure of the orbit.
* **The Dirac gate** (`eq_zero_of_diracProba_mem_limitMeasures`, plan-A1+ A13).  A Dirac mass can
  be a limit measure only at `0`: invariance forces its atom to be a fixed point of `T`, and `T`
  has only the fixed point `0` (`eq_zero_of_T32_eq_self`, W1).  So the whole atomic-Dirac defect
  class is reduced to the *single* statement `δ₀ ∉ limitMeasures 1` — that statement is target N1
  of angle A13 and is **open**; nothing here proves it.  It is not vacuous either:
  `limitMeasures_zero` shows `δ₀` really is the limit measure of the (degenerate) orbit at
  `ξ = 0`, so the exclusion has to use the arithmetic of `ξ`, exactly as `Z32/BalanceVectors.lean`
  predicted (the fixed point `0` is a genuine orbit-closure point at every finite level too).

## Indexing convention

`empirical ξ N` averages over the `N+1` points `n = 0, …, N`, so that it is a probability measure
for *every* `N` (an average over the empty range is not).  The shift is immaterial for limits and
is visible only in `integral_empirical_eq_birkhoff`, which reads `birkhoff f ξ (N+1)`.

## Main statements

* `empirical`, `limitMeasures` — the objects.
* `limitMeasures_nonempty`, `isCompact_limitMeasures` — existence and compactness.
* `limitMeasures_T32_invariant`, `map_T32_of_mem_limitMeasures`, `measurePreserving_of_mem_limitMeasures`
  — every limit measure is `T`-invariant.
* `equidistributed_iff_tendsto`, `equidistributed_iff_limitMeasures` — u.d. ⟺ `{Haar}`.
* `eq_zero_of_diracProba_mem_limitMeasures` — the Dirac gate; `limitMeasures_zero` — its sharpness.

## References

Plan A1+ §4 (L4–L5), §5 (A13), §6.1.  The invariance statement is Krylov–Bogolyubov, see
[EW11, Ch. 4]; the compactness input is Prokhorov's theorem in the compact case.
-/

namespace TH.S6

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

/-! ### The empirical measures -/

/-- The empirical measure of the orbit segment `x_ξ, T x_ξ, …, T^N x_ξ`, as a measure.  The
average is over `N+1` points, so that it is a probability measure for every `N`. -/
noncomputable def empiricalMeasure (ξ : ℝ) (N : ℕ) : Measure S6 :=
  ((N : ℝ≥0∞) + 1)⁻¹ • ∑ n ∈ Finset.range (N + 1), Measure.dirac (T32^[n] (wind ξ))

instance instIsProbabilityMeasureEmpiricalMeasure (ξ : ℝ) (N : ℕ) :
    IsProbabilityMeasure (empiricalMeasure ξ N) := by
  constructor
  rw [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, smul_eq_mul, Nat.cast_add, Nat.cast_one]
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

/-- The empirical measure `μ_{N} = (N+1)⁻¹ ∑_{n ≤ N} δ_{T^n x_ξ}` as a point of the compact space
`ProbabilityMeasure Σ₆`. -/
noncomputable def empirical (ξ : ℝ) (N : ℕ) : ProbabilityMeasure S6 :=
  ⟨empiricalMeasure ξ N, inferInstance⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem empirical_toMeasure (ξ : ℝ) (N : ℕ) :
    (empirical ξ N : Measure S6) = empiricalMeasure ξ N := rfl

/-- Integration against the empirical measure is the finite orbit average. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem integral_empirical {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : C(S6, E)) (ξ : ℝ) (N : ℕ) :
    ∫ x, g x ∂(empirical ξ N : Measure S6)
      = ((N : ℝ) + 1)⁻¹ • ∑ n ∈ Finset.range (N + 1), g (T32^[n] (wind ξ)) := by
  rw [empirical_toMeasure, empiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun i _ =>
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))]
  simp only [integral_dirac, ENNReal.toReal_inv]
  congr 1

/-- **The empirical measure computes the Birkhoff averages of W3.**  This is the bridge between
`Dictionary.lean`'s `birkhoff`, which is a bare finite sum, and the measure-theoretic object. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem integral_empirical_eq_birkhoff (f : C(S6, ℂ)) (ξ : ℝ) (N : ℕ) :
    ∫ x, f x ∂(empirical ξ N : Measure S6) = birkhoff f ξ (N + 1) := by
  rw [integral_empirical, birkhoff, Complex.real_smul]
  push_cast
  ring

/-- Convergence of the empirical integrals is convergence of the Birkhoff averages (the index
shift is absorbed). -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem tendsto_integral_empirical_iff (f : C(S6, ℂ)) (ξ : ℝ) (L : ℂ) :
    Tendsto (fun N => ∫ x, f x ∂(empirical ξ N : Measure S6)) atTop (𝓝 L)
      ↔ Tendsto (fun N => birkhoff f ξ N) atTop (𝓝 L) := by
  simp only [integral_empirical_eq_birkhoff]
  exact tendsto_add_atTop_iff_nat 1

/-! ### The set of limit measures -/

/-- **The limit measures of the orbit of `x_ξ`**: the weak-∗ cluster points of the empirical
measures.  Equidistribution is the statement that this set is `{Haar}`
(`equidistributed_iff_limitMeasures`). -/
def limitMeasures (ξ : ℝ) : Set (ProbabilityMeasure S6) :=
  {ν | MapClusterPt ν atTop (empirical ξ)}

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem mem_limitMeasures_iff {ξ : ℝ} {ν : ProbabilityMeasure S6} :
    ν ∈ limitMeasures ξ ↔ MapClusterPt ν atTop (empirical ξ) := Iff.rfl

/-- **Limit measures exist.**  `Σ₆` is compact, hence so is `ProbabilityMeasure Σ₆` (Prokhorov,
Mathlib's `instCompactSpaceProbabilityMeasure`), and every filter on a compact space has a cluster
point.  This is the half of the "Mathlib gap R-G" of `Z32/BalanceVectors.lean` that has closed. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem limitMeasures_nonempty (ξ : ℝ) : (limitMeasures ξ).Nonempty :=
  exists_clusterPt_of_compactSpace (Filter.map (empirical ξ) atTop)

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem isClosed_limitMeasures (ξ : ℝ) : IsClosed (limitMeasures ξ) :=
  isClosed_setOf_clusterPt

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem isCompact_limitMeasures (ξ : ℝ) : IsCompact (limitMeasures ξ) :=
  (isClosed_limitMeasures ξ).isCompact

/-! ### Invariance: the Krylov–Bogolyubov argument -/

/-- `f ∘ T` as a bounded continuous function. -/
noncomputable def compT32 (f : S6 →ᵇ ℝ) : S6 →ᵇ ℝ :=
  f.compContinuous ⟨T32, T32.continuous⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem compT32_apply (f : S6 →ᵇ ℝ) (x : S6) : compT32 f x = f (T32 x) := rfl

/-- The empirical integral of a bounded continuous function is the finite orbit average. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem integral_empirical_bcf (f : S6 →ᵇ ℝ) (ξ : ℝ) (N : ℕ) :
    ∫ x, f x ∂(empirical ξ N : Measure S6)
      = ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), f (T32^[n] (wind ξ)) := by
  simpa [smul_eq_mul] using integral_empirical f.toContinuousMap ξ N

/-- **The one-step defect telescopes.**  The empirical measure of the orbit segment and its
`T`-pushforward differ only through the two endpoints. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem integral_compT32_empirical_sub (f : S6 →ᵇ ℝ) (ξ : ℝ) (N : ℕ) :
    ∫ x, compT32 f x ∂(empirical ξ N : Measure S6) - ∫ x, f x ∂(empirical ξ N : Measure S6)
      = ((N : ℝ) + 1)⁻¹ * (f (T32^[N + 1] (wind ξ)) - f (wind ξ)) := by
  rw [integral_empirical_bcf, integral_empirical_bcf, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  have hstep : ∀ n : ℕ, compT32 f (T32^[n] (wind ξ)) - f (T32^[n] (wind ξ))
      = f (T32^[n + 1] (wind ξ)) - f (T32^[n] (wind ξ)) := by
    intro n
    rw [Function.iterate_succ_apply', compT32_apply]
  rw [Finset.sum_congr rfl fun n _ => hstep n]
  exact Finset.sum_range_sub (fun n => f (T32^[n] (wind ξ))) (N + 1)

/-- The defect vanishes in the limit: this is the whole content of Krylov–Bogolyubov. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem tendsto_integral_compT32_empirical_sub (f : S6 →ᵇ ℝ) (ξ : ℝ) :
    Tendsto (fun N => ∫ x, compT32 f x ∂(empirical ξ N : Measure S6)
      - ∫ x, f x ∂(empirical ξ N : Measure S6)) atTop (𝓝 0) := by
  have hbdd : ∀ N : ℕ, ‖∫ x, compT32 f x ∂(empirical ξ N : Measure S6)
      - ∫ x, f x ∂(empirical ξ N : Measure S6)‖ ≤ 2 * ‖f‖ / ((N : ℝ) + 1) := by
    intro N
    rw [integral_compT32_empirical_sub, norm_mul, div_eq_inv_mul]
    have h1 : ‖((N : ℝ) + 1)⁻¹‖ = ((N : ℝ) + 1)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : ‖f (T32^[N + 1] (wind ξ)) - f (wind ξ)‖ ≤ 2 * ‖f‖ :=
      (norm_sub_le _ _).trans (by
        linarith [f.norm_coe_le_norm (T32^[N + 1] (wind ξ)), f.norm_coe_le_norm (wind ξ)])
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine squeeze_zero_norm hbdd ?_
  refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/-- The Birkhoff-average identity survives to every limit measure: `∫ f ∘ T dν = ∫ f dν` for every
bounded continuous `f`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem integral_compT32_of_mem_limitMeasures {ξ : ℝ} {ν : ProbabilityMeasure S6}
    (hν : ν ∈ limitMeasures ξ) (f : S6 →ᵇ ℝ) :
    ∫ x, compT32 f x ∂(ν : Measure S6) = ∫ x, f x ∂(ν : Measure S6) := by
  have hclust : ClusterPt ν (Filter.map (empirical ξ) atTop) := hν.clusterPt
  haveI hne : Filter.NeBot (𝓝 ν ⊓ Filter.map (empirical ξ) atTop) := hclust
  set D : ProbabilityMeasure S6 → ℝ := fun μ =>
    ∫ x, compT32 f x ∂(μ : Measure S6) - ∫ x, f x ∂(μ : Measure S6) with hD
  have h1 : Tendsto D (𝓝 ν ⊓ Filter.map (empirical ξ) atTop) (𝓝 0) := by
    refine Tendsto.mono_left ?_ inf_le_right
    rw [hD, tendsto_map'_iff]
    exact tendsto_integral_compT32_empirical_sub f ξ
  have h2 : Tendsto D (𝓝 ν ⊓ Filter.map (empirical ξ) atTop) (𝓝 (D ν)) := by
    refine Tendsto.mono_left ?_ inf_le_left
    exact ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction (compT32 f)).sub
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f)).tendsto ν
  exact sub_eq_zero.mp (tendsto_nhds_unique h2 h1)

/-- **Every limit measure is `T`-invariant** (Krylov–Bogolyubov).  This is the *only* invariance
the orbit gives for free; recovering `σ₂`-invariance is the open input **H-inv** of the bridge
architecture (plan-A1+ §2.3, L8). -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem limitMeasures_T32_invariant {ξ : ℝ} {ν : ProbabilityMeasure S6} (hν : ν ∈ limitMeasures ξ) :
    ν.map (measurable_T32.aemeasurable (μ := (ν : Measure S6))) = ν := by
  refine tendsto_nhds_unique (l := (atTop : Filter ℕ)) (f := fun _ : ℕ => ν.map
    (measurable_T32.aemeasurable (μ := (ν : Measure S6)))) tendsto_const_nhds ?_
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hmap : ∫ x, f x ∂((ν.map (measurable_T32.aemeasurable (μ := (ν : Measure S6)))) : Measure S6)
      = ∫ x, f x ∂(ν : Measure S6) := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map measurable_T32.aemeasurable
      f.continuous.aestronglyMeasurable]
    exact integral_compT32_of_mem_limitMeasures hν f
  simp only [hmap]
  exact tendsto_const_nhds

/-- The same statement for the underlying measures. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem map_T32_of_mem_limitMeasures {ξ : ℝ} {ν : ProbabilityMeasure S6}
    (hν : ν ∈ limitMeasures ξ) : Measure.map T32 (ν : Measure S6) = (ν : Measure S6) := by
  have := congrArg (fun μ : ProbabilityMeasure S6 => (μ : Measure S6))
    (limitMeasures_T32_invariant hν)
  simpa using this

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem measurePreserving_of_mem_limitMeasures {ξ : ℝ} {ν : ProbabilityMeasure S6}
    (hν : ν ∈ limitMeasures ξ) :
    MeasurePreserving T32 (ν : Measure S6) (ν : Measure S6) :=
  ⟨measurable_T32, map_T32_of_mem_limitMeasures hν⟩

/-! ### Equidistribution is "the only limit measure is Haar" -/

/-- Haar measure as a point of `ProbabilityMeasure Σ₆`. -/
noncomputable def haarProb : ProbabilityMeasure S6 := ⟨haar, inferInstance⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem haarProb_toMeasure : (haarProb : Measure S6) = haar := rfl

/-- **W3's `Equidistributed` is weak-∗ convergence of the empirical measures.**  The left-hand
side is the Birkhoff-average definition of `Dictionary.lean`; the right-hand side is convergence
in the compact space `ProbabilityMeasure Σ₆`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem equidistributed_iff_tendsto (ξ : ℝ) :
    Equidistributed ξ ↔ Tendsto (empirical ξ) atTop (𝓝 haarProb) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  constructor
  · intro h f
    exact (tendsto_integral_empirical_iff f.toContinuousMap ξ _).mpr (h f.toContinuousMap)
  · intro h f
    exact (tendsto_integral_empirical_iff f ξ _).mp (h (BoundedContinuousFunction.mkOfCompact f))

/-- If the empirical measures converge, the limit is the unique cluster point. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem limitMeasures_eq_of_tendsto {ξ : ℝ} {ν : ProbabilityMeasure S6}
    (h : Tendsto (empirical ξ) atTop (𝓝 ν)) : limitMeasures ξ = {ν} := by
  ext μ
  simp only [mem_limitMeasures_iff, Set.mem_singleton_iff]
  constructor
  · intro hμ
    exact eq_of_nhds_neBot (hμ.clusterPt.mono h)
  · rintro rfl
    exact h.mapClusterPt

/-- Conversely, in a compact space a unique cluster point forces convergence.  This is the reason
the architecture passes to measures at all: `Σ₆` compact ⟹ `ProbabilityMeasure Σ₆` compact. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem tendsto_of_limitMeasures_eq {ξ : ℝ} {ν : ProbabilityMeasure S6}
    (h : limitMeasures ξ = {ν}) : Tendsto (empirical ξ) atTop (𝓝 ν) :=
  tendsto_nhds_of_unique_mapClusterPt fun μ hμ => by
    have : μ ∈ limitMeasures ξ := hμ
    rw [h] at this
    exact this

/-- **The dictionary at the level of measures.**  Equidistribution of the orbit of `x_ξ` — hence,
by W3's `weyl_dictionary`, u.d. mod 1 of the whole `ℤ[1/6]`-family `(r ξ (3/2)ⁿ)` — is exactly the
statement that Haar measure is the *only* weak-∗ limit measure of the empirical measures. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem equidistributed_iff_limitMeasures (ξ : ℝ) :
    Equidistributed ξ ↔ limitMeasures ξ = {haarProb} :=
  ⟨fun h => limitMeasures_eq_of_tendsto ((equidistributed_iff_tendsto ξ).mp h),
   fun h => (equidistributed_iff_tendsto ξ).mpr (tendsto_of_limitMeasures_eq h)⟩

/-- If Haar is the only limit measure then `(ξ (3/2)ⁿ)` is u.d. mod 1 — the target statement
**T**, reached through the W3 dictionary. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem ud_of_limitMeasures_eq {ξ : ℝ} (h : limitMeasures ξ = {haarProb}) :
    Bertin.UniformlyDistributedModOne (fun n => ξ * (3 / 2) ^ n) :=
  ud_of_equidistributed ((equidistributed_iff_limitMeasures ξ).mpr h)

/-! ### The Dirac gate -/

/-- **The Dirac gate** (plan-A1+ L4, angle A13).  A Dirac mass can only be a limit measure of the
orbit at the point `0`: `T`-invariance of `δ_p` forces `T p = p`, and `T` has no fixed point but
`0` (`eq_zero_of_T32_eq_self`).  Consequently "no Dirac limit measure at all" reduces to the
single statement `δ₀ ∉ limitMeasures ξ`, which is A13's target N1 and is **open**. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem eq_zero_of_diracProba_mem_limitMeasures {ξ : ℝ} {p : S6}
    (hp : diracProba p ∈ limitMeasures ξ) : p = 0 := by
  haveI : MeasurableSpace.SeparatesPoints S6 :=
    MeasurableSpace.separatesPoints_of_measurableSingletonClass
  have hmap := map_T32_of_mem_limitMeasures hp
  rw [show ((diracProba p : ProbabilityMeasure S6) : Measure S6) = Measure.dirac p from rfl,
    Measure.map_dirac' measurable_T32] at hmap
  exact eq_zero_of_T32_eq_self p (dirac_eq_dirac_iff.mp hmap)

/-! ### Non-vacuity: the degenerate orbit at `ξ = 0` -/

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem wind_zero : wind 0 = 0 := by
  show (QuotientAddGroup.mk ((0 : ℝ), (0 : ℚ_[2]), (0 : ℚ_[3])) : S6) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact Δ₆.zero_mem

@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem T32_iter_zero (n : ℕ) : T32^[n] (0 : S6) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

/-- The empirical measures of the orbit at `ξ = 0` are all `δ₀`: the orbit is the fixed point. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem empirical_zero (N : ℕ) : empirical 0 N = diracProba (0 : S6) := by
  refine Subtype.ext ?_
  show empiricalMeasure 0 N = Measure.dirac 0
  ext s hs
  rw [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [wind_zero, T32_iter_zero, Finset.sum_const, Finset.card_range, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by simp), one_mul]

/-- **The Dirac gate is sharp**: at `ξ = 0` the orbit really does collapse, and `δ₀` really is the
unique limit measure.  So excluding `δ₀` for `ξ ≠ 0` (A13-N1) must use the arithmetic of `ξ`, not
the structure of `Σ₆` — the same conclusion the finite-level no-go of `Z32/BalanceVectors.lean`
reached (its two witnesses, the fixed point `0` and the 2-cycle, are orbit-closure points at every
level). -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem limitMeasures_zero : limitMeasures 0 = {diracProba (0 : S6)} := by
  refine limitMeasures_eq_of_tendsto ?_
  rw [show empirical 0 = fun _ : ℕ => diracProba (0 : S6) from funext empirical_zero]
  exact tendsto_const_nhds

/-- Haar is not a Dirac mass — read off from `not_equidistributed_zero` (W3) through the
dictionary, with no computation of Haar measure of a cell. -/
@[category test, AMS 11, ref "A1plus", group "th_solenoid_limitmeasures"]
theorem diracProba_zero_ne_haarProb : diracProba (0 : S6) ≠ haarProb := by
  intro h
  refine not_equidistributed_zero ((equidistributed_iff_limitMeasures 0).mpr ?_)
  rw [limitMeasures_zero, h]

end TH.S6
