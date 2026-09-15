/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Factor
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import ForMathlib.Analysis.Equidistribution.ModOne
import ForMathlib.Analysis.Equidistribution.IntegralCriterion
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Theorem 7: the invariant-measure lemma, and the master target

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Theorem 7, quadratic case.

`BB61/Factor.lean` produced the continuous factor map `F : {0,1}^ℤ → 𝕋` with
`F(σⁿ ω̃) = ξ αⁿ mod 1`.  Theorem 7 turns that pointwise identity into a statement about
*measures*: the empirical measures of the orbit are the `F`-images of the empirical measures
of a shift orbit, and the latter subconverge to shift-invariant measures.

* `map_orbitEmp` — `λ_N = F_* ν_N`, the first sentence of Theorem 7.
* `exists_invariant_of_tendsto` — the second: if `λ_N → λ` along any filter refining `atTop`,
  then `λ = F_* μ` for a `σ`-invariant Borel probability measure `μ` on `{0,1}^ℤ`.  The proof
  is the note's: `ProbabilityMeasure {0,1}^ℤ` is compact (Prokhorov, `{0,1}^ℤ` being compact
  metrisable), `‖σ_*ν_N - ν_N‖ ≤ 2/N → 0` forces the limit to be invariant, and `F` is
  continuous so `F_*` passes to the limit.
* `not_equidistributed_of_no_invariant` — **the master target**, boxed in the note: if no
  `σ`-invariant `μ` has `F_*μ = Leb`, then Problem 10.61 holds at `α`.  The bridge from the
  counting definition of uniform distribution to weak-\* convergence of `λ_N` is
  `tendsto_emp_of_equidistributed`, which runs the repository's Riemann-criterion
  (`ForMathlib/Analysis/Equidistribution/IntegralCriterion.lean`) on the circle.

The other half of M1 Cor. 9 — the realization converse, M1 Prop. 8 — is not here.  Its
ergodic case is `BB61/Realization.lean`, which runs Birkhoff's pointwise ergodic theorem (the
vendored `BirkhoffErgodicThm` library; Mathlib has only the mean theorem) on a countable dense
family of test functions.  The general case, M1 Prop. 8(ii) — *saturation* — is
`BB61/Saturation.lean`, and needs no ergodic theorem at all.  With it the target below is an
**equivalence**: `BB61.QuadSetup.equidistributed_iff_exists_invariant`.  So nothing is lost in
the reduction, and a counterexample to the target would be a counterexample to 10.61 rather
than an obstruction to this proof strategy.
-/

namespace BB61

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

/-! ## Empirical measures -/

section Empirical

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- The empirical measure `(N+1)⁻¹ ∑_{n ≤ N} δ_{x n}` of the first `N+1` points of a
sequence.  Indexing by `N+1` rather than `N` keeps it a probability measure at every `N`. -/
noncomputable def empMeasure (x : ℕ → Ω) (N : ℕ) : Measure Ω :=
  ((N : ℝ≥0∞) + 1)⁻¹ • ∑ n ∈ Finset.range (N + 1), Measure.dirac (x n)

instance isProbabilityMeasure_empMeasure (x : ℕ → Ω) (N : ℕ) :
    IsProbabilityMeasure (empMeasure x N) := by
  constructor
  have h : (∑ n ∈ Finset.range (N + 1), Measure.dirac (x n)) Set.univ = ((N : ℝ≥0∞) + 1) := by
    simp
  rw [empMeasure, Measure.smul_apply, h, smul_eq_mul, ENNReal.inv_mul_cancel] <;> simp

/-- The empirical measure, bundled as a `ProbabilityMeasure`. -/
noncomputable def emp (x : ℕ → Ω) (N : ℕ) : ProbabilityMeasure Ω :=
  ⟨empMeasure x N, inferInstance⟩

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in
@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem toMeasure_emp (x : ℕ → Ω) (N : ℕ) :
    ((emp x N : ProbabilityMeasure Ω) : Measure Ω) = empMeasure x N := rfl

/-- Integration against the empirical measure is the arithmetic mean. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_emp (x : ℕ → Ω) (N : ℕ) (f : Ω →ᵇ ℝ) :
    ∫ ω, f ω ∂(emp x N : Measure Ω) = (∑ n ∈ Finset.range (N + 1), f (x n)) / (N + 1) := by
  have hsm : StronglyMeasurable (f : Ω → ℝ) := f.continuous.stronglyMeasurable
  rw [toMeasure_emp, empMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => f.integrable (Measure.dirac (x i)))]
  simp only [integral_dirac' _ _ hsm, smul_eq_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp)]
  simp [div_eq_inv_mul]

variable [MeasurableSpace Ω']

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in
/-- The push-forward of an empirical measure is the empirical measure of the image points —
the mechanism behind `λ_N = F_* ν_N`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem map_empMeasure (x : ℕ → Ω) (N : ℕ) {g : Ω → Ω'} (hg : Measurable g) :
    Measure.map g (empMeasure x N) = empMeasure (fun n => g (x n)) N := by
  ext s hs
  rw [Measure.map_apply hg hs, empMeasure, empMeasure, Measure.smul_apply, Measure.smul_apply,
    Measure.finsetSum_apply _ _ (g ⁻¹' s), Measure.finsetSum_apply _ _ s]
  refine congrArg _ (Finset.sum_congr rfl fun n _ => ?_)
  rw [Measure.dirac_apply' _ (hg hs), Measure.dirac_apply' _ hs]
  by_cases hmem : g (x n) ∈ s <;> simp [hmem]

end Empirical

/-! ## Push-forward of probability measures, as a continuous map -/

section PMap

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
  [MeasurableSpace Ω'] [TopologicalSpace Ω'] [BorelSpace Ω']

/-- Push-forward along a measurable map, on bundled probability measures. -/
noncomputable def pmap {g : Ω → Ω'} (hg : Measurable g) (ν : ProbabilityMeasure Ω) :
    ProbabilityMeasure Ω' := ν.map hg.aemeasurable

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [TopologicalSpace Ω'] [BorelSpace Ω'] in
@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem toMeasure_pmap {g : Ω → Ω'} (hg : Measurable g) (ν : ProbabilityMeasure Ω) :
    ((pmap hg ν : ProbabilityMeasure Ω') : Measure Ω') = Measure.map g (ν : Measure Ω) :=
  ProbabilityMeasure.toMeasure_map _ _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_pmap {g : Ω → Ω'} (hg : Continuous g) : Continuous (pmap hg.measurable) :=
  ProbabilityMeasure.continuous_map hg

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_pmap {g : Ω → Ω'} (hg : Continuous g) (ν : ProbabilityMeasure Ω)
    (f : Ω' →ᵇ ℝ) :
    ∫ z, f z ∂(pmap hg.measurable ν : Measure Ω') = ∫ ω, f (g ω) ∂(ν : Measure Ω) := by
  rw [toMeasure_pmap, integral_map hg.measurable.aemeasurable]
  exact f.continuous.aestronglyMeasurable

end PMap

/-! ## The circle, and uniform distribution as weak-\* convergence -/

instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
  constructor
  rw [AddCircle.measure_univ]
  norm_num

/-- Haar measure on `𝕋 = ℝ/ℤ`, as a probability measure; on `AddCircle 1` it is `volume`. -/
noncomputable def haarT : ProbabilityMeasure (AddCircle (1 : ℝ)) := ⟨volume, inferInstance⟩

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem toMeasure_haarT : ((haarT : ProbabilityMeasure (AddCircle (1 : ℝ)))
    : Measure (AddCircle (1 : ℝ))) = volume := rfl

/-- Reduction mod one does not see the integer part. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_fract (t : ℝ) :
    ((Int.fract t : ℝ) : AddCircle (1 : ℝ)) = ((t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  refine ⟨-⌊t⌋, ?_⟩
  simp only [neg_smul, zsmul_eq_mul, mul_one]
  rw [Int.fract]
  ring

/-- The integral of a continuous function over the circle is its integral over `[0,1]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_haarT (G : AddCircle (1 : ℝ) →ᵇ ℝ) :
    ∫ z, G z ∂(haarT : Measure (AddCircle (1 : ℝ)))
      = ∫ t in Set.Icc (0 : ℝ) 1, G ((t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h := AddCircle.integral_preimage (1 : ℝ) 0 (fun z => G z)
  rw [zero_add] at h
  rw [toMeasure_haarT, ← h]

/-- **Uniform distribution is weak-\* convergence of the empirical measures.**  If
`(s n)` is u.d. mod one then the empirical measures of `(s n mod 1)` converge to Haar
measure on `𝕋`.  This is the Riemann criterion of
`ForMathlib/Analysis/Equidistribution/IntegralCriterion.lean` read on the circle. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_emp_of_equidistributed {s : ℕ → ℝ} (h : IsEquidistributedModuloOne s) :
    Tendsto (fun N => emp (fun n => ((s n : ℝ) : AddCircle (1 : ℝ))) N) atTop (𝓝 haarT) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro G
  set g : ℝ → ℝ := fun t => G ((t : ℝ) : AddCircle (1 : ℝ)) with hgdef
  set y : ℕ → ℝ := fun n => Int.fract (s n) with hydef
  have hgcont : Continuous g := G.continuous.comp QuotientAddGroup.continuous_mk
  -- the Riemann criterion applies to `g` on `[0,1]`
  have hbdd : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ C :=
    ⟨‖G‖, fun t _ => by simpa [Real.norm_eq_abs] using G.norm_coe_le_norm _⟩
  have hae : volume {t ∈ Set.Icc (0 : ℝ) 1 | ¬ ContinuousAt g t} = 0 := by
    convert measure_empty (μ := (volume : Measure ℝ))
    ext t
    simp [hgcont.continuousAt]
  have hy : ∀ n, y n ∈ Set.Ico (0 : ℝ) 1 := fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have H : ∀ a b : ℝ, (0 : ℝ) ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N => (∑ m ∈ Finset.range N,
        (Set.Ico a b).indicator (fun _ => (1 : ℝ)) (y m)) / N) atTop (𝓝 ((b - a) / (1 - 0))) := by
    intro a b ha hab hb
    have hc := h.tendsto_count_Ico ha hab.le hb
    rw [show ((b - a) / (1 - 0)) = b - a by norm_num]
    refine hc.congr fun N => ?_
    congr 1
    rw [← Finset.sum_boole (fun m => Int.fract (s m) ∈ Set.Ico a b) (Finset.range N)]
    exact Finset.sum_congr rfl fun m _ => by simp [Set.indicator_apply, hydef]
  have key := tendsto_average_of_indicator_equidistributed (f := g) (by norm_num : (0:ℝ) < 1)
    hbdd hae y hy H
  -- shift the index and rewrite both sides
  have key' : Tendsto (fun N : ℕ => (∑ m ∈ Finset.range (N + 1), g (y m)) / (N + 1)) atTop
      (𝓝 ((∫ t in Set.Icc (0:ℝ) 1, g t) / (1 - 0))) := by
    have hk := key.comp (Filter.tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one] at hk
    exact hk
  rw [integral_haarT]
  have hL : ∀ N : ℕ,
      ∫ z, G z ∂(emp (fun n => ((s n : ℝ) : AddCircle (1 : ℝ))) N : Measure (AddCircle (1:ℝ)))
        = (∑ m ∈ Finset.range (N + 1), g (y m)) / (N + 1) := by
    intro N
    rw [integral_emp]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by simp only [hgdef, hydef, coe_fract]
  simp only [hL]
  simpa using key'

/-! ## Theorem 7 -/

/-- The empirical measures `ν_N` of the shift orbit of the padded word `ω̃ = padZ ε`. -/
noncomputable def orbitEmp (ε : ℕ → Bool) (N : ℕ) : ProbabilityMeasure Shift :=
  emp (fun n => shiftZ^[n] (padZ ε)) N

namespace QuadSetup

variable (P : QuadSetup)

/-- **M1 Theorem 7, first half**: `λ_N = F_* ν_N`.  The empirical measure of the orbit
`({ξ αⁿ})_{n ≤ N}` on `𝕋` is the `F`-image of the empirical measure of the shift orbit. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem map_orbitEmp (ε : ℕ → Bool) (N : ℕ) :
    pmap P.measurable_fMap (orbitEmp ε N)
      = emp (fun n => ((piVal P.α ε * P.α ^ n : ℝ) : AddCircle (1 : ℝ))) N := by
  refine ProbabilityMeasure.toMeasure_injective ?_
  rw [toMeasure_pmap, orbitEmp, toMeasure_emp, toMeasure_emp,
    map_empMeasure _ _ P.measurable_fMap]
  exact congrArg (fun z => empMeasure z N) (funext fun n => P.fMap_iterate_padZ ε n)

/-- **M1 Theorem 7, second half.**  If the empirical measures of the orbit converge weak-\*
along any `NeBot` filter refining `atTop` — in particular along the full sequence, or along
any subsequence — the limit is `F_* μ` for a `σ`-invariant Borel probability measure `μ` on
`{0,1}^ℤ`.

The three ingredients are exactly the note's: compactness of `ProbabilityMeasure {0,1}^ℤ`,
the telescoping bound `‖σ_*ν_N - ν_N‖ ≤ 2/(N+1)`, and continuity of `F`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_invariant_of_tendsto (ε : ℕ → Bool) {L : Filter ℕ} [L.NeBot] (hL : L ≤ atTop)
    {lam : ProbabilityMeasure (AddCircle (1 : ℝ))}
    (h : Tendsto (fun N => emp (fun n => ((piVal P.α ε * P.α ^ n : ℝ) : AddCircle (1 : ℝ))) N)
      L (𝓝 lam)) :
    ∃ μ : ProbabilityMeasure Shift,
      pmap continuous_shiftZ.measurable μ = μ ∧ pmap P.measurable_fMap μ = lam := by
  set x : ℕ → Shift := fun n => shiftZ^[n] (padZ ε) with hxdef
  set ν : ℕ → ProbabilityMeasure Shift := fun N => emp x N with hνdef
  -- a cluster point of the empirical measures
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (Filter.map ν L)
  have hGne : (𝓝 μ ⊓ Filter.map ν L).NeBot := hμ
  set G : Filter (ProbabilityMeasure Shift) := 𝓝 μ ⊓ Filter.map ν L with hGdef
  have hGμ : G ≤ 𝓝 μ := inf_le_left
  have hGν : G ≤ Filter.map ν L := inf_le_right
  have hGtop : G ≤ Filter.map ν atTop := hGν.trans (Filter.map_mono hL)
  have hid : Tendsto (fun ρ : ProbabilityMeasure Shift => ρ) G (𝓝 μ) := hGμ
  refine ⟨μ, ?_, ?_⟩
  · -- `σ`-invariance
    have hcont : Tendsto (pmap continuous_shiftZ.measurable) G
        (𝓝 (pmap continuous_shiftZ.measurable μ)) :=
      ((continuous_pmap continuous_shiftZ).continuousAt).tendsto.comp hid
    have hlim : Tendsto (pmap continuous_shiftZ.measurable) G (𝓝 μ) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      -- `B ρ = ∫ f dρ` converges to `∫ f dμ`, and `A ρ - B ρ → 0` along the orbit
      have hB : Tendsto (fun ρ : ProbabilityMeasure Shift => ∫ ω, f ω ∂(ρ : Measure Shift)) G
          (𝓝 (∫ ω, f ω ∂(μ : Measure Shift))) :=
        (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hid) f
      have hAB : Tendsto (fun ρ : ProbabilityMeasure Shift =>
          (∫ ω, f (shiftZ ω) ∂(ρ : Measure Shift)) - ∫ ω, f ω ∂(ρ : Measure Shift)) G (𝓝 0) := by
        refine Tendsto.mono_left ?_ hGtop
        rw [Filter.tendsto_map'_iff]
        have hcomp : ∀ N : ℕ,
            (∫ ω, f (shiftZ ω) ∂(ν N : Measure Shift)) - ∫ ω, f ω ∂(ν N : Measure Shift)
              = (f (x (N + 1)) - f (x 0)) / (N + 1) := by
          intro N
          have h1 : ∫ ω, f (shiftZ ω) ∂(ν N : Measure Shift)
              = (∑ n ∈ Finset.range (N + 1), f (x (n + 1))) / (N + 1) := by
            have := integral_emp x N (f.compContinuous ⟨shiftZ, continuous_shiftZ⟩)
            simp only [compContinuous_apply, ContinuousMap.coe_mk] at this
            rw [hνdef]
            refine this.trans (congrArg (· / ((N : ℝ) + 1)) (Finset.sum_congr rfl fun n _ => ?_))
            rw [hxdef]
            simp only
            rw [← Function.iterate_succ_apply' shiftZ n]
          have h2 : ∫ ω, f ω ∂(ν N : Measure Shift)
              = (∑ n ∈ Finset.range (N + 1), f (x n)) / (N + 1) := integral_emp x N f
          rw [h1, h2, div_sub_div_same]
          congr 1
          have e1 := Finset.sum_range_succ' (fun n => f (x n)) (N + 1)
          have e2 := Finset.sum_range_succ (fun n => f (x n)) (N + 1)
          linarith [e1, e2]
        simp only [Function.comp_def, hcomp]
        have hden : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        refine squeeze_zero_norm (a := fun N : ℕ => (2 * ‖f‖) / ((N : ℝ) + 1)) (fun N => ?_)
          (tendsto_const_nhds.div_atTop hden)
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < (N : ℝ) + 1)]
        gcongr
        calc |f (x (N + 1)) - f (x 0)| ≤ |f (x (N + 1))| + |f (x 0)| := abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := by
              gcongr <;> simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _
        _ = 2 * ‖f‖ := by ring
      have hA : Tendsto (fun ρ : ProbabilityMeasure Shift =>
          ∫ ω, f (shiftZ ω) ∂(ρ : Measure Shift)) G (𝓝 (∫ ω, f ω ∂(μ : Measure Shift))) := by
        have := hAB.add hB
        rw [zero_add] at this
        simpa using this
      simpa only [integral_pmap continuous_shiftZ] using hA
    exact tendsto_nhds_unique hcont hlim
  · -- the push-forward
    have hcont : Tendsto (pmap P.measurable_fMap) G (𝓝 (pmap P.measurable_fMap μ)) :=
      ((continuous_pmap P.continuous_fMap).continuousAt).tendsto.comp hid
    have hlim : Tendsto (pmap P.measurable_fMap) G (𝓝 lam) := by
      refine Tendsto.mono_left ?_ hGν
      rw [Filter.tendsto_map'_iff]
      refine h.congr fun N => ?_
      rw [Function.comp_apply, hνdef]
      exact (P.map_orbitEmp ε N).symm
    exact tendsto_nhds_unique hcont hlim

/-- **M1 Theorem 7, the master target.**  If no `σ`-invariant Borel probability measure `μ`
on `{0,1}^ℤ` satisfies `F_* μ = Leb_𝕋`, then Problem 10.61 holds at `α`: no `ξ ∈ C(α)` has
`(ξ αⁿ)` uniformly distributed modulo one.

This is the boxed statement of `note-1061-M1.html` §3. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_no_invariant
    (hno : ∀ μ : ProbabilityMeasure Shift,
      pmap continuous_shiftZ.measurable μ = μ → pmap P.measurable_fMap μ ≠ haarT)
    {ξ : ℝ} (hξ : ξ ∈ cantorSet P.α) :
    ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨ε, rfl⟩ := hξ
  intro hud
  obtain ⟨μ, hinv, hmap⟩ :=
    P.exists_invariant_of_tendsto ε (L := atTop) le_rfl (tendsto_emp_of_equidistributed hud)
  exact hno μ hinv hmap

/-- The contrapositive, in the form M1 Corollary 9 uses: a counterexample to 10.61 at `α`
produces a `σ`-invariant measure of the full `2`-shift whose `F`-image is Lebesgue. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_invariant_of_equidistributed {ξ : ℝ} (hξ : ξ ∈ cantorSet P.α)
    (hud : IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n) :
    ∃ μ : ProbabilityMeasure Shift,
      pmap continuous_shiftZ.measurable μ = μ ∧ pmap P.measurable_fMap μ = haarT := by
  obtain ⟨ε, rfl⟩ := hξ
  exact P.exists_invariant_of_tendsto ε (L := atTop) le_rfl (tendsto_emp_of_equidistributed hud)


/-! ### The same statements at the level of `Measure`

The bundled `ProbabilityMeasure` form is what the compactness argument needs; this is the
form the note states, with `σ`-invariance and `F_*μ = Leb` written as measure equalities. -/

/-- **The master target, unbundled** (M1 Theorem 7).  If every `σ`-invariant Borel
probability measure `μ` on `{0,1}^ℤ` has `F_* μ ≠ Leb_𝕋`, then Problem 10.61 holds at `α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_no_invariant_measure
    (hno : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ ≠ (volume : Measure (AddCircle (1 : ℝ))))
    {ξ : ℝ} (hξ : ξ ∈ cantorSet P.α) :
    ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  refine P.not_equidistributed_of_no_invariant (fun μ hinv hmap => ?_) hξ
  refine hno (μ : Measure Shift) μ.2 ?_ ?_
  · simpa using congrArg ProbabilityMeasure.toMeasure hinv
  · simpa using congrArg ProbabilityMeasure.toMeasure hmap

/-- **The contrapositive, unbundled** (M1 Cor. 9, easy direction).  A counterexample to
10.61 at `α` produces a `σ`-invariant Borel probability measure of the full `2`-shift whose
`F`-image is Lebesgue measure on `𝕋`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_invariant_measure_of_equidistributed {ξ : ℝ} (hξ : ξ ∈ cantorSet P.α)
    (hud : IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n) :
    ∃ μ : Measure Shift, IsProbabilityMeasure μ ∧ Measure.map shiftZ μ = μ ∧
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) := by
  obtain ⟨μ, hinv, hmap⟩ := P.exists_invariant_of_equidistributed hξ hud
  refine ⟨(μ : Measure Shift), μ.2, ?_, ?_⟩
  · simpa using congrArg ProbabilityMeasure.toMeasure hinv
  · simpa using congrArg ProbabilityMeasure.toMeasure hmap

end QuadSetup

end BB61
