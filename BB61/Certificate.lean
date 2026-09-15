/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Invariant
import Mathlib.Analysis.LocallyConvex.Separation
import ForMathlib.Analysis.Equidistribution.AddCircleWeyl
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M3 Theorem 9: completeness of the certificate scheme

Formal companion of `note-1061-M3.html` (milestone M3 of `plans/plan-1061.html`), §6,
quadratic case.

M1 Theorem 7 (`BB61/Invariant.lean`) reduced Problem 10.61 at `α` to a statement about the
shift-invariant measures of the full `2`-shift: if no `σ`-invariant `μ` has `F_*μ = Leb`, then
10.61 holds at `α`.  Theorem 9 says that this hypothesis is **never true for a bad reason**:
whenever it holds, it holds because of a *finite* certificate — a single mean-zero
trigonometric polynomial `G` on `𝕋` with

`∫ G ∘ F dμ ≥ c > 0` for every `σ`-invariant `μ`.

* `BB61.Certificate` — the certificate as a structure (a bounded continuous `G`, a constant
  `c > 0`, zero mean, and the lower bound).
* `QuadSetup.Certificate.no_invariant`, `QuadSetup.Certificate.not_equidistributed` — the easy
  direction: a certificate kills every invariant measure, hence (M1 Theorem 7) proves 10.61 at
  `α`.  This is the note's "Route D is always available".
* `QuadSetup.exists_certificate` — the content of Theorem 9: conversely, if no invariant
  measure maps to Lebesgue, a certificate exists.  The proof is the note's, with the
  separation performed in a finite-dimensional space: compactness of `M(σ)` first reduces the
  (infinite) family of test functions to a finite one `u`, and then `0` is separated from the
  compact convex set `V = {(∫ g∘F dμ - ∫ g)_{g ∈ u} : μ ∈ M(σ)} ⊆ ℝ^u` by geometric
  Hahn–Banach.
* `QuadSetup.nonempty_certificate_iff` — **Theorem 9**, as an equivalence between the
  invariant-measure hypothesis of M1 Theorem 7 and the existence of a certificate.
* `QuadSetup.exists_trigCertificate` — the certificate can be taken to be a real trigonometric
  polynomial `G = Re ∑_{h ∈ H} a_h e(h ·)` with `0 ∉ H`, which is the form Theorem 9 states
  and the form that makes the data finite.  This is the continuous certificate followed by a
  Fejér-type approximation (`span_fourier_closure_eq_top`).

The note's Theorem 9 is stated as an equivalence with "10.61 holds at `α`" on the left.  The
passage between "10.61 holds at `α`" and "no invariant `μ` has `F_*μ = Leb`" is M1 Cor. 9,
which sits downstream of this file: its converse half (M1 Prop. 8) is `BB61/Realization.lean`
for *ergodic* `μ` and `BB61/Saturation.lean` in general.  So the equivalence is formalised
here between the certificate and the *invariant-measure* statement, only the implication
`certificate → 10.61 at α` is exported to `IsEquidistributedModuloOne`, and the note's own
form is `BB61.QuadSetup.forall_not_equidistributed_iff_exists_trigCertificate` in
`BB61/Saturation.lean`.  Corollary 10
(`Σ₁`-ness) additionally needs the variational principle for topological pressure, also absent
from Mathlib, and is not formalised.
-/

namespace BB61

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

/-! ## Mixtures of probability measures

The set of invariant measures is convex, and the separation argument needs that convexity in
the concrete form "the mixture of two invariant measures is invariant". -/

section Mix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mixture `a·μ₀ + b·μ₁` of two measures. -/
noncomputable def mixMeasure (a b : ℝ) (μ₀ μ₁ : Measure Ω) : Measure Ω :=
  ENNReal.ofReal a • μ₀ + ENNReal.ofReal b • μ₁

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isProbabilityMeasure_mixMeasure {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ₀ μ₁ : Measure Ω) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] :
    IsProbabilityMeasure (mixMeasure a b μ₀ μ₁) := by
  constructor
  have h : (mixMeasure a b μ₀ μ₁) Set.univ = ENNReal.ofReal a + ENNReal.ofReal b := by
    simp [mixMeasure]
  rw [h, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem map_mixMeasure {Ω' : Type*} [MeasurableSpace Ω'] (a b : ℝ) (μ₀ μ₁ : Measure Ω)
    {g : Ω → Ω'} (hg : Measurable g) :
    Measure.map g (mixMeasure a b μ₀ μ₁)
      = mixMeasure a b (Measure.map g μ₀) (Measure.map g μ₁) := by
  rw [mixMeasure, mixMeasure, Measure.map_add _ _ hg, Measure.map_smul, Measure.map_smul]

/-- The mixture of two probability measures. -/
noncomputable def mix {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ₀ μ₁ : ProbabilityMeasure Ω) : ProbabilityMeasure Ω :=
  ⟨mixMeasure a b (μ₀ : Measure Ω) (μ₁ : Measure Ω),
    isProbabilityMeasure_mixMeasure ha hb hab _ _⟩

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem toMeasure_mix {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ₀ μ₁ : ProbabilityMeasure Ω) :
    ((mix ha hb hab μ₀ μ₁ : ProbabilityMeasure Ω) : Measure Ω)
      = mixMeasure a b (μ₀ : Measure Ω) (μ₁ : Measure Ω) := rfl

/-- Push-forward is affine: it commutes with mixtures. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pmap_mix {Ω' : Type*} [MeasurableSpace Ω']
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) {g : Ω → Ω'} (hg : Measurable g)
    (μ₀ μ₁ : ProbabilityMeasure Ω) :
    pmap hg (mix ha hb hab μ₀ μ₁) = mix ha hb hab (pmap hg μ₀) (pmap hg μ₁) := by
  refine ProbabilityMeasure.toMeasure_injective ?_
  rw [toMeasure_pmap, toMeasure_mix, toMeasure_mix, map_mixMeasure _ _ _ _ hg,
    toMeasure_pmap, toMeasure_pmap]

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- Integration is affine in the measure. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_mix {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ₀ μ₁ : ProbabilityMeasure Ω) (f : Ω →ᵇ ℝ) :
    ∫ ω, f ω ∂(mix ha hb hab μ₀ μ₁ : Measure Ω)
      = a * ∫ ω, f ω ∂(μ₀ : Measure Ω) + b * ∫ ω, f ω ∂(μ₁ : Measure Ω) := by
  rw [toMeasure_mix, mixMeasure,
    integral_add_measure ((f.integrable _).smul_measure (by simp))
      ((f.integrable _).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]

/-- `integral_mix` for a test function pulled back along a continuous map. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_mix_comp {Ω' : Type*} [TopologicalSpace Ω'] {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) (μ₀ μ₁ : ProbabilityMeasure Ω) (f : Ω' →ᵇ ℝ)
    {φ : Ω → Ω'} (hφ : Continuous φ) :
    ∫ ω, f (φ ω) ∂(mix ha hb hab μ₀ μ₁ : Measure Ω)
      = a * ∫ ω, f (φ ω) ∂(μ₀ : Measure Ω) + b * ∫ ω, f (φ ω) ∂(μ₁ : Measure Ω) :=
  integral_mix ha hb hab μ₀ μ₁ (f.compContinuous ⟨φ, hφ⟩)

end Mix

/-! ## `M(σ)`, the invariant measures of the full two-shift -/

/-- `M(σ)`: the set of shift-invariant Borel probability measures on `{0,1}^ℤ`. -/
def invMeasures : Set (ProbabilityMeasure Shift) :=
  {μ | pmap continuous_shiftZ.measurable μ = μ}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_invMeasures {μ : ProbabilityMeasure Shift} :
    μ ∈ invMeasures ↔ pmap continuous_shiftZ.measurable μ = μ := Iff.rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isClosed_invMeasures : IsClosed invMeasures :=
  isClosed_eq (continuous_pmap continuous_shiftZ) continuous_id

/-- `M(σ)` is compact: it is closed in the (compact) space of Borel probability measures on the
compact metrisable space `{0,1}^ℤ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isCompact_invMeasures : IsCompact invMeasures := isClosed_invMeasures.isCompact

/-- `M(σ)` is convex. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mix_mem_invMeasures {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {μ₀ μ₁ : ProbabilityMeasure Shift} (h₀ : μ₀ ∈ invMeasures) (h₁ : μ₁ ∈ invMeasures) :
    mix ha hb hab μ₀ μ₁ ∈ invMeasures := by
  have h := pmap_mix ha hb hab continuous_shiftZ.measurable μ₀ μ₁
  rw [mem_invMeasures] at h₀ h₁ ⊢
  rw [h, h₀, h₁]

/-! ## Certificates -/

/-- **A confinement certificate at `α`** (M3 §6, "Route D"): a bounded continuous
`G : 𝕋 → ℝ` of zero mean whose average along the factor map `F` is bounded below by a positive
constant on *every* shift-invariant measure. -/
structure Certificate (P : QuadSetup) where
  /-- The test function on the circle. -/
  G : AddCircle (1 : ℝ) →ᵇ ℝ
  /-- The positive lower bound it certifies. -/
  c : ℝ
  /-- The bound is positive. -/
  c_pos : 0 < c
  /-- `G` has zero mean on the circle: it is orthogonal to the constants. -/
  mean_zero : ∫ z, G z ∂(volume : Measure (AddCircle (1 : ℝ))) = 0
  /-- The certified bound. -/
  le_integral : ∀ μ ∈ invMeasures, c ≤ ∫ ω, G (P.fMap ω) ∂(μ : Measure Shift)

namespace Certificate

/-- A certificate kills every invariant measure: if `F_*μ` were Lebesgue, the certified
average would be the mean of `G`, namely `0 < c`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem no_invariant {P : QuadSetup} (cert : Certificate P) {μ : ProbabilityMeasure Shift}
    (hμ : μ ∈ invMeasures) : pmap P.measurable_fMap μ ≠ haarT := by
  intro h
  have h1 : ∫ ω, cert.G (P.fMap ω) ∂(μ : Measure Shift)
      = ∫ z, cert.G z ∂((pmap P.measurable_fMap μ : ProbabilityMeasure _) : Measure _) :=
    (integral_pmap P.continuous_fMap μ cert.G).symm
  rw [h, toMeasure_haarT, cert.mean_zero] at h1
  have h2 := cert.le_integral μ hμ
  rw [h1] at h2
  linarith [cert.c_pos]

/-- **A certificate proves 10.61 at `α`.**  Combined with M1 Theorem 7: if there is a
mean-zero `G` on `𝕋` whose average along `F` is uniformly positive over the invariant
measures, then no `ξ ∈ C(α)` has `(ξ αⁿ)` uniformly distributed modulo one.  This is the
note's "Route D is always available". -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed {P : QuadSetup} (cert : Certificate P) {ξ : ℝ}
    (hξ : ξ ∈ cantorSet P.α) :
    ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  P.not_equidistributed_of_no_invariant (fun _ hinv => cert.no_invariant hinv) hξ

end Certificate

/-! ## Trigonometric polynomials on the circle

The note states Theorem 9 with `G` a *real trigonometric polynomial*; that is the form in
which a certificate is finite data.  `trigPoly H a = Re ∑_{h ∈ H} a_h e(h ·)`. -/

/-- The real trigonometric polynomial `Re ∑_{h ∈ H} a_h e(h ·)` on `𝕋 = ℝ/ℤ`. -/
noncomputable def trigPoly (H : Finset ℤ) (a : ℤ → ℂ) : AddCircle (1 : ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => (∑ h ∈ H, a h * fourier h z).re,
      Complex.continuous_re.comp (continuous_finsetSum _ fun h _ =>
        continuous_const.mul (map_continuous (fourier h)))⟩

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem trigPoly_apply (H : Finset ℤ) (a : ℤ → ℂ) (z : AddCircle (1 : ℝ)) :
    trigPoly H a z = (∑ h ∈ H, a h * fourier h z).re := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integrable_char (h : ℤ) (a : ℂ) :
    Integrable (fun z : AddCircle (1 : ℝ) => a * fourier h z)
      (volume : Measure (AddCircle (1 : ℝ))) :=
  (continuous_const.mul (map_continuous (fourier h))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- A trigonometric polynomial with no constant term has zero mean: it is orthogonal to the
constants, which is the `∫ G dLeb = 0` of the note. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_trigPoly_eq_zero {H : Finset ℤ} (h0 : (0 : ℤ) ∉ H) (a : ℤ → ℂ) :
    ∫ z, trigPoly H a z ∂(volume : Measure (AddCircle (1 : ℝ))) = 0 := by
  have hint : ∀ h ∈ H, Integrable (fun z : AddCircle (1 : ℝ) => a h * fourier h z)
      (volume : Measure (AddCircle (1 : ℝ))) := fun h _ => integrable_char h (a h)
  have hsum : ∫ z, (∑ h ∈ H, a h * fourier h z) ∂(volume : Measure (AddCircle (1 : ℝ))) = 0 := by
    rw [MeasureTheory.integral_finsetSum H hint]
    refine Finset.sum_eq_zero fun h hh => ?_
    have hne : h ≠ 0 := fun hcon => h0 (hcon ▸ hh)
    rw [integral_const_mul, ← haarAddCircle_eq_volume, integral_fourier_eq_zero hne, mul_zero]
  have hI : Integrable (fun z : AddCircle (1 : ℝ) => ∑ h ∈ H, a h * fourier h z)
      (volume : Measure (AddCircle (1 : ℝ))) := integrable_finsetSum _ hint
  have hre : ∀ z : AddCircle (1 : ℝ),
      trigPoly H a z = RCLike.re (∑ h ∈ H, a h * fourier h z) := fun _ => rfl
  simp_rw [hre]
  rw [integral_re hI, hsum]
  simp

namespace QuadSetup

variable (P : QuadSetup)

/-! ### The completeness direction

The three steps of the note's proof, with the separation moved to a finite-dimensional space:
compactness of `M(σ)` reduces the family of test functions to a finite one; the image of
`M(σ)` in `ℝ^u` is compact, convex and misses `0`; Hahn–Banach separates. -/

/-- Integration of the finite combination `∑ i, aᵢ (Fᵢ - rᵢ)` against a probability measure,
pulled back along a continuous map. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_combo {Ω Ω' : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [TopologicalSpace Ω'] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (F : ι → (Ω' →ᵇ ℝ)) (r : ι → ℝ)
    {φ : Ω → Ω'} (hφ : Continuous φ) :
    ∫ ω, (∑ i, a i • (F i - BoundedContinuousFunction.const Ω' (r i))) (φ ω) ∂ν
      = ∑ i, a i * ((∫ ω, F i (φ ω) ∂ν) - r i) := by
  have hint : ∀ i : ι, Integrable (fun ω => F i (φ ω)) ν := fun i =>
    ((F i).compContinuous ⟨φ, hφ⟩).integrable ν
  have hpt : ∀ ω, (∑ i, a i • (F i - BoundedContinuousFunction.const Ω' (r i))) (φ ω)
      = ∑ i, a i * (F i (φ ω) - r i) := by
    intro ω
    simp [BoundedContinuousFunction.coe_sum]
  simp_rw [hpt]
  rw [MeasureTheory.integral_finsetSum (f := fun i ω => a i * (F i (φ ω) - r i)) Finset.univ
    (fun i _ => ((hint i).sub (integrable_const _)).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_sub (hint i) (integrable_const _)]
  simp

/-- **M3 Theorem 9, the completeness direction.**  If no `σ`-invariant measure of the full
`2`-shift pushes forward to Lebesgue measure under `F`, then a certificate exists. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_certificate
    (hno : ∀ μ ∈ invMeasures, pmap P.measurable_fMap μ ≠ haarT) :
    Nonempty (Certificate P) := by
  classical
  -- Step 1: finitely many test functions already detect that `F_*μ ≠ Leb`.
  set t : (AddCircle (1 : ℝ) →ᵇ ℝ) → Set (ProbabilityMeasure Shift) := fun g =>
    {μ | ∫ ω, g (P.fMap ω) ∂(μ : Measure Shift)
      = ∫ z, g z ∂(volume : Measure (AddCircle (1 : ℝ)))} with htdef
  have htc : ∀ g, IsClosed (t g) := by
    intro g
    refine isClosed_eq ?_ continuous_const
    exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (g.compContinuous ⟨P.fMap, P.continuous_fMap⟩)
  have hst : Disjoint invMeasures (⋂ g, t g) := by
    rw [Set.disjoint_left]
    intro μ hμinv hμt
    refine hno μ hμinv (ProbabilityMeasure.toMeasure_injective ?_)
    refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    rw [toMeasure_haarT, toMeasure_pmap,
      integral_map P.measurable_fMap.aemeasurable g.continuous.aestronglyMeasurable]
    exact Set.mem_iInter.mp hμt g
  obtain ⟨u, hu⟩ := isCompact_invMeasures.elim_finite_subfamily_closed t htc hst
  -- Step 2: the finite-dimensional picture.
  set Fi : ↥u → (AddCircle (1 : ℝ) →ᵇ ℝ) := fun g => (g : AddCircle (1 : ℝ) →ᵇ ℝ) with hFi
  set ri : ↥u → ℝ := fun g => ∫ z, Fi g z ∂(volume : Measure (AddCircle (1 : ℝ))) with hri
  set Ψ : ProbabilityMeasure Shift → (↥u → ℝ) := fun μ g =>
    (∫ ω, Fi g (P.fMap ω) ∂(μ : Measure Shift)) - ri g with hΨ
  have hΨcont : Continuous Ψ := by
    refine continuous_pi fun g => ?_
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      ((Fi g).compContinuous ⟨P.fMap, P.continuous_fMap⟩)).sub continuous_const
  have hVcompact : IsCompact (Ψ '' invMeasures) := isCompact_invMeasures.image hΨcont
  have hVconv : Convex ℝ (Ψ '' invMeasures) := by
    rintro _ ⟨μ₀, h₀, rfl⟩ _ ⟨μ₁, h₁, rfl⟩ a b ha hb hab
    refine ⟨mix ha hb hab μ₀ μ₁, mix_mem_invMeasures ha hb hab h₀ h₁, ?_⟩
    funext g
    simp only [hΨ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      integral_mix_comp ha hb hab μ₀ μ₁ (Fi g) P.continuous_fMap]
    linear_combination (ri g) * hab
  have h0V : (0 : ↥u → ℝ) ∉ Ψ '' invMeasures := by
    rintro ⟨μ, hμ, hΨ0⟩
    refine Set.disjoint_left.mp hu hμ (Set.mem_iInter.mpr fun g => Set.mem_iInter.mpr fun hg => ?_)
    have hg0 := congrFun hΨ0 ⟨g, hg⟩
    simp only [hΨ, hFi, hri, Pi.zero_apply, sub_eq_zero] at hg0
    exact hg0
  -- Step 3: separate `0` from the image.
  obtain ⟨f, w, hf0, hfV⟩ := geometric_hahn_banach_point_closed hVconv hVcompact.isClosed h0V
  have hw : 0 < w := by simpa using hf0
  have hfeq : ∀ v : ↥u → ℝ, f v = ∑ g : ↥u, v g * f (fun j => if g = j then 1 else 0) := by
    intro v
    have h := LinearMap.pi_apply_eq_sum_univ (f : (↥u → ℝ) →ₗ[ℝ] ℝ) v
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
    exact h
  set A : ↥u → ℝ := fun g => f (fun j => if g = j then 1 else 0) with hA
  -- Step 4: the certificate.
  refine ⟨{ G := ∑ g : ↥u, A g • (Fi g - BoundedContinuousFunction.const _ (ri g))
            c := w
            c_pos := hw
            mean_zero := ?_
            le_integral := ?_ }⟩
  · have h := integral_combo (volume : Measure (AddCircle (1 : ℝ))) A Fi ri
      (φ := id) continuous_id
    simpa [hri] using h
  · intro μ hμ
    have h := integral_combo (μ : Measure Shift) A Fi ri P.continuous_fMap
    rw [h]
    have hsep := hfV (Ψ μ) ⟨μ, hμ, rfl⟩
    rw [hfeq (Ψ μ)] at hsep
    refine le_trans hsep.le (le_of_eq (Finset.sum_congr rfl fun g _ => ?_))
    rw [hA, hΨ]
    ring

/-- **M3 Theorem 9.**  The hypothesis of M1 Theorem 7 — no shift-invariant measure of the full
`2`-shift has `F_*μ = Leb` — holds *if and only if* it is witnessed by a finite certificate.
So the certificate scheme is complete: no route can prove 10.61 at an `α` that this one
cannot. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem nonempty_certificate_iff :
    Nonempty (Certificate P) ↔ ∀ μ ∈ invMeasures, pmap P.measurable_fMap μ ≠ haarT :=
  ⟨fun ⟨cert⟩ _ hμ => cert.no_invariant hμ, P.exists_certificate⟩

/-- **M3 Theorem 9, in the note's form.**  When no `σ`-invariant measure pushes forward to
Lebesgue measure, the certificate can be taken to be a real trigonometric polynomial
`G = Re ∑_{h ∈ H} a_h e(h ·)` carried by a finite set `H` of *non-zero* frequencies: the
certificate is finite data.  The passage from the continuous certificate of
`exists_certificate` is a Fejér approximation (`span_fourier_closure_eq_top`) followed by
removal of the constant term, each of which costs at most a third of the certified gap. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_trigCertificate
    (hno : ∀ μ ∈ invMeasures, pmap P.measurable_fMap μ ≠ haarT) :
    ∃ (H : Finset ℤ) (a : ℤ → ℂ) (c : ℝ), (0 : ℤ) ∉ H ∧ 0 < c ∧
      ∫ z, trigPoly H a z ∂(volume : Measure (AddCircle (1 : ℝ))) = 0 ∧
      ∀ μ ∈ invMeasures, c ≤ ∫ ω, trigPoly H a (P.fMap ω) ∂(μ : Measure Shift) := by
  classical
  obtain ⟨cert⟩ := P.exists_certificate hno
  have hc3 : 0 < cert.c / 3 := by linarith [cert.c_pos]
  -- complexify the certificate and approximate it by a character sum
  set Gc : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun z => (cert.G z : ℂ), Complex.continuous_ofReal.comp cert.G.continuous⟩ with hGcdef
  have hmem : Gc ∈ closure (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top, Submodule.top_coe]
    exact Set.mem_univ _
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hmem (cert.c / 3) hc3
  obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (SetLike.mem_coe.mp hp)
  have hpz : ∀ z, p z = ∑ h ∈ cf.support, cf h * fourier h z := by
    intro z
    rw [← hcf]
    simp [Finsupp.sum]
  -- splitting off the constant term of the approximant
  have hsplit : ∀ z, trigPoly cf.support (⇑cf) z
      = trigPoly (cf.support.erase 0) (⇑cf) z + (cf 0).re := by
    intro z
    rw [trigPoly_apply, trigPoly_apply, ← Complex.add_re]
    congr 1
    by_cases h0 : (0 : ℤ) ∈ cf.support
    · rw [← Finset.sum_erase_add _ _ h0]
      simp
    · rw [Finset.erase_eq_of_notMem h0, Finsupp.notMem_support_iff.mp h0]
      simp
  have hmean0 : ∫ z, trigPoly (cf.support.erase 0) (⇑cf) z
      ∂(volume : Measure (AddCircle (1 : ℝ))) = 0 :=
    integral_trigPoly_eq_zero (Finset.notMem_erase 0 _) _
  -- the approximant is uniformly within `c/3` of the certificate
  have hsup : ∀ z, |trigPoly cf.support (⇑cf) z - cert.G z| ≤ cert.c / 3 := by
    intro z
    have h1 : trigPoly cf.support (⇑cf) z - cert.G z = (p z - Gc z).re := by
      rw [trigPoly_apply, ← hpz z, Complex.sub_re, hGcdef]
      simp
    rw [h1]
    calc |(p z - Gc z).re| ≤ ‖p z - Gc z‖ := Complex.abs_re_le_norm _
      _ = ‖(p - Gc) z‖ := by simp
      _ ≤ ‖p - Gc‖ := ContinuousMap.norm_coe_le_norm _ _
      _ = dist Gc p := by rw [dist_eq_norm, norm_sub_rev]
      _ ≤ cert.c / 3 := hdist.le
  -- hence its constant term is small
  have hrb : |(cf 0).re| ≤ cert.c / 3 := by
    have heq : ∫ z, (trigPoly cf.support (⇑cf) z - cert.G z)
        ∂(volume : Measure (AddCircle (1 : ℝ))) = (cf 0).re := by
      rw [integral_sub ((trigPoly cf.support (⇑cf)).integrable _) (cert.G.integrable _),
        cert.mean_zero, sub_zero]
      have h2 : ∫ z, trigPoly cf.support (⇑cf) z ∂(volume : Measure (AddCircle (1 : ℝ)))
          = ∫ z, (trigPoly (cf.support.erase 0) (⇑cf) z + (cf 0).re)
              ∂(volume : Measure (AddCircle (1 : ℝ))) :=
        integral_congr_ae (Filter.Eventually.of_forall hsplit)
      rw [h2, integral_add ((trigPoly (cf.support.erase 0) (⇑cf)).integrable _)
        (integrable_const _), hmean0]
      simp
    rw [← heq]
    have hle := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (AddCircle (1 : ℝ))))
      (f := fun z => trigPoly cf.support (⇑cf) z - cert.G z) (C := cert.c / 3)
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hsup z)
    simpa [Real.norm_eq_abs] using hle
  -- the mean-zero trigonometric polynomial is a certificate with constant `c/3`
  refine ⟨cf.support.erase 0, ⇑cf, cert.c / 3, Finset.notMem_erase 0 _, hc3, hmean0, ?_⟩
  intro μ hμ
  have hb := cert.le_integral μ hμ
  have hint0 : Integrable (fun ω => trigPoly (cf.support.erase 0) (⇑cf) (P.fMap ω))
      (μ : Measure Shift) :=
    ((trigPoly (cf.support.erase 0) (⇑cf)).compContinuous
      ⟨P.fMap, P.continuous_fMap⟩).integrable _
  have hintS : Integrable (fun ω => trigPoly cf.support (⇑cf) (P.fMap ω))
      (μ : Measure Shift) :=
    ((trigPoly cf.support (⇑cf)).compContinuous ⟨P.fMap, P.continuous_fMap⟩).integrable _
  have hintG : Integrable (fun ω => cert.G (P.fMap ω)) (μ : Measure Shift) :=
    (cert.G.compContinuous ⟨P.fMap, P.continuous_fMap⟩).integrable _
  have hd : ∫ ω, trigPoly (cf.support.erase 0) (⇑cf) (P.fMap ω) ∂(μ : Measure Shift)
      = (∫ ω, trigPoly cf.support (⇑cf) (P.fMap ω) ∂(μ : Measure Shift)) - (cf 0).re := by
    have h2 : ∫ ω, trigPoly cf.support (⇑cf) (P.fMap ω) ∂(μ : Measure Shift)
        = ∫ ω, (trigPoly (cf.support.erase 0) (⇑cf) (P.fMap ω) + (cf 0).re)
            ∂(μ : Measure Shift) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => hsplit _)
    rw [h2, integral_add hint0 (integrable_const _)]
    simp
  have hclose : |(∫ ω, trigPoly cf.support (⇑cf) (P.fMap ω) ∂(μ : Measure Shift))
      - ∫ ω, cert.G (P.fMap ω) ∂(μ : Measure Shift)| ≤ cert.c / 3 := by
    rw [← integral_sub hintS hintG]
    have hle := norm_integral_le_of_norm_le_const (μ := (μ : Measure Shift))
      (f := fun ω => trigPoly cf.support (⇑cf) (P.fMap ω) - cert.G (P.fMap ω))
      (C := cert.c / 3)
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hsup (P.fMap ω))
    simpa [Real.norm_eq_abs] using hle
  rw [hd]
  have h1 := abs_le.mp hclose
  have h2 := abs_le.mp hrb
  linarith [h1.1, h1.2, h2.1, h2.2, hb]

/-- **A trigonometric certificate proves 10.61 at `α`.**  The exported form of the easy
direction: a real trigonometric polynomial of zero mean whose average along `F` is uniformly
positive over the shift-invariant measures rules out uniform distribution of `(ξ αⁿ)` for
every `ξ ∈ C(α)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_trigPoly {H : Finset ℤ} {a : ℤ → ℂ} {c : ℝ} (hc : 0 < c)
    (hmean : ∫ z, trigPoly H a z ∂(volume : Measure (AddCircle (1 : ℝ))) = 0)
    (hlb : ∀ μ ∈ invMeasures, c ≤ ∫ ω, trigPoly H a (P.fMap ω) ∂(μ : Measure Shift))
    {ξ : ℝ} (hξ : ξ ∈ cantorSet P.α) :
    ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  Certificate.not_equidistributed ⟨trigPoly H a, c, hc, hmean, hlb⟩ hξ

/-- **M3 Theorem 9, trigonometric form.**  There is a mean-zero real trigonometric polynomial
`G` with `∫ G ∘ F dμ ≥ c > 0` for every shift-invariant `μ` *if and only if* no shift-invariant
`μ` has `F_*μ = Leb`.  Together with M1 Theorem 7 this is the note's completeness statement:
whenever the master target holds at `α`, a finite certificate witnesses it. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_trigCertificate_iff :
    (∃ (H : Finset ℤ) (a : ℤ → ℂ) (c : ℝ), (0 : ℤ) ∉ H ∧ 0 < c ∧
        ∫ z, trigPoly H a z ∂(volume : Measure (AddCircle (1 : ℝ))) = 0 ∧
        ∀ μ ∈ invMeasures, c ≤ ∫ ω, trigPoly H a (P.fMap ω) ∂(μ : Measure Shift))
      ↔ ∀ μ ∈ invMeasures, pmap P.measurable_fMap μ ≠ haarT := by
  refine ⟨fun ⟨H, a, c, _, hc, hmean, hlb⟩ μ hμ => ?_, P.exists_trigCertificate⟩
  exact Certificate.no_invariant ⟨trigPoly H a, c, hc, hmean, hlb⟩ hμ

end QuadSetup

end BB61
