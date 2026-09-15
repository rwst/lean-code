/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.PressureCriterion
import ForMathlib.Dynamics.EntropySemicontinuity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The exact price of a certificate: Theorem B(iii) of `paper.tex`

Formal companion of `paper.tex` §3.3 (Theorem 3.4, "the price of a certificate") and of
`note-1061-M3.html`.

For a finite set `H` of frequencies put

`K_H = {μ ∈ M(σ) : Φ_h(μ) = 0 for h ∈ H}`,  `Φ_h(μ) = ∫ e(h F) dμ`,
`E_H(α) = sup {h(μ) : μ ∈ K_H}`  (`sup ∅ = -∞`),
`ψ_a = Re ∑_{h ∈ H} a_h e(hF)`  for `a ∈ ℂ^H`.

Theorem 3.4 is the exact duality

`inf_{a ∈ ℂ^H} P(ψ_a) = E_H(α)`:

*every number a pressure minimisation reports is an upper approximation to the largest entropy an
invariant measure can have while being Fourier-flat to degree `H`.*

## What is proved here, and what is cited

The paper proves both halves through the variational principle for topological pressure, which is
a classical theorem far outside Mathlib.  This file splits the statement in two, so that the
citation is isolated and the duality itself is unconditional.

* `BB61.measurePressure ψ := sup_{μ ∈ M(σ)} (h_μ(σ,P) + ∫ψ dμ)` — the *measure* side of the
  variational principle, which needs no citation to define.
* `BB61.iInf_measurePressure_eq_priceEntropy` — **Theorem 3.4 with `measurePressure` in place of
  the topological pressure**, proved outright:
  `⨅_a measurePressure ψ_a = E_H(α)`.
  The paper proves this half by Sion's minimax theorem, which Mathlib does not have; the proof
  here is the underlying Lagrange duality done by hand, separating the point `(0, r)` from the
  hypograph `{(Φ(μ), t) : μ ∈ M(σ), t ≤ h(μ)}` by geometric Hahn–Banach in `ℝ^{2|H|} × ℝ`.  Its
  two structural inputs are the new `ForMathlib/Dynamics/EntropySemicontinuity.lean`: the entropy
  rate along the (clopen) coordinate partition is **concave** and **upper semicontinuous** in the
  measure, which is exactly what makes that hypograph convex and closed.
* `BB61.priceEntropy_le_iInf_partitionPressure` — the easy half of the paper's own statement,
  `E_H(α) ≤ ⨅_a P(ψ_a)`, also unconditional: it is the Jensen half of the variational principle
  (`ForMathlib/Dynamics/TopologicalPressure.lean`), which is proved.
* `BB61.exists_priceEntropy_eq` — `E_H(α)` is **attained** whenever `K_H ≠ ∅`, which is the
  remark the paper makes when it introduces `E_H`: `K_H` is compact and the entropy is upper
  semicontinuous on it.
* The reverse inequality for the *topological* pressure is the hard half of the variational
  principle; it is supplied as the one cited axiom
  `Walters.partitionPressure_le_measurePressure` of
  `CITED/WaltersVariationalPrinciple.lean`, and the paper's statement in full is
  `BB61.iInf_partitionPressure_eq_priceEntropy` in `BB61/PriceCompleteness.lean`.

## Conventions

Frequencies are carried by an arbitrary `Hs : Finset ℤ`; the paper's `H` is `Finset.Icc 1 H`.
Nothing here needs `0 ∉ Hs` (with `0 ∈ Hs` both sides are `-∞`, since `Φ_0 ≡ 1`).

As everywhere in this root the entropy is `entropyRate shiftZ μ coordPartition`, the entropy
relative to the time-zero coordinate partition, not `kolmogorovSinai shiftZ μ`; the two agree by
the Kolmogorov–Sinai generator theorem, which is not formalised (see `BB61/PressureCriterion.lean`).
-/

namespace BB61

open MeasureTheory Dynamics BoundedContinuousFunction
open scoped ENNReal

/-! ## The entropy of a measure on the shift, as a function of the measure -/

/-- `h_μ(σ, P)` for the time-zero coordinate partition `P`, as a function on the space of
probability measures of the shift. -/
noncomputable def shiftEntropy (μ : ProbabilityMeasure Shift) : ℝ :=
  entropyRate shiftZ (μ : Measure Shift) coordPartition

/-- The two cells of the coordinate partition are **clopen** — that is the whole reason the entropy
is semicontinuous in the measure. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isClopen_coordPartition_fiber (i : Bool) : IsClopen (coordPartition ⁻¹' {i}) :=
  (isClopen_discrete {i}).preimage (continuous_apply (0 : ℤ))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shiftEntropy_nonneg (μ : ProbabilityMeasure Shift) : 0 ≤ shiftEntropy μ :=
  entropyRate_nonneg _ _

/-- `h_μ(σ, P) ≤ log 2`: the coordinate partition has two cells. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shiftEntropy_le_log_two (μ : ProbabilityMeasure Shift) : shiftEntropy μ ≤ Real.log 2 := by
  have h := entropyRate_le_log_card (μ := (μ : Measure Shift)) shiftZ
    measurableSet_coordPartition_fiber
  simp only [Fintype.card_bool, Nat.cast_ofNat] at h
  exact h

/-- **The entropy is upper semicontinuous in the measure.** -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem upperSemicontinuous_shiftEntropy : UpperSemicontinuous shiftEntropy :=
  upperSemicontinuous_entropyRate continuous_shiftZ isClopen_coordPartition_fiber

/-- **The entropy is concave in the measure.** -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shiftEntropy_mix_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ₀ μ₁ : ProbabilityMeasure Shift) :
    a * shiftEntropy μ₀ + b * shiftEntropy μ₁ ≤ shiftEntropy (mix ha hb hab μ₀ μ₁) := by
  have h := entropyRate_smul_add_smul_le (μ₀ := (μ₀ : Measure Shift))
    (μ₁ := (μ₁ : Measure Shift)) ha hb hab shiftZ coordPartition
  simpa only [shiftEntropy, toMeasure_mix, mixMeasure] using h

/-- The hypograph of the entropy is closed: the semicontinuity, in the form the separation
argument uses. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isClosed_le_shiftEntropy :
    IsClosed {p : ProbabilityMeasure Shift × ℝ | p.2 ≤ shiftEntropy p.1} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨μ, t⟩ hp
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hp
  obtain ⟨s, hs1, hs2⟩ := exists_between hp
  rw [nhds_prod_eq]
  refine Filter.mem_of_superset
    (Filter.prod_mem_prod (upperSemicontinuous_shiftEntropy μ s hs1)
      (isOpen_Ioi.mem_nhds hs2)) ?_
  rintro ⟨ν, y⟩ ⟨hν, hy⟩
  exact not_le.2 (lt_trans hν (Set.mem_Ioi.1 hy))

/-- `M(σ)` is not empty: the point mass at the fixed point `…000…` is invariant. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem invMeasures_nonempty : invMeasures.Nonempty := by
  obtain ⟨μ, hμ⟩ : ∃ μ : ProbabilityMeasure Shift,
      (μ : Measure Shift) = Measure.dirac (fun _ : ℤ => false) :=
    ⟨⟨Measure.dirac (fun _ => false), inferInstance⟩, rfl⟩
  refine ⟨μ, ?_⟩
  show pmap continuous_shiftZ.measurable μ = μ
  refine ProbabilityMeasure.toMeasure_injective ?_
  rw [toMeasure_pmap, hμ, Measure.map_dirac' continuous_shiftZ.measurable]
  rfl

/-! ## The moments `Φ_h` and the moment map -/

/-- The real and imaginary parts of the character `e(h F)` on the shift, as bounded continuous
functions: `fourierObs P h true = Re e(hF)` and `fourierObs P h false = Im e(hF)`. -/
noncomputable def fourierObs (P : QuadSetup) (h : ℤ) : Bool → (Shift →ᵇ ℝ)
  | true => mkOfCompact ⟨fun ω => (fourier h (P.fMap ω)).re,
      Complex.continuous_re.comp ((map_continuous (fourier h)).comp P.continuous_fMap)⟩
  | false => mkOfCompact ⟨fun ω => (fourier h (P.fMap ω)).im,
      Complex.continuous_im.comp ((map_continuous (fourier h)).comp P.continuous_fMap)⟩

/-- `Φ_h(μ) = ∫ e(h F(ω)) dμ(ω)`: the `h`-th Fourier coefficient of the push-forward `F_*μ`. -/
noncomputable def fourierMoment (P : QuadSetup) (h : ℤ) (μ : ProbabilityMeasure Shift) : ℂ :=
  ∫ ω, fourier h (P.fMap ω) ∂(μ : Measure Shift)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integrable_fourier_comp (P : QuadSetup) (h : ℤ) (μ : ProbabilityMeasure Shift) :
    Integrable (fun ω => fourier h (P.fMap ω)) (μ : Measure Shift) :=
  ((map_continuous (fourier h)).comp P.continuous_fMap).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourierObs (P : QuadSetup) (h : ℤ) (b : Bool) (μ : ProbabilityMeasure Shift) :
    ∫ ω, fourierObs P h b ω ∂(μ : Measure Shift)
      = if b then (fourierMoment P h μ).re else (fourierMoment P h μ).im := by
  have hint := integrable_fourier_comp P h μ
  cases b with
  | false =>
      show ∫ ω, (fourier h (P.fMap ω)).im ∂(μ : Measure Shift) = _
      simpa [fourierMoment] using (integral_im hint)
  | true =>
      show ∫ ω, (fourier h (P.fMap ω)).re ∂(μ : Measure Shift) = _
      simpa [fourierMoment] using (integral_re hint)

/-- The **moment vector** of `μ`: the real and imaginary parts of `Φ_h(μ)`, `h ∈ Hs`, packed into a
finite-dimensional real vector.  This is the map that the separation argument works with. -/
noncomputable def momVec (P : QuadSetup) (Hs : Finset ℤ) (μ : ProbabilityMeasure Shift) :
    (↥Hs × Bool) → ℝ :=
  fun p => ∫ ω, fourierObs P (p.1 : ℤ) p.2 ω ∂(μ : Measure Shift)

/-- The moment map is weak-\* continuous: each coordinate is the integral of a bounded continuous
function. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_momVec (P : QuadSetup) (Hs : Finset ℤ) : Continuous (momVec P Hs) :=
  continuous_pi fun _ => ProbabilityMeasure.continuous_integral_boundedContinuousFunction _

/-- The moment map is affine. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem momVec_mix (P : QuadSetup) (Hs : Finset ℤ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (μ₀ μ₁ : ProbabilityMeasure Shift) :
    momVec P Hs (mix ha hb hab μ₀ μ₁) = a • momVec P Hs μ₀ + b • momVec P Hs μ₁ := by
  funext p
  simp only [momVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact integral_mix ha hb hab μ₀ μ₁ _

/-- `μ` is Fourier-flat on `Hs` exactly when its moment vector vanishes. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem momVec_eq_zero_iff (P : QuadSetup) (Hs : Finset ℤ) (μ : ProbabilityMeasure Shift) :
    momVec P Hs μ = 0 ↔ ∀ h ∈ Hs, fourierMoment P h μ = 0 := by
  constructor
  · intro hm h hh
    have h1 := congrFun hm (⟨h, hh⟩, true)
    have h2 := congrFun hm (⟨h, hh⟩, false)
    rw [momVec, integral_fourierObs] at h1 h2
    simp only [Pi.zero_apply, ite_true, Bool.false_eq_true, ite_false] at h1 h2
    exact Complex.ext h1 h2
  · intro hz
    funext p
    obtain ⟨⟨h, hh⟩, b⟩ := p
    rw [momVec, integral_fourierObs]
    cases b <;> simp [hz h hh]

/-! ## The potential `ψ_a`, and the pairing with the moments -/

/-- The potential `ψ_a = Re ∑_{h ∈ Hs} a_h e(hF)` on the shift. -/
noncomputable def fourierPotential (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ) : Shift → ℝ :=
  fun ω => trigPoly Hs a (P.fMap ω)

/-- `ψ_a` as a bounded continuous function on the (compact) shift space: it is `trigPoly` composed
with the continuous factor map `F`. -/
noncomputable def fourierPotentialBC (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ) : Shift →ᵇ ℝ :=
  (trigPoly Hs a).compContinuous ⟨P.fMap, P.continuous_fMap⟩

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_fourierPotentialBC (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ) :
    ⇑(fourierPotentialBC P Hs a) = fourierPotential P Hs a := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_fourierPotential (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ) :
    Continuous (fourierPotential P Hs a) :=
  (trigPoly Hs a).continuous.comp P.continuous_fMap

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_fourierPotential_le (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ) (ω : Shift) :
    |fourierPotential P Hs a ω| ≤ ‖trigPoly Hs a‖ := by
  have h := (trigPoly Hs a).norm_coe_le_norm (P.fMap ω)
  rwa [Real.norm_eq_abs] at h

/-- The real coefficient vector attached to `a ∈ ℂ^{Hs}`: the pairing `∫ψ_a dμ` is the ordinary dot
product of `momVec` with it. -/
def coefVec (Hs : Finset ℤ) (a : ℤ → ℂ) : (↥Hs × Bool) → ℝ :=
  fun p => if p.2 then (a (p.1 : ℤ)).re else -(a (p.1 : ℤ)).im

/-- The inverse of `coefVec`: every real vector on `↥Hs × Bool` comes from a coefficient vector
`a ∈ ℂ^{Hs}`. -/
noncomputable def coeffOfVec (Hs : Finset ℤ) (A : (↥Hs × Bool) → ℝ) : ℤ → ℂ :=
  fun h => if hh : h ∈ Hs then
    ((A (⟨h, hh⟩, true) : ℂ) - (A (⟨h, hh⟩, false) : ℂ) * Complex.I) else 0

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coefVec_coeffOfVec (Hs : Finset ℤ) (A : (↥Hs × Bool) → ℝ) :
    coefVec Hs (coeffOfVec Hs A) = A := by
  funext p
  obtain ⟨⟨h, hh⟩, b⟩ := p
  cases b <;> simp [coefVec, coeffOfVec, hh]

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem momVec_true (P : QuadSetup) (Hs : Finset ℤ) (μ : ProbabilityMeasure Shift) (h : ↥Hs) :
    momVec P Hs μ (h, true) = (fourierMoment P (h : ℤ) μ).re := by
  simp [momVec, integral_fourierObs]

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem momVec_false (P : QuadSetup) (Hs : Finset ℤ) (μ : ProbabilityMeasure Shift) (h : ↥Hs) :
    momVec P Hs μ (h, false) = (fourierMoment P (h : ℤ) μ).im := by
  simp [momVec, integral_fourierObs]

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coefVec_true (Hs : Finset ℤ) (a : ℤ → ℂ) (h : ↥Hs) :
    coefVec Hs a (h, true) = (a (h : ℤ)).re := by simp [coefVec]

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coefVec_false (Hs : Finset ℤ) (a : ℤ → ℂ) (h : ↥Hs) :
    coefVec Hs a (h, false) = -(a (h : ℤ)).im := by simp [coefVec]

/-- **The pairing.**  `∫ ψ_a dμ = ∑_{h ∈ Hs} Re(a_h Φ_h(μ))`, written as a dot product of the
moment vector with the real coefficient vector of `a`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourierPotential (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ)
    (μ : ProbabilityMeasure Shift) :
    ∫ ω, fourierPotential P Hs a ω ∂(μ : Measure Shift)
      = ∑ p : ↥Hs × Bool, momVec P Hs μ p * coefVec Hs a p := by
  classical
  have hint : ∀ h ∈ Hs, Integrable (fun ω => a h * fourier h (P.fMap ω)) (μ : Measure Shift) :=
    fun h _ => (integrable_fourier_comp P h μ).const_mul _
  have hsum : Integrable (fun ω => ∑ h ∈ Hs, a h * fourier h (P.fMap ω)) (μ : Measure Shift) :=
    integrable_finsetSum _ hint
  have hstep : ∫ ω, fourierPotential P Hs a ω ∂(μ : Measure Shift)
      = (∑ h ∈ Hs, a h * fourierMoment P h μ).re := by
    have hre : ∀ ω : Shift, fourierPotential P Hs a ω
        = RCLike.re (∑ h ∈ Hs, a h * fourier h (P.fMap ω)) := fun _ => rfl
    simp_rw [hre]
    rw [integral_re hsum, MeasureTheory.integral_finsetSum Hs hint, RCLike.re_to_complex]
    simp only [fourierMoment, integral_const_mul]
  rw [hstep, Complex.re_sum, ← Finset.sum_coe_sort Hs (fun h => (a h * fourierMoment P h μ).re),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fintype.sum_bool, momVec_true, momVec_false, coefVec_true, coefVec_false, Complex.mul_re]
  ring

/-! ## `K_H`, `E_H(α)`, and the measure side of the pressure -/

/-- `K_H = {μ ∈ M(σ) : Φ_h(μ) = 0 for h ∈ Hs}`, the invariant measures that are Fourier-flat to
degree `Hs`. -/
def flatSet (P : QuadSetup) (Hs : Finset ℤ) : Set (ProbabilityMeasure Shift) :=
  {μ | μ ∈ invMeasures ∧ ∀ h ∈ Hs, fourierMoment P h μ = 0}

/-- `E_H(α) = sup {h(μ) : μ ∈ K_H}`, with `sup ∅ = -∞`.  Taking values in `EReal` is what makes
`K_H = ∅` — the case in which a certificate of degree `H` exists — a value rather than an
exception. -/
noncomputable def priceEntropy (P : QuadSetup) (Hs : Finset ℤ) : EReal :=
  sSup ((fun μ => (shiftEntropy μ : EReal)) '' flatSet P Hs)

/-- `sup_{μ ∈ M(σ)} (h_μ(σ,P) + ∫ψ dμ)`: the measure side of the variational principle.  The
variational principle says it equals the topological pressure of `ψ`; the inequality `≤`, which is
all this file proves unconditionally, is Jensen's. -/
noncomputable def measurePressure (ψ : Shift → ℝ) : EReal :=
  sSup ((fun μ : ProbabilityMeasure Shift =>
    ((shiftEntropy μ + ∫ ω, ψ ω ∂(μ : Measure Shift) : ℝ) : EReal)) '' invMeasures)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem le_measurePressure {ψ : Shift → ℝ} {μ : ProbabilityMeasure Shift} (hμ : μ ∈ invMeasures) :
    ((shiftEntropy μ + ∫ ω, ψ ω ∂(μ : Measure Shift) : ℝ) : EReal) ≤ measurePressure ψ :=
  le_sSup ⟨μ, hμ, rfl⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurePressure_le {ψ : Shift → ℝ} {c : ℝ}
    (h : ∀ μ ∈ invMeasures, shiftEntropy μ + ∫ ω, ψ ω ∂(μ : Measure Shift) ≤ c) :
    measurePressure ψ ≤ (c : EReal) := by
  refine sSup_le ?_
  rintro _ ⟨μ, hμ, rfl⟩
  exact EReal.coe_le_coe (h μ hμ)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem le_priceEntropy (P : QuadSetup) (Hs : Finset ℤ) {μ : ProbabilityMeasure Shift}
    (hμ : μ ∈ flatSet P Hs) : ((shiftEntropy μ : ℝ) : EReal) ≤ priceEntropy P Hs :=
  le_sSup ⟨μ, hμ, rfl⟩

/-- Below a real bound on `E_H(α)`, every flat measure has entropy below that bound. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shiftEntropy_lt_of_priceEntropy_lt (P : QuadSetup) (Hs : Finset ℤ) {r : ℝ}
    (h : priceEntropy P Hs < (r : EReal)) {μ : ProbabilityMeasure Shift}
    (hμ : μ ∈ flatSet P Hs) : shiftEntropy μ < r := by
  exact_mod_cast lt_of_le_of_lt (le_priceEntropy P Hs hμ) h

/-- `K_H` is the invariant measures whose moment vector vanishes. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem flatSet_eq_inter_preimage (P : QuadSetup) (Hs : Finset ℤ) :
    flatSet P Hs = invMeasures ∩ (momVec P Hs) ⁻¹' {0} := by
  ext μ
  simp only [flatSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff]
  exact and_congr_right fun _ => (momVec_eq_zero_iff P Hs μ).symm

/-- `K_H` is compact: it is closed in `M(σ)`, which is compact. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isCompact_flatSet (P : QuadSetup) (Hs : Finset ℤ) : IsCompact (flatSet P Hs) := by
  rw [flatSet_eq_inter_preimage]
  exact isCompact_invMeasures.inter_right
    (isClosed_singleton.preimage (continuous_momVec P Hs))

/-- **`E_H(α)` is attained whenever `K_H ≠ ∅`** (`paper.tex` §3.3): entropy is upper
semicontinuous on the compact set `K_H`. -/
@[category research solved, AMS 37 28 11, ref "Bug12" "Wal82", group "bugeaud_10_61"]
theorem exists_priceEntropy_eq (P : QuadSetup) (Hs : Finset ℤ)
    (hne : (flatSet P Hs).Nonempty) :
    ∃ μ ∈ flatSet P Hs, priceEntropy P Hs = ((shiftEntropy μ : ℝ) : EReal) := by
  obtain ⟨μ, hμ, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne (isCompact_flatSet P Hs)
    (upperSemicontinuous_shiftEntropy.upperSemicontinuousOn _)
  refine ⟨μ, hμ, le_antisymm (sSup_le ?_) (le_priceEntropy P Hs hμ)⟩
  rintro _ ⟨ν, hν, rfl⟩
  exact EReal.coe_le_coe (hmax hν)

/-! ## The easy half: `E_H(α) ≤ inf_a P(ψ_a)` -/

/-- A flat measure annihilates every potential of its degree: `∫ ψ_a dμ = 0` for `μ ∈ K_H`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourierPotential_eq_zero (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ)
    {μ : ProbabilityMeasure Shift} (hμ : μ ∈ flatSet P Hs) :
    ∫ ω, fourierPotential P Hs a ω ∂(μ : Measure Shift) = 0 := by
  rw [integral_fourierPotential]
  have hm : momVec P Hs μ = 0 := (momVec_eq_zero_iff P Hs μ).2 hμ.2
  simp [hm]

/-- **The easy half of Theorem 3.4**, for the measure side: `E_H(α) ≤ ⨅_a measurePressure ψ_a`.
A flat measure contributes its full entropy to every `ψ_a`. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem priceEntropy_le_iInf_measurePressure (P : QuadSetup) (Hs : Finset ℤ) :
    priceEntropy P Hs ≤ ⨅ a : ℤ → ℂ, measurePressure (fourierPotential P Hs a) := by
  refine sSup_le ?_
  rintro _ ⟨μ, hμ, rfl⟩
  refine le_iInf fun a => ?_
  have h := le_measurePressure (ψ := fourierPotential P Hs a) hμ.1
  rwa [integral_fourierPotential_eq_zero P Hs a hμ, add_zero] at h

/-! ## The hard half: separating `(0, r)` from the hypograph -/

section Separation

variable (P : QuadSetup) (Hs : Finset ℤ)

/-- The hypograph of the entropy over the moment map:
`C = {(Φ(μ), t) : μ ∈ M(σ), t ≤ h(μ)} ⊆ ℝ^{2|H|} × ℝ`. -/
def entropyHypograph : Set (((↥Hs × Bool) → ℝ) × ℝ) :=
  {z | ∃ μ ∈ invMeasures, z.1 = momVec P Hs μ ∧ z.2 ≤ shiftEntropy μ}

/-- The hypograph is convex: the moment map is affine and the entropy is concave. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem convex_entropyHypograph : Convex ℝ (entropyHypograph P Hs) := by
  rintro ⟨v₀, t₀⟩ ⟨μ₀, hμ₀, hv₀, ht₀⟩ ⟨v₁, t₁⟩ ⟨μ₁, hμ₁, hv₁, ht₁⟩ a b ha hb hab
  have h0 : v₀ = momVec P Hs μ₀ := hv₀
  have h1 : v₁ = momVec P Hs μ₁ := hv₁
  have k0 : t₀ ≤ shiftEntropy μ₀ := ht₀
  have k1 : t₁ ≤ shiftEntropy μ₁ := ht₁
  refine ⟨mix ha hb hab μ₀ μ₁, mix_mem_invMeasures ha hb hab hμ₀ hμ₁, ?_, ?_⟩
  · show a • v₀ + b • v₁ = momVec P Hs (mix ha hb hab μ₀ μ₁)
    rw [momVec_mix P Hs ha hb hab, h0, h1]
  · refine le_trans ?_ (shiftEntropy_mix_ge ha hb hab μ₀ μ₁)
    show a • t₀ + b • t₁ ≤ a * shiftEntropy μ₀ + b * shiftEntropy μ₁
    simp only [smul_eq_mul]
    gcongr

/-- The hypograph is closed.  It is an increasing union of the compact slabs
`{(Φ(μ), t) : μ ∈ M(σ), -n ≤ t ≤ h(μ)}`, and every point of the closure lies in the interior of
one of the slabs' defining half-spaces. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isClosed_entropyHypograph : IsClosed (entropyHypograph P Hs) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_gt (-z.2)
  have hnz : -(n : ℝ) < z.2 := by linarith
  -- the `n`-th slab, as the image of a compact set
  set A : Set (ProbabilityMeasure Shift × ℝ) :=
    (invMeasures ×ˢ Set.Icc (-(n : ℝ)) (Real.log 2)) ∩ {p | p.2 ≤ shiftEntropy p.1} with hAdef
  have hAcompact : IsCompact A :=
    (isCompact_invMeasures.prod isCompact_Icc).inter_right isClosed_le_shiftEntropy
  set S : Set (((↥Hs × Bool) → ℝ) × ℝ) :=
    (fun p : ProbabilityMeasure Shift × ℝ => (momVec P Hs p.1, p.2)) '' A with hSdef
  have hScompact : IsCompact S :=
    hAcompact.image (((continuous_momVec P Hs).comp continuous_fst).prodMk continuous_snd)
  have hSC : S ⊆ entropyHypograph P Hs := by
    rintro _ ⟨⟨μ, t⟩, ⟨⟨hμ, -⟩, ht⟩, rfl⟩
    exact ⟨μ, hμ, rfl, ht⟩
  have hsub : (Set.univ ×ˢ Set.Ioi (-(n : ℝ))) ∩ entropyHypograph P Hs ⊆ S := by
    rintro ⟨v, t⟩ ⟨⟨-, ht⟩, μ, hμ, rfl, hle⟩
    exact ⟨(μ, t), ⟨⟨hμ, le_of_lt ht, le_trans hle (shiftEntropy_le_log_two μ)⟩, hle⟩, rfl⟩
  have hopen : IsOpen ((Set.univ : Set ((↥Hs × Bool) → ℝ)) ×ˢ Set.Ioi (-(n : ℝ))) :=
    isOpen_univ.prod isOpen_Ioi
  have hzmem : z ∈ (Set.univ : Set ((↥Hs × Bool) → ℝ)) ×ˢ Set.Ioi (-(n : ℝ)) :=
    ⟨trivial, hnz⟩
  have := hopen.inter_closure ⟨hzmem, hz⟩
  exact hSC (hScompact.isClosed.closure_subset (closure_mono hsub this))

end Separation

/-- **The hard half of Theorem 3.4**, for the measure side: any real number above `E_H(α)` is
already the value of some `measurePressure ψ_a`.

This is the paper's Sion-minimax step, done as Lagrange duality: the point `(0, r)` misses the
convex closed hypograph `C` of the entropy over the moment map, so geometric Hahn–Banach separates
them by an affine functional `(v, t) ↦ ⟨v, A⟩ + t c`; the vertical direction of `C` is unbounded
below, forcing `c ≤ 0`, and dividing by `c` (or, when `c = 0`, scaling the multiplier) turns the
separating functional into the coefficient vector of a potential of pressure below `r`. -/
@[category research solved, AMS 37 28 11, ref "Bug12" "Sio58", group "bugeaud_10_61"]
theorem exists_measurePressure_lt (P : QuadSetup) (Hs : Finset ℤ) {r : ℝ}
    (hr : priceEntropy P Hs < (r : EReal)) :
    ∃ a : ℤ → ℂ, measurePressure (fourierPotential P Hs a) < (r : EReal) := by
  classical
  -- the point `(0, r)` is not in the hypograph
  have hmem : ((0 : (↥Hs × Bool) → ℝ), r) ∉ entropyHypograph P Hs := by
    rintro ⟨μ, hμ, hv, ht⟩
    have hflat : μ ∈ flatSet P Hs :=
      ⟨hμ, (momVec_eq_zero_iff P Hs μ).1 hv.symm⟩
    exact absurd (shiftEntropy_lt_of_priceEntropy_lt P Hs hr hflat) (not_lt.2 ht)
  obtain ⟨f, u, hfx, hfC⟩ :=
    geometric_hahn_banach_point_closed (convex_entropyHypograph P Hs) (isClosed_entropyHypograph P Hs) hmem
  -- the coordinates of the separating functional
  obtain ⟨A, c, hsplit⟩ : ∃ (A : (↥Hs × Bool) → ℝ) (c : ℝ),
      ∀ (v : (↥Hs × Bool) → ℝ) (t : ℝ), f (v, t) = (∑ i, v i * A i) + t * c := by
    refine ⟨fun i => f ((fun j => if i = j then 1 else 0), 0), f (0, 1), fun v t => ?_⟩
    have h2 : f (v, 0) = ∑ i, v i * f ((fun j => if i = j then 1 else 0), 0) := by
      have h := LinearMap.pi_apply_eq_sum_univ
        ((f.comp (ContinuousLinearMap.inl ℝ ((↥Hs × Bool) → ℝ) ℝ)) :
          ((↥Hs × Bool) → ℝ) →ₗ[ℝ] ℝ) v
      simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, smul_eq_mul] using h
    have h1 : ((v, t) : ((↥Hs × Bool) → ℝ) × ℝ)
        = (v, 0) + t • ((0 : (↥Hs × Bool) → ℝ), (1 : ℝ)) := by simp
    rw [h1, map_add, map_smul, smul_eq_mul, h2]
  have hfr : r * c < u := by
    have := hfx
    rw [hsplit] at this
    simpa using this
  have hfhypo : ∀ μ ∈ invMeasures,
      u < (∑ i, momVec P Hs μ i * A i) + shiftEntropy μ * c := by
    intro μ hμ
    have := hfC (momVec P Hs μ, shiftEntropy μ) ⟨μ, hμ, rfl, le_rfl⟩
    rwa [hsplit] at this
  obtain ⟨μ₀, hμ₀⟩ := invMeasures_nonempty
  -- the vertical ray forces `c ≤ 0`
  have hcle : c ≤ 0 := by
    by_contra hcon
    push Not at hcon
    set Sv : ℝ := ∑ i, momVec P Hs μ₀ i * A i with hSv
    set t : ℝ := min (shiftEntropy μ₀) ((u - Sv - 1) / c) with htdef
    have hmemC : ((momVec P Hs μ₀, t) : ((↥Hs × Bool) → ℝ) × ℝ) ∈ entropyHypograph P Hs :=
      ⟨μ₀, hμ₀, rfl, min_le_left _ _⟩
    have hgt := hfC _ hmemC
    rw [hsplit] at hgt
    have h2 : t * c ≤ u - Sv - 1 := by
      have h3 := mul_le_mul_of_nonneg_right (min_le_right (shiftEntropy μ₀)
        ((u - Sv - 1) / c)) hcon.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hcon)] at h3
    linarith
  rcases lt_or_eq_of_le hcle with hcneg | hczero
  · -- `c < 0`: divide the functional by `c`
    refine ⟨coeffOfVec Hs (fun i => A i / c), ?_⟩
    refine lt_of_le_of_lt (measurePressure_le (c := u / c) ?_) ?_
    · intro μ hμ
      rw [integral_fourierPotential, coefVec_coeffOfVec]
      have hkey := hfhypo μ hμ
      have hcne : c ≠ 0 := ne_of_lt hcneg
      rw [le_div_iff_of_neg hcneg, add_mul]
      have hexp : (∑ p : ↥Hs × Bool, momVec P Hs μ p * (A p / c)) * c
          = ∑ p : ↥Hs × Bool, momVec P Hs μ p * A p := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        field_simp
      rw [hexp]
      linarith
    · exact_mod_cast (div_lt_iff_of_neg hcneg).2 (by linarith)
  · -- `c = 0`: the moment map misses `0`, and scaling the multiplier sends the pressure to `-∞`
    have hc0 : c = 0 := hczero
    have hu : 0 < u := by
      rw [hc0] at hfr; simpa using hfr
    have hSpos : ∀ μ ∈ invMeasures, u < ∑ i, momVec P Hs μ i * A i := by
      intro μ hμ
      have := hfhypo μ hμ
      rwa [hc0, mul_zero, add_zero] at this
    set lam : ℝ := max 0 ((Real.log 2 - r) / u) + 1 with hlam
    have hlampos : 0 < lam := by positivity
    have hlamgt : (Real.log 2 - r) / u < lam := by
      have : (Real.log 2 - r) / u ≤ max 0 ((Real.log 2 - r) / u) := le_max_right _ _
      linarith
    refine ⟨coeffOfVec Hs (fun i => -lam * A i), ?_⟩
    refine lt_of_le_of_lt (measurePressure_le (c := Real.log 2 - lam * u) ?_) ?_
    · intro μ hμ
      rw [integral_fourierPotential, coefVec_coeffOfVec]
      have hexp : (∑ p : ↥Hs × Bool, momVec P Hs μ p * (-lam * A p))
          = -lam * ∑ p : ↥Hs × Bool, momVec P Hs μ p * A p := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by ring
      rw [hexp]
      have h1 := hSpos μ hμ
      have h2 := shiftEntropy_le_log_two μ
      nlinarith
    · have : Real.log 2 - lam * u < r := by
        have := (div_lt_iff₀ hu).1 hlamgt
        linarith
      exact_mod_cast this

/-- **Theorem 3.4 (the price of a certificate), for the measure side of the variational
principle.**  For every finite set of frequencies,

`⨅_{a ∈ ℂ^H} sup_{μ ∈ M(σ)} (h(μ) + ∫ψ_a dμ) = E_H(α)`.

Unconditional: no cited axiom, and in particular no variational principle.  The paper's statement,
with the topological pressure on the left, is `BB61.iInf_partitionPressure_eq_priceEntropy` in
`BB61/PriceCompleteness.lean`. -/
@[category research solved, AMS 37 28 11, ref "Bug12" "Sio58", group "bugeaud_10_61"]
theorem iInf_measurePressure_eq_priceEntropy (P : QuadSetup) (Hs : Finset ℤ) :
    ⨅ a : ℤ → ℂ, measurePressure (fourierPotential P Hs a) = priceEntropy P Hs := by
  refine le_antisymm ?_ (priceEntropy_le_iInf_measurePressure P Hs)
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hr1, hr2⟩ := EReal.exists_between_coe_real hcon
  obtain ⟨a, ha⟩ := exists_measurePressure_lt P Hs hr1
  exact absurd (lt_of_le_of_lt (iInf_le _ a) ha) (not_lt.2 hr2.le)

/-! ## The Jensen bridge to the topological pressure -/

/-- Every element of the measure side is below the pressure over cylinders: this is the Jensen half
of the variational principle, `ForMathlib/Dynamics/TopologicalPressure.lean`. -/
@[category API, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurePressure_le_partitionPressure {ψ : Shift → ℝ} (hcont : Continuous ψ) {C : ℝ}
    (hC : ∀ ω, ψ ω ≤ C) : measurePressure ψ ≤ partitionPressure shiftZ ψ coordPartition := by
  refine sSup_le ?_
  rintro _ ⟨μ, hμ, rfl⟩
  have hinv : Measure.map shiftZ (μ : Measure Shift) = (μ : Measure Shift) := by
    have := hμ
    rw [mem_invMeasures] at this
    calc Measure.map shiftZ (μ : Measure Shift)
        = ((pmap continuous_shiftZ.measurable μ : ProbabilityMeasure Shift) : Measure Shift) :=
          (toMeasure_pmap _ _).symm
      _ = (μ : Measure Shift) := by rw [this]
  have hmp : MeasurePreserving shiftZ (μ : Measure Shift) (μ : Measure Shift) :=
    ⟨continuous_shiftZ.measurable, hinv⟩
  exact entropyRate_add_integral_le_partitionPressure hmp measurableSet_coordPartition_fiber
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hC

/-- **The easy half of Theorem 3.4 as the paper states it**: `E_H(α) ≤ ⨅_a P(ψ_a)`, with `P` the
pressure over cylinders.  Unconditional — the variational principle is used only in its proved
(Jensen) direction. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem priceEntropy_le_iInf_partitionPressure (P : QuadSetup) (Hs : Finset ℤ) :
    priceEntropy P Hs
      ≤ ⨅ a : ℤ → ℂ, partitionPressure shiftZ (fourierPotential P Hs a) coordPartition := by
  refine le_trans (priceEntropy_le_iInf_measurePressure P Hs) (le_iInf fun a => ?_)
  exact le_trans (iInf_le _ a) (measurePressure_le_partitionPressure
    (continuous_fourierPotential P Hs a)
    (fun ω => le_trans (le_abs_self _) (abs_fourierPotential_le P Hs a ω)))

end BB61
