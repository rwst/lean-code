/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Saturation
import BB61.Pressure
import ForMathlib.Dynamics.TopologicalPressure
import ForMathlib.Dynamics.PressureTransfer
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The pressure criterion: Theorem 12 of `note-1061-M3.html`

Formal companion of `note-1061-M3.html` §7 (milestone M3 of `plans/plan-1061.html`).

M3 replaced the Route-D linear programme by a **pressure certificate**: 10.61 holds at a Pisot
unit `α` as soon as some potential `ψ` that every counterexample measure annihilates has
topological pressure strictly below the entropy floor `h_min(α)`.  The argument is one line of the
variational principle,

`h(μ) = h(μ) + ∫ψ dμ ≤ P(ψ) < h_min(α)`,

contradicting the Ledrappier–Young floor `h(μ) ≥ h_min(α)` of M3 Theorem 11.

This file makes that line machine-checked.  The two halves it joins are:

* `BB61/Saturation.lean` — `QuadSetup.equidistributed_iff_exists_invariant_measure`: a point of
  `C(α)` is equidistributed **iff** some `σ`-invariant `μ` has `F_*μ = Leb`.  That is M1
  Corollary 9, and it is a theorem here, not a hypothesis.
* `ForMathlib/Dynamics/TopologicalPressure.lean` —
  `MeasureTheory.entropyRate_le_partitionPressure_of_integral_eq_zero`: the easy (Jensen) half of
  the variational principle, `h_μ(σ, P) + ∫ψ dμ ≤ P(σ, ψ, P)`, relative to a finite partition `P`.
  Here `P` is `coordPartition`, the time-zero coordinate partition of the full `2`-shift.

## What is a hypothesis, and why

Two inputs are supplied to `forall_not_equidistributed_of_partitionPressure_lt` rather than proved:

* **the entropy floor** (M3 Theorem 11).  It rests on the dimension theory of hyperbolic measures
  — exact dimensionality [BPS99] and the Ledrappier–Young formula [LY85] — which is far outside
  Mathlib.  It enters as `hfloor`.
* **the annihilation** `∫ψ dμ = 0` for every counterexample `μ`.  For `ψ = Re ∑_h a_h e(hF)` this
  is M1's `Φ_h(μ) = 0`, which is immediate from `F_*μ = Leb` (`BB61/Certificate.lean` proves the
  corresponding statement for `trigPoly`); it is left as `hann` so that the criterion applies
  verbatim to the *bounded Borel* potentials of M4, which are not continuous.

The floor is stated with `entropyRate σ μ coordPartition`, the entropy of `σ` **relative to the
coordinate partition**, rather than with `kolmogorovSinai σ μ`.  The two agree — `coordPartition`
generates the two-sided shift — but that identification is the Kolmogorov–Sinai generator theorem,
which `ForMathlib/Dynamics/KolmogorovSinai.lean` does not prove.  Since the floor is a cited input
either way, stating it in the relative form costs nothing and keeps the file citation-free.

## How `BB61/Pressure.lean` is joined to it

`BB61/Pressure.lean` certifies, in exact arithmetic at `α = 2 + √3`, that a window transfer
operator has growth rate below `½ log(2+√3)`.  The identification of `PathGrowth.psum` with
`Dynamics.partitionSum` of the window potential is `ForMathlib/Dynamics/PressureTransfer.lean`,
in general form (`TransferBound`, `partitionPressure_le_of_transferBound`); the state observable
it is applied to — the window itself — is `BB61/Window.lean`, which discharges the last two
hypotheses of `two_add_sqrt3_not_equidistributed_of_window` below and yields
`BB61.TwoAddSqrt3.two_add_sqrt3_not_equidistributed`: **10.61 at `2 + √3`**, on the entropy
floor alone.  `BB61/Floor.lean` then discharges that floor from the root's one cited axiom,
`LY.entropyRate_floor` (`CITED/LedrappierYoung.lean`), so `BB61.problem_10_61_two_add_sqrt3`
carries no hypothesis.
-/

namespace BB61

open MeasureTheory Dynamics PathGrowth

/-! ## The coordinate partition of the full `2`-shift -/

/-- The **time-zero coordinate partition** of `Shift = ℤ → Bool`: the two cells `{ω | ω 0 = false}`
and `{ω | ω 0 = true}`.  Its dynamical joins `⋁_{i<n} σ^{-i}P` are the cylinders on the coordinate
window `[0, n)`, so `Dynamics.partitionPressure shiftZ ψ coordPartition` is the topological
pressure of `ψ` computed over cylinders — the quantity every pressure machine of M3/M4 computes. -/
def coordPartition : Shift → Bool := fun ω => ω 0

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurableSet_coordPartition_fiber (i : Bool) :
    MeasurableSet (coordPartition ⁻¹' {i}) :=
  (measurable_pi_apply (0 : ℤ)) (measurableSet_singleton i)

/-- A bounded measurable function is integrable against a probability measure. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integrable_of_bounded {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ψ : Ω → ℝ} (hmeas : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) :
    Integrable ψ μ :=
  Integrable.mono' (integrable_const C) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

/-! ## The criterion -/

/-- **M3 Theorem 12.**  Let `ψ` be a bounded measurable potential on the full `2`-shift which every
`σ`-invariant measure with `F_*μ = Leb` annihilates, and suppose those measures obey an entropy
floor `h_min`.  If the pressure of `ψ` over cylinders is strictly below `h_min`, then Problem 10.61
holds at `α`: no point of `C(α)` has `(ξ αⁿ)` equidistributed mod 1.

The proof is the one line of the variational principle: such a `μ` would satisfy
`h_min ≤ h_μ(σ, P) = h_μ(σ, P) + ∫ψ dμ ≤ P(σ, ψ, P) < h_min`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem forall_not_equidistributed_of_partitionPressure_lt (P : QuadSetup) {hmin C : ℝ}
    {ψ : Shift → ℝ} (hmeas : Measurable ψ) (hC : ∀ ω, |ψ ω| ≤ C)
    (hann : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) → ∫ ω, ψ ω ∂μ = 0)
    (hfloor : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      hmin ≤ entropyRate shiftZ μ coordPartition)
    (hpress : partitionPressure shiftZ ψ coordPartition < (hmin : EReal)) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  intro ξ hξ hud
  obtain ⟨μ, hprob, hinv, hmap⟩ :=
    P.equidistributed_iff_exists_invariant_measure.mp ⟨ξ, hξ, hud⟩
  have : IsProbabilityMeasure μ := hprob
  have hmp : MeasurePreserving shiftZ μ μ := ⟨continuous_shiftZ.measurable, hinv⟩
  have hle : ((entropyRate shiftZ μ coordPartition : ℝ) : EReal)
      ≤ partitionPressure shiftZ ψ coordPartition :=
    entropyRate_le_partitionPressure_of_integral_eq_zero hmp measurableSet_coordPartition_fiber
      (integrable_of_bounded hmeas hC) (fun ω => (abs_le.1 (hC ω)).2)
      (hann μ hprob hinv hmap)
  have hfl : ((hmin : ℝ) : EReal) ≤ ((entropyRate shiftZ μ coordPartition : ℝ) : EReal) :=
    EReal.coe_le_coe (hfloor μ hprob hinv hmap)
  exact absurd (hfl.trans hle) (not_le.2 hpress)

/-- The contrapositive packaging: a pressure certificate below the floor forbids any invariant
measure with Lebesgue image, which is the master target of `BB61/Invariant.lean`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem no_invariant_of_partitionPressure_lt (P : QuadSetup) {hmin C : ℝ}
    {ψ : Shift → ℝ} (hmeas : Measurable ψ) (hC : ∀ ω, |ψ ω| ≤ C)
    (hann : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) → ∫ ω, ψ ω ∂μ = 0)
    (hfloor : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      hmin ≤ entropyRate shiftZ μ coordPartition)
    (hpress : partitionPressure shiftZ ψ coordPartition < (hmin : EReal)) :
    ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ ≠ (volume : Measure (AddCircle (1 : ℝ))) := by
  intro μ hprob hinv hmap
  obtain ⟨ξ, hξ, hud⟩ :=
    P.equidistributed_iff_exists_invariant_measure.mpr ⟨μ, hprob, hinv, hmap⟩
  exact forall_not_equidistributed_of_partitionPressure_lt P hmeas hC hann hfloor hpress ξ hξ hud


/-! ## The M4 form: a transfer certificate, mean-corrected -/

/-- **The M4 criterion.**  Everything a computed pressure certificate produces, assembled into one
implication.

The data is: a bounded measurable potential `g` on the shift (in M4, `g = log w_cell ∘ F`, the
logarithm of the weight of the cell of an equipartition of the circle that `F(ω)` falls into);
a **transfer bound** for it on a finite state set (in M4, the window: the state is the window
content, `tgt` slides it, and `weight` is the largest cell weight the window admits); an integer
**vector certificate** `b · (M v) ≤ a · v` for that transfer operator; the Lebesgue mean `m` of
`g`, which every counterexample measure must reproduce because `F_*μ = Leb`; and the entropy floor
`h_min`.  The conclusion is Problem 10.61 at `α`, as soon as

`log (a / b) - m < h_min`,

which is exactly `note-1061-M4.html`'s mean-corrected criterion — at `α = 2 + √3` the inequality
`BB61/Pressure.lean` discharges in exact `ℤ[√3]` arithmetic, as `log_rate_lt_floor`.

Note that `g` is required only to be **bounded and measurable**: the Jensen half of the variational
principle never used continuity, which is what lets M4 replace M3's Hölder potentials by cellwise
constant ones and make every weight rational. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem forall_not_equidistributed_of_transferBound (P : QuadSetup) {V : Type*}
    [Fintype V] [DecidableEq V] {g : Shift → ℝ} (hmeas : Measurable g) {Cg : ℝ}
    (hCg : ∀ ω, |g ω| ≤ Cg) (B : TransferBound shiftZ g coordPartition V) {a b : ℕ}
    (hb : 0 < b) (ha : 0 < a) (v : V → ℕ) (hv : ∀ q, 1 ≤ v q)
    (hcert : ∀ q, b * ∑ e ∈ outEdges (detE B.tgt) q, B.weight e.1 e.2.1 * v e.2.2 ≤ a * v q)
    {m hmin : ℝ}
    (hann : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) → ∫ ω, g ω ∂μ = m)
    (hfloor : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      hmin ≤ entropyRate shiftZ μ coordPartition)
    (hlt : Real.log ((a : ℝ) / b) - m < hmin) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  refine forall_not_equidistributed_of_partitionPressure_lt P (ψ := fun ω => g ω + -m)
    (hmeas.add_const _) (C := Cg + |m|) (fun ω => ?_) (fun μ hp hi hm => ?_) hfloor ?_
  · calc |g ω + -m| ≤ |g ω| + |(-m : ℝ)| := abs_add_le _ _
      _ ≤ Cg + |m| := by rw [abs_neg]; linarith [hCg ω]
  · have : IsProbabilityMeasure μ := hp
    rw [integral_add (integrable_of_bounded hmeas hCg) (integrable_const _), hann μ hp hi hm]
    simp
  · calc partitionPressure shiftZ (fun ω => g ω + -m) coordPartition
        = partitionPressure shiftZ g coordPartition + ((-m : ℝ) : EReal) :=
          partitionPressure_add_const
      _ ≤ ((Real.log ((a : ℝ) / b) : ℝ) : EReal) + ((-m : ℝ) : EReal) := by
          gcongr
          exact partitionPressure_le_of_transferBound B hb ha v hv hcert
      _ = ((Real.log ((a : ℝ) / b) - m : ℝ) : EReal) := by
          rw [← EReal.coe_add]; congr 1
      _ < (hmin : EReal) := EReal.coe_lt_coe hlt


/-! ## The capstone at `α = 2 + √3` -/

open TwoAddSqrt3 in
/-- **Problem 10.61 at `α = 2 + √3`, reduced to one modelling lemma and the two cited inputs.**

Everything numeric is discharged: the transfer certificate `certB` (exact in `ℤ[√3]`,
`BB61/Pressure.lean`) and the criterion `log_rate_lt_floor`,
`log(a/b) - (1/8) log W < ½ log(2+√3) = h_min`.  What has to be supplied is

* the **window modelling lemma** — a state observable `state` recording the content of the
  `N = M = 3` window, sliding under the shift (`hstate`) and dominating the cell potential
  (`hexp`).  This is the exact `ℤ[√3]` arithmetic of `BB61/m4_lean_cert.py`: the window value of
  each of the `128` words, the cell it can occupy, and M1 Lemma 6's truncation bound
  `ε = 123 - 71√3`;
* the **Lebesgue mean** `hann`, that `F_*μ = Leb` forces `∫ g dμ = (1/8) log W` — immediate from
  `g = log w_cell ∘ F` and the cells having equal Lebesgue measure `1/8`;
* the **entropy floor** `hfloor`, M3 Theorem 11 ([BPS99], [LY85]), cited.

`BB61/Window.lean` supplies the first two, leaving 10.61 at `2 + √3` resting on the floor
alone (`BB61.TwoAddSqrt3.two_add_sqrt3_not_equidistributed`); `BB61/Floor.lean` supplies the
third from the cited axiom (`BB61.problem_10_61_two_add_sqrt3`).

`α = 2 + √3` is the smallest `α` of the M0 sweep where Route A is blind (`A(α) = 1.0526 > 1`), so
this is not reachable by `BB61/RouteA.lean`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_add_sqrt3_not_equidistributed_of_window (P : QuadSetup)
    (hα : P.α = 2 + Real.sqrt 3) {g : Shift → ℝ} (hmeas : Measurable g) {Cg : ℝ}
    (hCg : ∀ ω, |g ω| ≤ Cg) (state : Shift → St)
    (hstate : ∀ ω, state (shiftZ ω) = tgtB (state ω) (coordPartition ω))
    (hexp : ∀ ω, Real.exp (g ω) ≤ (wB (state ω) (coordPartition ω) : ℝ))
    (hann : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      ∫ ω, g ω ∂μ = Real.log WW / 8)
    (hfloor : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      Real.log P.α / 2 ≤ entropyRate shiftZ μ coordPartition) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  refine forall_not_equidistributed_of_transferBound P hmeas hCg
    ⟨state, tgtB, wB, hstate, hexp⟩ (by norm_num [bb]) (by norm_num [aa]) vv one_le_vv certB
    hann hfloor ?_
  rw [hα]
  exact log_rate_lt_floor

end BB61
