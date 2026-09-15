/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.WeakStar
import BirkhoffErgodicThm.BirkhoffErgodicThm
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Proposition 8(i): the ergodic realization converse

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Proposition 8(i), quadratic case.

`BB61/Invariant.lean` proves the master target in one direction: a `ξ ∈ C(α)` whose orbit is
u.d. mod one produces a `σ`-invariant `μ` on `{0,1}^ℤ` with `F_*μ = Leb`.  Proposition 8 is
the converse — every invariant measure is *realized* by a point of `C(α)` — and its ergodic
half is a generic-point argument, which is what Birkhoff's pointwise ergodic theorem is for.
Mathlib has only the mean (von Neumann) theorem, so the pointwise one is vendored here as the
`BirkhoffErgodicThm` library (a port of `lua-vr/pointwise-birkhoff`).

The chain:

* `tendsto_birkhoffAverage_of_ergodic` — for an ergodic map the Birkhoff averages of an
  integrable function converge a.e. to its *mean*.  The port gives convergence to
  `invCondexp μ f φ = μ[φ | invariants f]`; ergodicity collapses that to a constant
  (`invCondexp_ae_eq_const`, via Mathlib's `PreErgodic.ae_eq_const_of_ae_eq_comp`), and the
  constant is `∫ φ dμ` because conditional expectation preserves the integral.
* `tendsto_of_dense_of_tendsto_integral` — weak-\* convergence of probability measures may be
  tested on a *dense* set of bounded continuous functions (the usual `3ε`).  Countability then
  comes from `C(𝕋, ℝ)` being separable, so one `μ`-full set of `ω` serves all test functions
  at once.
* `padZ_futures_apply` … `tendsto_dist_fMap_padZ` — the **padding estimate**.  Replacing a
  two-sided word `ω` by the one-sided word `ω⁺` padded with zeros changes nothing in the
  futures and only the far past of the window, so `|F(σⁿ ω̃) - F(σⁿ ω)| ≤
  (1+|β|)|β|ⁿ/(1-|β|) → 0`.  This is the note's "the padding costs nothing", made
  quantitative by `BB61/Factor.lean`'s window bound rather than by uniform continuity in the
  shift metric.
* `exists_tendsto_map_of_ergodic` — **Proposition 8(i)**: for every ergodic `σ`-invariant `μ`
  on `{0,1}^ℤ` there is `ξ ∈ C(α)` with `λ_N → F_*μ`.  `exists_tendsto_haarT_of_ergodic` is
  the case `F_*μ = Leb` that M1 Corollary 9 consumes.
* `equidistributed_of_tendsto_emp` — the **converse of `tendsto_emp_of_equidistributed`**:
  weak-\* convergence of the empirical measures to Haar measure is uniform distribution in the
  counting sense of `IsEquidistributedModuloOne`.  Weak-\* convergence contains the Weyl sums,
  and the converse half of Weyl's criterion is already proved in the repository
  (`Bertin.uniformlyDistributedModOne_of_weylCriterion`, whose `circBump` sandwich runs on
  `ForMathlib/Analysis/Equidistribution/AddCircleWeyl.lean`), so the bridge costs only the
  passage from a bounded-continuous test function to the two real characters.
* `exists_equidistributed_of_ergodic` — **M1 Corollary 9, ergodic half**: an ergodic `μ` with
  `F_*μ = Leb` makes 10.61 *fail* at `α`.

One thing this file does **not** do: it proves the "hence" of Prop. 8(i), `λ_N → F_*μ`, and
not the intermediate `ν_N → μ` on the shift space itself.  That would need the modulus "words
agreeing on a long central block have close `φ`-values" for *every* `φ ∈ C({0,1}^ℤ, ℝ)`, a
point-set fact about the product topology that has no Mathlib support, whereas `F`'s own
modulus is already in `Factor.lean`.  Nothing downstream uses the stronger form.

The **non-ergodic** case, M1 Prop. 8(ii), is `BB61/Saturation.lean`.  The ergodic case does
not imply it — `F_*μ = Leb` need not descend to the ergodic components of `μ` — and ergodic
decomposition does not bridge the gap either: from `F_*μ = ∫ F_*ν_x dμ(x) = Leb` one cannot
conclude `F_*ν_x = Leb` for any component, Lebesgue measure being an average of non-uniform
measures.  What closes it is saturation of the full shift, and `BB61/Saturation.lean` proves
that **without any ergodic theorem**, so it does not import the Birkhoff port.  With it, M1
Cor. 9 is an equivalence (`equidistributed_iff_exists_invariant`); this file's
`exists_equidistributed_of_ergodic` is the special case Prop. 8(i) already gave.
-/

namespace BB61

open MeasureTheory Filter Topology BoundedContinuousFunction MeasurableSpace
open TopologicalSpace (SeparableSpace exists_countable_dense)

/-! ## Birkhoff averages of an ergodic map converge to the mean -/

section ErgodicMean

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {f : X → X}

/-- For an ergodic map, the conditional expectation on the invariant `σ`-algebra is the
mean: the `invariants`-measurable function `μ[φ | invariants f]` is invariant, hence a.e.
constant, and its integral is `∫ φ dμ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem invCondexp_ae_eq_const (hf : Ergodic f μ) (φ : X → ℝ) :
    invCondexp μ f φ =ᵐ[μ] fun _ => ∫ x, φ x ∂μ := by
  have hmeas : Measurable[invariants f] (invCondexp μ f φ) :=
    stronglyMeasurable_condExp.measurable
  have hcomp : invCondexp μ f φ ∘ f = invCondexp μ f φ :=
    comp_eq_of_measurable_invariants hmeas
  obtain ⟨c, hc⟩ :=
    hf.toPreErgodic.ae_eq_const_of_ae_eq_comp (hmeas.le (invariants_le f)) hcomp
  have hint : ∫ x, invCondexp μ f φ x ∂μ = ∫ x, φ x ∂μ := integral_condExp (invariants_le f)
  have hc' : ∫ x, invCondexp μ f φ x ∂μ = c := by
    rw [integral_congr_ae hc]; simp
  have hceq : c = ∫ x, φ x ∂μ := hc'.symm.trans hint
  rw [hceq] at hc
  exact hc

/-- **Birkhoff's pointwise ergodic theorem, ergodic case.**  For an ergodic measure-preserving
map the Birkhoff averages of an integrable function converge `μ`-a.e. to its mean. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_birkhoffAverage_of_ergodic (hf : Ergodic f μ) {φ : X → ℝ}
    (hφ : Integrable φ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ f φ n x) atTop (𝓝 (∫ y, φ y ∂μ)) := by
  filter_upwards [birkhoffErgodicTheorem' μ hf.toMeasurePreserving hφ,
    invCondexp_ae_eq_const hf φ] with x hx hx'
  rwa [hx'] at hx

omit [MeasurableSpace X] in
/-- The Birkhoff average as an honest arithmetic mean. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem birkhoffAverage_eq_div (g : X → X) (φ : X → ℝ) (n : ℕ) (x : X) :
    birkhoffAverage ℝ g φ n x = (∑ i ∈ Finset.range n, φ (g^[i] x)) / n := by
  simp [birkhoffAverage, birkhoffSum, div_eq_inv_mul]

end ErgodicMean

/-! ## The padding estimate -/

/-- Padding the futures of `ω` by zeros changes no coordinate `≥ 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem padZ_futures_apply (ω : Shift) {k : ℤ} (hk : 1 ≤ k) : padZ (futures ω) k = ω k := by
  simp only [padZ, futures]
  split_ifs
  congr 1
  omega

/-- The two words have the same futures at every time. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem futures_iterate_padZ_futures (ω : Shift) (n : ℕ) :
    futures (shiftZ^[n] (padZ (futures ω))) = futures (shiftZ^[n] ω) := by
  funext j
  simp only [futures, shiftZ_iterate]
  exact padZ_futures_apply ω (by omega)

/-- Their pasts agree down to depth `n`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pasts_iterate_padZ_agree (ω : Shift) (n : ℕ) {m : ℕ} (hm : m ≤ n) :
    pasts (shiftZ^[n + 1] (padZ (futures ω))) m = pasts (shiftZ^[n + 1] ω) m := by
  simp only [pasts, shiftZ_iterate]
  exact padZ_futures_apply ω (by omega)

namespace QuadSetup

variable (P : QuadSetup)

/-- **The padding estimate.**  The zero-padded word tracks `ω` with a geometrically small
error, uniformly in the future: only the window's far past differs. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_fRaw_sub_padZ_le (ω : Shift) (n : ℕ) :
    |P.fRaw (shiftZ^[n + 1] (padZ (futures ω))) - P.fRaw (shiftZ^[n + 1] ω)|
      ≤ (1 + |P.β|) * |P.β| ^ (n + 1) / (1 - |P.β|) := by
  have hfut := futures_iterate_padZ_futures ω (n + 1)
  have key : P.fRaw (shiftZ^[n + 1] (padZ (futures ω))) - P.fRaw (shiftZ^[n + 1] ω)
      = P.wVal (pasts (shiftZ^[n + 1] ω))
        - P.wVal (pasts (shiftZ^[n + 1] (padZ (futures ω)))) := by
    simp only [fRaw, hfut]; ring
  rw [key, abs_sub_comm]
  exact P.abs_wVal_sub_le_of_agree fun m hm => pasts_iterate_padZ_agree ω n hm

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_fRaw_sub_padZ (ω : Shift) :
    Tendsto (fun n => P.fRaw (shiftZ^[n] (padZ (futures ω))) - P.fRaw (shiftZ^[n] ω))
      atTop (𝓝 0) := by
  have hβ := P.abs_beta_lt_one
  have hpow : Tendsto (fun n : ℕ => |P.β| ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg P.β) hβ).comp (tendsto_add_atTop_nat 1)
  have hgeom : Tendsto (fun n : ℕ => (1 + |P.β|) * |P.β| ^ (n + 1) / (1 - |P.β|)) atTop (𝓝 0) := by
    simpa using (hpow.const_mul (1 + |P.β|)).div_const (1 - |P.β|)
  rw [← tendsto_add_atTop_iff_nat 1]
  exact squeeze_zero_norm (fun n => by
    simpa [Real.norm_eq_abs] using P.abs_fRaw_sub_padZ_le ω n) hgeom

/-- The padded orbit and the original orbit have the same limit set on the circle. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_dist_fMap_padZ (ω : Shift) :
    Tendsto (fun n => dist (P.fMap (shiftZ^[n] (padZ (futures ω)))) (P.fMap (shiftZ^[n] ω)))
      atTop (𝓝 0) := by
  have hcont : Continuous fun t : ℝ => ‖((t : ℝ) : AddCircle (1 : ℝ))‖ :=
    continuous_norm.comp QuotientAddGroup.continuous_mk
  have h0 : ‖((0 : ℝ) : AddCircle (1 : ℝ))‖ = 0 := by simp
  have h := (hcont.tendsto 0).comp (P.tendsto_fRaw_sub_padZ ω)
  rw [h0] at h
  refine h.congr fun n => ?_
  rw [Function.comp_apply, dist_eq_norm]
  congr 1

/-! ## Proposition 8(i) -/

/-- **M1 Proposition 8(i), the ergodic realization converse.**  For every ergodic
`σ`-invariant Borel probability measure `μ` on `{0,1}^ℤ` there is a point `ξ ∈ C(α)` whose
orbit realizes `F_*μ`: the empirical measures `λ_N` of `({ξ αⁿ})_{n ≤ N}` converge weak-\* to
`F_*μ`.

The point is the note's: a `μ`-generic `ω` exists by Birkhoff (applied to a countable dense
family of test functions on `𝕋`), and padding its future by zeros — the one place where the
one-sided problem is forced into the two-sided model — moves `F(σⁿ ω)` by `O(|β|ⁿ)`, which
Cesàro averages do not see. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_tendsto_map_of_ergodic (μ : ProbabilityMeasure Shift)
    (hμ : Ergodic shiftZ (μ : Measure Shift)) :
    ∃ ξ ∈ cantorSet P.α,
      Tendsto (fun N => emp (fun n => ((ξ * P.α ^ n : ℝ) : AddCircle (1 : ℝ))) N) atTop
        (𝓝 (pmap P.measurable_fMap μ)) := by
  have : IsProbabilityMeasure (μ : Measure Shift) := μ.2
  have : SeparableSpace (AddCircle (1 : ℝ) →ᵇ ℝ) := by
    have h := ContinuousMap.isometryEquivBoundedOfCompact (AddCircle (1 : ℝ)) ℝ
    exact h.surjective.denseRange.separableSpace h.continuous
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (AddCircle (1 : ℝ) →ᵇ ℝ)
  -- a single `μ`-full set of generic points serves every `G` in the countable dense family
  have hbirk : ∀ G ∈ D, ∀ᵐ ω ∂(μ : Measure Shift),
      Tendsto (fun n => birkhoffAverage ℝ shiftZ (fun x => G (P.fMap x)) n ω) atTop
        (𝓝 (∫ x, G (P.fMap x) ∂(μ : Measure Shift))) := fun G _ =>
    tendsto_birkhoffAverage_of_ergodic hμ
      ((G.compContinuous ⟨P.fMap, P.continuous_fMap⟩).integrable _)
  obtain ⟨ω, hω⟩ := ((ae_ball_iff hDc).mpr hbirk).exists
  refine ⟨piVal P.α (futures ω), ⟨futures ω, rfl⟩, ?_⟩
  refine tendsto_of_dense_of_tendsto_integral hDd fun G hG => ?_
  set φ : Shift → ℝ := fun x => G (P.fMap x) with hφdef
  -- the orbit of `ξ` is the `F`-image of the orbit of the padded word
  have hsum : ∀ N : ℕ,
      ∫ z, G z ∂(emp (fun n => ((piVal P.α (futures ω) * P.α ^ n : ℝ) : AddCircle (1 : ℝ))) N
          : Measure (AddCircle (1 : ℝ)))
        = (∑ n ∈ Finset.range (N + 1), φ (shiftZ^[n] (padZ (futures ω)))) / (N + 1) := by
    intro N
    rw [integral_emp]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by
      simp only [hφdef, P.fMap_iterate_padZ (futures ω) n]
  have hdecomp : ∀ N : ℕ,
      (∑ n ∈ Finset.range (N + 1), φ (shiftZ^[n] (padZ (futures ω)))) / (N + 1)
        = (∑ n ∈ Finset.range (N + 1), φ (shiftZ^[n] ω)) / (N + 1)
          + (∑ n ∈ Finset.range (N + 1),
              (φ (shiftZ^[n] (padZ (futures ω))) - φ (shiftZ^[n] ω))) / (N + 1) := by
    intro N
    rw [Finset.sum_sub_distrib]
    ring
  -- Birkhoff along `ω`
  have hb : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), φ (shiftZ^[n] ω)) / (N + 1))
      atTop (𝓝 (∫ x, φ x ∂(μ : Measure Shift))) := by
    have h2 := (hω G hG).comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun N => ?_
    rw [Function.comp_apply, birkhoffAverage_eq_div]
    push_cast
    rfl
  -- the padding is invisible to Cesàro means
  have hc : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1),
      (φ (shiftZ^[n] (padZ (futures ω))) - φ (shiftZ^[n] ω))) / (N + 1)) atTop (𝓝 0) :=
    tendsto_cesaro_sub_of_dist G (P.tendsto_dist_fMap_padZ ω)
  have hlim := hb.add hc
  rw [add_zero] at hlim
  rw [integral_pmap P.continuous_fMap μ G]
  exact hlim.congr fun N => ((hsum N).trans (hdecomp N)).symm

/-- **M1 Proposition 8(i), the case Corollary 9 consumes.**  If an *ergodic* `σ`-invariant
`μ` has `F_*μ = Leb`, then some `ξ ∈ C(α)` has `λ_N → Leb` — the weak-\* half of "`(ξ αⁿ)` is
u.d. mod one". -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_tendsto_haarT_of_ergodic (μ : ProbabilityMeasure Shift)
    (hμ : Ergodic shiftZ (μ : Measure Shift)) (hmap : pmap P.measurable_fMap μ = haarT) :
    ∃ ξ ∈ cantorSet P.α,
      Tendsto (fun N => emp (fun n => ((ξ * P.α ^ n : ℝ) : AddCircle (1 : ℝ))) N) atTop
        (𝓝 haarT) := by
  simpa [hmap] using P.exists_tendsto_map_of_ergodic μ hμ

end QuadSetup

namespace QuadSetup

variable (P : QuadSetup)

/-- **M1 Corollary 9, ergodic half.**  If an *ergodic* `σ`-invariant measure `μ` of the full
`2`-shift satisfies `F_*μ = Leb`, then Problem 10.61 **fails** at `α`: some `ξ ∈ C(α)` has
`(ξ αⁿ)` uniformly distributed modulo one.

Together with `BB61.QuadSetup.exists_invariant_measure_of_equidistributed` (the easy half,
which returns an invariant — not necessarily ergodic — measure) this is M1 Cor. 9 on the
ergodic class.  `BB61/Saturation.lean` removes the ergodicity
(`BB61.QuadSetup.equidistributed_iff_exists_invariant`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_equidistributed_of_ergodic (μ : ProbabilityMeasure Shift)
    (hμ : Ergodic shiftZ (μ : Measure Shift)) (hmap : pmap P.measurable_fMap μ = haarT) :
    ∃ ξ ∈ cantorSet P.α, IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨ξ, hξ, hlim⟩ := P.exists_tendsto_haarT_of_ergodic μ hμ hmap
  exact ⟨ξ, hξ, equidistributed_of_tendsto_emp hlim⟩

end QuadSetup

end BB61
