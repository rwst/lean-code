/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Words
import BB61.MeanSelect
import BB61.WeakStar
import BB61.Certificate
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Proposition 8(ii): saturation

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Proposition 8(ii) and Corollary 9.

`BB61/Realization.lean` proves Proposition 8(i): an *ergodic* invariant measure of the full
`2`-shift is realized by a point of `C(α)`.  This file removes the ergodicity, which is what
Corollary 9 needs — the master target of `BB61/Invariant.lean` quantifies over all invariant
measures, and Lebesgue measure is not extreme, so the ergodic case does not imply the general
one and ergodic decomposition does not bridge the gap.

## What replaces the ergodic theorem

The note cites saturation of the full shift ([BM86] Th. VII, or Sigmund's specification
argument): every invariant measure has a generic point.  The proof here is **elementary and
uses no ergodic theorem at all** — neither Birkhoff nor von Neumann, and no ergodic
decomposition.  Two observations do the work.

*Invariance is a statement about means.*  For invariant `μ` and any observable `φ` the
window average `H_N(ω) = (1/N) ∑_{n<N} φ(σⁿ ω)` has `∫ H_N dμ = ∫ φ dμ` — **exactly**, for
every `N`, by invariance alone (`integral_orbAvg`).  So the target value is a mean, not a
limit.

*A mean is realized by an equal-weight sample.*  `BB61/MeanSelect.lean` picks, greedily,
points `ω_0, ω_1, …` whose equal-weight averages kill finitely many mean-zero observables
simultaneously.  No independence is needed: the partial-sum vector `s_q` obeys
`‖s_{q+1}‖² ≤ ‖s_q‖² + mC²` because *some* point has `⟨s_q, g⟩ ≤ 0`.

Concatenating the sampled windows into one digit word — `BB61/Words.lean` — then produces a
`ξ ∈ C(α)` whose orbit realizes `F_*μ`.  The staged word spends stage `j` on the first `j+1`
test functions at accuracy `1/(j+1)`, with atoms long enough that the window boundary is
negligible and stages long enough that the tail of the construction dominates: the running
average is then a Toeplitz average of stage averages, and converges.
-/

namespace BB61

open MeasureTheory Filter Topology BoundedContinuousFunction
open TopologicalSpace (SeparableSpace exists_countable_dense)

/-! ## Elementary helpers -/

/-- Blocks of `NN` consecutive terms. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sum_range_mul (NN : ℕ) (h : ℕ → ℝ) : ∀ q : ℕ,
    ∑ u ∈ Finset.range (NN * q), h u
      = ∑ l ∈ Finset.range q, ∑ r ∈ Finset.range NN, h (NN * l + r) := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Reduction mod one does not increase distances. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dist_addCircle_coe_le (x y : ℝ) :
    dist ((x : ℝ) : AddCircle (1 : ℝ)) ((y : ℝ) : AddCircle (1 : ℝ)) ≤ |x - y| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  simpa [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm :
      ‖((x - y : ℝ) : AddCircle (1 : ℝ))‖ ≤ ‖x - y‖)

/-- A bounded continuous function on the circle has a modulus of continuity read on `ℝ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_modulus (G : AddCircle (1 : ℝ) →ᵇ ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x y : ℝ, |x - y| ≤ ρ →
      |G ((x : ℝ) : AddCircle (1 : ℝ)) - G ((y : ℝ) : AddCircle (1 : ℝ))| ≤ η := by
  have hG : UniformContinuous (G : AddCircle (1 : ℝ) → ℝ) :=
    CompactSpace.uniformContinuous_of_continuous G.continuous
  obtain ⟨ρ, hρ, h⟩ := Metric.uniformContinuous_iff.mp hG η hη
  refine ⟨ρ / 2, by linarith, fun x y hxy => ?_⟩
  have hd : dist ((x : ℝ) : AddCircle (1 : ℝ)) ((y : ℝ) : AddCircle (1 : ℝ)) < ρ :=
    lt_of_le_of_lt (le_trans (dist_addCircle_coe_le x y) hxy) (by linarith)
  have h2 := h hd
  rw [Real.dist_eq] at h2
  exact h2.le

/-- Finitely many test functions share a modulus of continuity. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_common_modulus (ψ : ℕ → AddCircle (1 : ℝ) →ᵇ ℝ) (j : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, i ≤ j → ∀ x y : ℝ, |x - y| ≤ ρ →
      |ψ i ((x : ℝ) : AddCircle (1 : ℝ)) - ψ i ((y : ℝ) : AddCircle (1 : ℝ))| ≤ η := by
  induction j with
  | zero =>
    obtain ⟨ρ, hρ, h⟩ := exists_modulus (ψ 0) hη
    exact ⟨ρ, hρ, fun i hi => by rw [Nat.le_zero.mp hi]; exact h⟩
  | succ j ih =>
    obtain ⟨ρ, hρ, h⟩ := ih
    obtain ⟨ρ', hρ', h'⟩ := exists_modulus (ψ (j + 1)) hη
    refine ⟨min ρ ρ', lt_min hρ hρ', fun i hi x y hxy => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with hi' | hi'
    · exact h i (by omega) x y (le_trans hxy (min_le_left _ _))
    · rw [hi']; exact h' x y (le_trans hxy (min_le_right _ _))

namespace QuadSetup

variable (P : QuadSetup)

/-- The window modulus of `BB61/Factor.lean`, as a sequence. -/
noncomputable def winErr (R : ℕ) : ℝ :=
  (P.α⁻¹) ^ R + (1 + |P.β|) * |P.β| ^ (R + 1) / (1 - |P.β|)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_winErr : Tendsto P.winErr atTop (𝓝 0) := by
  have hβ := P.abs_beta_lt_one
  have hα : (0 : ℝ) ≤ P.α⁻¹ := (inv_pos_of_one_lt P.one_lt).le
  have hα1 : P.α⁻¹ < 1 := inv_lt_one_of_one_lt P.one_lt
  have h1 : Tendsto (fun R : ℕ => (P.α⁻¹) ^ R) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα hα1
  have h2 : Tendsto (fun R : ℕ => (1 + |P.β|) * |P.β| ^ (R + 1) / (1 - |P.β|)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun R : ℕ => |P.β| ^ (R + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg P.β) hβ).comp (tendsto_add_atTop_nat 1)
    simpa using (hpow.const_mul (1 + |P.β|)).div_const (1 - |P.β|)
  have h := h1.add h2
  rw [add_zero] at h
  exact h

/-- A window long enough for a prescribed accuracy. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_window {ρ : ℝ} (hρ : 0 < ρ) : ∃ R : ℕ, 1 ≤ R ∧ P.winErr R ≤ ρ := by
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.mp P.tendsto_winErr ρ hρ
  refine ⟨max 1 R₀, le_max_left _ _, ?_⟩
  have h := hR₀ (max 1 R₀) (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at h
  exact le_trans (le_abs_self _) h.le

/-! ## The orbit observable -/

/-- `ω ↦ (1/N) ∑_{r<N} G(F(σʳ ω))`, as a bounded continuous function on `{0,1}^ℤ`. -/
noncomputable def orbAvg (G : AddCircle (1 : ℝ) →ᵇ ℝ) (N : ℕ) : Shift →ᵇ ℝ :=
  (N : ℝ)⁻¹ • ∑ r ∈ Finset.range N, G.compContinuous
    ⟨fun ω => P.fMap (shiftZ^[r] ω), P.continuous_fMap.comp (continuous_shiftZ.iterate r)⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem orbAvg_apply (G : AddCircle (1 : ℝ) →ᵇ ℝ) (N : ℕ) (ω : Shift) :
    P.orbAvg G N ω = (N : ℝ)⁻¹ * ∑ r ∈ Finset.range N, G (P.fMap (shiftZ^[r] ω)) := by
  simp [orbAvg]

/-- Iterating a measure-preserving shift. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem map_iterate_shiftZ {μ : Measure Shift} (hinv : Measure.map shiftZ μ = μ) (n : ℕ) :
    Measure.map (shiftZ^[n]) μ = μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', ← Measure.map_map continuous_shiftZ.measurable
      (continuous_shiftZ.iterate n).measurable, ih, hinv]

/-- **Invariance is a statement about means.**  For an invariant measure the window average of
an observable has *exactly* the mean of the observable, for every window length. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_orbAvg {μ : Measure Shift} [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ) (G : AddCircle (1 : ℝ) →ᵇ ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, P.orbAvg G N ω ∂μ = ∫ ω, G (P.fMap ω) ∂μ := by
  have hterm : ∀ r : ℕ, ∫ ω, G (P.fMap (shiftZ^[r] ω)) ∂μ = ∫ ω, G (P.fMap ω) ∂μ := by
    intro r
    have hmeas : AEMeasurable (shiftZ^[r]) μ :=
      (continuous_shiftZ.iterate r).measurable.aemeasurable
    have := integral_map (μ := μ) (φ := shiftZ^[r]) hmeas
      (f := fun ω => G (P.fMap ω)) (by
        rw [map_iterate_shiftZ hinv r]
        exact (G.compContinuous ⟨P.fMap, P.continuous_fMap⟩).continuous.aestronglyMeasurable)
    rw [map_iterate_shiftZ hinv r] at this
    exact this.symm
  have hsum : ∫ ω, P.orbAvg G N ω ∂μ
      = (N : ℝ)⁻¹ * ∑ r ∈ Finset.range N, ∫ ω, G (P.fMap (shiftZ^[r] ω)) ∂μ := by
    rw [show (fun ω => P.orbAvg G N ω)
        = fun ω => (N : ℝ)⁻¹ * ∑ r ∈ Finset.range N, G (P.fMap (shiftZ^[r] ω)) from
      funext (P.orbAvg_apply G N)]
    rw [integral_const_mul, integral_finsetSum]
    intro r _
    exact (G.compContinuous
      ⟨fun ω => P.fMap (shiftZ^[r] ω),
        P.continuous_fMap.comp (continuous_shiftZ.iterate r)⟩).integrable μ
  rw [hsum]
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

end QuadSetup

/-! ## Two elementary bounds -/

/-- The trivial bound on a run of positions. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_sum_sub_le_of_bdd (f : ℕ → ℝ) (c M : ℝ) (hf : ∀ n, |f n| ≤ M) (hc : |c| ≤ M)
    (a b : ℕ) : |(∑ u ∈ Finset.range b, f (a + u)) - (b : ℝ) * c| ≤ (b : ℝ) * (2 * M) := by
  have hrw : (∑ u ∈ Finset.range b, f (a + u)) - (b : ℝ) * c
      = ∑ u ∈ Finset.range b, (f (a + u) - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrw]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * M) fun u _ => ?_) ?_
  · calc |f (a + u) - c| ≤ |f (a + u)| + |c| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hf (a + u)]
  · rw [Finset.card_range, nsmul_eq_mul]

namespace QuadSetup

variable (P : QuadSetup)

/-- The window average is bounded by the sup norm. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_orbAvg_le (G : AddCircle (1 : ℝ) →ᵇ ℝ) {N : ℕ} (hN : 0 < N) (ω : Shift) :
    |P.orbAvg G N ω| ≤ ‖G‖ := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [P.orbAvg_apply, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N : ℝ)⁻¹)]
  have h1 : |∑ r ∈ Finset.range N, G (P.fMap (shiftZ^[r] ω))| ≤ (N : ℝ) * ‖G‖ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ ‖G‖ fun r _ => ?_) ?_
    · simpa [Real.norm_eq_abs] using G.norm_coe_le_norm (P.fMap (shiftZ^[r] ω))
    · rw [Finset.card_range, nsmul_eq_mul]
  calc (N : ℝ)⁻¹ * |∑ r ∈ Finset.range N, G (P.fMap (shiftZ^[r] ω))|
      ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ‖G‖) := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖G‖ := by field_simp

/-! ## The atom estimate -/

/-- **The atom estimate.**  Over one atom of the staged word the observable tracks the
observable along the source, except within `R` of the two ends. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem atom_estimate (S : StageData) (G : AddCircle (1 : ℝ) →ᵇ ℝ) {j l R : ℕ} {ρ η : ℝ}
    (hl : l < S.AA j) (hR : 1 ≤ R) (hNN : 2 * R + 2 ≤ S.NN j) (hwin : P.winErr R ≤ ρ)
    (hmod : ∀ x y : ℝ, |x - y| ≤ ρ →
      |G ((x : ℝ) : AddCircle (1 : ℝ)) - G ((y : ℝ) : AddCircle (1 : ℝ))| ≤ η) (hη : 0 ≤ η) :
    |∑ r ∈ Finset.range (S.NN j),
        (G (P.fMap (shiftZ^[S.T j + S.NN j * l + r] (padZ S.word)))
          - G (P.fMap (shiftZ^[r] (S.om j l))))|
      ≤ (S.NN j : ℝ) * η + (2 * R + 2) * (2 * ‖G‖) := by
  set t : ℕ → ℝ := fun r => G (P.fMap (shiftZ^[S.T j + S.NN j * l + r] (padZ S.word)))
    - G (P.fMap (shiftZ^[r] (S.om j l))) with htdef
  have hGnn : (0 : ℝ) ≤ ‖G‖ := norm_nonneg G
  have hbd : ∀ r, |t r| ≤ 2 * ‖G‖ := by
    intro r
    have h1 : |G (P.fMap (shiftZ^[S.T j + S.NN j * l + r] (padZ S.word)))| ≤ ‖G‖ := by
      simpa [Real.norm_eq_abs] using G.norm_coe_le_norm _
    have h2 : |G (P.fMap (shiftZ^[r] (S.om j l)))| ≤ ‖G‖ := by
      simpa [Real.norm_eq_abs] using G.norm_coe_le_norm _
    calc |t r| ≤ |G (P.fMap (shiftZ^[S.T j + S.NN j * l + r] (padZ S.word)))|
          + |G (P.fMap (shiftZ^[r] (S.om j l)))| := abs_sub _ _
      _ ≤ 2 * ‖G‖ := by linarith
  have hgood : ∀ r, R + 1 ≤ r → r + R ≤ S.NN j → |t r| ≤ η := by
    intro r hr1 hr2
    have hfr : |P.fRaw (shiftZ^[S.T j + S.NN j * l + r] (padZ S.word))
        - P.fRaw (shiftZ^[r] (S.om j l))| ≤ P.winErr R := P.abs_fRaw_sub_le_agree S hl hr1 hr2
    exact hmod _ _ (le_trans hfr hwin)
  -- split the atom into head, body and tail
  set M : ℕ := S.NN j - R with hMdef
  have hM1 : R + 1 ≤ M + 1 := by omega
  have hM2 : M + 1 ≤ S.NN j := by omega
  have hsplit : ∑ r ∈ Finset.range (S.NN j), t r
      = ((∑ r ∈ Finset.Ico 0 (R + 1), t r) + ∑ r ∈ Finset.Ico (R + 1) (M + 1), t r)
        + ∑ r ∈ Finset.Ico (M + 1) (S.NN j), t r := by
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) hM1,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hM2, Finset.range_eq_Ico]
  have hhead : |∑ r ∈ Finset.Ico 0 (R + 1), t r| ≤ ((R : ℝ) + 1) * (2 * ‖G‖) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * ‖G‖) fun r _ => hbd r) ?_
    rw [Nat.card_Ico, nsmul_eq_mul]
    push_cast
    ring_nf
    rfl
  have htail : |∑ r ∈ Finset.Ico (M + 1) (S.NN j), t r| ≤ (R : ℝ) * (2 * ‖G‖) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * ‖G‖) fun r _ => hbd r) ?_
    rw [Nat.card_Ico, nsmul_eq_mul]
    have hcard : S.NN j - (M + 1) ≤ R := by omega
    have : ((S.NN j - (M + 1) : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hcard
    nlinarith
  have hbody : |∑ r ∈ Finset.Ico (R + 1) (M + 1), t r| ≤ (S.NN j : ℝ) * η := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ η fun r hr => ?_) ?_
    · rw [Finset.mem_Ico] at hr
      exact hgood r hr.1 (by omega)
    · rw [Nat.card_Ico, nsmul_eq_mul]
      have hcard : M + 1 - (R + 1) ≤ S.NN j := by omega
      have : ((M + 1 - (R + 1) : ℕ) : ℝ) ≤ (S.NN j : ℝ) := by exact_mod_cast hcard
      nlinarith
  rw [hsplit]
  calc |(∑ r ∈ Finset.Ico 0 (R + 1), t r) + (∑ r ∈ Finset.Ico (R + 1) (M + 1), t r)
        + ∑ r ∈ Finset.Ico (M + 1) (S.NN j), t r|
      ≤ |(∑ r ∈ Finset.Ico 0 (R + 1), t r) + ∑ r ∈ Finset.Ico (R + 1) (M + 1), t r|
        + |∑ r ∈ Finset.Ico (M + 1) (S.NN j), t r| := abs_add_le _ _
    _ ≤ (|∑ r ∈ Finset.Ico 0 (R + 1), t r| + |∑ r ∈ Finset.Ico (R + 1) (M + 1), t r|)
        + |∑ r ∈ Finset.Ico (M + 1) (S.NN j), t r| := by
          gcongr; exact abs_add_le _ _
    _ ≤ (((R : ℝ) + 1) * (2 * ‖G‖) + (S.NN j : ℝ) * η) + (R : ℝ) * (2 * ‖G‖) := by
          gcongr
    _ ≤ (S.NN j : ℝ) * η + (2 * R + 2) * (2 * ‖G‖) := by nlinarith

/-! ## The stage estimate -/

/-- **The stage estimate.**  Every prefix of a stage of the staged word has its observable
average within `δ` of the target `c`, up to a fixed additive `K` that the length of the stage
will make negligible.  The three errors are the window boundary of each atom (`δ₀`), the
greedy sampling error (`δ'`), and the modulus of continuity (`η`); the additive `K` covers the
prefixes too short for the greedy bound to have started, and the last incomplete atom. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem stage_estimate (S : StageData) (G : AddCircle (1 : ℝ) →ᵇ ℝ) {j R Q p : ℕ}
    {ρ η c δ' δ₀ δ K : ℝ}
    (hR : 1 ≤ R) (hNN : 2 * R + 2 ≤ S.NN j) (hwin : P.winErr R ≤ ρ)
    (hmod : ∀ x y : ℝ, |x - y| ≤ ρ →
      |G ((x : ℝ) : AddCircle (1 : ℝ)) - G ((y : ℝ) : AddCircle (1 : ℝ))| ≤ η)
    (hη : 0 ≤ η) (hδ' : 0 ≤ δ') (hδ₀ : 0 ≤ δ₀) (hc : |c| ≤ ‖G‖)
    (hp : p ≤ S.AA j * S.NN j)
    (hgre : ∀ q : ℕ, Q ≤ q → |∑ l ∈ Finset.range q,
        ((S.NN j : ℝ)⁻¹ * (∑ r ∈ Finset.range (S.NN j), G (P.fMap (shiftZ^[r] (S.om j l)))) - c)|
      ≤ δ' * q)
    (hbound₀ : (2 * R + 2) * (2 * ‖G‖) ≤ δ₀ * (S.NN j : ℝ))
    (hδ : η + δ' + δ₀ ≤ δ)
    (hK : ((S.NN j : ℝ) * ((Q : ℝ) + 1)) * (2 * ‖G‖) ≤ K) :
    |(∑ u ∈ Finset.range p, G (P.fMap (shiftZ^[S.T j + u] (padZ S.word)))) - p * c|
      ≤ p * δ + K := by
  have hGnn : (0 : ℝ) ≤ ‖G‖ := norm_nonneg G
  have hNNpos : 0 < S.NN j := S.NN_pos j
  have hNN0 : (0 : ℝ) < (S.NN j : ℝ) := by exact_mod_cast hNNpos
  have hδnn : 0 ≤ δ := by linarith
  set f : ℕ → ℝ := fun n => G (P.fMap (shiftZ^[n] (padZ S.word))) with hfdef
  have hfbd : ∀ n, |f n| ≤ ‖G‖ := fun n => by
    simpa [hfdef, Real.norm_eq_abs] using G.norm_coe_le_norm (P.fMap (shiftZ^[n] (padZ S.word)))
  -- the trivial bound on any run of positions
  have htriv : ∀ a b : ℕ, |(∑ u ∈ Finset.range b, f (a + u)) - (b : ℝ) * c|
      ≤ (b : ℝ) * (2 * ‖G‖) := by
    intro a b
    have hrw : (∑ u ∈ Finset.range b, f (a + u)) - (b : ℝ) * c
        = ∑ u ∈ Finset.range b, (f (a + u) - c) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hrw]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * ‖G‖) fun u _ => ?_) ?_
    · calc |f (a + u) - c| ≤ |f (a + u)| + |c| := abs_sub _ _
        _ ≤ 2 * ‖G‖ := by linarith [hfbd (a + u)]
    · rw [Finset.card_range, nsmul_eq_mul]
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  rcases le_or_gt p (S.NN j * (Q + 1)) with hcase | hcase
  · -- the prefix is too short for the greedy bound: the additive term covers it
    have h1 := htriv (S.T j) p
    have h2 : (p : ℝ) ≤ (S.NN j : ℝ) * ((Q : ℝ) + 1) := by exact_mod_cast hcase
    have h3 : (p : ℝ) * (2 * ‖G‖) ≤ K := le_trans (by nlinarith) hK
    have h4 : (0 : ℝ) ≤ (p : ℝ) * δ := mul_nonneg (Nat.cast_nonneg p) hδnn
    linarith
  · -- the generic case: `q` full atoms and a remainder
    set q := p / S.NN j with hqdef
    set s := p % S.NN j with hsdef
    have hpq : S.NN j * q + s = p := Nat.div_add_mod p (S.NN j)
    have hqQ : Q ≤ q := by
      have hcomm : (Q + 1) * S.NN j = S.NN j * (Q + 1) := Nat.mul_comm _ _
      have : Q + 1 ≤ q := by rw [hqdef, Nat.le_div_iff_mul_le hNNpos]; omega
      omega
    have hqAA : q ≤ S.AA j := by
      have h1 : p / S.NN j ≤ S.AA j * S.NN j / S.NN j := Nat.div_le_div_right hp
      rwa [Nat.mul_div_cancel _ hNNpos] at h1
    set A : ℕ → ℝ := fun l => ∑ r ∈ Finset.range (S.NN j),
      G (P.fMap (shiftZ^[r] (S.om j l))) with hAdef
    have hdecomp : ∑ u ∈ Finset.range p, f (S.T j + u)
        = (∑ l ∈ Finset.range q, ∑ r ∈ Finset.range (S.NN j), f (S.T j + S.NN j * l + r))
          + ∑ r ∈ Finset.range s, f (S.T j + S.NN j * q + r) := by
      conv_lhs => rw [← hpq]
      rw [Finset.sum_range_add, sum_range_mul]
      congr 1
      · exact Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun r _ => by congr 1; omega
      · exact Finset.sum_congr rfl fun r _ => by congr 1; omega
    -- the three pieces
    have hpiece1 : |∑ l ∈ Finset.range q,
        ((∑ r ∈ Finset.range (S.NN j), f (S.T j + S.NN j * l + r)) - A l)|
          ≤ (q : ℝ) * ((S.NN j : ℝ) * η + (2 * R + 2) * (2 * ‖G‖)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _
        ((S.NN j : ℝ) * η + (2 * R + 2) * (2 * ‖G‖)) fun l hl => ?_) ?_
      · have hlAA : l < S.AA j := lt_of_lt_of_le (Finset.mem_range.mp hl) hqAA
        have hat := P.atom_estimate S G hlAA hR hNN hwin hmod hη
        rwa [Finset.sum_sub_distrib] at hat
      · rw [Finset.card_range, nsmul_eq_mul]
    have hpiece2 : |(∑ l ∈ Finset.range q, A l) - (q : ℝ) * ((S.NN j : ℝ) * c)|
        ≤ (S.NN j : ℝ) * (δ' * q) := by
      have hid : (S.NN j : ℝ) * ∑ l ∈ Finset.range q, ((S.NN j : ℝ)⁻¹ * A l - c)
          = (∑ l ∈ Finset.range q, A l) - (q : ℝ) * ((S.NN j : ℝ) * c) := by
        rw [Finset.mul_sum]
        have hterm : ∀ l : ℕ, (S.NN j : ℝ) * ((S.NN j : ℝ)⁻¹ * A l - c)
            = A l - (S.NN j : ℝ) * c := by
          intro l; field_simp
        rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← hid, abs_mul, abs_of_nonneg hNN0.le]
      exact mul_le_mul_of_nonneg_left (hgre q hqQ) hNN0.le
    have hpiece3 : |(∑ r ∈ Finset.range s, f (S.T j + S.NN j * q + r)) - (s : ℝ) * c|
        ≤ (s : ℝ) * (2 * ‖G‖) := htriv (S.T j + S.NN j * q) s
    -- put them together
    have hpc : (p : ℝ) = (S.NN j : ℝ) * q + s := by exact_mod_cast hpq.symm
    have hsum : (∑ u ∈ Finset.range p, f (S.T j + u)) - (p : ℝ) * c
        = (∑ l ∈ Finset.range q,
            ((∑ r ∈ Finset.range (S.NN j), f (S.T j + S.NN j * l + r)) - A l))
          + ((∑ l ∈ Finset.range q, A l) - (q : ℝ) * ((S.NN j : ℝ) * c))
          + ((∑ r ∈ Finset.range s, f (S.T j + S.NN j * q + r)) - (s : ℝ) * c) := by
      rw [hdecomp, Finset.sum_sub_distrib, hpc]; ring
    have habs : |(∑ u ∈ Finset.range p, f (S.T j + u)) - (p : ℝ) * c|
        ≤ (q : ℝ) * ((S.NN j : ℝ) * η + (2 * R + 2) * (2 * ‖G‖))
          + (S.NN j : ℝ) * (δ' * q) + (s : ℝ) * (2 * ‖G‖) := by
      rw [hsum]
      calc |_ + _ + _| ≤ |_ + _| + |(∑ r ∈ Finset.range s,
              f (S.T j + S.NN j * q + r)) - (s : ℝ) * c| := abs_add_le _ _
        _ ≤ (|∑ l ∈ Finset.range q,
              ((∑ r ∈ Finset.range (S.NN j), f (S.T j + S.NN j * l + r)) - A l)|
              + |(∑ l ∈ Finset.range q, A l) - (q : ℝ) * ((S.NN j : ℝ) * c)|)
            + |(∑ r ∈ Finset.range s, f (S.T j + S.NN j * q + r)) - (s : ℝ) * c| := by
              gcongr; exact abs_add_le _ _
        _ ≤ _ := by gcongr
    -- arithmetic
    have hNNq : (S.NN j : ℝ) * q ≤ (p : ℝ) := by
      have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
      linarith
    have hsNN : (s : ℝ) ≤ (S.NN j : ℝ) := by
      have hlt : s < S.NN j := Nat.mod_lt _ hNNpos
      exact_mod_cast hlt.le
    have ha1 : (q : ℝ) * ((S.NN j : ℝ) * η + (2 * R + 2) * (2 * ‖G‖))
        ≤ (p : ℝ) * (η + δ₀) := by
      have h1 : (q : ℝ) * ((S.NN j : ℝ) * η + (2 * R + 2) * (2 * ‖G‖))
          ≤ (q : ℝ) * ((S.NN j : ℝ) * η + δ₀ * (S.NN j : ℝ)) := by
        have := Nat.cast_nonneg (α := ℝ) q
        nlinarith
      have h2 : (q : ℝ) * ((S.NN j : ℝ) * η + δ₀ * (S.NN j : ℝ))
          = ((S.NN j : ℝ) * q) * (η + δ₀) := by ring
      have h3 : ((S.NN j : ℝ) * q) * (η + δ₀) ≤ (p : ℝ) * (η + δ₀) :=
        mul_le_mul_of_nonneg_right hNNq (by linarith)
      linarith
    have ha2 : (S.NN j : ℝ) * (δ' * q) ≤ (p : ℝ) * δ' := by
      have : (S.NN j : ℝ) * (δ' * q) = ((S.NN j : ℝ) * q) * δ' := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hNNq hδ'
    have ha3 : (s : ℝ) * (2 * ‖G‖) ≤ K := by
      refine le_trans ?_ hK
      have h1 : (s : ℝ) * (2 * ‖G‖) ≤ (S.NN j : ℝ) * (2 * ‖G‖) :=
        mul_le_mul_of_nonneg_right hsNN (by linarith)
      have h2 : (S.NN j : ℝ) * (2 * ‖G‖) ≤ (S.NN j : ℝ) * ((Q : ℝ) + 1) * (2 * ‖G‖) := by
        have h3 : (S.NN j : ℝ) ≤ (S.NN j : ℝ) * ((Q : ℝ) + 1) := by nlinarith
        exact mul_le_mul_of_nonneg_right h3 (by linarith)
      linarith
    have ha4 : (p : ℝ) * (η + δ₀) + (p : ℝ) * δ' ≤ (p : ℝ) * δ := by
      have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      nlinarith
    linarith

end QuadSetup

/-! ## From the stage estimate to the limit -/

namespace StageData

variable (S : StageData)

/-- Telescoping the stage estimates over the completed stages. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_sum_T_sub (f : ℕ → ℝ) (c : ℝ) (EE : ℕ → ℝ)
    (h : ∀ j, |(∑ u ∈ Finset.range (S.stgLen j), f (S.T j + u)) - (S.stgLen j : ℝ) * c| ≤ EE j)
    (J : ℕ) :
    |(∑ n ∈ Finset.range (S.T J), f n) - (S.T J : ℝ) * c| ≤ ∑ j ∈ Finset.range J, EE j := by
  induction J with
  | zero => simp [T_zero]
  | succ J ih =>
    have hTs : S.T (J + 1) = S.T J + S.stgLen J := S.T_succ J
    have hs : (∑ n ∈ Finset.range (S.T (J + 1)), f n)
        = (∑ n ∈ Finset.range (S.T J), f n)
          + ∑ u ∈ Finset.range (S.stgLen J), f (S.T J + u) := by
      rw [hTs, Finset.sum_range_add]
    have hcc : (S.T (J + 1) : ℝ) * c = (S.T J : ℝ) * c + (S.stgLen J : ℝ) * c := by
      rw [hTs]; push_cast; ring
    rw [Finset.sum_range_succ, hs, hcc]
    have hrw : (∑ n ∈ Finset.range (S.T J), f n) + (∑ u ∈ Finset.range (S.stgLen J),
          f (S.T J + u)) - ((S.T J : ℝ) * c + (S.stgLen J : ℝ) * c)
        = ((∑ n ∈ Finset.range (S.T J), f n) - (S.T J : ℝ) * c)
          + ((∑ u ∈ Finset.range (S.stgLen J), f (S.T J + u)) - (S.stgLen J : ℝ) * c) := by
      ring
    rw [hrw]
    exact le_trans (abs_add_le _ _) (add_le_add ih (h J))

/-- **The Toeplitz step.**  If every prefix of every stage has its observable average within
`dd j` of `c` up to an additive `KK j`, with `dd j → 0` and the `KK` negligible against the
position of the stage, then the running average converges to `c`.

The intermediate `N` costs nothing: an incomplete stage contributes at most `p * dd J + KK J`,
which the very same bound covers. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_avg_of_stage (f : ℕ → ℝ) (c : ℝ) (dd KK : ℕ → ℝ)
    (hdd : ∀ j, 0 ≤ dd j) (hKK : ∀ j, 0 ≤ KK j)
    (hstage : ∀ j p, p ≤ S.stgLen j →
      |(∑ u ∈ Finset.range p, f (S.T j + u)) - (p : ℝ) * c| ≤ (p : ℝ) * dd j + KK j)
    (hlim : Tendsto dd atTop (𝓝 0))
    (hsmall : ∀ J : ℕ, 1 ≤ J →
      ((J : ℝ) + 1) * (∑ j ∈ Finset.range (J + 1), KK j) ≤ (S.T J : ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / (N : ℝ)) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- a tail on which `dd` is small
  obtain ⟨j₁, hj₁⟩ := Metric.tendsto_atTop.mp hlim (ε / 8) (by linarith)
  set j₀ := max 1 j₁ with hj₀def
  have hj₀ : ∀ j, j₀ ≤ j → dd j ≤ ε / 8 := by
    intro j hj
    have h := hj₁ j (le_trans (le_max_right 1 j₁) hj)
    rw [Real.dist_eq, sub_zero] at h
    exact le_trans (le_abs_self _) h.le
  set B := ∑ j ∈ Finset.range j₀, (S.stgLen j : ℝ) * dd j with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hdd j)
  -- a stage index beyond which the additive errors are negligible
  obtain ⟨J₁, hJ₁⟩ := exists_nat_gt (16 / ε)
  set Jstar := max j₀ (max 1 J₁) with hJstardef
  set N₀ := max (S.T Jstar) (max 1 ⌈8 * B / ε⌉₊) with hN₀def
  refine ⟨N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_left 1 _) (le_max_right (S.T Jstar) _)) hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hBN : B ≤ ε / 8 * (N : ℝ) := by
    have h1 : (⌈8 * B / ε⌉₊ : ℝ) ≤ (N : ℝ) := by
      have : ⌈8 * B / ε⌉₊ ≤ N :=
        le_trans (le_trans (le_max_right 1 _) (le_max_right (S.T Jstar) _)) hN
      exact_mod_cast this
    have h2 : 8 * B / ε ≤ (N : ℝ) := le_trans (Nat.le_ceil _) h1
    rw [div_le_iff₀ hε] at h2
    linarith
  set J := S.stg N with hJdef
  have hTJ : S.T J ≤ N := S.T_stg_le N
  have hNT : N < S.T (J + 1) := S.lt_T_stg_succ N
  have hJstar : Jstar ≤ J := by
    have h1 : S.T Jstar ≤ N := le_trans (le_max_left _ _) hN
    have h2 : S.T Jstar < S.T (J + 1) := lt_of_le_of_lt h1 hNT
    have := S.T_strictMono.lt_iff_lt.mp h2
    omega
  have hJ1 : 1 ≤ J := le_trans (le_trans (le_max_left 1 J₁) (le_max_right j₀ _)) hJstar
  have hj₀J : j₀ ≤ J := le_trans (le_max_left _ _) hJstar
  -- the split at `T J`
  set p := N - S.T J with hpdef
  have hp : p ≤ S.stgLen J := by have := S.T_succ J; omega
  have hNsplit : (∑ n ∈ Finset.range N, f n)
      = (∑ n ∈ Finset.range (S.T J), f n) + ∑ u ∈ Finset.range p, f (S.T J + u) := by
    have hNe : N = S.T J + p := by omega
    conv_lhs => rw [hNe]
    rw [Finset.sum_range_add]
  have hNcast : (N : ℝ) = (S.T J : ℝ) + (p : ℝ) := by
    have hNe : N = S.T J + p := by omega
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) hNe
  -- the completed stages
  have htot := S.abs_sum_T_sub f c (fun j => (S.stgLen j : ℝ) * dd j + KK j)
    (fun j => hstage j (S.stgLen j) le_rfl) J
  rw [Finset.sum_add_distrib] at htot
  -- the Toeplitz bound on the `dd` part
  have hTJR : (∑ j ∈ Finset.range J, (S.stgLen j : ℝ)) = (S.T J : ℝ) := by
    have h := S.sum_stgLen J
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) h
  have hdda : ∑ j ∈ Finset.range J, (S.stgLen j : ℝ) * dd j ≤ B + ε / 8 * (S.T J : ℝ) := by
    have hsp : ∑ j ∈ Finset.range J, (S.stgLen j : ℝ) * dd j
        = (∑ j ∈ Finset.Ico 0 j₀, (S.stgLen j : ℝ) * dd j)
          + ∑ j ∈ Finset.Ico j₀ J, (S.stgLen j : ℝ) * dd j := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le j₀) hj₀J]
    have htail : ∑ j ∈ Finset.Ico j₀ J, (S.stgLen j : ℝ) * dd j
        ≤ ε / 8 * (S.T J : ℝ) := by
      have h1 : ∑ j ∈ Finset.Ico j₀ J, (S.stgLen j : ℝ) * dd j
          ≤ ∑ j ∈ Finset.Ico j₀ J, (S.stgLen j : ℝ) * (ε / 8) :=
        Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left (hj₀ j (Finset.mem_Ico.mp hj).1) (Nat.cast_nonneg _)
      have h2 : ∑ j ∈ Finset.Ico j₀ J, (S.stgLen j : ℝ)
          ≤ ∑ j ∈ Finset.range J, (S.stgLen j : ℝ) := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl) fun _ _ _ => Nat.cast_nonneg _
      rw [← Finset.sum_mul] at h1
      have h3 : (∑ j ∈ Finset.Ico j₀ J, (S.stgLen j : ℝ)) * (ε / 8) ≤ (S.T J : ℝ) * (ε / 8) := by
        rw [← hTJR]
        exact mul_le_mul_of_nonneg_right h2 (by linarith)
      linarith
    have hhead : (∑ j ∈ Finset.Ico 0 j₀, (S.stgLen j : ℝ) * dd j) = B := by
      rw [hBdef, Finset.range_eq_Ico]
    rw [hsp, hhead]
    linarith
  -- the additive part
  have hJR : (16 : ℝ) / ε < (J : ℝ) + 1 := by
    have : (J₁ : ℝ) ≤ (J : ℝ) := by
      have : J₁ ≤ J := le_trans (le_trans (le_max_right 1 J₁) (le_max_right j₀ _)) hJstar
      exact_mod_cast this
    linarith
  set SK := (∑ j ∈ Finset.range J, KK j) + KK J with hSKdef
  have hSK0 : 0 ≤ SK := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range J) => hKK j)
    have := hKK J
    linarith
  have hSKle : ((J : ℝ) + 1) * SK ≤ (N : ℝ) := by
    have h1 : SK = ∑ j ∈ Finset.range (J + 1), KK j := by rw [hSKdef, Finset.sum_range_succ]
    have h2 := hsmall J hJ1
    rw [← h1] at h2
    have h3 : (S.T J : ℝ) ≤ (N : ℝ) := by exact_mod_cast hTJ
    linarith
  have hSKsmall : SK ≤ ε / 8 * (N : ℝ) := by
    have h1 : SK * (16 / ε) ≤ SK * ((J : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left hJR.le hSK0
    have h2 : SK * ((J : ℝ) + 1) ≤ (N : ℝ) := by linarith [hSKle]
    have h3 : SK * (16 / ε) ≤ (N : ℝ) := le_trans h1 h2
    rw [mul_div_assoc'] at h3
    rw [div_le_iff₀ hε] at h3
    linarith
  -- the incomplete stage
  have hpartial := hstage J p hp
  have hpN : (p : ℝ) ≤ (N : ℝ) := by
    have : p ≤ N := by omega
    exact_mod_cast this
  have hpdd : (p : ℝ) * dd J ≤ ε / 8 * (N : ℝ) := by
    have h1 : (p : ℝ) * dd J ≤ (p : ℝ) * (ε / 8) :=
      mul_le_mul_of_nonneg_left (hj₀ J hj₀J) (Nat.cast_nonneg _)
    have h2 : (p : ℝ) * (ε / 8) ≤ (N : ℝ) * (ε / 8) :=
      mul_le_mul_of_nonneg_right hpN (by linarith)
    linarith
  -- assemble
  have hTJN : (S.T J : ℝ) ≤ (N : ℝ) := by exact_mod_cast hTJ
  have hfinal : |(∑ n ∈ Finset.range N, f n) - (N : ℝ) * c| ≤ ε / 2 * (N : ℝ) := by
    have hrw : (∑ n ∈ Finset.range N, f n) - (N : ℝ) * c
        = ((∑ n ∈ Finset.range (S.T J), f n) - (S.T J : ℝ) * c)
          + ((∑ u ∈ Finset.range p, f (S.T J + u)) - (p : ℝ) * c) := by
      rw [hNsplit, hNcast]; ring
    rw [hrw]
    refine le_trans (abs_add_le _ _) ?_
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range J, KK j :=
      Finset.sum_nonneg fun j _ => hKK j
    have hKKJ : 0 ≤ KK J := hKK J
    have hstep : ε / 8 * (S.T J : ℝ) ≤ ε / 8 * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hTJN (by linarith)
    linarith [htot, hpartial, hdda, hSKsmall, hpdd]
  rw [Real.dist_eq]
  have hdiv : (∑ n ∈ Finset.range N, f n) / (N : ℝ) - c
      = ((∑ n ∈ Finset.range N, f n) - (N : ℝ) * c) / (N : ℝ) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hNR, div_lt_iff₀ hNR]
  calc |(∑ n ∈ Finset.range N, f n) - (N : ℝ) * c| ≤ ε / 2 * (N : ℝ) := hfinal
    _ < ε * (N : ℝ) := by nlinarith

end StageData

/-! ## The construction -/

namespace QuadSetup

variable (P : QuadSetup)

/-- **The staged word of an invariant measure.**  For an invariant `μ` and any countable
family of test functions on `𝕋` there is a staged word whose orbit averages converge to the
`μ`-means of the pullbacks, simultaneously in all test functions.

The stage parameters are all determined by the stage index alone, so no recursion is needed:
stage `j` works with the first `j+1` test functions at accuracy `1/(j+1)`, split evenly
between the modulus of continuity (`η`), the greedy sampling error (`δ'`) and the window
boundary of each atom (`δ₀`).  The number of atoms `AA j` is then chosen large enough that the
additive errors of all stages up to `j+1` are negligible against the position `T (j+1)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_word_of_invariant {μ : Measure Shift} [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ) (ψ : ℕ → AddCircle (1 : ℝ) →ᵇ ℝ) :
    ∃ S : StageData, ∀ i : ℕ, Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N, ψ i (P.fMap (shiftZ^[n] (padZ S.word)))) / (N : ℝ))
      atTop (𝓝 (∫ ω, ψ i (P.fMap ω) ∂μ)) := by
  classical
  set c : ℕ → ℝ := fun i => ∫ ω, ψ i (P.fMap ω) ∂μ with hcdef
  have hcbd : ∀ i, |c i| ≤ ‖ψ i‖ := by
    intro i
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => ψ i (P.fMap ω))
      (C := ‖ψ i‖) (Eventually.of_forall fun ω => (ψ i).norm_coe_le_norm _)
    simpa [hcdef, Real.norm_eq_abs] using h
  set Cb : ℕ → ℝ := fun j => 2 * (1 + ∑ i ∈ Finset.range (j + 1), ‖ψ i‖) with hCbdef
  have hCbpos : ∀ j, 0 < Cb j := by
    intro j
    have h : (0 : ℝ) ≤ ∑ i ∈ Finset.range (j + 1), ‖ψ i‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    rw [hCbdef]; simp only; linarith
  have hCbψ : ∀ j i, i ≤ j → 2 * ‖ψ i‖ ≤ Cb j := by
    intro j i hij
    have h1 : ‖ψ i‖ ≤ ∑ i' ∈ Finset.range (j + 1), ‖ψ i'‖ :=
      Finset.single_le_sum (f := fun i' => ‖ψ i'‖) (fun i' _ => norm_nonneg _)
        (Finset.mem_range.mpr (by omega))
    rw [hCbdef]; simp only; linarith
  -- stage parameters
  have hmodex : ∀ j : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, i ≤ j → ∀ x y : ℝ, |x - y| ≤ ρ →
      |ψ i ((x : ℝ) : AddCircle (1 : ℝ)) - ψ i ((y : ℝ) : AddCircle (1 : ℝ))|
        ≤ 1 / (3 * ((j : ℝ) + 1)) := fun j => exists_common_modulus ψ j (by positivity)
  choose ρ hρ0 hρ using hmodex
  have hwinex : ∀ j : ℕ, ∃ R : ℕ, 1 ≤ R ∧ P.winErr R ≤ ρ j := fun j => P.exists_window (hρ0 j)
  choose R hR1 hR2 using hwinex
  set NN : ℕ → ℕ := fun j =>
    max (2 * R j + 2) ⌈3 * ((j : ℝ) + 1) * (2 * (R j : ℝ) + 2) * (2 * Cb j)⌉₊ with hNNdef
  have hNN2R : ∀ j, 2 * R j + 2 ≤ NN j := fun j => le_max_left _ _
  have hNNpos : ∀ j, 0 < NN j := fun j => lt_of_lt_of_le (by omega) (hNN2R j)
  have hNNbig : ∀ j : ℕ, 3 * ((j : ℝ) + 1) * (2 * (R j : ℝ) + 2) * (2 * Cb j) ≤ (NN j : ℝ) := by
    intro j
    have hle : ⌈3 * ((j : ℝ) + 1) * (2 * (R j : ℝ) + 2) * (2 * Cb j)⌉₊ ≤ NN j :=
      le_max_right _ _
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hle)
  set Q : ℕ → ℕ := fun j => ⌈((j : ℝ) + 1) * (Cb j) ^ 2 * (3 * ((j : ℝ) + 1)) ^ 2⌉₊ with hQdef
  set KKv : ℕ → ℝ := fun j => (NN j : ℝ) * ((Q j : ℝ) + 1) * (2 * Cb j) with hKKdef
  have hKK0 : ∀ j, 0 ≤ KKv j := by
    intro j
    have h1 : (0 : ℝ) ≤ (NN j : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (Q j : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) ≤ 2 * Cb j := by linarith [hCbpos j]
    rw [hKKdef]; simp only
    exact mul_nonneg (mul_nonneg h1 h2) h3
  set Kn : ℕ → ℕ := fun j => ⌈KKv j⌉₊ with hKndef
  set AA : ℕ → ℕ := fun j => max 1 ((j + 2) * ∑ j' ∈ Finset.range (j + 2), Kn j') with hAAdef
  have hAApos : ∀ j, 0 < AA j := fun j => lt_of_lt_of_le one_pos (le_max_left _ _)
  -- the greedy samples
  have hgreedy : ∀ j : ℕ, ∃ om : ℕ → Shift, ∀ q : ℕ, Q j ≤ q → ∀ i, i < j + 1 →
      |∑ l ∈ Finset.range q, ((NN j : ℝ)⁻¹ *
        (∑ r ∈ Finset.range (NN j), ψ i (P.fMap (shiftZ^[r] (om l)))) - c i)|
        ≤ 1 / (3 * ((j : ℝ) + 1)) * (q : ℝ) := by
    intro j
    set g : ℕ → Shift →ᵇ ℝ := fun i =>
      P.orbAvg (ψ i) (NN j) - BoundedContinuousFunction.const Shift (c i) with hgdef
    have hgapp : ∀ i ω, g i ω = (NN j : ℝ)⁻¹ *
        (∑ r ∈ Finset.range (NN j), ψ i (P.fMap (shiftZ^[r] ω))) - c i := by
      intro i ω
      rw [hgdef]
      simp [P.orbAvg_apply]
    have hCbg : ∀ i, i < j + 1 → ‖g i‖ ≤ Cb j := by
      intro i hi
      rw [BoundedContinuousFunction.norm_le (le_of_lt (hCbpos j))]
      intro ω
      have h1 : |P.orbAvg (ψ i) (NN j) ω| ≤ ‖ψ i‖ := P.abs_orbAvg_le (ψ i) (hNNpos j) ω
      have h2 : |c i| ≤ ‖ψ i‖ := hcbd i
      have h3 : 2 * ‖ψ i‖ ≤ Cb j := hCbψ j i (by omega)
      rw [Real.norm_eq_abs, hgdef]
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply]
      calc |P.orbAvg (ψ i) (NN j) ω - c i| ≤ |P.orbAvg (ψ i) (NN j) ω| + |c i| := abs_sub _ _
        _ ≤ Cb j := by linarith
    have hmeang : ∀ i, i < j + 1 → ∫ x, g i x ∂μ = 0 := by
      intro i _
      have h1 : ∫ ω, P.orbAvg (ψ i) (NN j) ω ∂μ = c i :=
        P.integral_orbAvg hinv (ψ i) (hNNpos j)
      rw [hgdef]
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply]
      rw [integral_sub ((P.orbAvg (ψ i) (NN j)).integrable μ) (integrable_const _), h1,
        integral_const]
      simp
    obtain ⟨om, hom⟩ := exists_greedy_le μ (j + 1) g (Cb j) (1 / (3 * ((j : ℝ) + 1)))
      (by positivity) hCbg hmeang
    refine ⟨om, fun q hq i hi => ?_⟩
    have hthr : ((j + 1 : ℕ) : ℝ) * (Cb j) ^ 2 ≤ (1 / (3 * ((j : ℝ) + 1))) ^ 2 * (q : ℝ) := by
      have hqR : ((j : ℝ) + 1) * (Cb j) ^ 2 * (3 * ((j : ℝ) + 1)) ^ 2 ≤ (q : ℝ) := by
        refine le_trans (Nat.le_ceil _) ?_
        have : (Q j : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        rw [hQdef] at this
        exact this
      have hden : (0 : ℝ) < (3 * ((j : ℝ) + 1)) ^ 2 := by positivity
      have heq : (1 / (3 * ((j : ℝ) + 1))) ^ 2 * (q : ℝ) = (q : ℝ) / (3 * ((j : ℝ) + 1)) ^ 2 := by
        field_simp
      rw [heq, le_div_iff₀ hden]
      push_cast
      linarith
    have h := hom q hthr i hi
    simpa only [hgapp] using h
  choose om hom using hgreedy
  set S : StageData := ⟨NN, AA, om, hNNpos, hAApos⟩ with hSdef
  refine ⟨S, fun i => ?_⟩
  set dd : ℕ → ℝ := fun j => if j < i then 2 * ‖ψ i‖ + 1 else 1 / ((j : ℝ) + 1) with hdddef
  have hψbd : ∀ n : ℕ, |ψ i (P.fMap (shiftZ^[n] (padZ S.word)))| ≤ ‖ψ i‖ := fun n => by
    simpa [Real.norm_eq_abs] using (ψ i).norm_coe_le_norm (P.fMap (shiftZ^[n] (padZ S.word)))
  refine S.tendsto_avg_of_stage (fun n => ψ i (P.fMap (shiftZ^[n] (padZ S.word)))) (c i)
    dd KKv ?_ hKK0 ?_ ?_ ?_
  · -- `dd` is nonnegative
    intro j
    simp only [hdddef]
    split_ifs with h
    · positivity
    · positivity
  · -- the stage estimate
    intro j p hp
    by_cases hji : j < i
    · have htriv := abs_sum_sub_le_of_bdd
        (fun n => ψ i (P.fMap (shiftZ^[n] (padZ S.word)))) (c i) ‖ψ i‖ hψbd (hcbd i) (S.T j) p
      have hddj : dd j = 2 * ‖ψ i‖ + 1 := by
        simp only [hdddef]; split_ifs; rfl
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      have h1 : (p : ℝ) * (2 * ‖ψ i‖) ≤ (p : ℝ) * dd j := by
        rw [hddj]; nlinarith
      linarith [hKK0 j]
    · have hij : i ≤ j := by omega
      have hddj : dd j = 1 / ((j : ℝ) + 1) := by
        simp only [hdddef]; split_ifs; rfl
      rw [hddj]
      refine P.stage_estimate S (ψ i) (R := R j) (Q := Q j) (ρ := ρ j)
        (η := 1 / (3 * ((j : ℝ) + 1))) (δ' := 1 / (3 * ((j : ℝ) + 1)))
        (δ₀ := 1 / (3 * ((j : ℝ) + 1))) (hR1 j) (hNN2R j) (hR2 j) (hρ j i hij)
        (by positivity) (by positivity) (by positivity) (hcbd i) hp
        (fun q hq => hom j q hq i (by omega)) ?_ ?_ ?_
      · -- the window boundary
        have h1 : 2 * ‖ψ i‖ ≤ 2 * Cb j := by linarith [hCbψ j i hij, hCbpos j]
        have h2 : (0 : ℝ) ≤ 2 * (R j : ℝ) + 2 := by positivity
        have hpos : (0 : ℝ) < 3 * ((j : ℝ) + 1) := by positivity
        have key : (2 * (R j : ℝ) + 2) * (2 * ‖ψ i‖) * (3 * ((j : ℝ) + 1)) ≤ (NN j : ℝ) := by
          have hfac : (0 : ℝ) ≤ (2 * (R j : ℝ) + 2) * (3 * ((j : ℝ) + 1)) :=
            mul_nonneg h2 hpos.le
          have hstep := mul_le_mul_of_nonneg_left h1 hfac
          nlinarith [hstep, hNNbig j]
        calc (2 * (R j : ℝ) + 2) * (2 * ‖ψ i‖)
            = ((2 * (R j : ℝ) + 2) * (2 * ‖ψ i‖) * (3 * ((j : ℝ) + 1))) / (3 * ((j : ℝ) + 1)) := by
              field_simp
          _ ≤ (NN j : ℝ) / (3 * ((j : ℝ) + 1)) := by gcongr
          _ = 1 / (3 * ((j : ℝ) + 1)) * (NN j : ℝ) := by ring
      · -- the three thirds
        have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have heq : 1 / (3 * ((j : ℝ) + 1)) + 1 / (3 * ((j : ℝ) + 1)) + 1 / (3 * ((j : ℝ) + 1))
            = 1 / ((j : ℝ) + 1) := by field_simp; ring
        rw [heq]
      · -- the additive error
        have h1 : 2 * ‖ψ i‖ ≤ 2 * Cb j := by linarith [hCbψ j i hij, hCbpos j]
        have h2 : (0 : ℝ) ≤ (NN j : ℝ) * ((Q j : ℝ) + 1) := by positivity
        rw [hKKdef]
        simp only
        nlinarith
  · -- `dd → 0`
    have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop i] with j hj
    simp only [hdddef]
    split_ifs with h
    · omega
    · rfl
  · -- the additive errors are negligible
    intro J hJ
    obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    have hT : S.T (J' + 1) = S.T J' + AA J' * NN J' := S.T_succ J'
    have h1 : (AA J' : ℝ) ≤ (S.T (J' + 1) : ℝ) := by
      have hle : AA J' ≤ S.T (J' + 1) := by
        have h := Nat.le_mul_of_pos_right (AA J') (hNNpos J')
        omega
      exact_mod_cast hle
    have h2 : (((J' + 2) * ∑ j' ∈ Finset.range (J' + 2), Kn j' : ℕ) : ℝ) ≤ (AA J' : ℝ) := by
      have : (J' + 2) * ∑ j' ∈ Finset.range (J' + 2), Kn j' ≤ AA J' := le_max_right _ _
      exact_mod_cast this
    have h3 : ∑ j' ∈ Finset.range (J' + 2), KKv j' ≤ ∑ j' ∈ Finset.range (J' + 2), (Kn j' : ℝ) :=
      Finset.sum_le_sum fun j' _ => Nat.le_ceil _
    have h4 : (0 : ℝ) ≤ ((J' : ℝ) + 2) := by positivity
    have h5 : (((J' + 1 : ℕ) : ℝ) + 1) = ((J' : ℝ) + 2) := by push_cast; ring
    rw [h5]
    have h6 : ((J' : ℝ) + 2) * ∑ j' ∈ Finset.range (J' + 2), KKv j'
        ≤ ((J' : ℝ) + 2) * ∑ j' ∈ Finset.range (J' + 2), (Kn j' : ℝ) := by
      exact mul_le_mul_of_nonneg_left h3 h4
    have h7 : ((J' : ℝ) + 2) * ∑ j' ∈ Finset.range (J' + 2), (Kn j' : ℝ)
        = (((J' + 2) * ∑ j' ∈ Finset.range (J' + 2), Kn j' : ℕ) : ℝ) := by
      push_cast; ring
    linarith

/-! ## Proposition 8(ii) and Corollary 9 -/

/-- **M1 Proposition 8(ii), saturation.**  For **every** `σ`-invariant Borel probability
measure `μ` on `{0,1}^ℤ` — ergodic or not — there is a point `ξ ∈ C(α)` whose orbit realizes
`F_*μ`: the empirical measures `λ_N` of `({ξ αⁿ})_{n ≤ N}` converge weak-\* to `F_*μ`.

This is the note's saturation of the full shift, proved here without any ergodic theorem:
invariance makes the target an *exact* mean of window averages (`integral_orbAvg`), the greedy
selection of `BB61/MeanSelect.lean` realizes that mean by an equal-weight sample, and the
staged word of `BB61/Words.lean` concatenates the samples. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_tendsto_map_of_invariant (μ : ProbabilityMeasure Shift)
    (hμ : pmap continuous_shiftZ.measurable μ = μ) :
    ∃ ξ ∈ cantorSet P.α,
      Tendsto (fun N => emp (fun n => ((ξ * P.α ^ n : ℝ) : AddCircle (1 : ℝ))) N) atTop
        (𝓝 (pmap P.measurable_fMap μ)) := by
  have hpm : IsProbabilityMeasure (μ : Measure Shift) := μ.2
  have hinv : Measure.map shiftZ (μ : Measure Shift) = (μ : Measure Shift) := by
    have h := congrArg ProbabilityMeasure.toMeasure hμ
    rwa [toMeasure_pmap] at h
  have hsep : SeparableSpace (AddCircle (1 : ℝ) →ᵇ ℝ) := by
    have h := ContinuousMap.isometryEquivBoundedOfCompact (AddCircle (1 : ℝ)) ℝ
    exact h.surjective.denseRange.separableSpace h.continuous
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (AddCircle (1 : ℝ) →ᵇ ℝ)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → AddCircle (1 : ℝ) →ᵇ ℝ, D = Set.range ψ :=
    hDc.exists_eq_range hDd.nonempty
  obtain ⟨S, hS⟩ := P.exists_word_of_invariant hinv ψ
  refine ⟨piVal P.α S.word, ⟨S.word, rfl⟩, ?_⟩
  refine tendsto_of_dense_of_tendsto_integral hDd fun G hG => ?_
  rw [hψ] at hG
  obtain ⟨i, rfl⟩ := hG
  rw [integral_pmap P.continuous_fMap μ (ψ i)]
  have hstep := (hS i).comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def] at hstep
  refine hstep.congr fun N => ?_
  rw [integral_emp]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by rw [P.fMap_iterate_padZ]
  · push_cast; ring

/-- **M1 Corollary 9, the hard half.**  If *some* `σ`-invariant `μ` has `F_*μ = Leb` then
10.61 fails at `α`: some `ξ ∈ C(α)` has `(ξ αⁿ)` uniformly distributed modulo one. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_equidistributed_of_invariant (μ : ProbabilityMeasure Shift)
    (hμ : pmap continuous_shiftZ.measurable μ = μ)
    (hmap : pmap P.measurable_fMap μ = haarT) :
    ∃ ξ ∈ cantorSet P.α, IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨ξ, hξ, h⟩ := P.exists_tendsto_map_of_invariant μ hμ
  rw [hmap] at h
  exact ⟨ξ, hξ, equidistributed_of_tendsto_emp h⟩

/-- **M1 Corollary 9: the master target is an equivalence.**  There is a `ξ ∈ C(α)` with
`(ξ αⁿ)` uniformly distributed modulo one **iff** there is a `σ`-invariant Borel probability
measure `μ` on `{0,1}^ℤ` with `F_*μ = Leb_𝕋`.

So Problem 10.61 at `α` *is* the statement that no invariant measure of the full `2`-shift has
Lebesgue image: nothing is lost in the reduction of `BB61/Invariant.lean`, and a counterexample
to the master target would be a counterexample to 10.61, not merely an obstruction to this
proof strategy. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem equidistributed_iff_exists_invariant :
    (∃ ξ ∈ cantorSet P.α, IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n)
      ↔ ∃ μ : ProbabilityMeasure Shift,
        pmap continuous_shiftZ.measurable μ = μ ∧ pmap P.measurable_fMap μ = haarT := by
  constructor
  · rintro ⟨ξ, hξ, hud⟩
    exact P.exists_invariant_of_equidistributed hξ hud
  · rintro ⟨μ, hinv, hmap⟩
    exact P.exists_equidistributed_of_invariant μ hinv hmap

/-- **M1 Corollary 9, unbundled**, in the shape `BB61/Invariant.lean` states the master
target. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem equidistributed_iff_exists_invariant_measure :
    (∃ ξ ∈ cantorSet P.α, IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n)
      ↔ ∃ μ : Measure Shift, IsProbabilityMeasure μ ∧ Measure.map shiftZ μ = μ ∧
        Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) := by
  constructor
  · rintro ⟨ξ, hξ, hud⟩
    exact P.exists_invariant_measure_of_equidistributed hξ hud
  · rintro ⟨ν, hprob, hinv, hmap⟩
    obtain ⟨μ, hμ⟩ : ∃ μ : ProbabilityMeasure Shift, (μ : Measure Shift) = ν :=
      ⟨⟨ν, hprob⟩, rfl⟩
    refine P.equidistributed_iff_exists_invariant.mpr ⟨μ, ?_, ?_⟩
    · refine ProbabilityMeasure.toMeasure_injective ?_
      rw [toMeasure_pmap, hμ]
      exact hinv
    · refine ProbabilityMeasure.toMeasure_injective ?_
      rw [toMeasure_pmap, toMeasure_haarT, hμ]
      exact hmap

/-- **The master target, sharpened.**  Problem 10.61 holds at `α` *if and only if* no
`σ`-invariant Borel probability measure of the full `2`-shift has `F_*μ = Leb_𝕋`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem forall_not_equidistributed_iff :
    (∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n)
      ↔ ∀ μ : ProbabilityMeasure Shift,
        pmap continuous_shiftZ.measurable μ = μ → pmap P.measurable_fMap μ ≠ haarT := by
  have h := P.equidistributed_iff_exists_invariant
  constructor
  · intro hno μ hinv hmap
    obtain ⟨ξ, hξ, hud⟩ := h.mpr ⟨μ, hinv, hmap⟩
    exact hno ξ hξ hud
  · intro hno ξ hξ hud
    obtain ⟨μ, hinv, hmap⟩ := h.mp ⟨ξ, hξ, hud⟩
    exact hno μ hinv hmap

/-- **M3 Theorem 9, in the note's own form.**  Problem 10.61 holds at `α` — no `ξ ∈ C(α)` has
`(ξ αⁿ)` uniformly distributed modulo one — **if and only if** a finite certificate witnesses
it: a mean-zero real trigonometric polynomial `G` on `𝕋` and a `c > 0` with
`∫ G ∘ F dμ ≥ c` for every `σ`-invariant `μ`.

`BB61/Certificate.lean` proves the equivalence with the *invariant-measure* form of the
hypothesis and notes that the note states it with "10.61 holds at `α`" on the left; passing
between the two is exactly M1 Corollary 9, so this is the form the note claims. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem forall_not_equidistributed_iff_exists_trigCertificate :
    (∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n)
      ↔ ∃ (H : Finset ℤ) (a : ℤ → ℂ) (c : ℝ), (0 : ℤ) ∉ H ∧ 0 < c ∧
        ∫ z, trigPoly H a z ∂(volume : Measure (AddCircle (1 : ℝ))) = 0 ∧
        ∀ μ ∈ invMeasures, c ≤ ∫ ω, trigPoly H a (P.fMap ω) ∂(μ : Measure Shift) :=
  P.forall_not_equidistributed_iff.trans P.exists_trigCertificate_iff.symm

end QuadSetup

end BB61
