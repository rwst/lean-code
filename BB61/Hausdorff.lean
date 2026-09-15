/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.BoxDim
import ForMathlib.MeasureTheory.MassDistribution
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Count
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Lemma 1(iii): the Hausdorff dimension of `C(α)`

`BB61/BoxDim.lean` gives `dim_B C(α) = log 2 / log α` and, through
`Metric.dimH_le_upperBoxDim`, the ceiling `dim_H C(α) ≤ log 2 / log α`.  This file supplies the
matching floor, which completes Lemma 1(iii):

  `dim_H C(α) = dim_B C(α) = log 2 / log α`  for `α > 2`.

Mathlib has no iterated function systems and hence no Hutchinson formula, so the measure that
the mass distribution principle needs has to be built here.  It is the obvious one — the
Bernoulli(1/2) measure of the coding space, pushed forward by `π`:

* `coinMeasure` — `Measure.infinitePi` of the fair coin on `Bool`, with
  `coinMeasure_agreeSet`: a depth-`M` cylinder has mass `2^{-M}`.
* `codingMeasure α` — its image under `piVal α`, a probability measure carried by `C(α)`.
* `preimage_subset_agreeSet` — **strong separation, read backwards**: if a set has diameter
  below `g·α^{-M}` then all its `π`-preimages agree on `[0, M)`, because two words that first
  differ at `k < M` have `π`-values at least `g·α^{-k} ≥ g·α^{-M}` apart
  (`gap_mul_le_abs_piVal_sub`, M1 Lemma 1(iv)).  Hence `codingMeasure α s ≤ 2^{-M}`.
* `codingMeasure_frostman` — choosing `M` as large as that allows turns the estimate into the
  Frostman condition `codingMeasure α s ≤ C · (diam s)^d` with `d = log 2 / log α`, because
  `α^{-d} = 1/2` is exactly what makes the two sides scale alike.
* `le_dimH_cantorSet`, `dimH_cantorSet`, `dimH_eq_upperBoxDim_cantorSet` — the conclusion.

The mass distribution principle itself is
`MeasureTheory.Measure.le_dimH_of_frostman` in `ForMathlib/MeasureTheory/MassDistribution.lean`,
a two-line consequence of Mathlib's `Measure.le_hausdorffMeasure`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M1.html` Lemma 1(iii).
* K. Falconer, *Fractal Geometry*, Ch. 4.1 and Example 4.6.
-/

namespace BB61

open Metric MeasureTheory

open scoped NNReal ENNReal

/-! ## The fair coin measure on `{0,1}^ℕ` -/

/-- The fair coin on `Bool`. -/
noncomputable def coinBool : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure coinBool := by
  constructor
  rw [coinBool, Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  rw [show ((ENat.card Bool : ℕ∞) : ℝ≥0∞) = 2 by simp]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coinBool_singleton (b : Bool) : coinBool {b} = 2⁻¹ := by
  rw [coinBool, Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]

/-- The Bernoulli(1/2) measure on the coding space `{0,1}^ℕ`. -/
noncomputable def coinMeasure : Measure (ℕ → Bool) := Measure.infinitePi fun _ : ℕ => coinBool

instance : IsProbabilityMeasure coinMeasure := by unfold coinMeasure; infer_instance

/-- The depth-`M` cylinder through `e`. -/
def agreeSet (e : ℕ → Bool) (M : ℕ) : Set (ℕ → Bool) := {ε | ∀ i < M, ε i = e i}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem agreeSet_eq_pi (e : ℕ → Bool) (M : ℕ) :
    agreeSet e M = Set.pi (↑(Finset.range M)) (fun i => ({e i} : Set Bool)) := by
  ext ε
  simp [agreeSet, Set.mem_pi]

/-- A depth-`M` cylinder has coin mass `2^{-M}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coinMeasure_agreeSet (e : ℕ → Bool) (M : ℕ) :
    coinMeasure (agreeSet e M) = (2 : ℝ≥0∞)⁻¹ ^ M := by
  rw [agreeSet_eq_pi, coinMeasure,
    Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton (e i))]
  simp [coinBool_singleton, Finset.prod_const, Finset.card_range]

/-! ## The coding measure on `C(α)` -/

section Coding

variable {α : ℝ}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurable_piVal (hα : 1 < α) : Measurable (piVal α) :=
  (continuous_piVal hα).measurable

/-- The natural measure on `C(α)`: the fair coin pushed forward by the coding map. -/
noncomputable def codingMeasure (α : ℝ) : Measure ℝ := coinMeasure.map (piVal α)

/-- `codingMeasure α` is carried by `C(α)`, which therefore has positive mass — the input the
mass distribution principle needs. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem codingMeasure_cantorSet (hα : 1 < α) : codingMeasure α (cantorSet α) = 1 := by
  rw [codingMeasure, Measure.map_apply (measurable_piVal hα)
    (isCompact_cantorSet hα).isClosed.measurableSet,
    show piVal α ⁻¹' cantorSet α = Set.univ from
      Set.eq_univ_of_forall fun ε => ⟨ε, rfl⟩]
  exact measure_univ

/-! ## Strong separation, read backwards -/

/-- **M1 Lemma 1(iv) contrapositive.**  If every two points of `S` are closer than
`g·α^{-M}`, then all `π`-preimages of `S` agree on their first `M` letters: two words that
first differ at `k < M` have `π`-values at least `g·α^{-k} ≥ g·α^{-M}` apart. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem preimage_subset_agreeSet (hα : 1 < α) {S : Set ℝ} {M : ℕ} {e : ℕ → Bool}
    (he : e ∈ piVal α ⁻¹' S)
    (hsep : ∀ y ∈ S, ∀ z ∈ S, |y - z| < gap α * (α⁻¹) ^ M) :
    piVal α ⁻¹' S ⊆ agreeSet e M := by
  classical
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hinv0 : (0 : ℝ) ≤ α⁻¹ := (inv_pos.mpr hα0).le
  have hinv1 : α⁻¹ ≤ 1 := (inv_le_one_iff₀).mpr (Or.inr hα.le)
  have hgpos : 0 < gap α := by
    have h0 : |piVal α e - piVal α e| < gap α * (α⁻¹) ^ M := hsep _ he _ he
    rw [sub_self, abs_zero] at h0
    by_contra hcon
    push Not at hcon
    nlinarith [pow_nonneg hinv0 M]
  intro ε hε
  by_contra hcon
  simp only [agreeSet, Set.mem_ofPred_eq] at hcon
  push Not at hcon
  obtain ⟨i, hiM, hine⟩ := hcon
  have hex : ∃ k, ε k ≠ e k := ⟨i, hine⟩
  have hk : ε (Nat.find hex) ≠ e (Nat.find hex) := Nat.find_spec hex
  have hagree : ∀ j < Nat.find hex, ε j = e j := fun j hj => not_not.mp (Nat.find_min hex hj)
  have hkM : Nat.find hex < M := lt_of_le_of_lt (Nat.find_le hine) hiM
  have hb := gap_mul_le_abs_piVal_sub hα hagree hk
  have hlt := hsep _ hε _ he
  have hmono : gap α * (α⁻¹) ^ M ≤ gap α * (α⁻¹) ^ Nat.find hex :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hinv0 hinv1 hkM.le) hgpos.le
  linarith

/-- The measure of a set of small diameter: at most one depth-`M` cylinder meets its preimage. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem codingMeasure_le_pow_of_sep (hα : 1 < α) {S : Set ℝ} (hS : MeasurableSet S) {M : ℕ}
    (hsep : ∀ y ∈ S, ∀ z ∈ S, |y - z| < gap α * (α⁻¹) ^ M) :
    codingMeasure α S ≤ (2 : ℝ≥0∞)⁻¹ ^ M := by
  rw [codingMeasure, Measure.map_apply (measurable_piVal hα) hS]
  rcases Set.eq_empty_or_nonempty (piVal α ⁻¹' S) with h | ⟨e, he⟩
  · simp [h]
  · calc coinMeasure (piVal α ⁻¹' S) ≤ coinMeasure (agreeSet e M) :=
          measure_mono (preimage_subset_agreeSet hα he hsep)
      _ = (2 : ℝ≥0∞)⁻¹ ^ M := coinMeasure_agreeSet e M

/-- The same bound for an *arbitrary* set, via the closed ball it sits in.  The diameter is
paid for twice, which only moves a constant. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem codingMeasure_le_pow_of_ediam (hα : 1 < α) {s : Set ℝ} (hfin : ediam s ≠ ⊤) {M : ℕ}
    (hM : 2 * (ediam s).toReal < gap α * (α⁻¹) ^ M) :
    codingMeasure α s ≤ (2 : ℝ≥0∞)⁻¹ ^ M := by
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
  · simp
  · have hsub : s ⊆ Metric.closedBall x (ediam s).toReal := by
      intro y hy
      rw [Metric.mem_closedBall, dist_edist]
      exact ENNReal.toReal_mono hfin (Metric.edist_le_ediam_of_mem hy hx)
    refine (measure_mono hsub).trans ?_
    refine codingMeasure_le_pow_of_sep hα measurableSet_closedBall ?_
    intro y hy z hz
    rw [Metric.mem_closedBall, Real.dist_eq] at hy hz
    have : |y - z| ≤ 2 * (ediam s).toReal := by
      have := abs_sub_abs_le_abs_sub y z
      calc |y - z| = |(y - x) - (z - x)| := by ring_nf
        _ ≤ |y - x| + |z - x| := abs_sub _ _
        _ ≤ 2 * (ediam s).toReal := by linarith
    linarith

/-! ## The Frostman estimate -/

/-- `α^{-d} = 1/2` at `d = log 2 / log α`: the exponent at which the `2^{-M}` mass of a
depth-`M` cylinder and its `α^{-M}` diameter march in step.  Everything below is bookkeeping
around this one identity. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_rpow_logRatio (hα : 1 < α) :
    (α⁻¹) ^ (Real.log 2 / Real.log α) = 2⁻¹ := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hlog : Real.log α ≠ 0 := ne_of_gt (Real.log_pos hα)
  rw [Real.rpow_def_of_pos (inv_pos.mpr hα0), Real.log_inv,
    show -Real.log α * (Real.log 2 / Real.log α) = -Real.log 2 by field_simp,
    Real.exp_neg, Real.exp_log two_pos]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_pow_rpow_logRatio (hα : 1 < α) (M : ℕ) :
    ((α⁻¹) ^ M) ^ (Real.log 2 / Real.log α) = ((2 : ℝ)⁻¹) ^ M := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  rw [← Real.rpow_natCast (α⁻¹) M, ← Real.rpow_mul (inv_pos.mpr hα0).le,
    mul_comm (M : ℝ) _, Real.rpow_mul (inv_pos.mpr hα0).le, inv_rpow_logRatio hα,
    Real.rpow_natCast]

/-- **The Frostman condition for `codingMeasure α`** at the exponent `d = log 2 / log α`:
`μ s ≤ (2α/g)^d · (diam s)^d` for every set of diameter at most `g/4`.  Given `s`, the scale
`M` is chosen as large as the separation allows — `2·diam s < g·α^{-M}` but
`g·α^{-(M+1)} ≤ 2·diam s` — and then `α^{-d} = 1/2` converts the cylinder bound `2^{-M}` into
a power of the diameter. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem codingMeasure_frostman (h2 : 2 < α) {s : Set ℝ}
    (hs : ediam s ≤ ENNReal.ofReal (gap α / 4)) :
    codingMeasure α s
      ≤ ENNReal.ofReal ((2 * α / gap α) ^ (Real.log 2 / Real.log α))
        * ediam s ^ (Real.log 2 / Real.log α) := by
  classical
  have hα : (1 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have hg : 0 < gap α := (gap_pos_iff hα0).mpr h2
  have hd0 : 0 < Real.log 2 / Real.log α :=
    div_pos (Real.log_pos one_lt_two) (Real.log_pos hα)
  have hfin : ediam s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  have hδ0 : (0 : ℝ) ≤ (ediam s).toReal := ENNReal.toReal_nonneg
  have hδle : (ediam s).toReal ≤ gap α / 4 := by
    calc (ediam s).toReal ≤ (ENNReal.ofReal (gap α / 4)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
      _ = gap α / 4 := ENNReal.toReal_ofReal (by positivity)
  have hbase : (0 : ℝ) < 2 * α / gap α := div_pos (by linarith) hg
  rcases eq_or_lt_of_le hδ0 with hzero | hpos
  · -- a set of diameter zero is null: the cylinder bound holds at *every* depth
    have hall : ∀ M : ℕ, codingMeasure α s ≤ (2 : ℝ≥0∞)⁻¹ ^ M := fun M =>
      codingMeasure_le_pow_of_ediam hα hfin
        (by rw [← hzero]; simpa using mul_pos hg (pow_pos (inv_pos.mpr hα0) M))
    have hlim : Filter.Tendsto (fun M : ℕ => (2 : ℝ≥0∞)⁻¹ ^ M) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have hzero' : codingMeasure α s = 0 :=
      le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hall)) bot_le
    simp [hzero']
  · -- the scale: the least `N` with `g·α^{-N} ≤ 2·diam s`, and `M = N - 1`
    have hex : ∃ M : ℕ, gap α * (α⁻¹) ^ M ≤ 2 * (ediam s).toReal := by
      obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one
        (show (0 : ℝ) < 2 * (ediam s).toReal / gap α by positivity)
        (show α⁻¹ < 1 from inv_lt_one_of_one_lt₀ hα)
      refine ⟨M, le_of_lt ?_⟩
      calc gap α * (α⁻¹) ^ M < gap α * (2 * (ediam s).toReal / gap α) :=
            mul_lt_mul_of_pos_left hM hg
        _ = 2 * (ediam s).toReal := by field_simp
    have hnot0 : ¬ (gap α * (α⁻¹) ^ 0 ≤ 2 * (ediam s).toReal) := by
      rw [pow_zero, mul_one]
      linarith
    have hN0 : Nat.find hex ≠ 0 := by
      intro h
      have hspec := Nat.find_spec hex
      rw [h] at hspec
      exact hnot0 hspec
    obtain ⟨M, hMN⟩ : ∃ M, Nat.find hex = M + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hMlt : 2 * (ediam s).toReal < gap α * (α⁻¹) ^ M :=
      not_le.mp (Nat.find_min hex (m := M) (by omega))
    have hNspec : gap α * (α⁻¹) ^ (M + 1) ≤ 2 * (ediam s).toReal := by
      rw [← hMN]; exact Nat.find_spec hex
    have hmeas : codingMeasure α s ≤ (2 : ℝ≥0∞)⁻¹ ^ M :=
      codingMeasure_le_pow_of_ediam hα hfin hMlt
    -- the numeric core, in `ℝ`
    have hinvα : α⁻¹ * α = 1 := inv_mul_cancel₀ (ne_of_gt hα0)
    have hApos : (0 : ℝ) < (α⁻¹) ^ M := pow_pos (inv_pos.mpr hα0) M
    have hc : (0 : ℝ) < gap α / (2 * α) := div_pos hg (by linarith)
    have hstep : gap α * (α⁻¹) ^ M ≤ 2 * α * (ediam s).toReal := by
      have h1 : gap α * ((α⁻¹) ^ M * α⁻¹) ≤ 2 * (ediam s).toReal := by
        rw [← pow_succ]; exact hNspec
      have hL : gap α * ((α⁻¹) ^ M * α⁻¹) * α = gap α * (α⁻¹) ^ M := by
        rw [mul_assoc, mul_assoc, hinvα, mul_one]
      linarith [mul_le_mul_of_nonneg_right h1 hα0.le]
    have hlow : gap α / (2 * α) * (α⁻¹) ^ M ≤ (ediam s).toReal := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      linarith
    have hrpow : (gap α / (2 * α)) ^ (Real.log 2 / Real.log α) * ((2 : ℝ)⁻¹) ^ M
        ≤ (ediam s).toReal ^ (Real.log 2 / Real.log α) := by
      calc (gap α / (2 * α)) ^ (Real.log 2 / Real.log α) * ((2 : ℝ)⁻¹) ^ M
          = (gap α / (2 * α)) ^ (Real.log 2 / Real.log α)
              * ((α⁻¹) ^ M) ^ (Real.log 2 / Real.log α) := by rw [inv_pow_rpow_logRatio hα]
        _ = (gap α / (2 * α) * (α⁻¹) ^ M) ^ (Real.log 2 / Real.log α) :=
            (Real.mul_rpow hc.le hApos.le).symm
        _ ≤ (ediam s).toReal ^ (Real.log 2 / Real.log α) :=
            Real.rpow_le_rpow (mul_nonneg hc.le hApos.le) hlow hd0.le
    have hfinal : ((2 : ℝ)⁻¹) ^ M
        ≤ (2 * α / gap α) ^ (Real.log 2 / Real.log α)
          * (ediam s).toReal ^ (Real.log 2 / Real.log α) := by
      have hcd : (0 : ℝ) < (gap α / (2 * α)) ^ (Real.log 2 / Real.log α) :=
        Real.rpow_pos_of_pos hc _
      have hinvc : (2 * α / gap α) ^ (Real.log 2 / Real.log α)
          = ((gap α / (2 * α)) ^ (Real.log 2 / Real.log α))⁻¹ := by
        rw [show (2 * α / gap α) = (gap α / (2 * α))⁻¹ by field_simp, Real.inv_rpow hc.le]
      rw [hinvc, ← div_eq_inv_mul, le_div_iff₀ hcd]
      linarith
    have hcast : (2 : ℝ≥0∞)⁻¹ ^ M = ENNReal.ofReal (((2 : ℝ)⁻¹) ^ M) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2⁻¹),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    have hpow : ENNReal.ofReal ((ediam s).toReal ^ (Real.log 2 / Real.log α))
        = ediam s ^ (Real.log 2 / Real.log α) := by
      rw [← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_toReal hfin]
    refine hmeas.trans ?_
    rw [hcast, ← hpow, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hbase _).le]
    exact ENNReal.ofReal_le_ofReal hfinal

/-! ## M1 Lemma 1(iii), completed -/

/-- **The Hausdorff floor**: `dim_H C(α) ≥ log 2 / log α`, by the mass distribution principle
applied to `codingMeasure α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem le_dimH_cantorSet (h2 : 2 < α) :
    ENNReal.ofReal (Real.log 2 / Real.log α) ≤ dimH (cantorSet α) := by
  have hα : (1 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have hg : 0 < gap α := (gap_pos_iff hα0).mpr h2
  have hd0 : 0 < Real.log 2 / Real.log α :=
    div_pos (Real.log_pos one_lt_two) (Real.log_pos hα)
  have hbase : (0 : ℝ) < 2 * α / gap α := div_pos (by linarith) hg
  refine MeasureTheory.Measure.le_dimH_of_frostman (codingMeasure α) hd0.le
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hbase _)) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr (by positivity)) (fun s hs => codingMeasure_frostman h2 hs) ?_
  rw [codingMeasure_cantorSet hα]
  exact one_ne_zero

/-- **M1 Lemma 1(iii), in full**: `dim_H C(α) = log 2 / log α` for `α > 2`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dimH_cantorSet (h2 : 2 < α) :
    dimH (cantorSet α) = ENNReal.ofReal (Real.log 2 / Real.log α) := by
  have hα : (1 : ℝ) < α := by linarith
  have hd0 : 0 < Real.log 2 / Real.log α :=
    div_pos (Real.log_pos one_lt_two) (Real.log_pos hα)
  refine le_antisymm ?_ (le_dimH_cantorSet h2)
  have h := dimH_cantorSet_le hα
  have hcast : ((ENNReal.ofReal (Real.log 2 / Real.log α) : ℝ≥0∞) : EReal)
      = ((Real.log 2 / Real.log α : ℝ) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hd0.le]
  rw [← hcast] at h
  exact_mod_cast h

/-- **M1 Lemma 1(iii)**, the sentence as the note states it: the Hausdorff and box dimensions
of `C(α)` agree, and equal `log 2 / log α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dimH_eq_upperBoxDim_cantorSet (h2 : 2 < α) :
    (dimH (cantorSet α) : EReal) = upperBoxDim (cantorSet α) := by
  have hα : (1 : ℝ) < α := by linarith
  have hd0 : 0 < Real.log 2 / Real.log α :=
    div_pos (Real.log_pos one_lt_two) (Real.log_pos hα)
  rw [dimH_cantorSet h2, upperBoxDim_cantorSet h2, EReal.coe_ennreal_ofReal,
    max_eq_left hd0.le]

end Coding

end BB61
