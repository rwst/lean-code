/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.Solenoid.Bridge
import TH.RunCap
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Limit-measure non-degeneracy: the Dirac defect as a density statement

Angle **A13** of plan-A1+ (§5), work package W11 — the measure-theoretic half.  The elementary half
(the Dubickas run cap and the escape ladder) is `TH/RunCap.lean`; this file converts the open target

> **N1**  `δ₀ ∉ limitMeasures ξ`

into a statement about *densities of escapes*, and proves the converse implication that names the
missing input exactly.

## The reduction

W4 reduced the whole atomic-Dirac defect class to the single point `0`
(`eq_zero_of_diracProba_mem_limitMeasures`) and showed the reduction is sharp
(`limitMeasures_zero`).  What is added here is the arithmetic content of `δ₀`:

* `closedCell a b` — the **closed** level-`(0,0)` cell over `[a, b]`, the compact image of
  `[a,b] × ℤ₂ × ℤ₃`.  For `0 < a` and `b < 1` it misses `0` (`zero_notMem_closedCell`), and
  `wind η` lies in it exactly when `⟨η⟩ ∈ [a, b]` (`wind_mem_closedCell_iff`).
* `frequently_empirical_lt_of_mem_limitMeasures` — portmanteau in the *closed-set* direction: a
  limit measure starving a closed set forces the empirical measures to starve it frequently.  This
  is the mirror of `exists_mem_limitMeasures_measure_le` (W6), which runs open sets the other way.
* `fractLowerDensity_eq_zero_of_diracProba` — hence **`δ₀ ∈ limitMeasures ξ` forces the lower
  density of visits to every window `[a, b] ⊆ (0,1)` to vanish**, and conversely
  `notMem_limitMeasures_diracProba_of_lowerDensity_pos`: *any* window visited with positive lower
  density kills `δ₀`.  Through `Z32.V4` this reads `M6 ⟹ N1`
  (`notMem_limitMeasures_diracProba_of_M6`).

## The gap, exactly

Specialise the window to `[1/5, 4/5]`, which is precisely the escape set of `TH/RunCap.lean`
(`escapes_iff_fract`, `escCount_eq_fractCount`).  Then:

* `δ₀ ∈ limitMeasures 1` **⟹** `liminf escCount N / N = 0`
  (`escLowerDensity_eq_zero_of_diracProba`);
* the run cap **gives** `escCount N ≥ log₃((N+2)/5)` (`TH.escape_ladder`) — a set of density `0`.

So the two are consistent, and `TH.ladder_permits_density_zero` shows the consistency is not an
artifact of the proof: the ladder property is shared with the powers of three.  **A13-N1 is a
density statement and the Dubickas cap is a counting statement; nothing in this repository closes
the gap.**  What would close it, precisely: positive lower density of escapes.

## Footprint

`std3` (`propext`, `Classical.choice`, `Quot.sound`) with the single exception of the closing
corollary `notMem_limitMeasures_diracProba_of_bridge`, which routes through W6's `M6_of_bridge` and
therefore inherits `EL.rigidity_decomposition`.  It is recorded because it is ledger information —
N1 is *implied* by the bridge inputs, hence strictly cheaper than M7 — not because A13 uses it.

## References

* `plans/plan-A1+.html` §5 (angle A13, targets N1–N5), §4 L4–L5 (the Dirac gate), §7.2 (W11).
* `plans/report2-weyl.html` §7 Table D (A13).
-/

namespace TH.S6

open Filter MeasureTheory Metric Set
open scoped Topology ENNReal NNReal

/-! ### Closed level-`(0,0)` cells -/

/-- The **closed** level-`(0,0)` cell over `[a, b]`: the image of `[a,b] × ℤ₂ × ℤ₃`.  Compact, so
closed; and for `0 < a`, `b < 1` it avoids the fixed point `0`. -/
noncomputable def closedCell (a b : ℝ) : Set S6 :=
  QuotientAddGroup.mk '' (Icc a b ×ˢ (closedBall (0 : ℚ_[2]) 1 ×ˢ closedBall (0 : ℚ_[3]) 1))

@[category API, AMS 37 11, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem isCompact_closedCell (a b : ℝ) : IsCompact (closedCell a b) :=
  (isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).image
    QuotientAddGroup.continuous_mk

@[category API, AMS 37 11, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem isClosed_closedCell (a b : ℝ) : IsClosed (closedCell a b) :=
  (isCompact_closedCell a b).isClosed

@[category API, AMS 11, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem closedCell_box_subset_D {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) :
    Icc a b ×ˢ (closedBall (0 : ℚ_[2]) 1 ×ˢ closedBall (0 : ℚ_[3]) 1) ⊆ D := by
  rintro ⟨x, y, z⟩ ⟨hx, hy, hz⟩
  refine mem_D.mpr ⟨⟨ha.trans hx.1, lt_of_le_of_lt hx.2 hb⟩, ?_, ?_⟩
  · simpa using hy
  · simpa using hz

/-- At level `(0, 0)` the closed cell over `[a, b] ⊆ [0, 1)` is exactly the closed fractional-part
window: no residue condition survives (W3's `level_bridge`, in its closed form). -/
@[category research solved, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem wind_mem_closedCell_iff {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) (η : ℝ) :
    wind η ∈ closedCell a b ↔ Int.fract η ∈ Icc a b := by
  rw [closedCell, wind_repr,
    mk_mem_mk_image_iff (closedCell_box_subset_D ha hb) (wind_repr_mem_D η)]
  simp [Set.mem_prod, Padic.norm_int_le_one]

/-- The closed cells over `[a, b] ⊆ (0, 1)` avoid the fixed point. -/
@[category research solved, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem zero_notMem_closedCell {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    (0 : S6) ∉ closedCell a b := by
  rw [← wind_zero, wind_mem_closedCell_iff ha.le hb]
  simp only [Int.fract_zero, Set.mem_Icc, not_and, not_le]
  intro h
  linarith

/-! ### Counting the window -/

open scoped Classical in
/-- The dates `n < N` at which the orbit's fractional part lies in the closed window `[a, b]`. -/
noncomputable def fractCount (ξ a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (ξ * (3 / 2) ^ n) ∈ Icc a b).card

/-- The empirical frequency of the window `[a, b]` among the first `N` dates. -/
noncomputable def fractRatio (ξ a b : ℝ) (N : ℕ) : ℝ := (fractCount ξ a b N : ℝ) / N

/-- The lower density of visits to the closed window `[a, b]`. -/
noncomputable def fractLowerDensity (ξ a b : ℝ) : ℝ := liminf (fractRatio ξ a b) atTop

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem fractCount_le (ξ a b : ℝ) (N : ℕ) : fractCount ξ a b N ≤ N := by
  classical
  have := Finset.card_le_card
    (Finset.filter_subset (fun n => Int.fract (ξ * (3 / 2) ^ n) ∈ Icc a b) (Finset.range N))
  rwa [Finset.card_range] at this

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem fractRatio_nonneg (ξ a b : ℝ) (N : ℕ) : 0 ≤ fractRatio ξ a b N :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem fractRatio_le_one (ξ a b : ℝ) (N : ℕ) : fractRatio ξ a b N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [fractRatio, hN]
  · rw [fractRatio, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast fractCount_le ξ a b N

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem isBoundedUnder_le_fractRatio (ξ a b : ℝ) :
    IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) (fractRatio ξ a b) :=
  isBoundedUnder_of ⟨1, fun N => fractRatio_le_one ξ a b N⟩

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem isBoundedUnder_ge_fractRatio (ξ a b : ℝ) :
    IsBoundedUnder (· ≥ ·) (atTop : Filter ℕ) (fractRatio ξ a b) :=
  isBoundedUnder_of ⟨0, fun N => fractRatio_nonneg ξ a b N⟩

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem isCoboundedUnder_ge_fractRatio (ξ a b : ℝ) :
    IsCoboundedUnder (· ≥ ·) (atTop : Filter ℕ) (fractRatio ξ a b) :=
  (isBoundedUnder_le_fractRatio ξ a b).isCoboundedUnder_ge

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem fractLowerDensity_nonneg (ξ a b : ℝ) : 0 ≤ fractLowerDensity ξ a b :=
  le_liminf_of_le (isCoboundedUnder_ge_fractRatio ξ a b)
    (Eventually.of_forall fun N => fractRatio_nonneg ξ a b N)

/-- **The empirical mass of a closed window is its visit frequency.** -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem empirical_closedCell {ξ a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) (N : ℕ) :
    (empirical ξ N : Measure S6) (closedCell a b)
      = ((N : ℝ≥0∞) + 1)⁻¹ * (fractCount ξ a b (N + 1) : ℝ≥0∞) := by
  classical
  have hpred : ∀ n : ℕ,
      (T32^[n] (wind ξ) ∈ closedCell a b) ↔ (Int.fract (ξ * (3 / 2) ^ n) ∈ Icc a b) := by
    intro n
    rw [T32_iter_wind]
    exact wind_mem_closedCell_iff ha hb _
  have hsets : ((Finset.range (N + 1)).filter fun n => T32^[n] (wind ξ) ∈ closedCell a b)
      = ((Finset.range (N + 1)).filter fun n => Int.fract (ξ * (3 / 2) ^ n) ∈ Icc a b) := by
    ext n
    simp only [Finset.mem_filter, hpred n]
  have hsum : (empirical ξ N : Measure S6) (closedCell a b)
      = ((N : ℝ≥0∞) + 1)⁻¹ * ((((Finset.range (N + 1)).filter
        fun n => T32^[n] (wind ξ) ∈ closedCell a b).card : ℕ) : ℝ≥0∞) := by
    rw [empirical_toMeasure, empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      smul_eq_mul]
    congr 1
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Measure.dirac_apply, Set.indicator_apply]
    simp
  rw [hsum, hsets, fractCount]

/-! ### Portmanteau in the closed-set direction -/

/-- **If a limit measure starves a closed set, the empirical measures starve it frequently.**

The mirror of W6's `exists_mem_limitMeasures_measure_le`, which runs *open* sets in the opposite
direction.  Here the cluster filter `𝓝 ν ⊓ map (empirical ξ) atTop` carries `id` to `ν`, portmanteau
bounds the `limsup` of the closed set's mass by `ν`'s, and a nontrivial filter cannot contain a set
and its complement. -/
@[category research solved, AMS 37 28 60, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem frequently_empirical_lt_of_mem_limitMeasures {ξ : ℝ} {ν : ProbabilityMeasure S6}
    (hν : ν ∈ limitMeasures ξ) {C : Set S6} (hC : IsClosed C) {c : ℝ≥0∞}
    (hc : (ν : Measure S6) C < c) :
    ∃ᶠ N in atTop, (empirical ξ N : Measure S6) C < c := by
  have hclust : ClusterPt ν (Filter.map (empirical ξ) atTop) := hν.clusterPt
  haveI hne : (𝓝 ν ⊓ Filter.map (empirical ξ) atTop).NeBot := hclust
  have htend : Tendsto (id : ProbabilityMeasure S6 → ProbabilityMeasure S6)
      (𝓝 ν ⊓ Filter.map (empirical ξ) atTop) (𝓝 ν) := tendsto_id.mono_left inf_le_left
  have hlim : ((𝓝 ν ⊓ Filter.map (empirical ξ) atTop).limsup
      fun μ : ProbabilityMeasure S6 => (μ : Measure S6) C) ≤ (ν : Measure S6) C :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto htend hC
  have hev : ∀ᶠ μ : ProbabilityMeasure S6 in 𝓝 ν ⊓ Filter.map (empirical ξ) atTop,
      (μ : Measure S6) C < c :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim hc)
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hboth : ∀ᶠ μ : ProbabilityMeasure S6 in 𝓝 ν ⊓ Filter.map (empirical ξ) atTop,
      ((μ : Measure S6) C < c) ∧ ¬ ((μ : Measure S6) C < c) :=
    hev.and (Filter.Eventually.filter_mono inf_le_right (Filter.eventually_map.mpr hcon))
  obtain ⟨μ, h1, h2⟩ := hboth.exists
  exact h2 h1

/-! ### A13-N1 as a density statement -/

/-- **The reduction.**  If `δ₀` is a limit measure of the orbit of `ξ`, then every closed window
`[a, b] ⊆ (0, 1)` is visited with frequency below any prescribed `c > 0` infinitely often — the
orbit is confined to the two ends of `[0,1]` at full density along a subsequence. -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem frequently_fractRatio_lt_of_diracProba {ξ : ℝ}
    (h : diracProba (0 : S6) ∈ limitMeasures ξ) {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    {c : ℝ} (hc : 0 < c) :
    ∃ᶠ N in atTop, fractRatio ξ a b N < c := by
  have hC : IsClosed (closedCell a b) := isClosed_closedCell a b
  have hzero : ((diracProba (0 : S6) : ProbabilityMeasure S6) : Measure S6) (closedCell a b)
      = 0 := by
    show Measure.dirac (0 : S6) (closedCell a b) = 0
    rw [Measure.dirac_apply' _ hC.measurableSet,
      Set.indicator_of_notMem (zero_notMem_closedCell ha hb)]
  have hlt : ((diracProba (0 : S6) : ProbabilityMeasure S6) : Measure S6) (closedCell a b)
      < ENNReal.ofReal c := by
    rw [hzero]
    exact ENNReal.ofReal_pos.mpr hc
  have hfreq := frequently_empirical_lt_of_mem_limitMeasures h hC hlt
  have hshift : ∃ᶠ N in atTop, fractRatio ξ a b (N + 1) < c := by
    refine hfreq.mono fun N hN => ?_
    rw [empirical_closedCell ha.le hb N] at hN
    have hconv : ENNReal.ofReal (fractRatio ξ a b (N + 1))
        = ((N : ℝ≥0∞) + 1)⁻¹ * (fractCount ξ a b (N + 1) : ℝ≥0∞) := by
      rw [fractRatio, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
      push_cast
      ring
    rw [← hconv] at hN
    exact (ENNReal.ofReal_lt_ofReal_iff hc).mp hN
  rw [Filter.frequently_atTop] at hshift ⊢
  intro n
  obtain ⟨k, hk, hkp⟩ := hshift n
  exact ⟨k + 1, by omega, hkp⟩

/-- **A13-N1, reduced to a density statement.**  `δ₀ ∈ limitMeasures ξ` forces the lower density of
visits to *every* closed window `[a, b] ⊆ (0, 1)` to vanish. -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem fractLowerDensity_eq_zero_of_diracProba {ξ : ℝ}
    (h : diracProba (0 : S6) ∈ limitMeasures ξ) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    fractLowerDensity ξ a b = 0 := by
  refine le_antisymm ?_ (fractLowerDensity_nonneg ξ a b)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc1, hc2⟩ := exists_between hcon
  have hfreq := frequently_fractRatio_lt_of_diracProba h ha hb hc1
  have hev : ∀ᶠ N in atTop, c < fractRatio ξ a b N :=
    eventually_lt_of_lt_liminf hc2 (isBoundedUnder_ge_fractRatio ξ a b)
  obtain ⟨N, h1, h2⟩ := (hfreq.and_eventually hev).exists
  exact absurd h1 (not_lt.mpr h2.le)

/-- **The interface A13-N1 needs.**  Any window `[a, b] ⊆ (0, 1)` visited with *positive lower
density* excludes `δ₀` from the limit measures.  This is the exact converse of the reduction: N1 is
a density statement and nothing weaker. -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem notMem_limitMeasures_diracProba_of_lowerDensity_pos {ξ a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hpos : 0 < fractLowerDensity ξ a b) : diracProba (0 : S6) ∉ limitMeasures ξ := by
  intro h
  rw [fractLowerDensity_eq_zero_of_diracProba h ha hb] at hpos
  exact lt_irrefl 0 hpos

/-! ### The bridge to the `Z32` visit-density grid -/

/-- Unwrapping an arc that does not wrap: `Z32.inArc s t x` puts `⟨x⟩` in `[s, s+t)`. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem fract_mem_Ico_of_inArc {s t x : ℝ} (hs : 0 ≤ s) (hst : s + t ≤ 1)
    (h : Z32.inArc s t x) : Int.fract x ∈ Set.Ico s (s + t) := by
  have ht : 0 < t := lt_of_le_of_lt (Int.fract_nonneg (x - s)) h
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have hkey : Int.fract (x - s) = Int.fract (Int.fract x - s) := by
    have e : Int.fract x - s = x - s + ((-⌊x⌋ : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [e, Int.fract_add_intCast]
  rw [Z32.inArc, hkey] at h
  rcases le_or_gt s (Int.fract x) with hcase | hcase
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at h
    exact ⟨hcase, by linarith⟩
  · exfalso
    have e : Int.fract x - s = Int.fract x - s + 1 + ((-1 : ℤ) : ℝ) := by push_cast; ring
    rw [e, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at h
    linarith

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem visitCount_le_fractCount {ξ s t : ℝ} (hs : 0 ≤ s) (hst : s + t ≤ 1) (N : ℕ) :
    Z32.visitCount (3 / 2) ξ s t N ≤ fractCount ξ s (s + t) N := by
  classical
  refine Finset.card_le_card fun n hn => ?_
  obtain ⟨hlt, harc⟩ := Z32.mem_visits.mp hn
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨hlt, Set.Ico_subset_Icc_self (fract_mem_Ico_of_inArc hs hst harc)⟩

@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem lowerDensity_le_fractLowerDensity {ξ s t : ℝ} (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    Z32.lowerDensity (3 / 2) ξ s t ≤ fractLowerDensity ξ s (s + t) := by
  refine Filter.liminf_le_liminf (Eventually.of_forall fun N => ?_)
    (Z32.isBoundedUnder_ge_visitRatio _ _ _ _) (isCoboundedUnder_ge_fractRatio _ _ _)
  rw [Z32.visitRatio, fractRatio]
  gcongr
  exact_mod_cast visitCount_le_fractCount hs hst N

/-- **`V4 ⟹ N1` at a non-wrapping arc.**  Positive lower density of visits to any arc
`[s, s+t) ⊆ (0, 1)` excludes `δ₀`. -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem notMem_limitMeasures_diracProba_of_V4 {ξ s t : ℝ} (hs : 0 < s) (hst : s + t < 1)
    (h : Z32.V4 (3 / 2) ξ s t) : diracProba (0 : S6) ∉ limitMeasures ξ :=
  notMem_limitMeasures_diracProba_of_lowerDensity_pos hs hst
    (lt_of_lt_of_le h (lowerDensity_le_fractLowerDensity hs.le hst.le))

/-- **`M6 ⟹ N1`.**  If every arc is visited with positive lower density then `δ₀` is not a limit
measure: the whole atomic-Dirac defect class dies.  (Witness arc: `[1/4, 1/2)`.) -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem notMem_limitMeasures_diracProba_of_M6 {ξ : ℝ} (h : Z32.M6 (3 / 2) ξ) :
    diracProba (0 : S6) ∉ limitMeasures ξ :=
  notMem_limitMeasures_diracProba_of_V4 (s := 1 / 4) (t := 1 / 4) (by norm_num) (by norm_num)
    (h (1 / 4) (1 / 4) (by norm_num))

/-! ### The gap, at the escape window -/

/-- **Centered `ε` versus `Int.fract`.**  For `0 ≤ η ≤ 1/2`, being at distance at least `η` from
the nearest integer is being in the closed window `[η, 1 − η]` of the fractional part. -/
@[category API, AMS 11, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem mem_Icc_iff_le_abs_sub_round {x η : ℝ} (h1 : η ≤ 1 / 2) :
    Int.fract x ∈ Set.Icc η (1 - η) ↔ η ≤ |x - round x| := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hfr : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
  rw [round_eq]
  rcases lt_or_ge (Int.fract x) (1 / 2) with hc | hc
  · have hfloor : ⌊x + 1 / 2⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      constructor
      · linarith [hfr ▸ hf0]
      · linarith [hfr ▸ hc]
    rw [hfloor, show x - (⌊x⌋ : ℝ) = Int.fract x from hfr.symm, abs_of_nonneg hf0, Set.mem_Icc]
    exact ⟨fun hh => hh.1, fun hh => ⟨hh, by linarith⟩⟩
  · have hfloor : ⌊x + 1 / 2⌋ = ⌊x⌋ + 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast
        linarith [hfr ▸ hc]
      · push_cast
        linarith [hfr ▸ hf1]
    rw [hfloor]
    push_cast
    rw [show x - ((⌊x⌋ : ℝ) + 1) = Int.fract x - 1 by rw [hfr]; ring,
      abs_of_nonpos (by linarith), Set.mem_Icc]
    exact ⟨fun hh => by linarith [hh.2], fun hh => ⟨by linarith, by linarith⟩⟩

/-- The escape predicate of `TH/RunCap.lean` is exactly the window `[1/5, 4/5]`. -/
@[category research solved, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem escapes_iff_fract (n : ℕ) :
    Escapes n ↔ Int.fract ((1 : ℝ) * (3 / 2) ^ n) ∈ Icc (1 / 5 : ℝ) (4 / 5) := by
  have hone : (1 : ℝ) * ((3 : ℝ) / 2) ^ n = ((3 : ℝ) / 2) ^ n := one_mul _
  have hcast : (((3 / 2 : ℚ) ^ n : ℚ) : ℝ) = ((3 : ℝ) / 2) ^ n := by push_cast; ring
  have hround : round (((3 : ℝ) / 2) ^ n) = m n := by
    rw [← hcast, Rat.round_cast]
    rfl
  have heps : ((eps n : ℚ) : ℝ) = ((3 : ℝ) / 2) ^ n - ((round (((3 : ℝ) / 2) ^ n) : ℤ) : ℝ) := by
    rw [hround, eps]
    push_cast [hcast]
    ring
  have hiff1 : Escapes n ↔
      (1 / 5 : ℝ) ≤ |((3 : ℝ) / 2) ^ n - ((round (((3 : ℝ) / 2) ^ n) : ℤ) : ℝ)| := by
    rw [← heps, ← Rat.cast_abs, show ((1 : ℝ) / 5) = ((1 / 5 : ℚ) : ℝ) by norm_num, Rat.cast_le]
    exact Iff.rfl
  rw [hiff1, hone, show (4 / 5 : ℝ) = 1 - 1 / 5 by norm_num]
  exact (mem_Icc_iff_le_abs_sub_round (by norm_num)).symm

/-- The escape count of `TH/RunCap.lean` is the visit count of the window `[1/5, 4/5]`. -/
@[category research solved, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem escCount_eq_fractCount (N : ℕ) : escCount N = fractCount 1 (1 / 5) (4 / 5) N := by
  classical
  rw [escCount, fractCount]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, escapes_iff_fract n]

/-- **The A13-N1 gap, machine-checked.**  If `δ₀` is a limit measure of the orbit of `1`, then the
escapes of `TH/RunCap.lean` have lower density `0`.

Against this stands only `TH.escape_ladder`: `escCount N ≥ log₃((N+2)/5)`.  That is a set of
density `0`, so there is no contradiction — and by `TH.ladder_permits_density_zero` there cannot be
one, since the powers of three satisfy the same ladder property.  **A13-N1 needs a density
input.** -/
@[category research solved, AMS 11 37 28, ref "Dub09" "A1plus", group "weyl_a13_limitmeasures"]
theorem escLowerDensity_eq_zero_of_diracProba (h : diracProba (0 : S6) ∈ limitMeasures 1) :
    liminf (fun N : ℕ => (escCount N : ℝ) / N) atTop = 0 := by
  have hEq : (fun N : ℕ => (escCount N : ℝ) / (N : ℝ)) = fractRatio 1 (1 / 5) (4 / 5) := by
    funext N
    rw [fractRatio, escCount_eq_fractCount]
  rw [hEq]
  exact fractLowerDensity_eq_zero_of_diracProba h (by norm_num) (by norm_num)

/-! ### Ledger note: N1 is implied by the bridge

The single non-`std3` declaration of this file.  It records that A13-N1 sits *below* M7 in the
architecture: whatever proves the W6 inputs proves N1 as a by-product.  A13's purpose is the
opposite direction — to reach N1 without the rigidity engine. -/

/-- **The bridge inputs imply A13-N1.**  Footprint: `EL.rigidity_decomposition`, through W6's
`M6_of_bridge`. -/
@[category research solved, AMS 11 37 28, ref "Rud90" "EL03" "A1plus",
  group "weyl_a13_limitmeasures"]
theorem notMem_limitMeasures_diracProba_of_bridge {ξ ε : ℝ} (hε : 0 < ε)
    (hinv : TransverseRecovery ξ) (hent : EntropyProduction ξ ε) :
    diracProba (0 : S6) ∉ limitMeasures ξ :=
  notMem_limitMeasures_diracProba_of_M6 (M6_of_bridge hε hinv hent)

end TH.S6
