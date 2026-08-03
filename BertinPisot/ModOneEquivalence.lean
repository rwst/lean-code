/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BertinPisot.UniformDistribution
import ForMathlib.Analysis.Equidistribution.ModOne
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# The two uniform-distribution conventions agree

The corpus carries **two** definitions of "uniformly distributed modulo one", which grew up
independently and had never been compared:

* `Bertin.UniformlyDistributedModOne` (`BertinPisot/UniformDistribution.lean`, Bertin's Definition
  4.2) — *centered*: it counts `n < N` with `ε xₙ ∈ [a, b)` for `-1/2 ≤ a < b ≤ 1/2`, where
  `ε y = y - round y ∈ [-1/2, 1/2)` is the centered fractional part, and asks the proportion to
  tend to `b - a`;
* `IsEquidistributedModuloOne` (`ForMathlib/Analysis/Equidistribution/ModOne.lean`) — *`Int.fract`
  based*: it counts `n < N` with `Int.fract xₙ ∈ [c, d]` for `[c, d] ⊆ [0, 1]` and asks the
  proportion to tend to `(d - c) / (1 - 0)`.

The two differ in three ways at once: the representative window (`[-1/2, 1/2)` vs `[0, 1)`), the
interval shape (half-open `Ico` vs closed `Icc`), and the admissible degenerate case (Bertin
demands `a < b`, the `ForMathlib` version allows `c = d`). This file proves they are nevertheless
equivalent:

* `Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne`.

*Method.* Both definitions have an axiom-free route to the **Riemann-integral criterion**, and the
equivalence is cheapest there, because Riemann integrability is insensitive to the endpoints where
the two conventions disagree — no `Ico`/`Icc` bookkeeping survives into the final argument. The two
directions are mirror images:

* `→` feeds the 1-periodic test function `fractInd c d = 𝟙_{[c,d]} ∘ Int.fract` into
  `Bertin.integralCriterion_of_uniformlyDistributedModOne`;
* `←` feeds the 1-periodic test function `epsInd a b = 𝟙_{[a,b)} ∘ ε` into the `Int.fract`-side
  criterion `tendsto_average_fract_of_isEquidistributedModuloOne`, obtained here by instantiating
  the general engine `tendsto_average_of_indicator_equidistributed` at `[0, 1]`.

The bridge in both directions is that `ε` and `Int.fract` differ by an integer
(`Bertin.fract_ε`, `Bertin.ε_fract`), so a 1-periodic test function cannot tell them apart. The one
genuinely non-formal step is the `Icc`-to-`Ico` squeeze
(`tendsto_average_fract_of_isEquidistributedModuloOne`), needed because the engine wants half-open
intervals while `IsEquidistributedModuloOne` supplies closed ones.

*Consequences.* Results stated in either convention now transfer verbatim. In particular this
defuses the standing landmine recorded in the `FLP/` header — that the centered variant of a
statement proved for `Int.fract` is *not* a formal corollary — at the level of the u.d. predicate
itself.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §4.2.
  - [KN74] Kuipers, L. and Niederreiter, H. *Uniform Distribution of Sequences.* Wiley, 1974. §1.1.
-/

namespace Bertin

open Filter MeasureTheory
open scoped Topology

/-! ### `ε` and `Int.fract` differ by an integer -/

/-- The centered fractional part is 1-periodic. -/
@[category API, AMS 11, ref "Ber92"]
theorem ε_add_one (t : ℝ) : ε (t + 1) = ε t := by
  rw [ε, ε, show (t : ℝ) + 1 = t + ((1 : ℤ) : ℝ) by push_cast; ring, round_add_intCast]
  push_cast; ring

/-- `ε` is 1-periodic, as a `Function.Periodic`. -/
@[category API, AMS 11, ref "Ber92"]
theorem periodic_ε : Function.Periodic ε 1 := ε_add_one

/-- Taking the centered part after the fractional part changes nothing: both are representatives
of the same class mod 1. -/
@[category API, AMS 11, ref "Ber92"]
theorem ε_fract (y : ℝ) : ε (Int.fract y) = ε y := by
  rw [ε, ε, Int.fract, show y - (⌊y⌋ : ℝ) = y - ((⌊y⌋ : ℤ) : ℝ) from rfl, round_sub_intCast]
  push_cast; ring

/-- Taking the fractional part after the centered part changes nothing. -/
@[category API, AMS 11, ref "Ber92"]
theorem fract_ε (y : ℝ) : Int.fract (ε y) = Int.fract y := Int.fract_sub_intCast y (round y)

/-- On `(-1/2, 1/2)` the centered part is the identity. -/
@[category API, AMS 11, ref "Ber92"]
theorem ε_eq_self_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (-(1/2) : ℝ) (1/2)) : ε t = t := by
  have : round t = 0 := by
    rw [round_eq, Int.floor_eq_zero_iff]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [ε, this]; push_cast; ring

/-- On `(1/2, 1)` the centered part is the shift by `-1`. -/
@[category API, AMS 11, ref "Ber92"]
theorem ε_eq_sub_one_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (1/2 : ℝ) 1) : ε t = t - 1 := by
  have : round t = 1 := by
    rw [round_eq]
    exact Int.floor_eq_iff.mpr ⟨by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
  rw [ε, this]; push_cast; ring

/-! ### Continuity of interval indicators away from the endpoints -/

/-- The indicator of a closed interval is continuous at every point other than the two endpoints.
(No hypothesis relating `c` and `d` is needed: if `d < c` the interval is empty and the middle case
is vacuous.) -/
@[category API, AMS 11, ref "Ber92"]
theorem continuousAt_indicator_Icc {c d t : ℝ} (hc : t ≠ c) (hd : t ≠ d) :
    ContinuousAt (fun s : ℝ => if s ∈ Set.Icc c d then (1 : ℝ) else 0) t := by
  have hc0 : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t := continuousAt_const
  have hc1 : ContinuousAt (fun _ : ℝ => (1 : ℝ)) t := continuousAt_const
  rcases lt_or_gt_of_ne hc with h | h
  · refine hc0.congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    rw [if_neg (fun hm => absurd hm.1 (not_le.mpr hs))]
  · rcases lt_or_gt_of_ne hd with h' | h'
    · refine hc1.congr ?_
      filter_upwards [Ioo_mem_nhds h h'] with s hs
      rw [if_pos ⟨hs.1.le, hs.2.le⟩]
    · refine hc0.congr ?_
      filter_upwards [Ioi_mem_nhds h'] with s hs
      rw [if_neg (fun hm => absurd hm.2 (not_le.mpr hs))]

/-- The indicator of a half-open interval is continuous at every point other than the two
endpoints. -/
@[category API, AMS 11, ref "Ber92"]
theorem continuousAt_indicator_Ico {a b t : ℝ} (ha : t ≠ a) (hb : t ≠ b) :
    ContinuousAt (fun s : ℝ => if s ∈ Set.Ico a b then (1 : ℝ) else 0) t := by
  have hc0 : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t := continuousAt_const
  have hc1 : ContinuousAt (fun _ : ℝ => (1 : ℝ)) t := continuousAt_const
  rcases lt_or_gt_of_ne ha with h | h
  · refine hc0.congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    rw [if_neg (fun hm => absurd hm.1 (not_le.mpr hs))]
  · rcases lt_or_gt_of_ne hb with h' | h'
    · refine hc1.congr ?_
      filter_upwards [Ioo_mem_nhds h h'] with s hs
      rw [if_pos ⟨hs.1.le, hs.2⟩]
    · refine hc0.congr ?_
      filter_upwards [Ioi_mem_nhds h'] with s hs
      rw [if_neg (fun hm => absurd hm.2 (not_lt.mpr hs.le))]

/-! ### The two test functions -/

/-- The indicator of `[c, d]` read in `Int.fract` coordinates: a 1-periodic function of `t`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def fractInd (c d : ℝ) : ℝ → ℝ :=
  fun t => if Int.fract t ∈ Set.Icc c d then 1 else 0

/-- The indicator of `[a, b)` read in centered coordinates: a 1-periodic function of `t`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def epsInd (a b : ℝ) : ℝ → ℝ :=
  fun t => if ε t ∈ Set.Ico a b then 1 else 0

@[category API, AMS 11, ref "Ber92"]
theorem periodic_fractInd (c d : ℝ) : Function.Periodic (fractInd c d) 1 := by
  intro t; simp only [fractInd, Int.fract_add_one]

@[category API, AMS 11, ref "Ber92"]
theorem periodic_epsInd (a b : ℝ) : Function.Periodic (epsInd a b) 1 := by
  intro t; simp only [epsInd, ε_add_one]

/-! ### `fractInd` is Riemann-integrable on the centered window -/

private theorem fractInd_bdd (c d : ℝ) : ∃ C, ∀ t ∈ Set.Icc (-(1/2) : ℝ) (1/2), |fractInd c d t| ≤ C :=
  ⟨1, fun t _ => by rw [fractInd]; split <;> simp⟩

private theorem fractInd_ae (c d : ℝ) :
    volume {t ∈ Set.Icc (-(1/2) : ℝ) (1/2) | ¬ ContinuousAt (fractInd c d) t} = 0 := by
  have hsub : {t ∈ Set.Icc (-(1/2) : ℝ) (1/2) | ¬ ContinuousAt (fractInd c d) t}
      ⊆ ({-(1/2), 1/2, 0, c, d, c - 1, d - 1} : Set ℝ) := by
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    by_contra hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hmem
    refine ht.2 ?_
    have hlo : -(1/2) < t := lt_of_le_of_ne ht.1.1 (Ne.symm h1)
    have hhi : t < 1/2 := lt_of_le_of_ne ht.1.2 h2
    rcases lt_or_gt_of_ne h3 with hneg | hpos
    · -- `-1/2 < t < 0`: here `Int.fract s = s + 1` locally, so the indicator is that of `[c-1,d-1]`
      refine (continuousAt_indicator_Icc (c := c - 1) (d := d - 1) h6 h7).congr ?_
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < t by linarith) hneg] with s hs
      have hfr : Int.fract s = s + 1 := by
        rw [← Int.fract_add_one s, Int.fract_eq_self]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hiff : (s ∈ Set.Icc (c - 1) (d - 1)) ↔ (Int.fract s ∈ Set.Icc c d) := by
        rw [hfr]
        simp only [Set.mem_Icc]
        constructor <;> (rintro ⟨u, v⟩; exact ⟨by linarith, by linarith⟩)
      simp only [fractInd, hiff]
    · -- `0 < t < 1/2`: here `Int.fract s = s` locally
      refine (continuousAt_indicator_Icc (c := c) (d := d) h4 h5).congr ?_
      filter_upwards [Ioo_mem_nhds hpos (show t < (1 : ℝ) by linarith)] with s hs
      have hfr : Int.fract s = s := Int.fract_eq_self.mpr ⟨le_of_lt hs.1, hs.2⟩
      simp only [fractInd, hfr]
  exact measure_mono_null hsub (Set.Finite.measure_zero (Set.toFinite _) volume)

/-- `∫_{-1/2}^{1/2} 𝟙_{[c,d]}(Int.fract t) dt = d - c` when `[c, d] ⊆ [0, 1]`. -/
private theorem integral_fractInd {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    (∫ t in (-(1/2) : ℝ)..(1/2), fractInd c d t) = d - c := by
  -- Move to the window `[0, 1]` by periodicity.
  have hper : (∫ t in (-(1/2) : ℝ)..(-(1/2) + 1), fractInd c d t)
      = ∫ t in (0 : ℝ)..(0 + 1), fractInd c d t :=
    (periodic_fractInd c d).intervalIntegral_add_eq _ _
  rw [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num] at hper
  rw [hper]
  -- On `(0, 1)` the test function is the plain indicator of `[c, d]`.
  have hae : ∀ᵐ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      fractInd c d t = Set.indicator (Set.Icc c d) (fun _ => (1 : ℝ)) t := by
    have hone : ∀ᵐ t : ℝ, t ≠ 1 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hone] with t ht hmem
    have hfr : Int.fract t = t :=
      Int.fract_eq_self.mpr ⟨le_of_lt hmem.1, lt_of_le_of_ne hmem.2 ht⟩
    simp only [fractInd, hfr, Set.indicator_apply]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_congr_ae measurableSet_Ioc hae, setIntegral_indicator measurableSet_Icc,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  -- `volume (Ioc 0 1 ∩ [c, d]) = d - c`.
  have hvol : volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Icc c d) = ENNReal.ofReal (d - c) := by
    refine le_antisymm ?_ ?_
    · calc volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Icc c d)
          ≤ volume (Set.Icc c d) := measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal (d - c) := Real.volume_Icc
    · calc ENNReal.ofReal (d - c) = volume (Set.Ioo c d) := (Real.volume_Ioo).symm
        _ ≤ volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Icc c d) :=
            measure_mono (fun t ht => ⟨Set.mem_Ioc.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩,
              Set.Ioo_subset_Icc_self ht⟩)
  rw [hvol, ENNReal.toReal_ofReal (by linarith)]

/-! ### `epsInd` is Riemann-integrable on the `Int.fract` window -/

private theorem epsInd_bdd (a b : ℝ) : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, |epsInd a b t| ≤ C :=
  ⟨1, fun t _ => by rw [epsInd]; split <;> simp⟩

private theorem epsInd_ae (a b : ℝ) :
    volume {t ∈ Set.Icc (0 : ℝ) 1 | ¬ ContinuousAt (epsInd a b) t} = 0 := by
  have hsub : {t ∈ Set.Icc (0 : ℝ) 1 | ¬ ContinuousAt (epsInd a b) t}
      ⊆ ({0, 1, 1/2, a, b, a + 1, b + 1} : Set ℝ) := by
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    by_contra hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hmem
    refine ht.2 ?_
    have hlo : 0 < t := lt_of_le_of_ne ht.1.1 (Ne.symm h1)
    have hhi : t < 1 := lt_of_le_of_ne ht.1.2 h2
    rcases lt_or_gt_of_ne h3 with hlow | hhigh
    · -- `0 < t < 1/2`: here `ε s = s` locally
      refine (continuousAt_indicator_Ico (a := a) (b := b) h4 h5).congr ?_
      filter_upwards [Ioo_mem_nhds (show (-(1/2) : ℝ) < t by linarith) hlow] with s hs
      simp only [epsInd, ε_eq_self_of_mem_Ioo hs]
    · -- `1/2 < t < 1`: here `ε s = s - 1` locally, so the indicator is that of `[a+1, b+1)`
      refine (continuousAt_indicator_Ico (a := a + 1) (b := b + 1) h6 h7).congr ?_
      filter_upwards [Ioo_mem_nhds hhigh hhi] with s hs
      have hfr : ε s = s - 1 := ε_eq_sub_one_of_mem_Ioo hs
      have hiff : (s ∈ Set.Ico (a + 1) (b + 1)) ↔ (ε s ∈ Set.Ico a b) := by
        rw [hfr]
        simp only [Set.mem_Ico]
        constructor <;> (rintro ⟨u, v⟩; exact ⟨by linarith, by linarith⟩)
      simp only [epsInd, hiff]
  exact measure_mono_null hsub (Set.Finite.measure_zero (Set.toFinite _) volume)

/-- `∫_0^1 𝟙_{[a,b)}(ε t) dt = b - a` when `[a, b) ⊆ [-1/2, 1/2)`. -/
private theorem integral_epsInd {a b : ℝ} (ha : -(1/2) ≤ a) (hab : a < b) (hb : b ≤ 1/2) :
    (∫ t in (0 : ℝ)..1, epsInd a b t) = b - a := by
  -- Move to the centered window by periodicity.
  have hper : (∫ t in (0 : ℝ)..(0 + 1), epsInd a b t)
      = ∫ t in (-(1/2) : ℝ)..(-(1/2) + 1), epsInd a b t :=
    (periodic_epsInd a b).intervalIntegral_add_eq _ _
  rw [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num] at hper
  rw [hper]
  -- On `(-1/2, 1/2)` the test function is the plain indicator of `[a, b)`.
  have hae : ∀ᵐ t : ℝ, t ∈ Set.Ioc (-(1/2) : ℝ) (1/2) →
      epsInd a b t = Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)) t := by
    have hone : ∀ᵐ t : ℝ, t ≠ 1/2 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hone] with t ht hmem
    have hfr : ε t = t :=
      ε_eq_self_of_mem_Ioo ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩
    simp only [epsInd, hfr, Set.indicator_apply]
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
    setIntegral_congr_ae measurableSet_Ioc hae, setIntegral_indicator measurableSet_Ico,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hvol : volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico a b) = ENNReal.ofReal (b - a) := by
    refine le_antisymm ?_ ?_
    · calc volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico a b)
          ≤ volume (Set.Icc a b) := measure_mono (fun t ht => Set.Ico_subset_Icc_self ht.2)
        _ = ENNReal.ofReal (b - a) := Real.volume_Icc
    · calc ENNReal.ofReal (b - a) = volume (Set.Ioo a b) := (Real.volume_Ioo).symm
        _ ≤ volume (Set.Ioc (-(1/2) : ℝ) (1/2) ∩ Set.Ico a b) :=
            measure_mono (fun t ht => ⟨Set.mem_Ioc.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩,
              Set.Ioo_subset_Ico_self ht⟩)
  rw [hvol, ENNReal.toReal_ofReal (by linarith)]

/-! ### The `Int.fract`-side integral criterion -/

/-- The Riemann-integral criterion in `Int.fract` coordinates: an `IsEquidistributedModuloOne`
sequence averages every Riemann-integrable test function against `∫_{[0,1]}`.

This instantiates the general engine `tendsto_average_of_indicator_equidistributed` at `[0, 1]`.
The one piece of real work is converting the **closed**-interval counts supplied by
`IsEquidistributedModuloOne` into the **half-open** counts the engine expects, which is done by a
squeeze: `[a, b-η] ⊆ [a, b) ⊆ [a, b]`, and both outer limits are `b - a` up to `η`. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses tendsto_average_of_indicator_equidistributed]
theorem tendsto_average_fract_of_isEquidistributedModuloOne {x : ℕ → ℝ}
    (h : IsEquidistributedModuloOne x) {f : ℝ → ℝ}
    (hbdd : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f t| ≤ C)
    (hae : volume {t ∈ Set.Icc (0 : ℝ) 1 | ¬ ContinuousAt f t} = 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (𝓝 ((∫ t in Set.Icc (0 : ℝ) 1, f t) / (1 - 0))) := by
  classical
  -- Closed-interval counts, straight from the hypothesis.
  have hIcc : ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ 1 →
      Tendsto (fun N : ℕ => (((Finset.range N).filter
        (fun m => Int.fract (x m) ∈ Set.Icc c d)).card : ℝ) / N) atTop (𝓝 (d - c)) := by
    intro c d hc hcd hd
    have := h c d hcd (Set.Icc_subset_Icc hc hd)
    rwa [show (d - c) / (1 - 0) = d - c by norm_num] at this
  -- The half-open counts the engine wants, by squeezing between two closed ones.
  have hIco : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N : ℕ => (((Finset.range N).filter
        (fun m => Int.fract (x m) ∈ Set.Ico a b)).card : ℝ) / N) atTop (𝓝 (b - a)) := by
    intro a b ha hab hb
    rw [Metric.tendsto_atTop]
    intro δ hδ
    set η := min (δ/2) ((b - a)/2) with hη
    have hη0 : 0 < η := lt_min (by linarith) (by linarith)
    have hηδ : η ≤ δ/2 := min_le_left _ _
    have hηb : η ≤ (b - a)/2 := min_le_right _ _
    have hup := hIcc a b ha (le_of_lt hab) hb
    have hlo := hIcc a (b - η) ha (by linarith) (by linarith)
    rw [Metric.tendsto_atTop] at hup hlo
    obtain ⟨N₁, hN₁⟩ := hup (δ/2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := hlo (δ/2) (by linarith)
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
    have h2 := hN₂ N (le_trans (le_max_right _ _) hN)
    rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
    -- Dividing a `≤` between counts by `N` is monotone (also when `N = 0`).
    have key : ∀ u v : ℝ, u ≤ v → u / (N : ℝ) ≤ v / (N : ℝ) := by
      intro u v huv
      rw [div_eq_mul_one_div u, div_eq_mul_one_div v]
      exact mul_le_mul_of_nonneg_right huv (one_div_nonneg.mpr (Nat.cast_nonneg N))
    -- Monotonicity of the counts along `[a, b-η] ⊆ [a, b) ⊆ [a, b]`.
    have hlower : (((Finset.range N).filter
          (fun m => Int.fract (x m) ∈ Set.Icc a (b - η))).card : ℝ) / N
        ≤ (((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Ico a b)).card : ℝ) / N := by
      refine key _ _ ?_
      have : ((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Icc a (b - η))).card
          ≤ ((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Ico a b)).card := by
        refine Finset.card_le_card (fun m hm => ?_)
        simp only [Finset.mem_filter, Set.mem_Icc, Set.mem_Ico] at hm ⊢
        exact ⟨hm.1, hm.2.1, by linarith [hm.2.2]⟩
      exact_mod_cast this
    have hupper : (((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Ico a b)).card : ℝ) / N
        ≤ (((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Icc a b)).card : ℝ) / N := by
      refine key _ _ ?_
      have : ((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Ico a b)).card
          ≤ ((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Icc a b)).card := by
        refine Finset.card_le_card (fun m hm => ?_)
        simp only [Finset.mem_filter, Set.mem_Icc, Set.mem_Ico] at hm ⊢
        exact ⟨hm.1, hm.2.1, le_of_lt hm.2.2⟩
      exact_mod_cast this
    constructor <;> linarith
  -- Feed the half-open counts to the engine.
  have hH : ∀ a b : ℝ, (0 : ℝ) ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N : ℕ => (∑ m ∈ Finset.range N,
        (Set.Ico a b).indicator (fun _ => (1 : ℝ)) (Int.fract (x m))) / N) atTop
        (𝓝 ((b - a) / (1 - 0))) := by
    intro a b ha hab hb
    have hsum : ∀ N : ℕ, (∑ m ∈ Finset.range N,
        (Set.Ico a b).indicator (fun _ => (1 : ℝ)) (Int.fract (x m)))
          = (((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Ico a b)).card : ℝ) := by
      intro N; simp only [Set.indicator_apply]; rw [Finset.sum_boole]
    simp_rw [hsum]
    rw [show (b - a) / (1 - 0) = b - a by norm_num]
    exact hIco a b ha hab hb
  exact tendsto_average_of_indicator_equidistributed (c := 0) (d := 1) (by norm_num) hbdd hae
    (fun n => Int.fract (x n)) (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) hH

/-! ### The equivalence -/

/-- **Bertin's centered definition implies the `Int.fract` definition.** -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses integralCriterion_of_uniformlyDistributedModOne]
theorem isEquidistributedModuloOne_of_uniformlyDistributedModOne (x : ℕ → ℝ)
    (h : UniformlyDistributedModOne x) : IsEquidistributedModuloOne x := by
  classical
  intro c d hcd hsub
  have hc : 0 ≤ c := (hsub (Set.left_mem_Icc.mpr hcd)).1
  have hd : d ≤ 1 := (hsub (Set.right_mem_Icc.mpr hcd)).2
  have hcrit := integralCriterion_of_uniformlyDistributedModOne x h (fractInd c d)
    ⟨fractInd_bdd c d, fractInd_ae c d⟩
  rw [integral_fractInd hc hcd hd] at hcrit
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, fractInd c d (ε (x n)))
      = (((Finset.range N).filter (fun m => Int.fract (x m) ∈ Set.Icc c d)).card : ℝ) := by
    intro N
    simp only [fractInd, fract_ε]
    rw [Finset.sum_boole]
  simp_rw [hsum] at hcrit
  rw [show (d - c) / (1 - 0) = d - c by norm_num]
  exact hcrit

/-- **The `Int.fract` definition implies Bertin's centered definition.** -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses tendsto_average_fract_of_isEquidistributedModuloOne]
theorem uniformlyDistributedModOne_of_isEquidistributedModuloOne (x : ℕ → ℝ)
    (h : IsEquidistributedModuloOne x) : UniformlyDistributedModOne x := by
  classical
  intro a b ha hab hb
  have hcrit := tendsto_average_fract_of_isEquidistributedModuloOne h
    (f := epsInd a b) (epsInd_bdd a b) (epsInd_ae a b)
  have hconv : (∫ t in Set.Icc (0 : ℝ) 1, epsInd a b t) / (1 - 0) = b - a := by
    rw [← integral_epsInd ha hab hb,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc]
    norm_num
  rw [hconv] at hcrit
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, epsInd a b (Int.fract (x n)))
      = (countModOne x a b N : ℝ) := by
    intro N
    simp only [epsInd, ε_fract, countModOne]
    rw [Finset.sum_boole]
  simp_rw [hsum] at hcrit
  exact hcrit

/-- **The two uniform-distribution conventions agree.** Bertin's centered Definition 4.2 and the
`Int.fract`-based `IsEquidistributedModuloOne` define the same class of sequences, so any result
proved in one convention transfers verbatim to the other. -/
@[category research solved, AMS 11, ref "Ber92" "KN74",
  formal_uses isEquidistributedModuloOne_of_uniformlyDistributedModOne
    uniformlyDistributedModOne_of_isEquidistributedModuloOne]
theorem uniformlyDistributedModOne_iff_isEquidistributedModuloOne (x : ℕ → ℝ) :
    UniformlyDistributedModOne x ↔ IsEquidistributedModuloOne x :=
  ⟨isEquidistributedModuloOne_of_uniformlyDistributedModOne x,
    uniformlyDistributedModOne_of_isEquidistributedModuloOne x⟩

end Bertin
