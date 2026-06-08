/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# The Riemann-integral (Weyl) criterion for equidistribution

For a point sequence `(yₙ)` in a compact interval `[c, d]`, this file upgrades the
*interval-indicator* equidistribution hypothesis

  `(1/N) · #{ n < N | yₙ ∈ [a, b) }  →  (b - a) / (d - c)`   for every `[a, b) ⊆ [c, d)`

to the *integral criterion*

  `(1/N) · ∑_{n < N} f (yₙ)  →  (1/(d - c)) · ∫_c^d f`        for every Riemann-integrable `f`,

where "Riemann-integrable" is taken in the sense of **Lebesgue's criterion**: `f` is bounded on
`[c, d]` and its set of discontinuities there is Lebesgue-null (see `Real.volume`). This is the
content of `tendsto_average_of_indicator_equidistributed`.

The proof approximates `f` from below and above by the **dyadic step functions** `lowerStep`,
`upperStep` (the infimum / supremum of `f` over the `2ⁿ` dyadic subintervals of `[c, d]`). At every
continuity point the two approximants pinch together as `n → ∞`; since the discontinuity set is
null, dominated convergence gives `∫ lowerStepₙ, ∫ upperStepₙ → ∫ f` and `f` integrable
(`isRiemann_dct`). The interval-indicator hypothesis pins the limit of `(1/N) ∑ f(yₙ)` between the
two step-function averages, and an `ε`-squeeze finishes.

This is the standard route to the Riemann-integral form of **Weyl's equidistribution criterion**;
the dyadic-step half is the "bounded + a.e.-continuous ⇒ Riemann-integrable" direction of Lebesgue's
criterion (cf. Rudin, *Principles of Mathematical Analysis*, Thm 11.33).
-/

open MeasureTheory Filter Topology Set

/-- Length of a dyadic subinterval of `[c, d]` at level `n`: `(d - c) / 2ⁿ`. -/
noncomputable def pieceLen (c d : ℝ) (n : ℕ) : ℝ := (d - c) / 2 ^ n

/-- The `k`-th dyadic subinterval of `[c, d]` at level `n`, half-open:
`[c + k·(d-c)/2ⁿ, c + (k+1)·(d-c)/2ⁿ)`. For `k < 2ⁿ` these tile `[c, d)`. -/
def pieceSet (c d : ℝ) (n k : ℕ) : Set ℝ :=
  Ico (c + (k : ℝ) * pieceLen c d n) (c + ((k : ℝ) + 1) * pieceLen c d n)

/-- The index of the dyadic subinterval of level `n` containing `x` (for `x ∈ [c, d)`). -/
noncomputable def pieceIdx (c d : ℝ) (n : ℕ) (x : ℝ) : ℕ := (⌊(x - c) / pieceLen c d n⌋).toNat

/-- A dyadic step function on `[c, d]` at level `n`: the finite combination
`∑_{k < 2ⁿ} v k · 𝟙_{pieceSet c d n k}` of indicators of the level-`n` dyadic subintervals. -/
noncomputable def stepFun (c d : ℝ) (n : ℕ) (v : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), v k * (pieceSet c d n k).indicator (fun _ => (1 : ℝ)) x

/-- The lower dyadic approximant of `f` at level `n`: the infimum of `f` over each level-`n`
dyadic subinterval. -/
noncomputable def lowerStep (f : ℝ → ℝ) (c d : ℝ) (n : ℕ) : ℝ → ℝ :=
  stepFun c d n (fun k => sInf (f '' pieceSet c d n k))

/-- The upper dyadic approximant of `f` at level `n`: the supremum of `f` over each level-`n`
dyadic subinterval. -/
noncomputable def upperStep (f : ℝ → ℝ) (c d : ℝ) (n : ℕ) : ℝ → ℝ :=
  stepFun c d n (fun k => sSup (f '' pieceSet c d n k))

private theorem pieceLen_pos {c d : ℝ} (hcd : c < d) (n : ℕ) : 0 < pieceLen c d n :=
  div_pos (by linarith) (by positivity)

private theorem measurableSet_pieceSet {c d : ℝ} {n k : ℕ} : MeasurableSet (pieceSet c d n k) :=
  measurableSet_Ico

private theorem mem_pieceSet_pieceIdx {c d : ℝ} (hcd : c < d) {n : ℕ} {x : ℝ} (hx : x ∈ Ico c d) :
    x ∈ pieceSet c d n (pieceIdx c d n x) := by
  have hδ : 0 < pieceLen c d n := pieceLen_pos hcd n
  have hr0 : 0 ≤ (x - c) / pieceLen c d n := div_nonneg (by linarith [hx.1]) hδ.le
  have hcast : ((pieceIdx c d n x : ℕ) : ℝ) = ((⌊(x - c) / pieceLen c d n⌋ : ℤ) : ℝ) := by
    rw [pieceIdx]; exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr hr0)
  rw [pieceSet, Set.mem_Ico, hcast]
  have hlo : (⌊(x - c) / pieceLen c d n⌋ : ℝ) ≤ (x - c) / pieceLen c d n := Int.floor_le _
  have hhi : (x - c) / pieceLen c d n < ⌊(x - c) / pieceLen c d n⌋ + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hδ] at hlo
  rw [div_lt_iff₀ hδ] at hhi
  exact ⟨by linarith, by linarith⟩

private theorem pieceIdx_lt {c d : ℝ} (hcd : c < d) {n : ℕ} {x : ℝ} (hx : x ∈ Ico c d) :
    pieceIdx c d n x < 2 ^ n := by
  have hδ : 0 < pieceLen c d n := pieceLen_pos hcd n
  have hr0 : 0 ≤ (x - c) / pieceLen c d n := div_nonneg (by linarith [hx.1]) hδ.le
  have hrlt : (x - c) / pieceLen c d n < 2 ^ n := by
    rw [pieceLen, div_div_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < d - c)]
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) n, hx.2]
  have hnn : (0:ℤ) ≤ ⌊(x - c) / pieceLen c d n⌋ := Int.floor_nonneg.mpr hr0
  have hlt : ⌊(x - c) / pieceLen c d n⌋ < ((2 ^ n : ℕ) : ℤ) := by
    rw [Int.floor_lt]; push_cast; exact hrlt
  rw [pieceIdx]; omega

private theorem stepFun_apply_of_mem {c d : ℝ} (hcd : c < d) {n : ℕ} (v : ℕ → ℝ) {x : ℝ}
    (hx : x ∈ Ico c d) : stepFun c d n v x = v (pieceIdx c d n x) := by
  have key : ∀ k ∈ Finset.range (2 ^ n), k ≠ pieceIdx c d n x →
      v k * (pieceSet c d n k).indicator (fun _ => (1:ℝ)) x = 0 := by
    intro k _ hk
    have hxnot : x ∉ pieceSet c d n k := by
      intro hmem
      have hδ : 0 < pieceLen c d n := pieceLen_pos hcd n
      rw [pieceSet, Set.mem_Ico] at hmem
      have e1 : (k : ℝ) ≤ (x - c) / pieceLen c d n := by rw [le_div_iff₀ hδ]; linarith [hmem.1]
      have e2 : (x - c) / pieceLen c d n < (k : ℝ) + 1 := by rw [div_lt_iff₀ hδ]; linarith [hmem.2]
      have hfloor : ⌊(x - c) / pieceLen c d n⌋ = (k : ℤ) := by
        rw [Int.floor_eq_iff]; exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
      apply hk; rw [pieceIdx, hfloor]; simp
    rw [Set.indicator_of_notMem hxnot, mul_zero]
  rw [stepFun, Finset.sum_eq_single_of_mem (pieceIdx c d n x)
      (Finset.mem_range.mpr (pieceIdx_lt hcd hx)) key,
      Set.indicator_of_mem (mem_pieceSet_pieceIdx hcd hx), mul_one]

private theorem pieceSet_subset_Icc {c d : ℝ} (hcd : c < d) {n k : ℕ} (hk : k < 2 ^ n) :
    pieceSet c d n k ⊆ Icc c d := by
  have hδ : 0 < pieceLen c d n := pieceLen_pos hcd n
  intro y hy
  rw [pieceSet, Set.mem_Ico] at hy
  rw [Set.mem_Icc]
  refine ⟨by linarith [hy.1, mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) hδ.le], ?_⟩
  have hkk : ((k : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast hk
  have key : ((k:ℝ) + 1) * pieceLen c d n ≤ d - c := by
    calc ((k:ℝ) + 1) * pieceLen c d n ≤ 2 ^ n * pieceLen c d n :=
          mul_le_mul_of_nonneg_right hkk hδ.le
      _ = d - c := by rw [pieceLen]; field_simp
  linarith [hy.2, key]

private theorem bddBelow_image {c d : ℝ} (hcd : c < d) {f : ℝ → ℝ} {C : ℝ}
    (hbdd : ∀ t ∈ Icc c d, |f t| ≤ C) {n k : ℕ} (hk : k < 2 ^ n) :
    BddBelow (f '' pieceSet c d n k) := by
  refine ⟨-C, ?_⟩; rintro _ ⟨y, hy, rfl⟩
  have := hbdd y (pieceSet_subset_Icc hcd hk hy); rw [abs_le] at this; linarith [this.1]

private theorem bddAbove_image {c d : ℝ} (hcd : c < d) {f : ℝ → ℝ} {C : ℝ}
    (hbdd : ∀ t ∈ Icc c d, |f t| ≤ C) {n k : ℕ} (hk : k < 2 ^ n) :
    BddAbove (f '' pieceSet c d n k) := by
  refine ⟨C, ?_⟩; rintro _ ⟨y, hy, rfl⟩
  have := hbdd y (pieceSet_subset_Icc hcd hk hy); rw [abs_le] at this; linarith [this.2]

private theorem measurable_stepFun {c d : ℝ} (n : ℕ) (v : ℕ → ℝ) : Measurable (stepFun c d n v) := by
  unfold stepFun
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_const.indicator measurableSet_pieceSet).const_mul (v k)

private theorem measurable_lowerStep {c d : ℝ} (f : ℝ → ℝ) (n : ℕ) :
    Measurable (lowerStep f c d n) := by unfold lowerStep; exact measurable_stepFun n _

private theorem measurable_upperStep {c d : ℝ} (f : ℝ → ℝ) (n : ℕ) :
    Measurable (upperStep f c d n) := by unfold upperStep; exact measurable_stepFun n _

private theorem lowerStep_le {c d : ℝ} (hcd : c < d) {f : ℝ → ℝ} {C : ℝ}
    (hbdd : ∀ t ∈ Icc c d, |f t| ≤ C) {n : ℕ} {x : ℝ} (hx : x ∈ Ico c d) :
    lowerStep f c d n x ≤ f x := by
  rw [lowerStep, stepFun_apply_of_mem hcd _ hx]
  exact csInf_le (bddBelow_image hcd hbdd (pieceIdx_lt hcd hx)) ⟨x, mem_pieceSet_pieceIdx hcd hx, rfl⟩

private theorem le_upperStep {c d : ℝ} (hcd : c < d) {f : ℝ → ℝ} {C : ℝ}
    (hbdd : ∀ t ∈ Icc c d, |f t| ≤ C) {n : ℕ} {x : ℝ} (hx : x ∈ Ico c d) :
    f x ≤ upperStep f c d n x := by
  rw [upperStep, stepFun_apply_of_mem hcd _ hx]
  exact le_csSup (bddAbove_image hcd hbdd (pieceIdx_lt hcd hx)) ⟨x, mem_pieceSet_pieceIdx hcd hx, rfl⟩

private theorem abs_lowerStep_le {c d : ℝ} (hcd : c < d) {f : ℝ → ℝ} {C : ℝ}
    (hbdd : ∀ t ∈ Icc c d, |f t| ≤ C) {n : ℕ} {x : ℝ} (hx : x ∈ Ico c d) :
    |lowerStep f c d n x| ≤ C := by
  rw [lowerStep, stepFun_apply_of_mem hcd _ hx]
  have hsub : pieceSet c d n (pieceIdx c d n x) ⊆ Icc c d :=
    pieceSet_subset_Icc hcd (pieceIdx_lt hcd hx)
  have hxin : x ∈ pieceSet c d n (pieceIdx c d n x) := mem_pieceSet_pieceIdx hcd hx
  have hbb : BddBelow (f '' pieceSet c d n (pieceIdx c d n x)) :=
    ⟨-C, by rintro _ ⟨y, hy, rfl⟩; linarith [abs_le.mp (hbdd y (hsub hy))]⟩
  rw [abs_le]
  refine ⟨le_csInf ⟨f x, x, hxin, rfl⟩ ?_, le_trans (csInf_le hbb ⟨x, hxin, rfl⟩) ?_⟩
  · rintro _ ⟨y, hy, rfl⟩; linarith [abs_le.mp (hbdd y (hsub hy))]
  · linarith [abs_le.mp (hbdd x (hsub hxin))]

private theorem abs_upperStep_le {c d : ℝ} (hcd : c < d) {f : ℝ → ℝ} {C : ℝ}
    (hbdd : ∀ t ∈ Icc c d, |f t| ≤ C) {n : ℕ} {x : ℝ} (hx : x ∈ Ico c d) :
    |upperStep f c d n x| ≤ C := by
  rw [upperStep, stepFun_apply_of_mem hcd _ hx]
  have hsub : pieceSet c d n (pieceIdx c d n x) ⊆ Icc c d :=
    pieceSet_subset_Icc hcd (pieceIdx_lt hcd hx)
  have hxin : x ∈ pieceSet c d n (pieceIdx c d n x) := mem_pieceSet_pieceIdx hcd hx
  have hba : BddAbove (f '' pieceSet c d n (pieceIdx c d n x)) :=
    ⟨C, by rintro _ ⟨y, hy, rfl⟩; linarith [abs_le.mp (hbdd y (hsub hy))]⟩
  rw [abs_le]
  refine ⟨le_trans ?_ (le_csSup hba ⟨x, hxin, rfl⟩), csSup_le ⟨f x, x, hxin, rfl⟩ ?_⟩
  · linarith [abs_le.mp (hbdd x (hsub hxin))]
  · rintro _ ⟨y, hy, rfl⟩; linarith [abs_le.mp (hbdd y (hsub hy))]

private theorem setIntegral_indicator_pieceSet {c d : ℝ} (hcd : c < d) {n k : ℕ} (hk : k < 2 ^ n) :
    ∫ x in Icc c d, (pieceSet c d n k).indicator (fun _ => (1:ℝ)) x = pieceLen c d n := by
  have hdiff : c + ((k:ℝ) + 1) * pieceLen c d n - (c + (k:ℝ) * pieceLen c d n) = pieceLen c d n := by
    ring
  rw [setIntegral_indicator measurableSet_pieceSet,
      Set.inter_eq_self_of_subset_right (pieceSet_subset_Icc hcd hk),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def, pieceSet, Real.volume_Ico, hdiff,
      ENNReal.toReal_ofReal (pieceLen_pos hcd n).le]

private theorem setIntegral_stepFun {c d : ℝ} (hcd : c < d) (n : ℕ) (v : ℕ → ℝ) :
    ∫ x in Icc c d, stepFun c d n v x = ∑ k ∈ Finset.range (2 ^ n), v k * pieceLen c d n := by
  unfold stepFun
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_const_mul, setIntegral_indicator_pieceSet hcd (Finset.mem_range.mp hk)]
  · intro k _
    have hfin : volume (Icc c d) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hc : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Icc c d)) := integrableOn_const hfin
    exact (hc.indicator measurableSet_pieceSet).const_mul (v k)

/-- Local oscillation control: at a continuity point of `f`, the spread of `f` over a sequence of
shrinking sets containing the point tends to `0`. -/
private theorem tendsto_sSup_sub_sInf_of_continuousAt {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousAt f x)
    {S : ℕ → Set ℝ} {r : ℕ → ℝ} (hxS : ∀ n, x ∈ S n) (hr : Tendsto r atTop (𝓝 0))
    (hSr : ∀ n, S n ⊆ Metric.closedBall x (r n))
    {C : ℝ} (hbdd : ∀ n, ∀ y ∈ S n, |f y| ≤ C) :
    Tendsto (fun n => sSup (f '' S n) - sInf (f '' S n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hf (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hr) δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hne : (f '' S n).Nonempty := ⟨f x, x, hxS n, rfl⟩
  have hba : BddAbove (f '' S n) := ⟨C, by rintro _ ⟨y, hy, rfl⟩; linarith [abs_le.mp (hbdd n y hy)]⟩
  have hbb : BddBelow (f '' S n) := ⟨-C, by rintro _ ⟨y, hy, rfl⟩; linarith [abs_le.mp (hbdd n y hy)]⟩
  have hrn : |r n| < δ := by have := hN n hn; rwa [Real.dist_eq, sub_zero] at this
  have hclose : ∀ y ∈ S n, |f y - f x| < ε / 4 := by
    intro y hy
    have hyx : dist y x < δ := by
      have hle : dist y x ≤ r n := by have := hSr n hy; rwa [Metric.mem_closedBall] at this
      calc dist y x ≤ r n := hle
        _ ≤ |r n| := le_abs_self _
        _ < δ := hrn
    have := hδf hyx; rwa [Real.dist_eq] at this
  have hsup : sSup (f '' S n) ≤ f x + ε / 4 := by
    apply csSup_le hne; rintro _ ⟨y, hy, rfl⟩; linarith [abs_lt.mp (hclose y hy)]
  have hinf : f x - ε / 4 ≤ sInf (f '' S n) := by
    apply le_csInf hne; rintro _ ⟨y, hy, rfl⟩; linarith [abs_lt.mp (hclose y hy)]
  have hge : sInf (f '' S n) ≤ sSup (f '' S n) := csInf_le_csSup hne hbb hba
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]; linarith

private theorem tendsto_pieceLen {c d : ℝ} : Tendsto (fun n => pieceLen c d n) atTop (𝓝 0) := by
  have h : Tendsto (fun n => (d - c) * (1/2 : ℝ) ^ n) atTop (𝓝 ((d - c) * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul (d - c)
  rw [mul_zero] at h
  exact h.congr (fun n => by rw [pieceLen, div_pow, one_pow, mul_one_div])

private theorem pieceSet_pieceIdx_subset_closedBall {c d : ℝ} (hcd : c < d) {n : ℕ} {x : ℝ}
    (hx : x ∈ Ico c d) :
    pieceSet c d n (pieceIdx c d n x) ⊆ Metric.closedBall x (pieceLen c d n) := by
  intro y hy
  have hxmem := mem_pieceSet_pieceIdx (n := n) hcd hx
  rw [pieceSet, Set.mem_Ico] at hy hxmem
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  exact ⟨by linarith [hy.1, hxmem.2], by linarith [hy.2, hxmem.1]⟩

/-- At each continuity point of `f` in `[c, d)`, the upper and lower dyadic approximants pinch
together: `upperStepₙ x - lowerStepₙ x → 0`. -/
private theorem tendsto_upperStep_sub_lowerStep {c d : ℝ} (hcd : c < d) {f : ℝ → ℝ} {C : ℝ}
    (hbdd : ∀ t ∈ Icc c d, |f t| ≤ C) {x : ℝ} (hx : x ∈ Ico c d) (hf : ContinuousAt f x) :
    Tendsto (fun n => upperStep f c d n x - lowerStep f c d n x) atTop (𝓝 0) := by
  have hcollapse : (fun n => upperStep f c d n x - lowerStep f c d n x)
      = (fun n => sSup (f '' pieceSet c d n (pieceIdx c d n x))
                - sInf (f '' pieceSet c d n (pieceIdx c d n x))) := by
    funext n
    rw [upperStep, lowerStep, stepFun_apply_of_mem hcd _ hx, stepFun_apply_of_mem hcd _ hx]
  rw [hcollapse]
  exact tendsto_sSup_sub_sInf_of_continuousAt hf
    (fun n => mem_pieceSet_pieceIdx hcd hx) tendsto_pieceLen
    (fun n => pieceSet_pieceIdx_subset_closedBall hcd hx)
    (fun n y hy => hbdd y (pieceSet_subset_Icc hcd (pieceIdx_lt hcd hx) hy))

/-- Sampling a dyadic step function: under interval-indicator equidistribution of `(yₘ)`, the
average `(1/N) ∑_{m<N} (stepFun … v) (yₘ)` converges to `(∑_k v k · pieceLen) / (d - c)`. -/
private theorem tendsto_average_stepFun {c d : ℝ} (hcd : c < d) {n : ℕ} (v : ℕ → ℝ) {y : ℕ → ℝ}
    (H : ∀ a b : ℝ, c ≤ a → a < b → b ≤ d →
        Tendsto (fun N => (∑ m ∈ Finset.range N, (Ico a b).indicator (fun _ => (1:ℝ)) (y m)) / N)
          atTop (𝓝 ((b - a) / (d - c)))) :
    Tendsto (fun N => (∑ m ∈ Finset.range N, stepFun c d n v (y m)) / N) atTop
      (𝓝 ((∑ k ∈ Finset.range (2 ^ n), v k * pieceLen c d n) / (d - c))) := by
  have hδ : 0 < pieceLen c d n := pieceLen_pos hcd n
  have hrw : ∀ N : ℕ, (∑ m ∈ Finset.range N, stepFun c d n v (y m)) / N
      = ∑ k ∈ Finset.range (2 ^ n),
          v k * ((∑ m ∈ Finset.range N, (pieceSet c d n k).indicator (fun _ => (1:ℝ)) (y m)) / N) := by
    intro N
    simp only [stepFun]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
  rw [tendsto_congr hrw]
  have htarget : (∑ k ∈ Finset.range (2 ^ n), v k * pieceLen c d n) / (d - c)
      = ∑ k ∈ Finset.range (2 ^ n), v k * (pieceLen c d n / (d - c)) := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun k _ => mul_div_assoc _ _ _
  rw [htarget]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkk : k < 2 ^ n := Finset.mem_range.mp hk
  have haa : c ≤ c + (k:ℝ) * pieceLen c d n := by nlinarith [Nat.cast_nonneg (α := ℝ) k, hδ.le]
  have hab : c + (k:ℝ) * pieceLen c d n < c + ((k:ℝ) + 1) * pieceLen c d n := by nlinarith [hδ]
  have hbb : c + ((k:ℝ) + 1) * pieceLen c d n ≤ d := by
    have hkr : ((k:ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast hkk
    have hle : ((k:ℝ) + 1) * pieceLen c d n ≤ d - c := by
      calc ((k:ℝ) + 1) * pieceLen c d n ≤ 2 ^ n * pieceLen c d n :=
            mul_le_mul_of_nonneg_right hkr hδ.le
        _ = d - c := by rw [pieceLen]; field_simp
    linarith
  have hlen : c + ((k:ℝ) + 1) * pieceLen c d n - (c + (k:ℝ) * pieceLen c d n) = pieceLen c d n := by
    ring
  have hH := H (c + (k:ℝ) * pieceLen c d n) (c + ((k:ℝ) + 1) * pieceLen c d n) haa hab hbb
  rw [hlen] at hH
  exact hH.const_mul (v k)

/-- An `ε`-squeeze: if `Sf` is pinched, for every `n`, between sequences `Sl n`, `Su n` whose
`N`-limits `al n`, `au n` both tend (in `n`) to `L`, then `Sf → L`. -/
private theorem tendsto_of_double_squeeze {Sf : ℕ → ℝ} {Sl Su : ℕ → ℕ → ℝ} {al au : ℕ → ℝ} {L : ℝ}
    (hle : ∀ n N, Sl n N ≤ Sf N) (hge : ∀ n N, Sf N ≤ Su n N)
    (hSl : ∀ n, Tendsto (Sl n) atTop (𝓝 (al n))) (hSu : ∀ n, Tendsto (Su n) atTop (𝓝 (au n)))
    (hal : Tendsto al atTop (𝓝 L)) (hau : Tendsto au atTop (𝓝 L)) :
    Tendsto Sf atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn1, hn2⟩ : ∃ n, |al n - L| < ε / 2 ∧ |au n - L| < ε / 2 := by
    obtain ⟨N1, h1⟩ := (Metric.tendsto_atTop.mp hal) (ε / 2) (by positivity)
    obtain ⟨N2, h2⟩ := (Metric.tendsto_atTop.mp hau) (ε / 2) (by positivity)
    refine ⟨max N1 N2, ?_, ?_⟩
    · have := h1 (max N1 N2) (le_max_left _ _); rwa [Real.dist_eq] at this
    · have := h2 (max N1 N2) (le_max_right _ _); rwa [Real.dist_eq] at this
  obtain ⟨M1, hM1⟩ := (Metric.tendsto_atTop.mp (hSl n)) (ε / 2) (by positivity)
  obtain ⟨M2, hM2⟩ := (Metric.tendsto_atTop.mp (hSu n)) (ε / 2) (by positivity)
  refine ⟨max M1 M2, fun N hN => ?_⟩
  have b1 : |Sl n N - al n| < ε / 2 := by
    have := hM1 N (le_trans (le_max_left _ _) hN); rwa [Real.dist_eq] at this
  have b2 : |Su n N - au n| < ε / 2 := by
    have := hM2 N (le_trans (le_max_right _ _) hN); rwa [Real.dist_eq] at this
  rw [Real.dist_eq, abs_lt]; rw [abs_lt] at hn1 hn2 b1 b2
  exact ⟨by linarith [hle n N], by linarith [hge n N]⟩

/-- **Lebesgue's criterion, dyadic form.** If `f` is bounded on `[c, d]` and its set of
discontinuities there is Lebesgue-null, then `f` is integrable on `[c, d]` and the integrals of its
lower and upper dyadic approximants both converge to `∫_{[c,d]} f`. -/
theorem isRiemann_dct {c d : ℝ} (hcd : c < d) {f : ℝ → ℝ} {C : ℝ}
    (hbdd : ∀ t ∈ Icc c d, |f t| ≤ C) (hae : volume {t ∈ Icc c d | ¬ ContinuousAt f t} = 0) :
    IntegrableOn f (Icc c d) ∧
    Tendsto (fun n => ∫ x in Icc c d, lowerStep f c d n x) atTop (𝓝 (∫ x in Icc c d, f x)) ∧
    Tendsto (fun n => ∫ x in Icc c d, upperStep f c d n x) atTop (𝓝 (∫ x in Icc c d, f x)) := by
  have hfin : volume (Icc c d) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have haeIco : ∀ᵐ x ∂(volume.restrict (Icc c d)), x ∈ Ico c d := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ d := by
      rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hne] with x hx hxmem
    exact ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx⟩
  have hcont : ∀ᵐ x ∂(volume.restrict (Icc c d)), ContinuousAt f x := by
    rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
    have hset : {x | ¬ (x ∈ Icc c d → ContinuousAt f x)} = {t ∈ Icc c d | ¬ ContinuousAt f t} := by
      ext x; simp only [Set.mem_setOf_eq, Classical.not_imp]
    rw [hset]; exact hae
  have hlimg : ∀ᵐ x ∂(volume.restrict (Icc c d)),
      Tendsto (fun n => lowerStep f c d n x) atTop (𝓝 (f x)) := by
    filter_upwards [haeIco, hcont] with x hx hcv
    have h0 : Tendsto (fun n => f x - lowerStep f c d n x) atTop (𝓝 0) :=
      squeeze_zero (fun n => by linarith [lowerStep_le (n := n) hcd hbdd hx])
        (fun n => by linarith [le_upperStep (n := n) hcd hbdd hx])
        (tendsto_upperStep_sub_lowerStep hcd hbdd hx hcv)
    have := h0.const_sub (f x); simpa using this
  have hlimG : ∀ᵐ x ∂(volume.restrict (Icc c d)),
      Tendsto (fun n => upperStep f c d n x) atTop (𝓝 (f x)) := by
    filter_upwards [haeIco, hcont] with x hx hcv
    have h0 : Tendsto (fun n => upperStep f c d n x - f x) atTop (𝓝 0) :=
      squeeze_zero (fun n => by linarith [le_upperStep (n := n) hcd hbdd hx])
        (fun n => by linarith [lowerStep_le (n := n) hcd hbdd hx])
        (tendsto_upperStep_sub_lowerStep hcd hbdd hx hcv)
    have := h0.add_const (f x); simpa using this
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Icc c d)) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (measurable_lowerStep f n).aestronglyMeasurable) hlimg
  have hfbd : ∀ᵐ x ∂(volume.restrict (Icc c d)), ‖f x‖ ≤ C := by
    filter_upwards [haeIco] with x hx
    have hl := abs_le.mp (abs_lowerStep_le (n := 0) hcd hbdd hx)
    have hu := abs_le.mp (abs_upperStep_le (n := 0) hcd hbdd hx)
    have h1 := lowerStep_le (n := 0) hcd hbdd hx
    have h2 := le_upperStep (n := 0) hcd hbdd hx
    rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [hl.1], by linarith [hu.2]⟩
  have hCint : Integrable (fun _ : ℝ => C) (volume.restrict (Icc c d)) := integrableOn_const hfin
  have hbl : ∀ n, ∀ᵐ x ∂(volume.restrict (Icc c d)), ‖lowerStep f c d n x‖ ≤ C := fun n => by
    filter_upwards [haeIco] with x hx; rw [Real.norm_eq_abs]; exact abs_lowerStep_le hcd hbdd hx
  have hbu : ∀ n, ∀ᵐ x ∂(volume.restrict (Icc c d)), ‖upperStep f c d n x‖ ≤ C := fun n => by
    filter_upwards [haeIco] with x hx; rw [Real.norm_eq_abs]; exact abs_upperStep_le hcd hbdd hx
  refine ⟨hCint.mono' hfmeas hfbd, ?_, ?_⟩
  · exact tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (measurable_lowerStep f n).aestronglyMeasurable) hCint hbl hlimg
  · exact tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (measurable_upperStep f n).aestronglyMeasurable) hCint hbu hlimG

/-- **Riemann-integral (Weyl) criterion for equidistribution.** Let `(yₙ)` be a sequence in
`[c, d)` (`c < d`) such that for every subinterval `[a, b) ⊆ [c, d)` the proportion of indices
`n < N` with `yₙ ∈ [a, b)` tends to `(b - a) / (d - c)`. Then for every function `f` that is
bounded on `[c, d]` with a Lebesgue-null discontinuity set (i.e. Riemann-integrable, by Lebesgue's
criterion), the average `(1/N) ∑_{n<N} f(yₙ)` converges to `(1/(d - c)) ∫_{[c,d]} f`. -/
theorem tendsto_average_of_indicator_equidistributed {f : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (hbdd : ∃ C, ∀ t ∈ Icc c d, |f t| ≤ C)
    (hae : volume {t ∈ Icc c d | ¬ ContinuousAt f t} = 0)
    (y : ℕ → ℝ) (hy : ∀ n, y n ∈ Ico c d)
    (H : ∀ a b : ℝ, c ≤ a → a < b → b ≤ d →
        Tendsto (fun N => (∑ m ∈ Finset.range N, (Ico a b).indicator (fun _ => (1:ℝ)) (y m)) / N)
          atTop (𝓝 ((b - a) / (d - c)))) :
    Tendsto (fun N => (∑ m ∈ Finset.range N, f (y m)) / N) atTop
      (𝓝 ((∫ t in Icc c d, f t) / (d - c))) := by
  obtain ⟨C, hbddC⟩ := hbdd
  obtain ⟨hfint, hlow, hupp⟩ := isRiemann_dct hcd hbddC hae
  apply tendsto_of_double_squeeze
    (Sl := fun n N => (∑ m ∈ Finset.range N, lowerStep f c d n (y m)) / N)
    (Su := fun n N => (∑ m ∈ Finset.range N, upperStep f c d n (y m)) / N)
    (al := fun n => (∫ x in Icc c d, lowerStep f c d n x) / (d - c))
    (au := fun n => (∫ x in Icc c d, upperStep f c d n x) / (d - c))
  · intro n N; gcongr with m hm; exact lowerStep_le hcd hbddC (hy m)
  · intro n N; gcongr with m hm; exact le_upperStep hcd hbddC (hy m)
  · intro n
    have h := tendsto_average_stepFun hcd (n := n) (fun k => sInf (f '' pieceSet c d n k)) (y := y) H
    rw [← setIntegral_stepFun hcd n (fun k => sInf (f '' pieceSet c d n k))] at h
    simpa only [lowerStep] using h
  · intro n
    have h := tendsto_average_stepFun hcd (n := n) (fun k => sSup (f '' pieceSet c d n k)) (y := y) H
    rw [← setIntegral_stepFun hcd n (fun k => sSup (f '' pieceSet c d n k))] at h
    simpa only [upperStep] using h
  · exact hlow.div_const (d - c)
  · exact hupp.div_const (d - c)
