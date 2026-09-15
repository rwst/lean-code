/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Confinement
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# R0: full support at `1+√2` and at `(3+√5)/2`

Placeholder docstring, filled in at the end.
-/

namespace BB61

open Set

/-! ## The covering lemma (R0 Lemma 2) -/

/-- One greedy step: the digit taken at residual `w`, in a base-`r` system with digit set
`{0, 1, …, n}`.  Take as much as the residual allows, but never more than `n`. -/
noncomputable def covDigitAt (n : ℕ) (w : ℝ) : ℕ := min n ⌊w⌋₊

/-- The residual of the greedy after `i` steps, rescaled by `r⁻ⁱ`. -/
noncomputable def covRes (r : ℝ) (n : ℕ) (y : ℝ) : ℕ → ℝ
  | 0 => y
  | i + 1 => (covRes r n y i - (covDigitAt n (covRes r n y i) : ℝ)) / r

/-- The greedy digit stream for the target `y`. -/
noncomputable def covDigit (r : ℝ) (n : ℕ) (y : ℝ) (i : ℕ) : ℕ :=
  covDigitAt n (covRes r n y i)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem covDigit_le (r : ℝ) (n : ℕ) (y : ℝ) (i : ℕ) : covDigit r n y i ≤ n :=
  min_le_left _ _

/-- **The greedy step keeps the residual in range.**  If `n + rL = L` and `rL ≥ 1`, then
subtracting the greedy digit from a point of `[0, L]` lands in `[0, rL]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sub_covDigitAt_mem {r L : ℝ} {n : ℕ} (hL : (n : ℝ) + r * L = L) (hrL : 1 ≤ r * L)
    {w : ℝ} (hw : w ∈ Set.Icc 0 L) : w - (covDigitAt n w : ℝ) ∈ Set.Icc 0 (r * L) := by
  obtain ⟨hw0, hwL⟩ := hw
  rcases Nat.lt_or_ge n ⌊w⌋₊ with hf | hf
  · have hmin : covDigitAt n w = n := min_eq_left hf.le
    rw [hmin]
    have hn : (n : ℝ) < (⌊w⌋₊ : ℝ) := by exact_mod_cast hf
    have hfw : ((⌊w⌋₊ : ℕ) : ℝ) ≤ w := Nat.floor_le hw0
    exact ⟨by linarith, by linarith⟩
  · have hmin : covDigitAt n w = ⌊w⌋₊ := min_eq_right hf
    rw [hmin]
    refine ⟨by linarith [Nat.floor_le hw0], ?_⟩
    have := Nat.lt_floor_add_one w
    linarith

/-- **The greedy invariant**: every residual stays in `[0, L]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem covRes_mem {r L : ℝ} {n : ℕ} (hr : 0 < r) (hL : (n : ℝ) + r * L = L) (hrL : 1 ≤ r * L)
    {y : ℝ} (hy : y ∈ Set.Icc 0 L) (i : ℕ) : covRes r n y i ∈ Set.Icc 0 L := by
  induction i with
  | zero => exact hy
  | succ i ih =>
      obtain ⟨h0, h1⟩ := sub_covDigitAt_mem hL hrL ih
      have hstep : covRes r n y (i + 1)
          = (covRes r n y i - (covDigitAt n (covRes r n y i) : ℝ)) / r := rfl
      rw [hstep]
      refine ⟨div_nonneg h0 hr.le, ?_⟩
      rw [div_le_iff₀ hr]
      linarith [h1]

/-- **The greedy partial-sum identity**: after `m` steps the digits taken account for `y`
up to the rescaled residual. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem covRes_partial {r : ℝ} (hr : r ≠ 0) (n : ℕ) (y : ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (covDigit r n y i : ℝ) * r ^ i + r ^ m * covRes r n y m = y := by
  induction m with
  | zero => simp [covRes]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hstep : covRes r n y (m + 1)
          = (covRes r n y m - (covDigit r n y m : ℝ)) / r := rfl
      rw [hstep, pow_succ]
      field_simp
      linarith [ih]

/-- **R0 Lemma 2, the constructive half.**  If `n + rL = L` and `rL ≥ 1`, every point of
`[0, L]` is `∑_{i≥0} u_i rⁱ` for digits `u_i ∈ {0,…,n}` — and the digits are the greedy
ones.  This is the covering lemma of `note-1061-R0.html` §3, in the form the two
`confCircle = univ` theorems below consume. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_covDigit {r L : ℝ} {n : ℕ} (hr0 : 0 < r) (hr1 : r < 1)
    (hL : (n : ℝ) + r * L = L) (hrL : 1 ≤ r * L) {y : ℝ} (hy : y ∈ Set.Icc 0 L) :
    ∑' i : ℕ, (covDigit r n y i : ℝ) * r ^ i = y := by
  have hsum : Summable fun i : ℕ => (covDigit r n y i : ℝ) * r ^ i := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left (n : ℝ))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast covDigit_le r n y i) (by positivity)
  have hpart := hsum.hasSum.tendsto_sum_nat
  have htail : Filter.Tendsto (fun m : ℕ => r ^ m * covRes r n y m) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (fun m => ?_)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul L)
    have hm := covRes_mem hr0 hL hrL hy m
    have hp : (0 : ℝ) ≤ r ^ m := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hm.1), mul_comm L]
    exact mul_le_mul_of_nonneg_left hm.2 hp
  have hy' : Filter.Tendsto
      (fun m : ℕ => ∑ i ∈ Finset.range m, (covDigit r n y i : ℝ) * r ^ i)
      Filter.atTop (nhds y) := by
    have : (fun m : ℕ => ∑ i ∈ Finset.range m, (covDigit r n y i : ℝ) * r ^ i)
        = fun m : ℕ => y - r ^ m * covRes r n y m := by
      funext m
      linarith [covRes_partial hr0.ne' n y m]
    rw [this]
    simpa using tendsto_const_nhds.sub htail
  exact tendsto_nhds_unique hpart hy'

/-- **R0 Lemma 2, the easy half**: a digit sum with digits `≤ n` lies in `[0, L]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_digit_mem_Icc {r L : ℝ} {n : ℕ} (hr0 : 0 < r) (hr1 : r < 1)
    (hL : (n : ℝ) + r * L = L) {u : ℕ → ℕ} (hu : ∀ i, u i ≤ n) :
    ∑' i : ℕ, (u i : ℝ) * r ^ i ∈ Set.Icc 0 L := by
  have hgeom : Summable fun i : ℕ => (n : ℝ) * r ^ i :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  have hsum : Summable fun i : ℕ => (u i : ℝ) * r ^ i := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hgeom
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hu i) (by positivity)
  refine ⟨tsum_nonneg fun i => by positivity, ?_⟩
  have hle : ∑' i : ℕ, (u i : ℝ) * r ^ i ≤ ∑' i : ℕ, (n : ℝ) * r ^ i :=
    hsum.tsum_le_tsum (fun i =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hu i) (by positivity)) hgeom
  have hval : ∑' i : ℕ, (n : ℝ) * r ^ i = (n : ℝ) * (1 - r)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
  rw [hval] at hle
  refine hle.trans (le_of_eq ?_)
  have hne : (1 : ℝ) - r ≠ 0 := by linarith
  field_simp
  linarith [hL]

/-! ## Splitting a `{0,1,2}` digit stream into two bits

A digit `u i ∈ {0,1,2}` is the sum of its low and high bits, and those are the two
one-sided words `(ε, δ)` the confinement set is built from. -/

/-- The low bit of a digit in `{0,1,2}`. -/
def loBit (u : ℕ → ℕ) (i : ℕ) : Bool := decide (1 ≤ u i)

/-- The high bit of a digit in `{0,1,2}`. -/
def hiBit (u : ℕ → ℕ) (i : ℕ) : Bool := decide (2 ≤ u i)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_loBit_add_dR_hiBit {u : ℕ → ℕ} {i : ℕ} (h : u i ≤ 2) :
    dR (loBit u) i + dR (hiBit u) i = (u i : ℝ) := by
  rcases Nat.lt_or_ge (u i) 1 with h1 | h1
  · have h0 : u i = 0 := by omega
    simp [dR, loBit, hiBit, h0]
  · rcases Nat.lt_or_ge (u i) 2 with h2 | h2
    · have h0 : u i = 1 := by omega
      simp [dR, loBit, hiBit, h0]
    · have h0 : u i = 2 := by omega
      simp only [dR, loBit, hiBit, h0]
      norm_num

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_dR_pow_abs {r : ℝ} (hr : |r| < 1) (ε : ℕ → Bool) :
    Summable fun k : ℕ => dR ε k * r ^ k := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg r) hr) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |dR ε k| * |r| ^ k ≤ 1 * |r| ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [abs_of_nonneg (dR_nonneg ε k)]; exact dR_le_one ε k
  _ = |r| ^ k := one_mul _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_natCast_pow {r : ℝ} {n : ℕ} (hr0 : 0 ≤ r) (hr1 : r < 1) {u : ℕ → ℕ}
    (hu : ∀ i, u i ≤ n) : Summable fun i : ℕ => (u i : ℝ) * r ^ i := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left (n : ℝ))
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hu i) (by positivity)

/-! ## The two halves of the factor map as digit sums -/

namespace QuadSetup

variable (P : QuadSetup)

/-- `π(ε)` as a digit sum in base `α⁻¹` with exponents starting at `0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_eq_tsum (ε : ℕ → Bool) :
    piVal P.α ε = (P.α - 1) * P.α⁻¹ * ∑' k : ℕ, dR ε k * (P.α⁻¹) ^ k := by
  have h : ∑' k : ℕ, dR ε k * (P.α⁻¹) ^ (k + 1)
      = P.α⁻¹ * ∑' k : ℕ, dR ε k * (P.α⁻¹) ^ k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by rw [pow_succ']; ring
  rw [piVal, h, mul_assoc]

/-- `S(δ)` as a digit sum in base `β`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wVal_eq_tsum (δ : ℕ → Bool) :
    P.wVal δ = (P.β - 1) * ∑' m : ℕ, dR δ m * P.β ^ m := by
  rw [wVal, ← tsum_mul_left]
  exact tsum_congr fun m => by rw [cCoef]; ring

/-- **The circle criterion, positive form.**  If the confinement set contains the unit
interval then it reduces onto the whole circle. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_eq_univ_of_Icc_subset (h : Set.Icc (0 : ℝ) 1 ⊆ P.confSet) :
    P.confCircle = Set.univ := by
  rw [P.confCircle_eq_image]
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) z
  exact ⟨Int.fract u, h ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩, coe_fract u⟩

/-- The membership shape the two theorems below feed to `confSet_eq`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_confSet (ε δ : ℕ → Bool) : piVal P.α ε - P.wVal δ ∈ P.confSet :=
  ⟨joinW ε δ, by rw [fRaw, futures_joinW, pasts_joinW]⟩

end QuadSetup


/-! ## The engine at a unit of norm `+1`: both halves in the same base

When `β = α⁻¹` the future half `π(ε)` and the past half `S(δ)` are digit systems in the
*same* base `β`, with the same scale factor `1-β`, so `F̃` is a single digit system with
digits `{0,1,2}` — R0 Cor. 3's step (S1)–(S3), which at a norm `+1` unit needs neither the
parity relabelling nor the `{0,1}+ρE` split. -/

namespace QuadSetup

variable (P : QuadSetup)

/-- **R0 Cor. 3, the digit identity.**  At `β = α⁻¹`, `π(loBit u) - S(hiBit u)` is the
base-`β` digit sum of `u`, scaled by `1-β`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sub_wVal_eq_of_beta_eq_inv (hβ : P.β = P.α⁻¹) {u : ℕ → ℕ} (hu : ∀ i, u i ≤ 2) :
    piVal P.α (loBit u) - P.wVal (hiBit u)
      = (1 - P.β) * ∑' k : ℕ, (u k : ℝ) * P.β ^ k := by
  have hα0 : P.α ≠ 0 := ne_of_gt P.alpha_pos
  have hfac : (P.α - 1) * P.β = 1 - P.β := by rw [hβ]; field_simp
  have hβabs : |P.β| < 1 := P.abs_beta_lt_one
  have hs1 := summable_dR_pow_abs hβabs (loBit u)
  have hs2 := summable_dR_pow_abs hβabs (hiBit u)
  have hsplit : ∑' k : ℕ, (u k : ℝ) * P.β ^ k
      = (∑' k : ℕ, dR (loBit u) k * P.β ^ k) + ∑' k : ℕ, dR (hiBit u) k * P.β ^ k := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr fun k => by rw [← dR_loBit_add_dR_hiBit (hu k)]; ring
  rw [P.piVal_eq_tsum, P.wVal_eq_tsum, ← hβ, hfac, hsplit]
  ring

end QuadSetup

/-! ## R0 Corollary 3: full support at `α = (3+√5)/2` -/

private theorem sqrt5_lt : Real.sqrt 5 < 7 / 3 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private theorem two_lt_sqrt5 : (2 : ℝ) < Real.sqrt 5 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- `α = (3+√5)/2 = φ²`, the root of `X² - 3X + 1`: trace `3`, norm `+1`, conjugate
`(3-√5)/2 = α⁻¹`.  The second of the two quadratic Pisot units in `(2,3]`. -/
noncomputable def goldenSq : QuadSetup where
  a := 3
  b := -1
  α := (3 + Real.sqrt 5) / 2
  root := by
    have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    push_cast
    nlinarith [h]
  one_lt := by have := two_lt_sqrt5; show (1 : ℝ) < (3 + Real.sqrt 5) / 2; linarith
  conj_lt := by
    have h1 := two_lt_sqrt5
    have h2 := sqrt5_lt
    rw [abs_lt]
    push_cast
    constructor <;> · show _ < _; linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_alpha : goldenSq.α = (3 + Real.sqrt 5) / 2 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_beta : goldenSq.β = (3 - Real.sqrt 5) / 2 := by
  show ((3 : ℤ) : ℝ) - (3 + Real.sqrt 5) / 2 = (3 - Real.sqrt 5) / 2
  push_cast; ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_beta_pos : 0 < goldenSq.β := by
  rw [goldenSq_beta]; have := sqrt5_lt; linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_beta_lt_one : goldenSq.β < 1 := by
  rw [goldenSq_beta]; have := two_lt_sqrt5; linarith

/-- The covering condition of R0 Lemma 2 at `n = 2`, `r = ρ`: `3ρ ≥ 1`, i.e. `α ≤ 3`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_one_le_three_beta : 1 ≤ 3 * goldenSq.β := by
  rw [goldenSq_beta]; have := sqrt5_lt; linarith

/-- `α` is a unit: `β = α⁻¹`, which is what puts both halves in the same base. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_beta_eq_inv : goldenSq.β = goldenSq.α⁻¹ := by
  have hα0 : goldenSq.α ≠ 0 := ne_of_gt goldenSq.alpha_pos
  have h : goldenSq.α * goldenSq.β = 1 := by
    rw [goldenSq_alpha, goldenSq_beta]
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [h5]
  field_simp
  linear_combination h

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_Icc_subset_confSet : Set.Icc (0 : ℝ) 2 ⊆ goldenSq.confSet := by
  intro y hy
  obtain ⟨hy0, hy2⟩ := hy
  have hρ0 : 0 < goldenSq.β := goldenSq_beta_pos
  have hρ1 : goldenSq.β < 1 := goldenSq_beta_lt_one
  have h3ρ : 1 ≤ 3 * goldenSq.β := goldenSq_one_le_three_beta
  have hden : (0 : ℝ) < 1 - goldenSq.β := by linarith
  have hL : ((2 : ℕ) : ℝ) + goldenSq.β * (2 / (1 - goldenSq.β)) = 2 / (1 - goldenSq.β) := by
    push_cast; field_simp; ring
  have hrL : 1 ≤ goldenSq.β * (2 / (1 - goldenSq.β)) := by
    rw [show goldenSq.β * (2 / (1 - goldenSq.β)) = 2 * goldenSq.β / (1 - goldenSq.β) by ring,
      le_div_iff₀ hden]
    linarith
  have ht : y / (1 - goldenSq.β) ∈ Set.Icc (0 : ℝ) (2 / (1 - goldenSq.β)) := by
    constructor
    · positivity
    · gcongr
  have htsum : ∑' k : ℕ, ((covDigit goldenSq.β 2 (y / (1 - goldenSq.β)) k : ℕ) : ℝ)
      * goldenSq.β ^ k = y / (1 - goldenSq.β) := tsum_covDigit hρ0 hρ1 hL hrL ht
  have hval := goldenSq.sub_wVal_eq_of_beta_eq_inv goldenSq_beta_eq_inv
    (covDigit_le goldenSq.β 2 (y / (1 - goldenSq.β)))
  rw [htsum] at hval
  have hy' : (1 - goldenSq.β) * (y / (1 - goldenSq.β)) = y := by field_simp
  rw [hy'] at hval
  exact hval ▸ goldenSq.mem_confSet _ _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_cCoef_nonpos (m : ℕ) : goldenSq.cCoef m ≤ 0 := by
  rw [QuadSetup.cCoef]
  have h1 := goldenSq_beta_lt_one
  have hm : (0 : ℝ) ≤ goldenSq.β ^ m := pow_nonneg goldenSq_beta_pos.le m
  nlinarith

/-- At a norm `+1` unit every window coefficient is negative, so `K ⊆ [-1, 0]` with both
endpoints attained: `P = 0` and `Q = 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_wMax : goldenSq.wMax = 0 := by
  have h : (fun m : ℕ => max (goldenSq.cCoef m) 0) = fun _ => (0 : ℝ) := by
    funext m; exact max_eq_right (goldenSq_cCoef_nonpos m)
  rw [QuadSetup.wMax, h, tsum_zero]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_wMin : goldenSq.wMin = -1 := by
  rw [QuadSetup.wMin, ← goldenSq.tsum_cCoef]
  exact tsum_congr fun m => min_eq_left (goldenSq_cCoef_nonpos m)

/-- **R0 Corollary 3.**  At `α = (3+√5)/2`, `C(α) - K = [0, 2]` — an identity of sets, and
the full convex hull `[-P, 1+Q]`, so no slack is being spent. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_confSet : goldenSq.confSet = Set.Icc 0 2 := by
  refine Set.Subset.antisymm ?_ goldenSq_Icc_subset_confSet
  rw [goldenSq.confSet_eq]
  rintro _ ⟨t, ht, s, hs, rfl⟩
  have h1 := cantorSet_subset_Icc goldenSq.one_lt ht
  have h2 := goldenSq.windowSet_subset_Icc hs
  rw [goldenSq_wMin, goldenSq_wMax] at h2
  exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- **R0 Corollary 3, gate G-1 at the companion unit.**  `X((3+√5)/2) = 𝕋`: the
confinement set of M1 Prop. 4 is the *whole* circle.  The folder's first positive instance
of `confCircle`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_confCircle : goldenSq.confCircle = Set.univ :=
  goldenSq.confCircle_eq_univ_of_Icc_subset fun _ hy =>
    goldenSq_Icc_subset_confSet ⟨hy.1, by linarith [hy.2]⟩

/-- **No support argument can decide 10.61 at `(3+√5)/2`.**  The effective criterion of
`BB61/Covering.lean` — some open subinterval of `(0,1)` missed by every orbit at every
time — is *unavailable* here, because it would force `X(α) ≠ 𝕋`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_no_avoided_interval :
    ¬ ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ (ε : ℕ → Bool) (n : ℕ),
        Int.fract (piVal goldenSq.α ε * goldenSq.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  rintro ⟨x, r, hr, hsub, havoid⟩
  exact goldenSq.confCircle_ne_univ_of_avoided hr hsub havoid goldenSq_confCircle

/-! ## The parity toolbox for a unit of norm `-1`

At `β = -ρ` the two halves sit in bases `ρ` and `-ρ`.  R0 (S2) removes the sign by the
digit relabelling `δ_m ↦ a_m`, `a_m = δ_m` at even `m` and `a_m = 1 - δ_m` at odd `m`; the
price is the constant `∑_{m odd} ρᵐ = ρ/(1-ρ²)`, which at `1+√2` is exactly `1/2`. -/

/-- The even part of the geometric series: `∑_{m even} ρᵐ = (1-ρ²)⁻¹`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_ite_even {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑' m : ℕ, (if Even m then ρ ^ m else 0) = (1 - ρ ^ 2)⁻¹ := by
  have hsq0 : (0 : ℝ) ≤ ρ ^ 2 := by positivity
  have hsq1 : ρ ^ 2 < 1 := by nlinarith
  set f : ℕ → ℝ := fun m => if Even m then ρ ^ m else 0 with hfdef
  have hev : ∀ k : ℕ, f (2 * k) = (ρ ^ 2) ^ k := by
    intro k; rw [hfdef]; simp only
    rw [ite_eq_left_of_eq_true _ _ (eq_true (even_two_mul k)), pow_mul]
  have hod : ∀ k : ℕ, f (2 * k + 1) = 0 := by
    intro k
    rw [hfdef]; simp only
    exact ite_eq_right_of_eq_false _ _ (eq_false (by simp))
  have he : Summable fun k : ℕ => f (2 * k) := by
    simp only [hev]; exact summable_geometric_of_lt_one hsq0 hsq1
  have ho : Summable fun k : ℕ => f (2 * k + 1) := by
    simp only [hod]; exact summable_zero
  rw [← tsum_even_add_odd he ho]
  simp only [hev, hod]
  rw [tsum_geometric_of_lt_one hsq0 hsq1, tsum_zero, add_zero]

/-- The odd part of the geometric series: `∑_{m odd} ρᵐ = ρ(1-ρ²)⁻¹`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_ite_odd {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑' m : ℕ, (if Even m then (0 : ℝ) else ρ ^ m) = ρ * (1 - ρ ^ 2)⁻¹ := by
  have hsq0 : (0 : ℝ) ≤ ρ ^ 2 := by positivity
  have hsq1 : ρ ^ 2 < 1 := by nlinarith
  set f : ℕ → ℝ := fun m => if Even m then (0 : ℝ) else ρ ^ m with hfdef
  have hev : ∀ k : ℕ, f (2 * k) = 0 := by
    intro k; rw [hfdef]; simp only
    exact ite_eq_left_of_eq_true _ _ (eq_true (even_two_mul k))
  have hod : ∀ k : ℕ, f (2 * k + 1) = ρ * (ρ ^ 2) ^ k := by
    intro k
    rw [hfdef]; simp only
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp)), pow_succ, pow_mul]
    ring
  have he : Summable fun k : ℕ => f (2 * k) := by
    simp only [hev]; exact summable_zero
  have ho : Summable fun k : ℕ => f (2 * k + 1) := by
    simp only [hod]; exact (summable_geometric_of_lt_one hsq0 hsq1).mul_left _
  rw [← tsum_even_add_odd he ho]
  simp only [hev, hod]
  rw [tsum_zero, zero_add, tsum_mul_left, tsum_geometric_of_lt_one hsq0 hsq1]

/-- **R0 (S2), the digit relabelling.**  `δ_m = a_m` at even `m` and `δ_m = 1 - a_m` at
odd `m`. -/
def parityFlip (a : ℕ → Bool) (m : ℕ) : Bool := if Even m then a m else !(a m)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_parityFlip_even {a : ℕ → Bool} {m : ℕ} (h : Even m) :
    dR (parityFlip a) m = dR a m := by simp [parityFlip, dR, h]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_parityFlip_odd {a : ℕ → Bool} {m : ℕ} (h : ¬ Even m) :
    dR (parityFlip a) m = 1 - dR a m := by
  have hp : parityFlip a m = !(a m) := by
    rw [parityFlip]; exact ite_eq_right_of_eq_false _ _ (eq_false h)
  simp only [dR, hp]
  cases a m <;> norm_num

/-- **R0 (S2), the identity.**  The base-`(-ρ)` digit sum of `parityFlip a` is the
base-`ρ` digit sum of `a`, less the constant `∑_{m odd} ρᵐ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_dR_parityFlip {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (a : ℕ → Bool) :
    ∑' m : ℕ, dR (parityFlip a) m * (-ρ) ^ m
      = (∑' m : ℕ, dR a m * ρ ^ m) - ρ * (1 - ρ ^ 2)⁻¹ := by
  have habs : |(-ρ)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have hs1 : Summable fun m : ℕ => dR a m * ρ ^ m := summable_dR_pow' h0 h1 a
  have hs2 : Summable fun m : ℕ => dR (parityFlip a) m * (-ρ) ^ m :=
    summable_dR_pow_abs habs _
  have hpt : ∀ m : ℕ, dR a m * ρ ^ m - dR (parityFlip a) m * (-ρ) ^ m
      = if Even m then (0 : ℝ) else ρ ^ m := by
    intro m
    by_cases hm : Even m
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), hm.neg_pow, dR_parityFlip_even hm]; ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hm), (Nat.not_even_iff_odd.mp hm).neg_pow,
        dR_parityFlip_odd hm]
      ring
  have hsub : ∑' m : ℕ, (dR a m * ρ ^ m - dR (parityFlip a) m * (-ρ) ^ m)
      = ρ * (1 - ρ ^ 2)⁻¹ := by
    rw [tsum_congr hpt]; exact tsum_ite_odd h0 h1
  rw [hs1.tsum_sub hs2] at hsub
  linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem consW_succ (b : Bool) (a : ℕ → Bool) (k : ℕ) : consW b a (k + 1) = a k := by
  simp [consW]

/-- **The shift**: peeling the constant digit off a base-`ρ` digit sum. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_dR_consW {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (b : Bool) (a : ℕ → Bool) :
    ∑' m : ℕ, dR (consW b a) m * ρ ^ m
      = dR (consW b a) 0 + ρ * ∑' k : ℕ, dR a k * ρ ^ k := by
  have hs : Summable fun m : ℕ => dR (consW b a) m * ρ ^ m := summable_dR_pow' h0 h1 _
  rw [hs.tsum_eq_zero_add]
  congr 1
  · simp
  · rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hc : dR (consW b a) (k + 1) = dR a k := by simp only [dR, consW_succ]
    rw [hc, pow_succ']
    ring

/-! ## R0 Theorem 1: full support at `α = 1+√2` -/

private theorem sqrt2_lt : Real.sqrt 2 < 3 / 2 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private theorem one_lt_sqrt2 : (1 : ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `α = 1+√2`, the silver ratio: the root of `X² - 2X - 1`, trace `2`, norm `-1`,
conjugate `1-√2 = -α⁻¹`.  Bugeaud Problem 10.61's named open case. -/
noncomputable def silver : QuadSetup where
  a := 2
  b := 1
  α := 1 + Real.sqrt 2
  root := by push_cast; nlinarith [sqrt2_sq]
  one_lt := by
    have := one_lt_sqrt2
    show (1 : ℝ) < 1 + Real.sqrt 2
    linarith
  conj_lt := by
    have h1 := one_lt_sqrt2
    have h2 := sqrt2_lt
    rw [abs_lt]
    push_cast
    constructor <;> · show _ < _; linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_alpha : silver.α = 1 + Real.sqrt 2 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_inv : silver.α⁻¹ = Real.sqrt 2 - 1 := by
  have h : silver.α * (Real.sqrt 2 - 1) = 1 := by
    show (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1
    nlinarith [sqrt2_sq]
  exact inv_eq_of_mul_eq_one_right h

/-- `β = -α⁻¹`: `α` is a unit of norm `-1`, which is what makes the two halves sit in
bases of opposite sign and forces the relabelling (S2). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_beta : silver.β = -(Real.sqrt 2 - 1) := by
  show ((2 : ℤ) : ℝ) - (1 + Real.sqrt 2) = -(Real.sqrt 2 - 1)
  push_cast; ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_rho_pos : (0 : ℝ) < Real.sqrt 2 - 1 := by have := one_lt_sqrt2; linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_rho_lt_one : Real.sqrt 2 - 1 < 1 := by have := sqrt2_lt; linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_one_sub_rho_sq : (1 : ℝ) - (Real.sqrt 2 - 1) ^ 2 = 2 * (Real.sqrt 2 - 1) := by
  nlinarith [sqrt2_sq]

/-- **The exact constant of R0 (S2)**: `∑_{m odd} ρᵐ = ρ/(1-ρ²) = 1/2`, an identity that
holds at `1+√2` and nowhere else among the quadratic Pisot units. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_odd_sum : (Real.sqrt 2 - 1) * (1 - (Real.sqrt 2 - 1) ^ 2)⁻¹ = 1 / 2 := by
  have hne : Real.sqrt 2 - 1 ≠ 0 := ne_of_gt silver_rho_pos
  rw [silver_one_sub_rho_sq]
  field_simp

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_even_sum :
    (1 - (Real.sqrt 2 - 1) ^ 2)⁻¹ = (Real.sqrt 2 + 1) / 2 := by
  have h0 : (0 : ℝ) < 2 * (Real.sqrt 2 - 1) := by have := silver_rho_pos; linarith
  rw [silver_one_sub_rho_sq, eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), inv_mul_eq_div,
    div_eq_iff (ne_of_gt h0)]
  nlinarith [sqrt2_sq]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_consW_zero (b : Bool) (a : ℕ → Bool) :
    dR (consW b a) 0 = if b then 1 else 0 := by simp only [dR, consW_zero]

/-- **R0 Theorem 1, steps (S1)–(S3).**  At `α = 1+√2`, the words `ε = loBit u` and
`δ = parityFlip (consW b (hiBit u))` give
`π(ε) - S(δ) = √2·(a₀ + ρ·∑ᵢ uᵢ ρⁱ) - √2/2`, `ρ = √2-1`.  Every free bit of the pair
`(ε, δ)` is accounted for exactly once, which is why the digit system is `{0,1} + ρ·E`
with `E` the `{0,1,2}` system. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_sub_wVal (b : Bool) {u : ℕ → ℕ} (hu : ∀ i, u i ≤ 2) :
    piVal silver.α (loBit u) - silver.wVal (parityFlip (consW b (hiBit u)))
      = Real.sqrt 2 * (dR (consW b (hiBit u)) 0
          + (Real.sqrt 2 - 1) * ∑' k : ℕ, (u k : ℝ) * (Real.sqrt 2 - 1) ^ k)
        - Real.sqrt 2 / 2 := by
  have hρ0 := silver_rho_pos
  have hρ1 := silver_rho_lt_one
  have hα : silver.α - 1 = Real.sqrt 2 := by rw [silver_alpha]; ring
  have hs1 := summable_dR_pow' hρ0.le hρ1 (loBit u)
  have hs2 := summable_dR_pow' hρ0.le hρ1 (hiBit u)
  have hsplit : ∑' k : ℕ, (u k : ℝ) * (Real.sqrt 2 - 1) ^ k
      = (∑' k : ℕ, dR (loBit u) k * (Real.sqrt 2 - 1) ^ k)
        + ∑' k : ℕ, dR (hiBit u) k * (Real.sqrt 2 - 1) ^ k := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr fun k => by rw [← dR_loBit_add_dR_hiBit (hu k)]; ring
  rw [QuadSetup.piVal_eq_tsum, QuadSetup.wVal_eq_tsum, hα, silver_inv, silver_beta,
    tsum_dR_parityFlip hρ0.le hρ1, tsum_dR_consW hρ0.le hρ1, silver_odd_sum, hsplit]
  ring

/-- **R0 Theorem 1, step (S4): the covering.**  At `α = 1+√2` every point of
`[-√2/2, 2+√2/2]` is `π(ε) - S(δ)` for an explicit pair of one-sided words: choose the top
bit `a₀` by whether the rescaled target exceeds `√2`, then run the greedy of R0 Lemma 2 at
`r = ρ = √2-1`, `n = 2`, `L = 2+√2` (`ρL = √2 ≥ 1`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_Icc_subset_confSet :
    Set.Icc (-(Real.sqrt 2 / 2)) (2 + Real.sqrt 2 / 2) ⊆ silver.confSet := by
  intro y hy
  obtain ⟨hy0, hy2⟩ := hy
  have hρ0 := silver_rho_pos
  have hρ1 := silver_rho_lt_one
  have hne : Real.sqrt 2 - 1 ≠ 0 := ne_of_gt hρ0
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by have := one_lt_sqrt2; linarith
  have hrhoL : (Real.sqrt 2 - 1) * (2 + Real.sqrt 2) = Real.sqrt 2 := by nlinarith [sqrt2_sq]
  have hrhoL' : (2 + Real.sqrt 2) * (Real.sqrt 2 - 1) = Real.sqrt 2 := by nlinarith [sqrt2_sq]
  set w : ℝ := (y + Real.sqrt 2 / 2) / Real.sqrt 2 with hwdef
  have hsw : Real.sqrt 2 * w = y + Real.sqrt 2 / 2 := by rw [hwdef]; field_simp
  have hw0 : 0 ≤ w := div_nonneg (by linarith) hs2.le
  have hw1 : w ≤ 1 + Real.sqrt 2 := by
    rw [hwdef, div_le_iff₀ hs2]; nlinarith [sqrt2_sq]
  set b : Bool := decide (Real.sqrt 2 < w) with hbdef
  set d0 : ℝ := if b then 1 else 0 with hd0def
  have hstep : 0 ≤ w - d0 ∧ w - d0 ≤ Real.sqrt 2 := by
    by_cases hb : Real.sqrt 2 < w
    · have hd : d0 = 1 := by rw [hd0def, hbdef]; simp [hb]
      rw [hd]
      exact ⟨by linarith [one_lt_sqrt2], by linarith⟩
    · have hd : d0 = 0 := by rw [hd0def, hbdef]; simp [hb]
      push Not at hb
      rw [hd]
      exact ⟨by linarith, by linarith⟩
  set t : ℝ := (w - d0) / (Real.sqrt 2 - 1) with htdef
  have hL : ((2 : ℕ) : ℝ) + (Real.sqrt 2 - 1) * (2 + Real.sqrt 2) = 2 + Real.sqrt 2 := by
    push_cast; rw [hrhoL]
  have hrL : 1 ≤ (Real.sqrt 2 - 1) * (2 + Real.sqrt 2) := by
    rw [hrhoL]; linarith [one_lt_sqrt2]
  have ht : t ∈ Set.Icc (0 : ℝ) (2 + Real.sqrt 2) := by
    refine ⟨div_nonneg hstep.1 hρ0.le, ?_⟩
    rw [htdef, div_le_iff₀ hρ0, hrhoL']
    exact hstep.2
  have htsum : ∑' k : ℕ, ((covDigit (Real.sqrt 2 - 1) 2 t k : ℕ) : ℝ)
      * (Real.sqrt 2 - 1) ^ k = t := tsum_covDigit hρ0 hρ1 hL hrL ht
  have hval := silver_sub_wVal b (covDigit_le (Real.sqrt 2 - 1) 2 t)
  rw [htsum, dR_consW_zero, ← hd0def] at hval
  have hrt : (Real.sqrt 2 - 1) * t = w - d0 := by rw [htdef]; field_simp
  rw [hrt] at hval
  have hfin : Real.sqrt 2 * (d0 + (w - d0)) - Real.sqrt 2 / 2 = y := by
    rw [show d0 + (w - d0) = w by ring, hsw]; ring
  rw [hfin] at hval
  exact hval ▸ silver.mem_confSet _ _

/-! ### The window at `1+√2`: `P = √2/2`, `Q = 1 + √2/2` -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_cCoef (m : ℕ) :
    silver.cCoef m = -Real.sqrt 2 * (-(Real.sqrt 2 - 1)) ^ m := by
  rw [QuadSetup.cCoef, silver_beta]
  congr 1
  ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_max_cCoef (m : ℕ) :
    max (silver.cCoef m) 0
      = Real.sqrt 2 * (if Even m then (0 : ℝ) else (Real.sqrt 2 - 1) ^ m) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by have := one_lt_sqrt2; linarith
  have hpow : (0 : ℝ) ≤ (Real.sqrt 2 - 1) ^ m := pow_nonneg silver_rho_pos.le m
  rw [silver_cCoef]
  by_cases hm : Even m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), hm.neg_pow, mul_zero]
    exact max_eq_right (by nlinarith)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm), (Nat.not_even_iff_odd.mp hm).neg_pow,
      show -Real.sqrt 2 * -(Real.sqrt 2 - 1) ^ m
        = Real.sqrt 2 * (Real.sqrt 2 - 1) ^ m by ring]
    exact max_eq_left (mul_nonneg hs2.le hpow)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_min_cCoef (m : ℕ) :
    min (silver.cCoef m) 0
      = -Real.sqrt 2 * (if Even m then (Real.sqrt 2 - 1) ^ m else 0) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by have := one_lt_sqrt2; linarith
  have hpow : (0 : ℝ) ≤ (Real.sqrt 2 - 1) ^ m := pow_nonneg silver_rho_pos.le m
  rw [silver_cCoef]
  by_cases hm : Even m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), hm.neg_pow]
    exact min_eq_left (by nlinarith)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm), (Nat.not_even_iff_odd.mp hm).neg_pow, mul_zero,
      show -Real.sqrt 2 * -(Real.sqrt 2 - 1) ^ m
        = Real.sqrt 2 * (Real.sqrt 2 - 1) ^ m by ring]
    exact min_eq_right (mul_nonneg hs2.le hpow)

/-- **M1 Lemma 3 at `1+√2`**: `P = ∑_{c_m>0} c_m = √2/2`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_wMax : silver.wMax = Real.sqrt 2 / 2 := by
  rw [QuadSetup.wMax, tsum_congr silver_max_cCoef, tsum_mul_left,
    tsum_ite_odd silver_rho_pos.le silver_rho_lt_one, silver_odd_sum]
  ring

/-- **M1 Lemma 3 at `1+√2`**: `-Q = ∑_{c_m<0} c_m = -(1 + √2/2)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_wMin : silver.wMin = -(1 + Real.sqrt 2 / 2) := by
  rw [QuadSetup.wMin, tsum_congr silver_min_cCoef, tsum_mul_left,
    tsum_ite_even silver_rho_pos.le silver_rho_lt_one, silver_even_sum]
  linear_combination (-1 / 2 : ℝ) * sqrt2_sq

/-- `diam K = P + Q = 1 + √2` at `α = 1+√2` — comfortably above M1 Lemma 3's floor
`diam K ≥ d - 1 = 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_diam_window : silver.wMax - silver.wMin = 1 + Real.sqrt 2 := by
  rw [silver_wMax, silver_wMin]; ring

/-- **R0 Theorem 1.**  At `α = 1+√2`, `C(α) - K = [-√2/2, 2+√2/2]` — an identity of sets,
by one digit relabelling and one covering lemma, with no thickness and no gap lemma. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_confSet :
    silver.confSet = Set.Icc (-(Real.sqrt 2 / 2)) (2 + Real.sqrt 2 / 2) := by
  refine Set.Subset.antisymm ?_ silver_Icc_subset_confSet
  rw [silver.confSet_eq]
  rintro _ ⟨t, ht, s, hs, rfl⟩
  have h1 := cantorSet_subset_Icc silver.one_lt ht
  have h2 := silver.windowSet_subset_Icc hs
  rw [silver_wMin, silver_wMax] at h2
  exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- **R0 F1, sharpness.**  The interval of Theorem 1 has length `1 + diam K`, the largest
it could possibly be: Theorem 1 computes the convex hull `[-P, 1+Q]` rather than merely
covering an interval inside it, so no slack is being spent. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_confSet_length :
    2 + Real.sqrt 2 / 2 - -(Real.sqrt 2 / 2) = 1 + (silver.wMax - silver.wMin) := by
  rw [silver_diam_window]; ring

/-- **R0 Theorem 1, gate G-1.**  `X(1+√2) = 𝕋`: the confinement set of M1 Prop. 4 is the
whole circle, with a margin of `2+√2` over the threshold `1`.  Equivalently
`F(Ω(1+√2)) = 𝕋`, the precondition Route 4 of `plan-BB61-counterexample.html` needs. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_confCircle : silver.confCircle = Set.univ := by
  refine silver.confCircle_eq_univ_of_Icc_subset fun y hy => ?_
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by have := one_lt_sqrt2; linarith
  exact silver_Icc_subset_confSet ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- **No support argument can decide 10.61 at `1+√2`.**  The effective criterion of
`BB61/Covering.lean` — some open subinterval of `(0,1)` missed by every orbit at every
time — cannot hold at the silver ratio: it would force `X(α) ≠ 𝕋`.  This is the
machine-checked form of "the gap lane is shut at `1+√2`", and it is citation-free: it uses
neither Newhouse thickness nor the gap lemma. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_no_avoided_interval :
    ¬ ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ (ε : ℕ → Bool) (n : ℕ),
        Int.fract (piVal silver.α ε * silver.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  rintro ⟨x, r, hr, hsub, havoid⟩
  exact silver.confCircle_ne_univ_of_avoided hr hsub havoid silver_confCircle

end BB61
