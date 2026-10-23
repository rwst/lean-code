/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LineCoverST
import QuantitativeSubspace.Numerics

/-!
# The line count of Problem 10.13 is below `3.87·10⁹` (WP A3 of plan-beyond-BB13)

`BB13.failures_line_cover_ST` puts the failures `‖(3/2)ⁿ‖ < (3/4)ⁿ`, `n ≥ 20`, on at most
`lineCountST δ` lines, from Subspace-Theorems' explicit count in two variables. This file evaluates
the count at `δ = 13/50` by rational arithmetic: `lineCountST (13/50) ≤ 3.87·10⁹`
(`BB13.lineCountST_le`), so the failures `n ≥ 20` lie on at most `3 870 000 000` lines
(`BB13.failures_line_cover_ST_num`) — **with no cited axiom**, against `K(ε*) ≈ 1.86·10¹²` of the
cited [BE08] Cor. 5.2 (`BB13.failures_line_cover`) and below the computational record
`2³⁶ + 2³⁴ ≈ 8.59·10¹⁰` by a factor `22`.

The three terms of the count, with `η = δ/448 = 13/22400` and the chain length
`m = ⌈(2/3) log 12 · η⁻²⌉ = 4 918 449 ≤ 4 920 000` (`BB13.frame_chainLength_le`):

| term | value | bound | lemma |
|---|---|---|---|
| small | `δ⁻¹((2·10³)² + 8 log log 4)` | `1.5385·10⁷` | `BB13.frame_small_le` |
| middle | `1 + log(X₀/log 2^{4/δ}) / log(1 + δ/4)` | `1.8419·10⁹` | `BB13.frame_middle_le` |
| large | `2 + m (1 + log(16(m+1)/η) / log(1 + δ/4))` | `2.0093·10⁹` | `BB13.frame_largeCount_le` |

The middle term is as large as the large one because the threshold `X₀` carries Evertse's factor
`max(1, 2(m+1)/η)^(m+1) ≤ (2³⁴)^(m+1)` (`BB13.frame_factor_pow_le`): `X₀ ≤ 2⁸⁴ (2³⁴)^(m+1)`
(`BB13.frame_threshold_le`), and everything else in `X₀` is absorbed in `2⁸⁴`. The places above
`S` are exactly those over `2` and `3` (`BB13.systemPlacesOver_frameS`), with absolute norms `2`
and `3` (`BB13.absNorm_finitePlace_le`). Logarithms: `log 2 < 0.6931471808` (Mathlib), `log 3`
from `BB13/Constants.lean`, and `log(1 + 13/200) ≥ 26/413`, the first term of the series of
`2 artanh(13/413)` (`BB13.log_frame_gap_ge`). Gate G-1 (`BB13/g1_count.py`) gives `3.86·10⁹`
for the exact value.

The parts that do not depend on the frame are Subspace-Theorems'
`QuantitativeSubspace/Numerics.lean` (item M2 of `plans/plan-beyond-BB13.html` §7), which first
grew out of this file: the places of `ℚ` (`NumberField.systemPlacesOver_rat`,
`Rat.absNorm_maximalIdeal_finitePlace`), the chain length
(`NumberField.subspaceChainLength_one_le`), the large term from rational bounds
(`NumberField.systemLargeCountTwo_evertse_le_of_le`), and the threshold over `ℚ` in closed form
(`NumberField.systemThresholdTwo_rat_le`, with `h(ℙ¹) ≤ 6`); what is left here is `norm_num` at
`δ = 13/50` and `S = {2, 3}`.

## Main results

* `BB13.lineCountST_le`: `lineCountST (13/50) ≤ 3.87·10⁹`.
* `BB13.failures_line_cover_ST_num`: the failures `n ≥ 20` lie on at most `3.87·10⁹` lines.

## References

* `plans/plan-beyond-BB13.html`, §3.4, WP A3.
-/

namespace BB13

open NumberField IsDedekindDomain Height Module Finset

/-! ### The places of the frame -/

open scoped Classical in
/-- The places of `ℚ` over `S = {2, 3}` are the places at `2` and `3`
(`NumberField.systemPlacesOver_rat`). -/
theorem systemPlacesOver_frameS :
    systemPlacesOver ℚ frameS = {FinitePlace.mk v2, FinitePlace.mk v3} := by
  rw [systemPlacesOver_rat]
  ext V
  simp only [frameS, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl | rfl, rfl⟩ <;> simp
  · rintro (rfl | rfl) <;> simp

/-- The absolute norm of the prime of `𝓞 ℚ` over `p` is at most `p`; it is `p`
(`Rat.absNorm_maximalIdeal_finitePlace`). -/
theorem absNorm_finitePlace_le (p : Nat.Primes) :
    Ideal.absNorm (Rat.finitePlace p).maximalIdeal.asIdeal ≤ (p : ℕ) :=
  (Rat.absNorm_maximalIdeal_finitePlace p).le

theorem absNorm_v2 : Ideal.absNorm v2.asIdeal = 2 := Rat.absNorm_maximalIdeal_finitePlace prime2

theorem absNorm_v3 : Ideal.absNorm v3.asIdeal = 3 := Rat.absNorm_maximalIdeal_finitePlace prime3

open scoped Classical in
theorem card_frameS : #frameS = 2 := Finset.card_pair v2_ne_v3

open scoped Classical in
/-- Minkowski's constant at the frame is `2 · 2 · 3 = 12` (`NumberField.scalarConst_rat`). -/
theorem scalarConst_frameS_le : scalarConst ℚ frameS ≤ 12 := by
  rw [scalarConst_rat]
  unfold frameS
  rw [Finset.prod_pair v2_ne_v3, absNorm_v2, absNorm_v3]
  norm_num

/-! ### The chain length and the large term -/

/-- The frame's Roth lemma is Evertse's, with Rémond's heights on `(ℙ¹)ᵐ`. -/
theorem frameRoth_toRothParams : frameRoth.toRothParams = RothParams.evertse fun m ↦
    (MvPolynomial.resultantHeight (MvPolynomial.archEmbedded_of_numberField ℚ)
      (Prod.fst_surjective (α := Fin m) (β := Fin 2))).botBound 1 := rfl

theorem log_twelve_le : Real.log 12 ≤ 2.4849066505 := by
  have h : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  rw [h]
  linarith [Real.log_two_lt_d9, log_three_le]

/-- `log(1 + 13/200) ≥ 26/413`, the first term of the series of `2 artanh(13/413)`
(`Real.two_mul_div_two_add_le_log_one_add`). -/
theorem log_frame_gap_ge : (26 / 413 : ℝ) ≤ Real.log (1 + 13 / 50 / 4) := by
  have h := Real.two_mul_div_two_add_le_log_one_add (x := 13 / 50 / 4) (by norm_num)
  norm_num at h ⊢
  linarith

theorem frame_eps : 2 * systemEps 1 (13 / 50) = 13 / 100 := by norm_num [systemEps]

theorem frame_absBound : systemAbsBound 1 2 = 6 := by norm_num [systemAbsBound]

theorem frame_eta : subspaceEta 1 (13 / 100) 6 = 13 / 22400 := by norm_num [subspaceEta]

/-- The chain length at the frame: `m = ⌈(2/3) log 12 · (22400/13)²⌉ = 4 918 449 ≤ 4 920 000`
(`NumberField.subspaceChainLength_one_le`). -/
theorem frame_chainLength_le : subspaceChainLength 1 3 (13 / 100) 6 ≤ 4920000 := by
  refine subspaceChainLength_one_le (Λ := 2.4849066505) ?_ ?_
  · rw [show (4 : ℝ) * ((3 : ℕ) : ℝ) = 12 by norm_num]
    exact log_twelve_le
  · rw [frame_eta]
    norm_num

/-- **The large term at `δ = 13/50`**: `systemLargeCountTwo ≤ 2.0093·10⁹`
(`NumberField.systemLargeCountTwo_evertse_le_of_le` with `m ≤ 4.92·10⁶`,
`log(16(m + 1)/η) ≤ 37 log 2` and `log(1 + δ/4) ≥ 26/413`). -/
theorem frame_largeCount_le :
    systemLargeCountTwo frameRoth.toRothParams 1 3 (13 / 50) ≤ 2009300000 := by
  have hm : subspaceChainLength 1 3 (2 * systemEps 1 (13 / 50)) (systemAbsBound 1 2) ≤
      4920000 := by
    rw [frame_eps, frame_absBound]
    exact frame_chainLength_le
  have hΛ : Real.log (16 * (((4920000 : ℕ) : ℝ) + 1) /
      subspaceEta 1 (2 * systemEps 1 (13 / 50)) (systemAbsBound 1 2)) ≤ 37 * 0.6931471808 := by
    rw [frame_eps, frame_absBound, frame_eta]
    calc _ ≤ Real.log (2 ^ 37) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 37 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ _ := by linarith [Real.log_two_lt_d9]
  rw [frameRoth_toRothParams]
  refine (systemLargeCountTwo_evertse_le_of_le _ le_rfl (by norm_num) hm hΛ (by norm_num)
    log_frame_gap_ge).trans ?_
  norm_num

/-! ### The threshold -/

theorem log_two_le_one : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]

/-- Evertse's factor at the frame: `max(1, 2(m+1)/η)^(m+1) ≤ (2³⁴)^(m+1)`. -/
theorem frame_factor_pow_le :
    max 1 (2 * ((subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1) / (13 / 22400))
      ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1)
      ≤ ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) := by
  have hm : (subspaceChainLength 1 3 (13 / 100) 6 : ℝ) ≤ 4920000 := by
    exact_mod_cast frame_chainLength_le
  refine pow_le_pow_left₀ (by positivity) (max_le (by norm_num) ?_) _
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

open scoped Classical in
/-- **The threshold at the frame**: `X₀ ≤ 2⁸⁴ (2³⁴)^(m+1)`,
`m = subspaceChainLength 1 3 (13/100) 6`, from Subspace-Theorems' closed form over `ℚ` (`NumberField.systemThresholdTwo_rat_le`, with
`h(ℙ¹) ≤ 6` for Rémond's heights). -/
theorem frame_threshold_le :
    systemThresholdTwo ℚ frameS (fun v ↦ v) frameForms frameRoth.toRothParams 3 1 (13 / 50) ≤
      2 ^ 84 * ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) := by
  have hT := systemThresholdTwo_rat_le (fun m ↦ (MvPolynomial.resultantHeight
      (MvPolynomial.archEmbedded_of_numberField ℚ)
      (Prod.fst_surjective (α := Fin m) (β := Fin 2))).botBound 1)
    (fun _ ↦ MvPolynomial.resultantHeight_botBound_one_le _ _) (Fintype.card_fin 2)
    (fun _ ↦ AbsoluteValue.liesOver_self _) (fun _ _ ↦ AbsoluteValue.liesOver_self _)
    (frameSystem_isNormalized (δ := 13 / 50) (by norm_num) thirteen_fiftieths_le)
    (by norm_num)
  rw [frameRoth_toRothParams]
  refine hT.trans ?_
  have hsum : ∑ q ∈ frameS, Real.log (Ideal.absNorm q.asIdeal : ℝ) =
      Real.log 2 + Real.log 3 := by
    unfold frameS
    rw [Finset.sum_pair v2_ne_v3, absNorm_v2, absNorm_v3]
    norm_num
  have hprod : ∏ q ∈ frameS, (Ideal.absNorm q.asIdeal : ℝ) = 6 := by
    unfold frameS
    rw [Finset.prod_pair v2_ne_v3, absNorm_v2, absNorm_v3]
    norm_num
  rw [card_frameS, hsum, hprod, show (13 : ℝ) / 50 / 2 = 13 / 100 by norm_num]
  have hm : (subspaceChainLength 1 3 (13 / 100) 6 : ℝ) ≤ 4920000 := by
    exact_mod_cast frame_chainLength_le
  have hm0 : (0 : ℝ) ≤ subspaceChainLength 1 3 (13 / 100) 6 := Nat.cast_nonneg _
  have hZ : (1 : ℝ) ≤ ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) :=
    one_le_pow₀ (by norm_num)
  have hF : max 1 (896 * ((subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1) / (13 / 50))
      ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) ≤
      ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) := by
    refine pow_le_pow_left₀ (by positivity) (max_le (by norm_num) ?_) _
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  generalize ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) = Z at hZ hF ⊢
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_le
  have hl12 := log_twelve_le
  -- the coefficient
  have hP : ratThresholdCoeffTwo 2 6 (13 / 50) (subspaceChainLength 1 3 (13 / 100) 6) ≤
      2 ^ 79 * Z := by
    rw [ratThresholdCoeffTwo]
    have hF1 : (1 : ℝ) ≤ max 1 (896 * ((subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1) /
        (13 / 50)) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) := one_le_pow₀ (le_max_left _ _)
    generalize max 1 (896 * ((subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1) / (13 / 50))
      ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) = F at hF hF1 ⊢
    generalize (subspaceChainLength 1 3 (13 / 100) 6 : ℝ) = m at hm hm0 ⊢
    have hF0 : 0 ≤ F := by linarith
    rw [div_le_iff₀ (by norm_num)]
    have h1 : 16 * (1 + ((2 : ℕ) : ℝ)) * F * (m + 1) ^ 2 * (m + max 6 0 + 40 * (1 + ((2 : ℕ) : ℝ))
        + 5) ≤ 48 * Z * (2 ^ 23) ^ 2 * 2 ^ 24 := by
      have hmax : max (6 : ℝ) 0 = 6 := by norm_num
      rw [hmax]
      push_cast
      have hm1 : m + 1 ≤ 2 ^ 23 := by linarith
      have hm2 : m + 6 + 40 * (1 + 2) + 5 ≤ 2 ^ 24 := by linarith
      calc 16 * (1 + 2) * F * (m + 1) ^ 2 * (m + 6 + 40 * (1 + 2) + 5)
          = 48 * F * (m + 1) ^ 2 * (m + 6 + 40 * (1 + 2) + 5) := by ring
        _ ≤ 48 * Z * (2 ^ 23) ^ 2 * 2 ^ 24 := by gcongr
    push_cast at h1 ⊢
    norm_num at h1 ⊢
    nlinarith
  have hP0 : 0 ≤ ratThresholdCoeffTwo 2 6 (13 / 50) (subspaceChainLength 1 3 (13 / 100) 6) := by
    rw [ratThresholdCoeffTwo]
    positivity
  refine max_le ?_ (max_le ?_ ?_)
  · have hs : 4 * (1 + ((2 : ℕ) : ℝ)) * Real.log 1 + (Real.log 2 + Real.log 3) + 1 ≤ 3 := by
      rw [Real.log_one]; linarith
    have hs0 : 0 ≤ 4 * (1 + ((2 : ℕ) : ℝ)) * Real.log 1 + (Real.log 2 + Real.log 3) + 1 := by
      rw [Real.log_one]
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
      linarith
    calc _ ≤ 2 ^ 79 * Z * 3 := mul_le_mul hP hs hs0 (by positivity)
      _ ≤ _ := by linarith
  · norm_num; linarith
  · rw [show (2 : ℝ) * 6 = 12 by norm_num]
    simp only [systemHeightThreshold, Nat.factorial]
    norm_num
    linarith

/-- **The middle term at `δ = 13/50`**: `1 + log(systemMiddleRatio)/log(1 + δ/4) ≤ 1.8419·10⁹`. -/
theorem frame_middle_le :
    1 + Real.log (systemMiddleRatio 1 2 1 (13 / 50)
        (systemThresholdTwo ℚ frameS (fun v ↦ v) frameForms frameRoth.toRothParams 3 1 (13 / 50))) /
      Real.log (1 + 13 / 50 / 4) ≤ 1841900000 := by
  have hX := frame_threshold_le
  have hm : (subspaceChainLength 1 3 (13 / 100) 6 : ℝ) ≤ 4920000 := by
    exact_mod_cast frame_chainLength_le
  have hZ : (1 : ℝ) ≤ ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) :=
    one_le_pow₀ (by norm_num)
  have hlogZ : Real.log (((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1)) =
      34 * ((subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1) * Real.log 2 := by
    rw [Real.log_pow, Real.log_pow]; push_cast; ring
  generalize ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) = Z at hX hZ hlogZ
  generalize systemThresholdTwo ℚ frameS (fun v ↦ v) frameForms frameRoth.toRothParams 3 1
    (13 / 50) = X at hX
  -- the denominator of the ratio is at least `log 2 ≥ 1/2`
  have hL : 1 / 2 ≤ ((1 : ℕ) : ℝ) * Real.log (max (2 * 1) ((2 : ℕ) ^ (2 * (2 : ℕ) / (13 / 50) : ℝ))) := by
    have h2 : Real.log 2 ≤ Real.log (max (2 * 1) ((2 : ℕ) ^ (2 * (2 : ℕ) / (13 / 50) : ℝ))) :=
      Real.log_le_log (by norm_num) (by simp)
    have := Real.log_two_gt_d9
    norm_num at h2 ⊢; linarith
  have hR : systemMiddleRatio 1 2 1 (13 / 50) X ≤ 2 ^ 85 * Z := by
    rw [systemMiddleRatio]
    refine max_le (by nlinarith) ?_
    rw [div_le_iff₀ (by linarith)]
    rcases le_total X 0 with hX0 | hX0
    · nlinarith
    · nlinarith
  have hR1 : 1 ≤ systemMiddleRatio 1 2 1 (13 / 50) X := le_max_left _ _
  have hlogR : Real.log (systemMiddleRatio 1 2 1 (13 / 50) X) ≤
      (85 + 34 * (4920000 + 1)) * 0.6931471808 := by
    calc _ ≤ Real.log (2 ^ 85 * Z) := Real.log_le_log (by linarith) hR
      _ = 85 * Real.log 2 + 34 * ((subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1) * Real.log 2 := by
          rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow, hlogZ]; push_cast; ring
      _ ≤ _ := by
          have := Real.log_two_lt_d9
          have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          nlinarith
  have hlog0 : 0 ≤ Real.log (systemMiddleRatio 1 2 1 (13 / 50) X) := Real.log_nonneg hR1
  have hq : Real.log (systemMiddleRatio 1 2 1 (13 / 50) X) / Real.log (1 + 13 / 50 / 4) ≤
      (85 + 34 * (4920000 + 1)) * 0.6931471808 / (26 / 413) :=
    div_le_div₀ (by norm_num) hlogR (by norm_num) log_frame_gap_ge
  norm_num at hq ⊢
  linarith

/-- The small term at `δ = 13/50`: `(50/13)((2·10³)² + 8 log log 4) ≤ 1.5385·10⁷`. -/
theorem frame_small_le :
    (13 / 50 : ℝ)⁻¹ * ((10 ^ 3 * 2) ^ 2 + 4 * 2 * Real.log (Real.log 4)) ≤ 15385000 := by
  have h4 : Real.log 4 ≤ 4 := (Real.log_le_self (by norm_num)).trans le_rfl
  have h4' : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h : Real.log (Real.log 4) ≤ 4 := (Real.log_le_self h4'.le).trans h4
  norm_num
  linarith

/-- **The number of lines of the failures at `δ = 13/50` is below `3.87·10⁹`** (WP A3 of
plan-beyond-BB13): small term `≤ 1.5385·10⁷`, middle term `≤ 1.8419·10⁹`, large term
`≤ 2.0093·10⁹`. Against `K(ε*) ≈ 1.86·10¹²` of the cited [BE08] Cor. 5.2 and the computational
record `2³⁶ + 2³⁴ ≈ 8.59·10¹⁰`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem lineCountST_le : lineCountST (13 / 50) ≤ 3870000000 := by
  have h1 := frame_small_le
  have h2 := frame_middle_le
  have h3 := frame_largeCount_le
  rw [lineCountST]
  linarith

/-- **The failures `n ≥ 20` of Problem 10.13 lie on at most `3.87·10⁹` lines** through the origin:
the slopes `linePoint n = mₙ2ⁿ/3ⁿ` lie in a set of at most `3 870 000 000` rationals. No cited
axiom; compare `BB13.failures_line_cover` (`K(ε*) ≈ 1.86·10¹²`, cited [BE08] Cor. 5.2). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_ST_num :
    ∃ R : Finset ℚ, R.card ≤ 3870000000 ∧
      ∀ n : ℕ, 20 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ST (δ := 13 / 50) (by norm_num) thirteen_fiftieths_le
  exact ⟨R, by exact_mod_cast hcard.trans lineCountST_le, hR⟩

end BB13
