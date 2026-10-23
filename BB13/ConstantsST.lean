/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LineCoverST

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
(`BB13.frame_threshold_le`, from Subspace-Theorems' `NumberField.systemThresholdTwo_le`), and
everything else in `X₀` is absorbed in `2⁸⁴`. The places above `S` are exactly those over `2` and
`3` (`BB13.systemPlacesOver_frameS`), with absolute norms at most `2` and `3`
(`BB13.absNorm_finitePlace_le`). Logarithms: `log 2 < 0.6931471808` (Mathlib), `log 3` from
`BB13/Constants.lean`, and `log(1 + 13/200) ≥ 26/413`, the first term of the series of
`2 artanh(13/413)` (`BB13.log_frame_gap_ge`). Gate G-1 (`BB13/g1_count.py`) gives `3.86·10⁹`
for the exact value.

## Main results

* `BB13.lineCountST_le`: `lineCountST (13/50) ≤ 3.87·10⁹`.
* `BB13.failures_line_cover_ST_num`: the failures `n ≥ 20` lie on at most `3.87·10⁹` lines.

## References

* `plans/plan-beyond-BB13.html`, §3.4, WP A3.
-/

namespace BB13

open NumberField IsDedekindDomain Height Module Finset

open scoped Classical in
theorem systemPlacesOver_frameS :
    systemPlacesOver ℚ frameS = {FinitePlace.mk v2, FinitePlace.mk v3} := by
  ext V
  rw [mem_systemPlacesOver, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, hp, hV⟩
    have h1 : V.maximalIdeal.asIdeal = p.asIdeal := by
      have hV' := hV.over
      rw [FinitePlace.maximalIdeal_mk] at hV'
      rw [hV', Ideal.under]
      ext x
      simp only [Ideal.mem_comap]
      exact Iff.rfl
    have h2 : V = FinitePlace.mk p := by
      rw [← FinitePlace.mk_maximalIdeal V, HeightOneSpectrum.asIdeal_injective h1]
    rcases (mem_frameS_iff p).1 hp with rfl | rfl
    · exact Or.inl h2
    · exact Or.inr h2
  · rintro (rfl | rfl)
    · refine ⟨v2, (mem_frameS_iff _).2 (Or.inl rfl), ?_⟩
      exact ⟨by rw [Ideal.under]; ext x; simp only [Ideal.mem_comap]; exact Iff.rfl⟩
    · refine ⟨v3, (mem_frameS_iff _).2 (Or.inr rfl), ?_⟩
      exact ⟨by rw [Ideal.under]; ext x; simp only [Ideal.mem_comap]; exact Iff.rfl⟩

theorem mk_v2_ne_mk_v3 : FinitePlace.mk v2 ≠ FinitePlace.mk v3 := by
  rw [finitePlace_mk_v2, finitePlace_mk_v3]
  intro h
  have := congrArg Subtype.val (Rat.finitePlace_injective h)
  simp [prime2, prime3] at this

open scoped Classical in
theorem card_systemPlacesOver_frameS : #(systemPlacesOver ℚ frameS) = 2 := by
  rw [systemPlacesOver_frameS, Finset.card_pair mk_v2_ne_mk_v3]

/-- The absolute norm of the prime of `𝓞 ℚ` over `p` is at most `p`. -/
theorem absNorm_finitePlace_le (p : Nat.Primes) :
    Ideal.absNorm (Rat.finitePlace p).maximalIdeal.asIdeal ≤ (p : ℕ) := by
  have hp : (p : ℕ).Prime := p.2
  have hx : ((p : ℕ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := FinitePlace.apply_mul_absNorm_pow_eq_one (Rat.finitePlace p) hx
  have hv : Rat.finitePlace p (((p : ℕ) : 𝓞 ℚ) : ℚ) = ((p : ℕ) : ℝ)⁻¹ := by
    rw [Rat.finitePlace_apply]
    have : Fact (p : ℕ).Prime := ⟨hp⟩
    simp
  rw [hv] at h
  set N := Ideal.absNorm (Rat.finitePlace p).maximalIdeal.asIdeal
  set k := multiplicity (Rat.finitePlace p).maximalIdeal.asIdeal (Ideal.span {((p : ℕ) : 𝓞 ℚ)})
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hp.pos
  have hNk : (N : ℝ) ^ k = (p : ℕ) := by
    field_simp at h
    linarith
  have hNk' : N ^ k = (p : ℕ) := by exact_mod_cast hNk
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero] at hNk'
    exact absurd hNk'.symm hp.one_lt.ne'
  · calc N ≤ N ^ k := Nat.le_self_pow hk.ne' N
      _ = (p : ℕ) := hNk'

/-! ### The chain length and the large term -/

theorem log_twelve_le : Real.log 12 ≤ 2.4849066505 := by
  have h : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  rw [h]
  linarith [Real.log_two_lt_d9, log_three_le]

/-- `log(1 + 13/200) ≥ 26/413`, the first term of the series of `2 artanh(13/413)`. -/
theorem log_frame_gap_ge : (26 / 413 : ℝ) ≤ Real.log (1 + 13 / 50 / 4) := by
  have h := Real.hasSum_log_one_add_inv (a := 200 / 13) (by norm_num)
  have h0 := le_hasSum h 0 fun k _ ↦ by positivity
  norm_num at h0 ⊢
  linarith

theorem frame_eps : 2 * systemEps 1 (13 / 50) = 13 / 100 := by norm_num [systemEps]

theorem frame_absBound : systemAbsBound 1 2 = 6 := by norm_num [systemAbsBound]

theorem frame_eta : subspaceEta 1 (13 / 100) 6 = 13 / 22400 := by norm_num [subspaceEta]

/-- The chain length at the frame: `m = ⌈(2/3) log 12 · (22400/13)²⌉ = 4 918 449 ≤ 4 920 000`. -/
theorem frame_chainLength_le : subspaceChainLength 1 3 (13 / 100) 6 ≤ 4920000 := by
  rw [subspaceChainLength, frame_eta, Nat.ceil_le]
  have h := log_twelve_le
  norm_num
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **The large term at `δ = 13/50`**: `systemLargeCountTwo ≤ 2.0093·10⁹`. -/
theorem frame_largeCount_le :
    systemLargeCountTwo frameRoth.toRothParams 1 3 (13 / 50) ≤ 2009300000 := by
  have hr : frameRoth.toRothParams.ratio = evertseRatio := rfl
  rw [systemLargeCountTwo, hr, frame_eps, frame_absBound, evertseRatio, frame_eta]
  have hm := frame_chainLength_le
  generalize subspaceChainLength 1 3 (13 / 100) 6 = m at hm ⊢
  have hmR : (m : ℝ) ≤ 4920000 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hL := log_frame_gap_ge
  have harg : 4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹ ≤ 2 ^ 37 := by
    rw [inv_div]
    rw [mul_div_assoc', div_le_iff₀ (by norm_num)]
    nlinarith
  have harg1 : 1 ≤ 4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹ := by
    rw [inv_div, mul_div_assoc', le_div_iff₀ (by norm_num)]
    nlinarith
  have hlog : Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹) ≤ 37 * 0.6931471808 := by
    calc _ ≤ Real.log (2 ^ 37) := Real.log_le_log (by linarith) harg
      _ = 37 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 37 * 0.6931471808 := by linarith [Real.log_two_lt_d9]
  have hlog0 : 0 ≤ Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹) := Real.log_nonneg harg1
  have hq : Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹) / Real.log (1 + 13 / 50 / (2 * 2))
      ≤ 37 * 0.6931471808 / (26 / 413) := by
    have : (2 : ℝ) * 2 = 4 := by norm_num
    rw [this]
    exact div_le_div₀ (by norm_num) hlog (by norm_num) hL
  have hq0 : 0 ≤ Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹) /
      Real.log (1 + 13 / 50 / (2 * 2)) :=
    div_nonneg hlog0 (Real.log_nonneg (by norm_num))
  have : (m : ℝ) * (1 + Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹) /
      Real.log (1 + 13 / 50 / (2 * 2))) ≤ 4920000 * (1 + 37 * 0.6931471808 / (26 / 413)) :=
    mul_le_mul hmR (by linarith) (by linarith) (by norm_num)
  norm_num at this ⊢
  linarith

theorem card_infinitePlace_rat : Fintype.card (InfinitePlace ℚ) = 1 :=
  Fintype.card_eq_one_iff.2 ⟨Rat.infinitePlace, fun _ ↦ Subsingleton.elim _ _⟩

theorem frame_eps_one : systemEps 1 (13 / 50) = 13 / 200 := by norm_num [systemEps]

theorem frameRoth_factor (n s : ℕ) (ε A : ℝ) : frameRoth.toRothParams.factor n s ε A =
    n * max 1 (2 * ((subspaceChainLength n s ε A : ℝ) + 1) / subspaceEta n ε A)
      ^ (subspaceChainLength n s ε A + 1) * ((subspaceChainLength n s ε A : ℝ) + 1) := rfl

theorem frameRoth_shift_le (n s : ℕ) (ε A : ℝ) : frameRoth.toRothParams.shift n s ε A ≤
    8 + (subspaceChainLength n s ε A : ℝ) + 2 := by
  show max ((MvPolynomial.resultantHeight (MvPolynomial.archEmbedded_of_numberField ℚ)
    Prod.fst_surjective).botBound 1) 0 + _ + 2 ≤ _
  have hb := MvPolynomial.resultantHeight_botBound_le (MvPolynomial.archEmbedded_of_numberField ℚ)
    (Prod.fst_surjective (α := Fin (subspaceChainLength n s ε A + 1)) (β := Fin 2)) 1
  have h4 : Real.log (2 * ((1 + 1 : ℕ) : ℝ)) ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (x := 2 * ((1 + 1 : ℕ) : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  have : max ((MvPolynomial.resultantHeight (MvPolynomial.archEmbedded_of_numberField ℚ)
      (Prod.fst_surjective (α := Fin (subspaceChainLength n s ε A + 1)) (β := Fin 2))).botBound 1)
      0 ≤ 8 := by
    refine max_le (hb.trans ?_) (by norm_num)
    norm_num at h4 ⊢; linarith
  linarith

/-! ### The coefficients of the threshold at the frame -/

theorem log_two_le_one : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]

theorem detCoeff_one_two_le : detCoeff 1 2 ≤ 5 := by
  have := log_two_le_one
  simp only [detCoeff, Nat.factorial]; norm_num; linarith

theorem detCoeff_one_one : detCoeff 1 1 = 1 := by simp [detCoeff]

theorem auxCoeff_frame_le : auxCoeff 1 2 1 2 ≤ 128 := by
  have := log_two_le_one; have := detCoeff_one_two_le
  simp only [auxCoeff]; norm_num; linarith

theorem auxCoeff_frame_nonneg : 0 ≤ auxCoeff 1 2 1 2 := auxCoeff_nonneg 1 2 1 2

theorem frame_refIndex_le : ⌈2 * ((1 : ℕ) : ℝ) / (13 / 22400) + 1⌉₊ ≤ 3448 := by
  rw [Nat.ceil_le]; norm_num

theorem refCoeff_frame_le : refCoeff 1 2 1 2 ⌈2 * ((1 : ℕ) : ℝ) / (13 / 22400) + 1⌉₊ ≤ 2 ^ 25 := by
  have hB := frame_refIndex_le
  generalize ⌈2 * ((1 : ℕ) : ℝ) / (13 / 22400) + 1⌉₊ = B at hB ⊢
  have hBR : (B : ℝ) ≤ 3448 := by exact_mod_cast hB
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hlog : Real.log B ≤ 3448 := (Real.log_le_self hB0).trans hBR
  have hlog0 : 0 ≤ Real.log B := Real.log_natCast_nonneg B
  have := detCoeff_one_two_le
  simp only [refCoeff]; norm_num
  nlinarith

theorem kappaCoeff_frame_le : kappaCoeff 1 (Nat.choose 2 1) 1 (1 + 2) ≤ 128 := by
  have := log_two_le_one
  simp only [kappaCoeff, detCoeff_one_one]; norm_num; linarith

theorem log_le_self_nat (n : ℕ) : Real.log n ≤ n := Real.log_le_self (Nat.cast_nonneg n)

theorem patternConstCoeff_frame_le : patternConstCoeff 1 2 1 2 ≤ 64 := by
  have := detCoeff_one_two_le
  have h3 := log_le_self_nat 3; have h4 := log_le_self_nat 4; have h5 := log_le_self_nat 5
  simp only [patternConstCoeff, invCoeff]; norm_num at h3 h4 h5 ⊢; linarith

theorem patternHeightCoeff_frame_le : patternHeightCoeff 1 2 1 2 ≤ 256 := by
  have := detCoeff_one_two_le; have := log_two_le_one
  simp only [patternHeightCoeff]; norm_num; nlinarith

theorem rankCoeff_frame_le : rankCoeff 1 2 2 (13 / 200) ≤ 1024 := by
  have := detCoeff_one_two_le; have := log_two_le_one
  have h3 := log_le_self_nat 3
  have hpi : Real.log (2 * Real.pi) ≤ 7 :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith [Real.pi_lt_four])
  simp only [rankCoeff, rankNumCoeff, basisCoeff, Nat.factorial]; norm_num at h3 ⊢
  nlinarith

theorem frame_chainLength_succ_le : (subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1 ≤ 2 ^ 23 := by
  have : (subspaceChainLength 1 3 (13 / 100) 6 : ℝ) ≤ 4920000 := by
    exact_mod_cast frame_chainLength_le
  linarith

theorem frame_max_le :
    max 1 (2 * ((subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1) / (13 / 22400)) ≤ 2 ^ 34 := by
  have hm : (subspaceChainLength 1 3 (13 / 100) 6 : ℝ) ≤ 4920000 := by
    exact_mod_cast frame_chainLength_le
  refine max_le (by norm_num) ?_
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

theorem frame_shift_nonneg : 0 ≤ frameRoth.toRothParams.shift 1 3 (13 / 100) 6 :=
  frameRoth.toRothParams.shift_nonneg (by norm_num) (by norm_num)

/-- Evertse's factor at the frame: `max(1, 2(m+1)/η)^(m+1) ≤ (2³⁴)^(m+1)`. -/
theorem frame_factor_pow_le :
    max 1 (2 * ((subspaceChainLength 1 3 (13 / 100) 6 : ℝ) + 1) / (13 / 22400))
      ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1)
      ≤ ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) := by
  have h := frame_chainLength_succ_le
  have hm : (subspaceChainLength 1 3 (13 / 100) 6 : ℝ) ≤ 4920000 := by
    exact_mod_cast frame_chainLength_le
  refine pow_le_pow_left₀ (by positivity) (max_le (by norm_num) ?_) _
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

/-- **The coefficient `penultimateCoeff` at the frame**: `≤ 2⁸⁰ (2³⁴)^(m+1)`. Everything but
Evertse's factor is absorbed in `2⁸⁰`. -/
theorem frame_penultimateCoeff_le :
    penultimateCoeff frameRoth.toRothParams 1 2 1 2 3 1 (13 / 100) 6 ≤
      2 ^ 80 * ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) := by
  have hsh := frameRoth_shift_le 1 3 (13 / 100) 6
  have hm1 := frame_chainLength_succ_le
  have hlog4 : Real.log (2 * ((1 : ℕ) + 1) * (1 : ℕ)) ≤ 4 := by
    have := log_le_self_nat 4; norm_num at this ⊢; linarith
  have hZ : (1 : ℝ) ≤ ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) :=
    one_le_pow₀ (by norm_num)
  rw [penultimateCoeff, frameRoth_factor, frame_eta]
  calc _ ≤ 1 + 8 * (((1 : ℕ) : ℝ) + 1) * (((1 : ℕ) : ℝ) * 4 + 128 + 2 * 2 ^ 25) / (13 / 100) +
        8 * ((1 + 2 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) *
          ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) * 2 ^ 23 * 2 ^ 23 *
          (128 + (8 + 2 ^ 23 + 2) * ((1 : ℕ) : ℝ)) + 128) / (13 / 100) +
        (4 * ((((1 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) * 64 + 256) + 1) / (13 / 100) := by
        gcongr
        all_goals first
          | exact auxCoeff_frame_le | exact refCoeff_frame_le | exact kappaCoeff_frame_le
          | exact patternConstCoeff_frame_le | exact patternHeightCoeff_frame_le
          | exact frame_max_le | linarith
          | exact add_nonneg auxCoeff_frame_nonneg (mul_nonneg frame_shift_nonneg (by norm_num))
    _ ≤ _ := by norm_num; linarith

/-! ### The threshold and the middle term -/

open scoped Classical in
theorem card_frameS : #frameS = 2 := Finset.card_pair v2_ne_v3

theorem absNorm_v2_le : Ideal.absNorm v2.asIdeal ≤ 2 := absNorm_finitePlace_le prime2

theorem absNorm_v3_le : Ideal.absNorm v3.asIdeal ≤ 3 := absNorm_finitePlace_le prime3

theorem log_absNorm_v2_le : Real.log (Ideal.absNorm v2.asIdeal) ≤ 2 :=
  (log_le_self_nat _).trans (by exact_mod_cast absNorm_v2_le)

theorem log_absNorm_v3_le : Real.log (Ideal.absNorm v3.asIdeal) ≤ 3 :=
  (log_le_self_nat _).trans (by exact_mod_cast absNorm_v3_le)

open scoped Classical in
theorem scalarConst_frameS_le : scalarConst ℚ frameS ≤ 12 := by
  have h2 : (Ideal.absNorm v2.asIdeal : ℝ) ≤ 2 := by exact_mod_cast absNorm_v2_le
  have h3 : (Ideal.absNorm v3.asIdeal : ℝ) ≤ 3 := by exact_mod_cast absNorm_v3_le
  rw [scalarConst]
  unfold frameS
  rw [Finset.prod_pair v2_ne_v3, Rat.numberField_discr]
  simp only [finrank_self, pow_one, Int.cast_one, abs_one, Real.sqrt_one, mul_one]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Ideal.absNorm v2.asIdeal),
    Nat.cast_nonneg (α := ℝ) (Ideal.absNorm v3.asIdeal)]

open scoped Classical in
/-- **The threshold at the frame**: `X₀ ≤ 2⁸⁴ (2³⁴)^(m+1)`, `m = subspaceChainLength 1 3 (13/100) 6`. -/
theorem frame_threshold_le :
    systemThresholdTwo ℚ frameS (fun v ↦ v) frameForms frameRoth.toRothParams 3 1 (13 / 50) ≤
      2 ^ 84 * ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) := by
  have hT := systemThresholdTwo_le frameRoth.toRothParams (Fintype.card_fin 2)
    (fun _ ↦ AbsoluteValue.liesOver_self _) (fun _ _ ↦ AbsoluteValue.liesOver_self _)
    (frameSystem_isNormalized (δ := 13 / 50) (by norm_num) thirteen_fiftieths_le)
  rw [card_systemPlacesOver_frameS] at hT
  simp only [Fintype.card_fin, finrank_self, card_infinitePlace_rat, Rat.numberField_discr,
    Int.cast_one, abs_one, Real.log_one, mul_zero, zero_add, frame_eps,
    frame_absBound, systemPlacesOver_frameS, Finset.sum_pair mk_v2_ne_mk_v3,
    FinitePlace.maximalIdeal_mk, mul_one, Nat.cast_one, card_frameS] at hT
  rw [frame_eps_one] at hT
  refine hT.trans ?_
  have hZ : (1 : ℝ) ≤ ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) :=
    one_le_pow₀ (by norm_num)
  have hpen := frame_penultimateCoeff_le
  generalize ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) = Z at hZ hpen ⊢
  have hr := rankCoeff_frame_le
  have hQ1 := log_absNorm_v2_le
  have hQ2 := log_absNorm_v3_le
  have hQ0 : 0 ≤ Real.log (Ideal.absNorm v2.asIdeal) + Real.log (Ideal.absNorm v3.asIdeal) + 1 := by
    have := Real.log_natCast_nonneg (Ideal.absNorm v2.asIdeal)
    have := Real.log_natCast_nonneg (Ideal.absNorm v3.asIdeal)
    linarith
  have hP : 1 + rankCoeff 1 2 2 (13 / 200) + penultimateCoeff frameRoth.toRothParams 1 2 1 2 3 1
      (13 / 100) 6 ≤ 2 ^ 81 * Z := by linarith
  have hsc0 : 0 ≤ scalarConst ℚ frameS := by rw [scalarConst]; positivity
  have hμ : Real.log (scalarConst ℚ frameS) ≤ 12 := (Real.log_le_self hsc0).trans scalarConst_frameS_le
  have hl2 := log_two_le_one
  refine max_le ?_ (max_le ?_ ?_)
  · calc _ ≤ 2 ^ 81 * Z * 6 := mul_le_mul hP (by linarith) hQ0 (by positivity)
      _ ≤ _ := by linarith
  · norm_num; linarith
  · simp only [systemHeightThreshold, Nat.factorial]; norm_num; linarith

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
