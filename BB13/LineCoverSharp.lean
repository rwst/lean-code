/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LineCoverRho

/-!
# The line cover with the frame's own weights (item M3 of plan-beyond-BB13)

`BB13/LineCoverRho.lean` puts the exceptions `‖(3/2)ⁿ‖ < (3/4)ⁿ`, `n ≥ 20`, on at most
`1.05·10⁹` lines. Almost all of that number is `η⁻²`: the chain length of the Subspace Theorem is
`m ≈ (2/3) log(4s) η⁻²`, and both halves of the count are `≈ m log(m/η)/log ρ₀`. There
`η = δ/448`, from Subspace-Theorems' generic choices for a system in two variables: half of the
weight spent on the scalar that absorbs the constants, the margin `systemEps = δ/4` below the
weight `-δ/2` that the domain actually has, the generic absolute weight `A = 6`, and
`subspaceEta`'s `ε / (8 (n+1)² (A+1))`, which gives the deviation error half of the budget
(the audit of item M3, `BB13/m3_audit.py`).

Subspace-Theorems' interval result at explicit parameters
(`NumberField.exists_forall_mem_interval_systemSet_two_of_rothLemmaAt`) takes all of these from
the frame, and leaves the chain length `m` and `η` to the caller:

* the scalar costs `τ δ` with `τ = 1/1000` instead of `δ/2`, so the domain has weight `-W`,
  `W = (1 - τ) δ`;
* the frame's exponents have positive weight `2 - θ` (`frame_posWeight`), so the domain has
  absolute weight at most `A₀ = 2 (2 - θ) + (1 + τ) δ ≈ 3.0`, against `6`;
* Layer 5.2's pattern is read with the sum of the ratios pinned by the multidegree, so the
  deviation error of Steps IV and VI is charged `η · 2 |c₁ - c₂|` per place instead of
  `η · 2 (|c₁| + |c₂|)`: every place of the frame has a nonnegative exponent
  (`frame_negWeight`), and the deviation weight is at most `2 (2 + δ) ≈ 4.52` against
  `2 A₀ ≈ 6.0` (`NumberField.approxDevWeight`);
* `η` and the margin `ε` are any with `-W/2 + η · 2 (2 + δ) ≤ -ε/4`: `η` takes all of the budget
  of Steps IV and VI but the margin, and the margin `ε = 1/1000` only costs `log ε⁻¹` in the
  threshold;
* the chain length is any `m` with Layer 5.2's `log ((q + 1) / q · f) < (m + 1) · layerRate 1 η`
  for the frame's `f = 3` distinct forms, and Evertse's Roth lemma is used at this `m` and `η`
  (`NumberField.rothLemmaAt_evertse`);
* Siegel's lemma is used at the exponent `q = 999` (at most `999/1000` as many conditions as
  unknowns) instead of the book's `q = 1` (half): the `2` of `log (2 f)` becomes `1000/999`,
  and the auxiliary polynomial's height constant, which only enters the threshold, is charged
  `q` times;
* `Finset.layerRate 1 η ≥ 6 η² - 16 η³` is the variance form of the Chernoff bound of Layer 5.2:
  the variance `1/12` of the exponent of one variable instead of its raw second moment `1/3`,
  at a Bennett factor `1 + 8η/3` (`Finset.layerRate_one_ge`), against the book's `3 η² / 2`.

At `δ = 13/50` this is `η = 1433/50000 = δ/9.07`, `m = 241` and at most `22 900` lines
(`failures_line_cover_sharp_num`): about `45 600` times fewer than `lineCountRho`. Std3: no
cited axiom.

## Main results

* `BB13.frame_posWeight`: the positive weight of the frame's exponents is `2 - θ`.
* `BB13.frame_negWeight`: every place of the frame has a nonnegative exponent.
* `BB13.lineCountExplicit`, `BB13.failures_line_cover_explicit`: the count at given `δ`, `τ`,
  `η`, `q`, `ε` and `m`.
* `BB13.failures_line_cover_sharp_num`, `BB13.failures_line_cover_ten_sharp`: at most
  `22 900` lines, for the exceptions `n ≥ 20` and `n ≥ 10`.

## References

* `plans/plan-beyond-BB13.html`, §7, item M3.
-/

namespace BB13

open NumberField IsDedekindDomain Height Module Finset

/-! ### The positive weight of the frame -/

open scoped Classical in
/-- **The frame's exponents have positive weight `2 - θ`**: `1 - θ` and `1` at `∞`, nothing at
`2` and `3`. -/
theorem frame_posWeight {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ epsStar - 1 / 1000) :
    systemPosWeight (frameExp ((epsStar - δ) / 2)) = 2 - theta := by
  have hη : (epsStar - δ) / 2 ≤ theta - 1 / 2 := by
    rw [epsStar_eq_two_theta_sub_one]; linarith
  have hθ := theta_pos
  have hθ1 := theta_lt_one
  have hpair : ∑ q : frameS, ∑ i, max (frameExp ((epsStar - δ) / 2) (.inr q) i) 0
      = ∑ q ∈ frameS, ∑ i : Fin 2, max
        ((if q = v2 then ![-theta + (epsStar - δ) / 2, 0] else ![0, -1 + (epsStar - δ) / 2]) i)
          0 :=
    Finset.sum_coe_sort frameS fun q ↦ ∑ i : Fin 2, max
      ((if q = v2 then ![-theta + (epsStar - δ) / 2, 0] else ![0, -1 + (epsStar - δ) / 2]) i) 0
  rw [systemPosWeight, Fintype.sum_sum_type, hpair]
  unfold frameS
  rw [Finset.sum_pair v2_ne_v3, Fintype.sum_unique]
  simp only [frameExp, Fin.sum_univ_two, v2_ne_v3.symm, ite_true, ite_false]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - theta), max_eq_left zero_le_one,
    max_eq_right (by linarith : -theta + (epsStar - δ) / 2 ≤ 0), max_eq_right le_rfl,
    max_eq_right (by linarith : -1 + (epsStar - δ) / 2 ≤ 0)]
  ring

/-- **Every place of the frame has a nonnegative exponent** (`1` at `∞`, `0` at `2` and `3`), so
the derivative of the auxiliary polynomial costs nothing in the deviation weight. -/
theorem frame_negWeight (η : ℝ) : systemNegWeight (frameExp η) = 0 := by
  refine Finset.sum_eq_zero fun p _ ↦ max_eq_right ?_
  have h : ∃ i, 0 ≤ frameExp η p i := by
    rcases p with _ | q
    · exact ⟨1, by simp [frameExp]⟩
    · by_cases hq : q.1 = v2
      · exact ⟨1, by simp [frameExp, hq]⟩
      · exact ⟨0, by simp [frameExp, hq]⟩
  obtain ⟨i, hi⟩ := h
  exact neg_nonpos.2 (hi.trans (le_ciSup (Finite.bddAbove_range _) i))

/-! ### The count at explicit parameters -/

open scoped Classical in
/-- The threshold of the frame at the explicit parameters `δ`, `τ`, `η`, Siegel's exponent `q`,
`ε`, `m`, with Evertse's height cost at `m` and `η` (`NumberField.rothLemmaAt_evertse` for
Rémond's heights), at least `2·10⁵`. -/
noncomputable def frameX0Explicit (δ τ η q ε : ℝ) (m : ℕ) : ℝ :=
  max (systemThresholdTwoExplicit ℚ frameS (fun v ↦ v) frameForms m 1 δ τ η q ε
      (((1 : ℕ) : ℝ) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1))
      (max ((MvPolynomial.resultantHeight (MvPolynomial.archEmbedded_of_numberField ℚ)
        (Prod.fst_surjective (α := Fin (m + 1)) (β := Fin 2))).botBound 1) 0 + (m : ℝ) + 2))
    200000

/-- **The number of lines of the exceptions at explicit parameters**: two exceptional subspaces,
`1 + log(16 (m + 1) η⁻¹ (1 + 10⁻⁵))/log ρ₀` lines for each of the `m` intervals of ratio
`4σ⁻¹ = 16 (m + 1)/η` (Evertse's `σ`), and `1 + log(X₀/(10⁵ log 3))/log ρ₀` lines below the
threshold. -/
noncomputable def lineCountExplicit (δ τ η q ε : ℝ) (m : ℕ) : ℝ :=
  2 + (m : ℝ) * (1 + Real.log (16 * ((m : ℝ) + 1) / η * (1 + 1 / 100000)) /
        Real.log (6309 / 5000)) +
    (1 + Real.log (frameX0Explicit δ τ η q ε m / (Real.log 3 * 100001)) /
      Real.log (6309 / 5000))

/-- **The exceptions `n ≥ 20` lie on at most `lineCountExplicit δ τ η q ε m` lines**, for
`0 < δ ≤ ε* − 1/1000`, `τ > 0`, `0 < η ≤ 1`, any margin `0 < ε ≤ (1 - τ) δ` within the budget
`-(1 - τ) δ / 2 + η · 2 (2 + δ) ≤ -ε/4`, any Siegel exponent `q ≥ 1` and any chain
length `m` with `log (3 (q + 1) / q) < (m + 1) · layerRate 1 η` (Layer 5.2's condition for the
frame's three forms):
Subspace-Theorems' interval result at these parameters with Evertse's Roth lemma, above `X₀`,
counted interval by interval with the elementary gap `ρ₀`, and the census with the same gap below
`X₀`. No cited axiom. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_explicit {δ τ η q ε : ℝ} {m : ℕ} (hδ0 : 0 < δ)
    (hδ : δ ≤ epsStar - 1 / 1000) (hτ : 0 < τ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hεW : ε ≤ (1 - τ) * δ)
    (hbudget : -((1 - τ) * δ) / 2 + η * (2 * (2 + δ)) ≤ -(ε / 4))
    (hq : 1 ≤ q) (hm : Real.log ((q + 1) / q * 3) < ((m : ℝ) + 1) * Finset.layerRate 1 η) :
    ∃ R : Finset ℚ, (#R : ℝ) ≤ lineCountExplicit δ τ η q ε m ∧
      ∀ n : ℕ, 20 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  classical
  have hX₀2 : (200000 : ℝ) ≤ frameX0Explicit δ τ η q ε m := le_max_right _ _
  have hR := rothLemmaAt_evertse.{0} (K := ℚ) (fun k ↦ MvPolynomial.resultantHeight
    (MvPolynomial.archEmbedded_of_numberField ℚ) (Prod.fst_surjective (α := Fin k) (β := Fin 2)))
    (n := 1) (m := m) le_rfl hη0 hη1
  obtain ⟨T, hT2, hTtop, 𝒯, h𝒯, h𝒯ge, hint⟩ :=
    exists_forall_mem_interval_systemSet_two_of_rothLemmaAt (Fintype.card_fin 2) frameS
    (fun v ↦ v) (fun v ↦ AbsoluteValue.liesOver_self _)
    (fun v _ ↦ AbsoluteValue.liesOver_self _) (frameSystem_isNormalized hδ0 hδ) hτ hε
    (by rw [finrank_self]; push_cast; linarith) hη0 (by positivity) (by positivity)
    (by positivity) hR (by
      refine le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (min_le_right _ _) hη0.le)) ?_
      rw [finrank_self, frame_negWeight]
      push_cast
      linarith)
    (f := 3) (by rw [finrank_self]) hq (by push_cast; exact hm)
    (X₀ := frameX0Explicit δ τ η q ε m) (le_max_left _ _)
  set X₀ := frameX0Explicit δ τ η q ε m with hX₀
  have hρeq : 4 * (η / (4 * ((m : ℝ) + 1)))⁻¹ = 16 * ((m : ℝ) + 1) / η := by
    rw [inv_div]; ring
  set ρ := 16 * ((m : ℝ) + 1) / η with hρ
  rw [hρeq] at hint
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, le_div_iff₀ hη0]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hl3 := one_lt_log_three
  have hl3' := log_three_le
  have hl2 := log_two_le_one
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlr : 0 < Real.log (6309 / 5000) := Real.log_pos (by norm_num)
  set lH : ℕ → ℝ := fun n ↦ Real.log (mulHeightAff (framePt n)) with hlH
  -- the exceptions in an interval, and below the threshold
  set F : ℝ → Finset ℕ := fun s ↦ (range (⌈ρ * s⌉₊ + 1)).filter fun n ↦
    20 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ s ≤ lH n ∧ lH n < ρ * s with hF
  set Fm : Finset ℕ := (range (⌈X₀⌉₊ + 1)).filter fun n ↦
    20 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ lH n < X₀ with hFm
  set per : ℝ := 1 + Real.log (ρ * (1 + 1 / 100000)) / Real.log (6309 / 5000) with hper
  have hper0 : 0 ≤ per := by
    have : 0 ≤ Real.log (ρ * (1 + 1 / 100000)) := Real.log_nonneg (by nlinarith)
    have := div_nonneg this hlr.le
    linarith
  have hFs : ∀ s ∈ 𝒯, (#((F s).image linePoint) : ℝ) ≤ per := by
    intro s hs
    have hsX := (h𝒯ge s hs).trans' hX₀2
    have hApos : 0 < (s - Real.log 2) / Real.log 3 := div_pos (by linarith) (by linarith)
    have h := card_image_linePoint_le (A := (s - Real.log 2) / Real.log 3)
      (B := ρ * s / Real.log 3) ?_ ?_ (F s) (fun n hn ↦ (mem_filter.1 hn).2.2.1) ?_ ?_
    · have key : Real.log (ρ * s / Real.log 3 / ((s - Real.log 2) / Real.log 3)) ≤
          Real.log (ρ * (1 + 1 / 100000)) := by
        refine Real.log_le_log (div_pos (by positivity) hApos) ?_
        rw [div_le_iff₀ hApos, mul_div_assoc', div_le_div_iff_of_pos_right (by linarith)]
        have : 0 ≤ s / 100000 - (1 + 1 / 100000) * Real.log 2 := by linarith
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ρ) this]
      have := div_le_div_of_nonneg_right key hlr.le
      rw [hper]
      linarith
    · rw [le_div_iff₀ (by linarith)]; nlinarith
    · exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
    · intro n hn
      obtain ⟨-, -, hnf, h1, -⟩ := mem_filter.1 hn
      rw [div_le_iff₀ (by linarith)]
      linarith [(log_mulHeightAff_framePt hnf).2]
    · intro n hn
      obtain ⟨-, -, hnf, -, h2⟩ := mem_filter.1 hn
      rw [lt_div_iff₀ (by linarith)]
      linarith [(log_mulHeightAff_framePt hnf).1]
  have hFm' : (#(Fm.image linePoint) : ℝ) ≤
      1 + Real.log (X₀ / (Real.log 3 * 100001)) / Real.log (6309 / 5000) := by
    have h := card_image_linePoint_le (A := 100001) (B := X₀ / Real.log 3) le_rfl ?_ Fm
      (fun n hn ↦ (mem_filter.1 hn).2.2.1) ?_ ?_
    · rwa [div_div] at h
    · rw [le_div_iff₀ (by linarith)]; nlinarith
    · intro n hn
      obtain ⟨-, h20, hnf, -⟩ := mem_filter.1 hn
      have : 100001 ≤ n := by
        by_contra hlt
        rcases (failures_up_to_100000 n (by omega) (by omega)).1 hnf with h | h | h | h | h <;>
          omega
      exact_mod_cast this
    · intro n hn
      obtain ⟨-, -, hnf, h2⟩ := mem_filter.1 hn
      rw [lt_div_iff₀ (by linarith)]
      linarith [(log_mulHeightAff_framePt hnf).1]
  refine ⟨T.image subspaceSlope ∪ 𝒯.biUnion (fun s ↦ (F s).image linePoint) ∪
    Fm.image linePoint, ?_, fun n hn hnf ↦ ?_⟩
  · have h1 : (#(T.image subspaceSlope ∪ 𝒯.biUnion (fun s ↦ (F s).image linePoint) ∪
        Fm.image linePoint) : ℝ) ≤ #(T.image subspaceSlope) +
          #(𝒯.biUnion (fun s ↦ (F s).image linePoint)) + #(Fm.image linePoint) := by
      exact_mod_cast (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    have h2 : (#(T.image subspaceSlope) : ℝ) ≤ 2 := by exact_mod_cast card_image_le.trans hT2
    have h3 : (#(𝒯.biUnion (fun s ↦ (F s).image linePoint)) : ℝ) ≤ m * per :=
      calc (#(𝒯.biUnion (fun s ↦ (F s).image linePoint)) : ℝ)
          ≤ ∑ s ∈ 𝒯, (#((F s).image linePoint) : ℝ) := by exact_mod_cast card_biUnion_le
        _ ≤ ∑ _s ∈ 𝒯, per := sum_le_sum hFs
        _ = #𝒯 * per := by rw [sum_const, nsmul_eq_mul]
        _ ≤ m * per := mul_le_mul_of_nonneg_right (by exact_mod_cast h𝒯) hper0
    rw [lineCountExplicit, ← hX₀, ← hρ, ← hper]
    linarith
  · have hb := log_mulHeightAff_framePt hnf
    have hn0 : (n : ℝ) ≤ lH n := by
      have : (n : ℝ) ≤ n * Real.log 3 := le_mul_of_one_le_right (Nat.cast_nonneg n) hl3.le
      linarith [hb.1]
    by_cases hlt : lH n < X₀
    · refine mem_union_right _ (mem_image_of_mem _ (mem_filter.2 ⟨mem_range.2 ?_, hn, hnf, hlt⟩))
      have : n < ⌈X₀⌉₊ := Nat.lt_ceil.2 (hn0.trans_lt hlt)
      omega
    push Not at hlt
    rcases hint (framePt n) (frame_mem_systemSet hδ0 hδ hn hnf) hlt with ⟨U, hU, hxU⟩ |
      ⟨s, hs, h1, h2⟩
    · have hy : framePt n 1 ≠ 0 := by simp [framePt, (frameY_pos n).ne']
      refine mem_union_left _ (mem_union_left _ (mem_image.2 ⟨U, hU, ?_⟩))
      rw [subspaceSlope_eq (hTtop U hU) hxU hy]
      simp [linePoint, framePt]
    · refine mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨s, hs, mem_image_of_mem _
        (mem_filter.2 ⟨mem_range.2 ?_, hn, hnf, h1, h2⟩)⟩))
      have : n < ⌈ρ * s⌉₊ := Nat.lt_ceil.2 (hn0.trans_lt h2)
      omega

/-! ### The constant at `δ = 13/50`, `τ = 1/1000`, `η = 1433/50000`, `q = 999`, `ε = 1/1000`,
`m = 241` -/

theorem theta_ge : (0.6309 : ℝ) ≤ theta := by
  rw [theta, le_div_iff₀ (Real.log_pos (by norm_num))]
  linarith [Real.log_two_gt_d9, log_three_le]

/-- The budget of Steps IV and VI at `δ = 13/50`, `τ = 1/1000`, `η = 1433/50000`, `ε = 1/1000`,
with the deviation weight `2 (2 + δ)`: `η` takes all but `0.3 %` of it. -/
theorem explicit_budget : -((1 - 1 / 1000) * (13 / 50)) / 2 + 1433 / 50000 *
    (2 * (2 + 13 / 50)) ≤ -((1 / 1000 : ℝ) / 4) := by
  norm_num

/-- Layer 5.2's condition at `η = 1433/50000`, Siegel's exponent `q = 999` and `m = 241`:
`log (3 · 1000/999) < (m + 1) · layerRate 1 η`, from `layerRate 1 η ≥ 6 η² - 16 η³` and
`log (1000/999) ≤ 1/999`. -/
theorem explicit_chain :
    Real.log ((999 + 1) / 999 * 3) < (((241 : ℕ) : ℝ) + 1) * Finset.layerRate 1 (1433 / 50000) := by
  have h := Finset.layerRate_one_ge (η := 1433 / 50000) (by norm_num)
  have h999 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1000 / 999 by norm_num)
  rw [show ((999 : ℝ) + 1) / 999 * 3 = 1000 / 999 * 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  norm_num at h h999 ⊢
  linarith [log_three_le]

open scoped Classical in
/-- **The threshold at the explicit parameters**: `X₀ ≤ 2⁵⁰ (2³ · 3⁷)^(m+1)` for `m ≤ 241`, from
Subspace-Theorems' closed form over `ℚ` (`NumberField.systemThresholdTwoExplicit_rat_le`, with
`h(ℙ¹) ≤ 6` for Rémond's heights); `2³ · 3⁷ = 17 496 ≥ 2 (m + 1)/η`. -/
theorem frameX0Explicit_le {m : ℕ} (hm : m ≤ 241) :
    frameX0Explicit (13 / 50) (1 / 1000) (1433 / 50000) 999 (1 / 1000) m ≤
      2 ^ 50 * ((2 : ℝ) ^ 3 * 3 ^ 7) ^ (m + 1) := by
  have hT := systemThresholdTwoExplicit_rat_le (fun m ↦ (MvPolynomial.resultantHeight
      (MvPolynomial.archEmbedded_of_numberField ℚ)
      (Prod.fst_surjective (α := Fin m) (β := Fin 2))).botBound 1)
    (fun _ ↦ MvPolynomial.resultantHeight_botBound_one_le _ _) (Fintype.card_fin 2)
    (fun _ ↦ AbsoluteValue.liesOver_self _) (fun _ _ ↦ AbsoluteValue.liesOver_self _)
    (frameSystem_isNormalized (δ := 13 / 50) (by norm_num) thirteen_fiftieths_le) m (1 / 1000)
    (η := 1433 / 50000) (q := 999) (ε := 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hsum : ∑ q ∈ frameS, Real.log (Ideal.absNorm q.asIdeal : ℝ) =
      Real.log 2 + Real.log 3 := by
    unfold frameS
    rw [Finset.sum_pair v2_ne_v3, absNorm_v2, absNorm_v3]
    norm_num
  have hprod : ∏ q ∈ frameS, (Ideal.absNorm q.asIdeal : ℝ) = 6 := by
    unfold frameS
    rw [Finset.prod_pair v2_ne_v3, absNorm_v2, absNorm_v3]
    norm_num
  rw [card_frameS, hsum, hprod] at hT
  have hmR : (m : ℝ) ≤ 241 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hZ : (1 : ℝ) ≤ ((2 : ℝ) ^ 3 * 3 ^ 7) ^ (m + 1) := one_le_pow₀ (by norm_num)
  have hF : max 1 (2 * ((m : ℝ) + 1) / (1433 / 50000)) ^ (m + 1)
      ≤ ((2 : ℝ) ^ 3 * 3 ^ 7) ^ (m + 1) := by
    refine pow_le_pow_left₀ (by positivity) (max_le (by norm_num) ?_) _
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  refine max_le (hT.trans ?_) ?_
  · generalize ((2 : ℝ) ^ 3 * 3 ^ 7) ^ (m + 1) = Z at hZ hF ⊢
    have hl2 := Real.log_two_lt_d9
    have hl3 := log_three_le
    -- the coefficient
    have hP : ratThresholdCoeffTwoExplicit 2 6 (1 / 1000) (1433 / 50000) 999 m ≤ 2 ^ 48 * Z := by
      rw [ratThresholdCoeffTwoExplicit]
      have hF1 : (1 : ℝ) ≤ max 1 (2 * ((m : ℝ) + 1) / (1433 / 50000)) ^ (m + 1) :=
        one_le_pow₀ (le_max_left _ _)
      generalize max 1 (2 * ((m : ℝ) + 1) / (1433 / 50000)) ^ (m + 1) = F at hF hF1 ⊢
      generalize (m : ℝ) = x at hmR hm0 ⊢
      have hF0 : 0 ≤ F := by linarith
      rw [div_le_iff₀ (by norm_num)]
      have h1 : 8 * (1 + ((2 : ℕ) : ℝ)) * F * (x + 1) ^ 2 *
          (x + max 6 0 + 999 * (40 * (1 + ((2 : ℕ) : ℝ)) + 3) + 2) ≤ 24 * Z * 58564 * 123126 := by
        have hmax : max (6 : ℝ) 0 = 6 := by norm_num
        rw [hmax]
        push_cast
        have hm1 : (x + 1) ^ 2 ≤ 58564 := by nlinarith
        have hm2 : x + 6 + 999 * (40 * (1 + 2) + 3) + 2 ≤ 123126 := by linarith
        calc 8 * (1 + 2) * F * (x + 1) ^ 2 * (x + 6 + 999 * (40 * (1 + 2) + 3) + 2)
            = 24 * F * (x + 1) ^ 2 * (x + 6 + 999 * (40 * (1 + 2) + 3) + 2) := by ring
          _ ≤ 24 * Z * 58564 * 123126 := by gcongr
      push_cast at h1 ⊢
      norm_num at h1 ⊢
      nlinarith
    have hP0 : 0 ≤ ratThresholdCoeffTwoExplicit 2 6 (1 / 1000) (1433 / 50000) 999 m := by
      rw [ratThresholdCoeffTwoExplicit]
      positivity
    refine max_le ?_ (max_le ?_ ?_)
    · have hs : 4 * (1 + ((2 : ℕ) : ℝ)) * Real.log 1 + (Real.log 2 + Real.log 3) + 1 ≤ 3 := by
        rw [Real.log_one]; linarith
      have hs0 : 0 ≤ 4 * (1 + ((2 : ℕ) : ℝ)) * Real.log 1 + (Real.log 2 + Real.log 3) + 1 := by
        rw [Real.log_one]
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
        linarith
      calc _ ≤ 2 ^ 48 * Z * 3 := mul_le_mul hP hs hs0 (by positivity)
        _ ≤ _ := by linarith
    · norm_num; linarith
    · rw [show (2 : ℝ) * 6 = 12 by norm_num]
      simp only [systemHeightThreshold, Nat.factorial]
      norm_num
      have h12 := log_twelve_le
      have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
  · have : (1 : ℝ) ≤ ((2 : ℝ) ^ 3 * 3 ^ 7) ^ (m + 1) := hZ
    nlinarith

/-- **`lineCountExplicit ≤ 22 900`** at `δ = 13/50`, `τ = 1/1000`, `η = 1433/50000`, `q = 999`,
`ε = 1/1000`, `m ≤ 241`: `m` intervals of at most `51.96` lines each (`1.25·10⁴`), and
`log X₀ ≤ 50 log 2 + (m + 1) log (2³ · 3⁷)` below the threshold (`1.03·10⁴`). -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem lineCountExplicit_le {m : ℕ} (hm : m ≤ 241) :
    lineCountExplicit (13 / 50) (1 / 1000) (1433 / 50000) 999 (1 / 1000) m ≤ 22900 := by
  have hX := frameX0Explicit_le hm
  have hX2 : (200000 : ℝ) ≤
      frameX0Explicit (13 / 50) (1 / 1000) (1433 / 50000) 999 (1 / 1000) m :=
    le_max_right _ _
  have hρ := log_rho_ge
  have hl2 := Real.log_two_lt_d9
  have hl3 := one_lt_log_three
  have hl3' := log_three_le
  rw [lineCountExplicit]
  have hmR : (m : ℝ) ≤ 241 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlogZ : Real.log (((2 : ℝ) ^ 3 * 3 ^ 7) ^ (m + 1))
      = ((m : ℝ) + 1) * (3 * Real.log 2 + 7 * Real.log 3) := by
    rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hZ : (1 : ℝ) ≤ ((2 : ℝ) ^ 3 * 3 ^ 7) ^ (m + 1) := one_le_pow₀ (by norm_num)
  generalize ((2 : ℝ) ^ 3 * 3 ^ 7) ^ (m + 1) = Z at hX hZ hlogZ
  generalize frameX0Explicit (13 / 50) (1 / 1000) (1433 / 50000) 999 (1 / 1000) m = X at hX hX2
  generalize (m : ℝ) = x at hmR hm0 hlogZ ⊢
  -- one interval: `16 (m + 1)/η (1 + 10⁻⁵) ≤ 2⁶ · 3⁷`
  have hratio : 16 * (x + 1) / (1433 / 50000) * (1 + 1 / 100000) ≤ (2 : ℝ) ^ 6 * 3 ^ 7 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
    nlinarith
  have hlogρ : Real.log (16 * (x + 1) / (1433 / 50000) * (1 + 1 / 100000)) ≤ 11.84917 := by
    calc _ ≤ Real.log ((2 : ℝ) ^ 6 * 3 ^ 7) :=
          Real.log_le_log (by positivity) hratio
      _ = 6 * Real.log 2 + 7 * Real.log 3 := by
          rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast
          ring
      _ ≤ _ := by linarith
  have hlogρ0 : 0 ≤ Real.log (16 * (x + 1) / (1433 / 50000) * (1 + 1 / 100000)) := by
    refine Real.log_nonneg ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
    nlinarith
  have hper : Real.log (16 * (x + 1) / (1433 / 50000) * (1 + 1 / 100000)) /
      Real.log (6309 / 5000) ≤ 11.84917 / 0.23253 :=
    div_le_div₀ (by norm_num) hlogρ (by norm_num) hρ
  have hper0 : 0 ≤ Real.log (16 * (x + 1) / (1433 / 50000) * (1 + 1 / 100000)) /
      Real.log (6309 / 5000) := div_nonneg hlogρ0 (by linarith)
  -- below the threshold
  have hden : 1 ≤ Real.log 3 * 100001 := by nlinarith
  have hX0 : 0 < X := by linarith
  have hlogX : Real.log (X / (Real.log 3 * 100001)) ≤ 50 * 0.6931471808
      + (241 + 1) * (3 * 0.6931471808 + 7 * 1.0986122888) := by
    calc Real.log (X / (Real.log 3 * 100001)) ≤ Real.log X :=
          Real.log_le_log (by positivity) (div_le_self hX0.le hden)
      _ ≤ Real.log (2 ^ 50 * Z) := Real.log_le_log hX0 hX
      _ = 50 * Real.log 2 + (x + 1) * (3 * Real.log 2 + 7 * Real.log 3) := by
          rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow, hlogZ]; push_cast; ring
      _ ≤ _ := by
          have h0 : 0 ≤ 3 * Real.log 2 + 7 * Real.log 3 := by
            have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
            linarith
          nlinarith
  have hlogX0 : 0 ≤ Real.log (X / (Real.log 3 * 100001)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; nlinarith)
  have hbelow : Real.log (X / (Real.log 3 * 100001)) / Real.log (6309 / 5000) ≤
      (50 * 0.6931471808 + (241 + 1) * (3 * 0.6931471808 + 7 * 1.0986122888)) / 0.23253 :=
    div_le_div₀ (by norm_num) hlogX (by norm_num) hρ
  have hint : x * (1 + Real.log (16 * (x + 1) / (1433 / 50000) * (1 + 1 / 100000)) /
      Real.log (6309 / 5000)) ≤ 241 * (1 + 11.84917 / 0.23253) := by
    have h1 : 0 ≤ 1 + Real.log (16 * (x + 1) / (1433 / 50000) * (1 + 1 / 100000)) /
        Real.log (6309 / 5000) := by linarith
    calc _ ≤ 241 * (1 + Real.log (16 * (x + 1) / (1433 / 50000) * (1 + 1 / 100000)) /
          Real.log (6309 / 5000)) := mul_le_mul_of_nonneg_right hmR h1
      _ ≤ _ := by linarith
  norm_num at hint hbelow ⊢
  linarith

/-- **The exceptions `‖(3/2)ⁿ‖ < (3/4)ⁿ`, `n ≥ 20`, lie on at most `22 900` lines.** -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_sharp_num :
    ∃ R : Finset ℚ, #R ≤ 22900 ∧
      ∀ n : ℕ, 20 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨R, hR, hmem⟩ := failures_line_cover_explicit (δ := 13 / 50) (τ := 1 / 1000)
    (η := 1433 / 50000) (q := 999) (ε := 1 / 1000) (m := 241) (by norm_num) thirteen_fiftieths_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) explicit_budget
    (by norm_num) explicit_chain
  exact ⟨R, by exact_mod_cast hR.trans (lineCountExplicit_le le_rfl), hmem⟩

/-- **The exceptions `‖(3/2)ⁿ‖ < (3/4)ⁿ`, `n ≥ 10`, lie on at most `22 900` lines**: there are
none in `[10, 20)`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_ten_sharp :
    ∃ R : Finset ℚ, R.card ≤ 22900 ∧
      ∀ n : ℕ, 10 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_sharp_num
  refine ⟨R, hcard, fun n hn hnf ↦ ?_⟩
  rcases lt_or_ge n 20 with h | h
  · rcases (failures_up_to_256 n (by omega) (by omega)).1 hnf with h' | h' | h' | h' | h' <;>
      omega
  · exact hR n h hnf

end BB13
