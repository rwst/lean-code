/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.IntervalST
import BB13.ConstantsST
import BB13.CensusSweep

/-!
# The line cover with the elementary gap principle (WP A5 of plan-beyond-BB13)

`BB13/ConstantsST.lean` puts the exceptions `‖(3/2)ⁿ‖ < (3/4)ⁿ`, `n ≥ 20`, on at most
`3.87·10⁹` lines, by Subspace-Theorems' count in two variables. That count spends a generic gap
principle, of ratio `1 + δ/4 ≈ 1.065` in the height, twice: once inside each of the
`m ≈ 4.9·10⁶` intervals of the Subspace Theorem, and once on the range below the threshold
`X₀`. BB13 has a much better gap principle of its own. Two exceptions `a < b` on distinct lines
are not linked (`sameTower_of_linkable`), so `b ≥ ρ₀ a` with `ρ₀ = 1.2618` as soon as
`a > 10⁵` (`rho_gap`, from `BB13.gap_of_nonlink`). Since `log H(xₙ) = n log 3 + O(1)`, this is
a gap of ratio `ρ₀` in the log-height, against `1 + δ/4`: `log ρ₀ = 0.2325` against `0.0630`.

This file reassembles the count with it:

* the Subspace Theorem only as an **interval result** (`BB13.exists_interval_of_isNormalizedSystem_two`):
  above `X₀`, the frame points lie in two subspaces or have `log H` in `m` intervals of ratio
  `4σ⁻¹`, each meeting at most `1 + log(4σ⁻¹(1 + 10⁻⁵))/log ρ₀ ≈ 111` lines;
* **below `X₀`** no Subspace input at all: the census leaves no exception in `[20, 10⁵]`, and the
  exceptions in `(10⁵, X₀/log 3)` meet at most `1 + log(X₀/(10⁵ log 3))/log ρ₀` lines.

The small-solutions term of the generic count (`1.5·10⁷`) disappears, since the census covers
the small range. At `δ = 13/50` the total is at most `1.05·10⁹` lines
(`failures_line_cover_rho_num`), against `3.87·10⁹` from the generic count, `8.59·10¹⁰` from the
computational record and `K(ε*) ≈ 1.86·10¹²` from [BE08] Cor. 5.2. Std3: no cited axiom.

## Main results

* `BB13.sameTower_of_linkable`: linked exceptions lie on one line.
* `BB13.rho_gap`: exceptions `10⁵ < a < b` on distinct lines have `ρ₀ a ≤ b`.
* `BB13.card_image_linePoint_le`: exceptions in `[A, B)`, `A > 10⁵`, meet at most
  `1 + log(B/A)/log ρ₀` lines.
* `BB13.lineCountRho`, `BB13.failures_line_cover_rho`: the reassembled count, for every
  `0 < δ ≤ ε* − 1/1000`.
* `BB13.failures_line_cover_rho_num`, `BB13.failures_line_cover_ten_rho`: at most
  `1 050 000 000` lines, for the exceptions `n ≥ 20` and `n ≥ 10`.

## References

* Y. Bugeaud and J.-H. Evertse, Acta Arith. **133** (2008), Cor. 5.2.
* `plans/plan-beyond-BB13.html`, §3.4, WP A5.
-/

namespace BB13

open NumberField IsDedekindDomain Height Module Finset

/-! ### The elementary gap principle between lines -/

/-- **Linked exceptions lie on one line**: if `a < b` are exceptions with `2 (3/4)ᵃ 3ᵇ⁻ᵃ ≤ 1`,
then `3ᵇ⁻ᵃ mₐ = 2ᵇ⁻ᵃ m_b` (`BB13.linkage_of_linkable`), so their frame points are collinear. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_of_linkable {a b : ℕ} (hab : a < b) (ha : IsFailure 3 2 (3 / 4) a)
    (hb : IsFailure 3 2 (3 / 4) b) (hl : Linkable 3 (3 / 4) a b) : SameTower a b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab.le
  have h := linkage_of_linkable 3 2 (3 / 4) a d (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ha hb hl
  have h' : (3 : ℚ) ^ d * (Mnum 3 2 a : ℚ) = 2 ^ d * (Mnum 3 2 (a + d) : ℚ) := by
    exact_mod_cast h
  simp only [SameTower, linePoint, frameX, frameY]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity), pow_add, pow_add]
  linear_combination ((2 : ℚ) ^ a * 3 ^ a) * h'

/-- **The gap between lines**: exceptions `10⁵ < a < b` on distinct lines have
`b ≥ ρ₀ a`, `ρ₀ = 6309/5000 = 1.2618`. They are not linked (`sameTower_of_linkable`), and
`BB13.gap_of_nonlink` applies at threshold `100001`, where `ρ₀ < 1 + ε* − θ/100001`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem rho_gap {a b : ℕ} (ha : 100001 ≤ a) (hab : a < b) (hfa : IsFailure 3 2 (3 / 4) a)
    (hfb : IsFailure 3 2 (3 / 4) b) (hne : ¬ SameTower a b) : (6309 / 5000 : ℝ) * a ≤ b := by
  refine gap_of_nonlink 3 (3 / 4) (6309 / 5000) a b 100001 (by norm_num) (by norm_num) hab ha
    (by norm_num) (lt_of_not_ge fun h ↦ hne (sameTower_of_linkable hab hfa hfb h)) ?_
  have h43 : Real.log (1 / (3 / 4 : ℝ)) = Real.log (4 / 3) := by norm_num
  rw [h43]
  push_cast
  linarith [log_four_thirds_ge, log_three_le, Real.log_two_lt_d9]

/-- `log ρ₀ ≥ 0.23253`: three terms of the series of `2 artanh(1309/11309)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem log_rho_ge : (0.23253 : ℝ) ≤ Real.log (6309 / 5000) := by
  have h := Real.hasSum_log_one_add_inv (a := 5000 / 1309) (by norm_num)
  have h0 := sum_le_hasSum (range 3) (fun k _ ↦ by positivity) h
  have e : (1 : ℝ) + (5000 / 1309)⁻¹ = 6309 / 5000 := by norm_num
  rw [e] at h0
  norm_num [Finset.sum_range_succ] at h0
  linarith

/-! ### Counting lacunary sets -/

/-- In a set of naturals with gap ratio `ρ ≥ 1` and all elements `≥ A ≥ 0`, some element is at
least `ρ^(#s − 1) A`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem exists_mem_pow_le_of_gap {ρ A : ℝ} (hρ : 1 ≤ ρ) (s : Finset ℕ) :
    (∀ a ∈ s, ∀ b ∈ s, a < b → ρ * a ≤ b) → (∀ a ∈ s, A ≤ a) → s.Nonempty →
      ∃ b ∈ s, ρ ^ (#s - 1) * A ≤ b := by
  induction s using Finset.induction_on_max with
  | empty => intro _ _ h; exact absurd h Finset.not_nonempty_empty
  | insert a s ha ih =>
    intro hgap hA _
    have has : a ∉ s := fun h ↦ lt_irrefl a (ha a h)
    rw [card_insert_of_notMem has]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, mem_insert_self _ _, by simpa using hA a (mem_insert_self _ _)⟩
    obtain ⟨b, hb, hbA⟩ := ih
      (fun x hx y hy hxy ↦ hgap x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy)
      (fun x hx ↦ hA x (mem_insert_of_mem hx)) hs
    refine ⟨a, mem_insert_self _ _, ?_⟩
    have hab := hgap b (mem_insert_of_mem hb) a (mem_insert_self _ _) (ha b hb)
    have hcard : #s + 1 - 1 = (#s - 1) + 1 := by have := hs.card_pos; omega
    rw [hcard, pow_succ]
    calc ρ ^ (#s - 1) * ρ * A = ρ * (ρ ^ (#s - 1) * A) := by ring
      _ ≤ ρ * b := mul_le_mul_of_nonneg_left hbA (by linarith)
      _ ≤ a := hab

/-- **A lacunary set in `[A, B)` is small**: a set of naturals in `[A, B)`, `0 < A ≤ B`, with gap
ratio `ρ > 1` has at most `1 + log(B/A)/log ρ` elements. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem card_le_of_gap {ρ A B : ℝ} (hρ : 1 < ρ) (hA : 0 < A) (hAB : A ≤ B) (s : Finset ℕ)
    (hgap : ∀ a ∈ s, ∀ b ∈ s, a < b → ρ * a ≤ b) (hAs : ∀ a ∈ s, A ≤ a)
    (hBs : ∀ a ∈ s, (a : ℝ) < B) :
    (#s : ℝ) ≤ 1 + Real.log (B / A) / Real.log ρ := by
  have hlρ : 0 < Real.log ρ := Real.log_pos hρ
  have hBA : 0 ≤ Real.log (B / A) / Real.log ρ :=
    div_nonneg (Real.log_nonneg ((one_le_div hA).2 hAB)) hlρ.le
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [card_empty, Nat.cast_zero]; linarith
  obtain ⟨b, hb, hbA⟩ := exists_mem_pow_le_of_gap hρ.le s hgap hAs hs
  have hpow : ρ ^ (#s - 1) < B / A := by
    rw [lt_div_iff₀ hA]; exact hbA.trans_lt (hBs b hb)
  have hlog : ((#s - 1 : ℕ) : ℝ) * Real.log ρ < Real.log (B / A) := by
    rw [← Real.log_pow]; exact Real.log_lt_log (by positivity) hpow
  have hc : (#s : ℝ) = ((#s - 1 : ℕ) : ℝ) + 1 := by
    have := hs.card_pos
    rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  have : ((#s - 1 : ℕ) : ℝ) ≤ Real.log (B / A) / Real.log ρ := by
    rw [le_div_iff₀ hlρ]; exact hlog.le
  linarith

/-- **Exceptions in `[A, B)`, `A ≥ 100001`, meet at most `1 + log(B/A)/log ρ₀` lines.** The least
exception of each line in the range form a `ρ₀`-lacunary set (`rho_gap`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem card_image_linePoint_le {A B : ℝ} (hA : 100001 ≤ A) (hAB : A ≤ B) (F : Finset ℕ)
    (hF : ∀ n ∈ F, IsFailure 3 2 (3 / 4) n) (hAF : ∀ n ∈ F, A ≤ n) (hBF : ∀ n ∈ F, (n : ℝ) < B) :
    (#(F.image linePoint) : ℝ) ≤ 1 + Real.log (B / A) / Real.log (6309 / 5000) := by
  classical
  set S := F.filter fun n ↦ ∀ m ∈ F, m < n → linePoint m ≠ linePoint n with hS
  have hsub : F.image linePoint ⊆ S.image linePoint := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hr
    set G := F.filter fun m ↦ linePoint m = linePoint n with hG
    have hGne : G.Nonempty := ⟨n, mem_filter.2 ⟨hn, rfl⟩⟩
    have hm := mem_filter.1 (G.min'_mem hGne)
    refine mem_image.2 ⟨G.min' hGne, mem_filter.2 ⟨hm.1, fun m hmF hlt heq ↦ ?_⟩, hm.2⟩
    have : G.min' hGne ≤ m := G.min'_le m (mem_filter.2 ⟨hmF, heq.trans hm.2⟩)
    omega
  have hSc : (#S : ℝ) ≤ 1 + Real.log (B / A) / Real.log (6309 / 5000) := by
    refine card_le_of_gap (by norm_num) (by linarith) hAB S (fun a ha b hb hab ↦ ?_)
      (fun a ha ↦ hAF a (mem_filter.1 ha).1) (fun a ha ↦ hBF a (mem_filter.1 ha).1)
    have ha' := (mem_filter.1 ha).1
    have hb' := mem_filter.1 hb
    have ha1 : 100001 ≤ a := by
      have : (100001 : ℝ) ≤ a := hA.trans (hAF a ha')
      exact_mod_cast this
    exact rho_gap ha1 hab (hF a ha') (hF b hb'.1) (hb'.2 a ha' hab)
  calc (#(F.image linePoint) : ℝ) ≤ #(S.image linePoint) := by exact_mod_cast card_le_card hsub
    _ ≤ #S := by exact_mod_cast card_image_le
    _ ≤ _ := hSc

/-! ### The heights of the frame points -/

theorem one_lt_log_three : 1 < Real.log 3 := by linarith [log_three_ge]

/-- `n log 3 ≤ log H(xₙ) ≤ n log 3 + log 2` for an exception `n`. -/
theorem log_mulHeightAff_framePt {n : ℕ} (hnf : IsFailure 3 2 (3 / 4) n) :
    n * Real.log 3 ≤ Real.log (mulHeightAff (framePt n)) ∧
      Real.log (mulHeightAff (framePt n)) ≤ n * Real.log 3 + Real.log 2 := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  constructor
  · rw [← Real.log_pow]
    exact Real.log_le_log h3 (pow_le_mulHeightAff_framePt n)
  · have hle : mulHeightAff (framePt n) ≤ 3 ^ n * 2 := by
      refine (mulHeightAff_framePt_le hnf).trans (mul_le_mul_of_nonneg_left ?_ h3.le)
      have : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    calc Real.log (mulHeightAff (framePt n)) ≤ Real.log (3 ^ n * 2) :=
          Real.log_le_log (mulHeightAff_pos _) hle
      _ = n * Real.log 3 + Real.log 2 := by
          rw [Real.log_mul h3.ne' (by norm_num), Real.log_pow]

/-! ### The reassembled count -/

open scoped Classical in
/-- The threshold of the frame, at least `2·10⁵`. -/
noncomputable def frameX0 (δ : ℝ) : ℝ :=
  max (systemThresholdTwo ℚ frameS (fun v ↦ v) frameForms frameRoth.toRothParams 3 1 δ) 200000

/-- **The number of lines of the exceptions with the elementary gap**: two exceptional
subspaces, `1 + log(4σ⁻¹(1 + 10⁻⁵))/log ρ₀` lines for each of the `m` intervals of the Subspace
Theorem, and `1 + log(X₀/(10⁵ log 3))/log ρ₀` lines below the threshold. -/
noncomputable def lineCountRho (δ : ℝ) : ℝ :=
  2 + (subspaceChainLength 1 3 (2 * systemEps 1 δ) (systemAbsBound 1 2) : ℝ) *
      (1 + Real.log (4 * (frameRoth.ratio 1 3 (2 * systemEps 1 δ) (systemAbsBound 1 2))⁻¹ *
        (1 + 1 / 100000)) / Real.log (6309 / 5000)) +
    (1 + Real.log (frameX0 δ / (Real.log 3 * 100001)) / Real.log (6309 / 5000))

/-- **The exceptions `n ≥ 20` lie on at most `lineCountRho δ` lines**, for every
`0 < δ ≤ ε* − 1/1000`: Subspace-Theorems' interval result in two variables above `X₀`, counted
interval by interval with the elementary gap `ρ₀`, and the census with the same gap below `X₀`.
No cited axiom. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_rho {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ epsStar - 1 / 1000) :
    ∃ R : Finset ℚ, (#R : ℝ) ≤ lineCountRho δ ∧
      ∀ n : ℕ, 20 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  classical
  have hX₀2 : (200000 : ℝ) ≤ frameX0 δ := le_max_right _ _
  obtain ⟨T, hT2, hTtop, 𝒯, h𝒯, h𝒯ge, hint⟩ := exists_interval_of_isNormalizedSystem_two
    frameRoth (Fintype.card_fin 2) frameS (fun v ↦ v) (fun v ↦ AbsoluteValue.liesOver_self _)
    (fun v _ ↦ AbsoluteValue.liesOver_self _) (frameSystem_isNormalized hδ0 hδ)
    (X₀ := frameX0 δ) (le_max_left _ _)
  simp only [finrank_self, mul_one] at h𝒯 hint
  set X₀ := frameX0 δ with hX₀
  set m := subspaceChainLength 1 3 (2 * systemEps 1 δ) (systemAbsBound 1 2) with hm
  have hε2 : 0 < 2 * systemEps 1 δ := by rw [systemEps]; positivity
  have hA0 : (0 : ℝ) ≤ systemAbsBound 1 2 := by rw [systemAbsBound]; positivity
  have hσ0 := frameRoth.ratio_pos (n := 1) (s := 3) hε2 hA0
  have hσ1 := frameRoth.ratio_le_one (n := 1) (s := 3) hε2 hA0
  set ρ := 4 * (frameRoth.ratio 1 3 (2 * systemEps 1 δ) (systemAbsBound 1 2))⁻¹ with hρ
  have hρ1 : 1 ≤ ρ := by
    have : 1 ≤ (frameRoth.ratio 1 3 (2 * systemEps 1 δ) (systemAbsBound 1 2))⁻¹ :=
      (one_le_inv₀ hσ0).2 hσ1
    linarith
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
    have e : ρ * (1 + 1 / 100000) =
        4 * (frameRoth.ratio 1 3 (2 * systemEps 1 δ) (systemAbsBound 1 2))⁻¹ *
          (1 + 1 / 100000) := rfl
    rw [lineCountRho, ← hX₀, ← e, ← hm, ← hper]
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

/-! ### The constant at `δ = 13/50` -/

theorem frameX0_le : frameX0 (13 / 50) ≤
    2 ^ 84 * ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) := by
  refine max_le frame_threshold_le ?_
  have : (1 : ℝ) ≤ ((2 : ℝ) ^ 34) ^ (subspaceChainLength 1 3 (13 / 100) 6 + 1) :=
    one_le_pow₀ (by norm_num)
  nlinarith

/-- **`lineCountRho (13/50) ≤ 1.05·10⁹`**: `m ≤ 4.92·10⁶` intervals of at most `111.3` lines
each (`5.48·10⁸`), and `log X₀ ≤ (84 + 34(m + 1)) log 2` below the threshold (`4.99·10⁸`). -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem lineCountRho_le : lineCountRho (13 / 50) ≤ 1050000000 := by
  have hr : frameRoth.toRothParams.ratio = evertseRatio := rfl
  have hX := frameX0_le
  have hX2 : (200000 : ℝ) ≤ frameX0 (13 / 50) := le_max_right _ _
  have hρ := log_rho_ge
  have hl2 := Real.log_two_lt_d9
  have hl3 := one_lt_log_three
  rw [lineCountRho, frame_eps, frame_absBound, hr, evertseRatio, frame_eta]
  have hm := frame_chainLength_le
  generalize subspaceChainLength 1 3 (13 / 100) 6 = m at hm hX ⊢
  have hmR : (m : ℝ) ≤ 4920000 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have harg : 4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹ ≤ 2 ^ 37 := by
    rw [inv_div, mul_div_assoc', div_le_iff₀ (by norm_num)]
    nlinarith
  have harg1 : 1 ≤ 4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹ := by
    rw [inv_div, mul_div_assoc', le_div_iff₀ (by norm_num)]
    nlinarith
  -- one interval
  have hlog : Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹ * (1 + 1 / 100000)) ≤
      37 * 0.6931471808 + 1 / 100000 := by
    rw [Real.log_mul (by positivity) (by norm_num)]
    have h1 : Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹) ≤ 37 * 0.6931471808 :=
      calc _ ≤ Real.log (2 ^ 37) := Real.log_le_log (by linarith) harg
        _ = 37 * Real.log 2 := by rw [Real.log_pow]; norm_num
        _ ≤ 37 * 0.6931471808 := by linarith
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 100000 by norm_num)
    linarith
  have hlog0 : 0 ≤ Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹ * (1 + 1 / 100000)) :=
    Real.log_nonneg (by nlinarith)
  have hq := div_le_div₀ (by norm_num) hlog (by norm_num) hρ
  have hq0 := div_nonneg hlog0 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6309 / 5000))
  have hint : (m : ℝ) * (1 + Real.log (4 * (13 / 22400 / (4 * ((m : ℝ) + 1)))⁻¹ *
      (1 + 1 / 100000)) / Real.log (6309 / 5000)) ≤
        4920000 * (1 + (37 * 0.6931471808 + 1 / 100000) / 0.23253) :=
    mul_le_mul hmR (by linarith) (by linarith) (by norm_num)
  -- below the threshold
  have hX0 : 0 < frameX0 (13 / 50) := by linarith
  have hc1 : 1 ≤ Real.log 3 * 100001 := by nlinarith
  have hmid : Real.log (frameX0 (13 / 50) / (Real.log 3 * 100001)) ≤
      (84 + 34 * ((m : ℝ) + 1)) * 0.6931471808 := by
    rw [Real.log_div hX0.ne' (by positivity)]
    have hc := Real.log_nonneg hc1
    have hXl : Real.log (frameX0 (13 / 50)) ≤ (84 + 34 * ((m : ℝ) + 1)) * Real.log 2 := by
      calc _ ≤ Real.log (2 ^ 84 * ((2 : ℝ) ^ 34) ^ (m + 1)) := Real.log_le_log hX0 hX
        _ = _ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
            Real.log_pow]
          push_cast; ring
    have : (84 + 34 * ((m : ℝ) + 1)) * Real.log 2 ≤ (84 + 34 * ((m : ℝ) + 1)) * 0.6931471808 :=
      mul_le_mul_of_nonneg_left hl2.le (by positivity)
    linarith
  have hmq := div_le_div₀ (by positivity) hmid (by norm_num) hρ
  have hmq' : (84 + 34 * ((m : ℝ) + 1)) * 0.6931471808 / 0.23253 ≤
      (84 + 34 * (4920000 + 1)) * 0.6931471808 / 0.23253 := by
    gcongr
  linarith

/-- **The exceptions `n ≥ 20` lie on at most `1 050 000 000` lines**, no cited axiom: the
interval result of the Subspace Theorem, counted with the elementary gap `ρ₀`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_rho_num :
    ∃ R : Finset ℚ, R.card ≤ 1050000000 ∧
      ∀ n : ℕ, 20 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_rho (δ := 13 / 50) (by norm_num)
    thirteen_fiftieths_le
  refine ⟨R, ?_, hR⟩
  have := hcard.trans lineCountRho_le
  exact_mod_cast this

/-- **Theorem A″.** The exceptions `‖(3/2)ⁿ‖ < (3/4)ⁿ` with `n ≥ 10` lie on at most
`1 050 000 000` lines through the origin; `[10, 20)` holds no exception by the kernel census. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_ten_rho :
    ∃ R : Finset ℚ, R.card ≤ 1050000000 ∧
      ∀ n : ℕ, 10 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_rho_num
  refine ⟨R, hcard, fun n hn hnf ↦ ?_⟩
  rcases lt_or_ge n 20 with h | h
  · rcases (failures_up_to_256 n (by omega) (by omega)).1 hnf with h' | h' | h' | h' | h' <;>
      omega
  · exact hR n h hnf

end BB13
