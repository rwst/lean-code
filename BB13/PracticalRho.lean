/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.TheoremsST
import BB13.Census

/-!
# The one-parameter practical bound (item P3 of plan-beyond-BB13)

`BB13.practical_bound_min'` bounds `F(N) = #{n ≤ N : ‖(3/2)ⁿ‖ < (3/4)ⁿ}` by a minimum of two arms
with two height parameters: the relation-height `H` (failures per line above `10⁵`) for the
Diophantine arm, and the threshold-height `H_thr` (failures per tower base) for the elementary
arm `H_thr · #towers(N)`, `#towers(N) ≤ 12 + log_{6/5} N`.

The elementary gap between lines (`BB13.rho_gap`) makes the second parameter unnecessary. The
least exceptions of distinct lines above `10⁵` form a `ρ₀`-lacunary set, `ρ₀ = 1.2618`, so the
lines meeting `[1, N]` number at most `4 + 1 + ⌊log(N/100001)/log ρ₀⌋` (`linesUpTo_ncard_le`):
the census contributes the four lines of `{1}, {2, 3}, {4}, {7}`, and `1/log ρ₀ ≤ 4.3005`. Hence

`F(N) ≤ 5 + H · min(1.05·10⁹, 1 + ⌊4.3005 ln(N/100001)⌋)`   (`practical_bound_rho`),

with the single parameter `H` of Theorems B and C.

Nothing is lost against the two-parameter form. Linked exceptions share a line
(`BB13.sameTower_of_linkable`), so the lines meeting `[1, N]` are at most as many as the tower
bases (`linesUpTo_ncard_le_towerBases`). Conversely, above `7` the two tower notions coincide:
a line fibre is a run of consecutive integers (`mem_lineFibre_of_le`, from
`BB13.mem_lineFibre_add_iff`), consecutive exceptions `n, n + 1` are linked for `n ≥ 7`
(`linkable_succ`), so a line fibre with least member `≥ 7` is one chain of linked exceptions
(`lineFibre_chain`), and the tower bases `b ≥ 8` are exactly the least exceptions of their lines
(`isTowerBase_iff_least`).

## Main results

* `BB13.highLines_ncard_le_num`: the exceptions in `[100001, N]` meet at most
  `1 + ⌊4.3005 ln(N/100001)⌋` lines.
* `BB13.linesUpTo_ncard_le_num`: the exceptions in `[1, N]` meet at most
  `5 + ⌊4.3005 ln(N/100001)⌋` lines.
* `BB13.practical_bound_rho`: the one-parameter practical bound.
* `BB13.isTowerBase_iff_least`, `BB13.lineFibre_chain`, `BB13.linesUpTo_ncard_le_towerBases`:
  the two tower notions above `7`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 — Prob. 10.13.
* `plans/plan-beyond-BB13.html`, §4.2, item P3.
-/

namespace BB13

open Finset

/-! ### Lacunary sets in a closed range -/

/-- `log ρ₀ ≥ 0.232539`: three terms of the series of `2 artanh(1309/11309)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem log_rho_ge' : (0.232539 : ℝ) ≤ Real.log (6309 / 5000) := by
  have h0 := Real.sum_range_le_log_one_add_inv (a := 5000 / 1309) (by norm_num) 3
  have e : (1 : ℝ) + (5000 / 1309)⁻¹ = 6309 / 5000 := by norm_num
  rw [e] at h0
  norm_num [Finset.sum_range_succ] at h0
  linarith

/-- `card_le_of_gap` for a closed range `[A, B]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem card_le_of_gap_le {ρ A B : ℝ} (hρ : 1 < ρ) (hA : 0 < A) (hAB : A ≤ B) (s : Finset ℕ)
    (hgap : ∀ a ∈ s, ∀ b ∈ s, a < b → ρ * a ≤ b) (hAs : ∀ a ∈ s, A ≤ a)
    (hBs : ∀ a ∈ s, (a : ℝ) ≤ B) :
    (#s : ℝ) ≤ 1 + Real.log (B / A) / Real.log ρ := by
  have hlρ : 0 < Real.log ρ := Real.log_pos hρ
  have hBA : 0 ≤ Real.log (B / A) / Real.log ρ :=
    div_nonneg (Real.log_nonneg ((one_le_div hA).2 hAB)) hlρ.le
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [card_empty, Nat.cast_zero]; linarith
  obtain ⟨v, hv, hvA⟩ := Real.exists_mem_pow_mul_le_of_lacunary hρ.le
    (s.image (Nat.cast : ℕ → ℝ))
    (by
      simp only [mem_image]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      exact hgap a ha b hb (by exact_mod_cast hab))
    (by simp only [mem_image]; rintro _ ⟨a, ha, rfl⟩; exact hAs a ha) (hs.image _)
  rw [card_image_of_injective _ Nat.cast_injective] at hvA
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
  have hbA := hvA
  have hpow : ρ ^ (#s - 1) ≤ B / A := by
    rw [le_div_iff₀ hA]; exact hbA.trans (hBs b hb)
  have hlog : ((#s - 1 : ℕ) : ℝ) * Real.log ρ ≤ Real.log (B / A) := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hpow
  have hc : (#s : ℝ) = ((#s - 1 : ℕ) : ℝ) + 1 := by
    have := hs.card_pos
    rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  have : ((#s - 1 : ℕ) : ℝ) ≤ Real.log (B / A) / Real.log ρ := by
    rw [le_div_iff₀ hlρ]; exact hlog
  linarith

/-- `card_image_linePoint_le` for a closed range `[A, B]`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem card_image_linePoint_le_of_le {A B : ℝ} (hA : 100001 ≤ A) (hAB : A ≤ B) (F : Finset ℕ)
    (hF : ∀ n ∈ F, IsFailure 3 2 (3 / 4) n) (hAF : ∀ n ∈ F, A ≤ n) (hBF : ∀ n ∈ F, (n : ℝ) ≤ B) :
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
    refine card_le_of_gap_le (by norm_num) (by linarith) hAB S (fun a ha b hb hab ↦ ?_)
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

/-! ### The lines meeting `[1, N]` -/

/-- The exceptions in `[100001, N]`. -/
def failuresHighUpTo (N : ℕ) : Set ℕ := {n | 100001 ≤ n ∧ n ≤ N ∧ IsFailure 3 2 (3 / 4) n}

/-- The lines (slopes) of the exceptions in `[100001, N]`. -/
def highLines (N : ℕ) : Set ℚ := linePoint '' failuresHighUpTo N

/-- The lines (slopes) of the exceptions in `[1, N]`. -/
def linesUpTo (N : ℕ) : Set ℚ := linePoint '' failuresUpTo N

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem failuresHighUpTo_finite (N : ℕ) : (failuresHighUpTo N).Finite :=
  (Set.finite_Icc 100001 N).subset fun _ ⟨h1, hN, _⟩ ↦ Set.mem_Icc.mpr ⟨h1, hN⟩

/-- **The exceptions in `[100001, N]` meet at most `1 + ⌊log(N/100001)/log ρ₀⌋` lines.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem highLines_ncard_le (N : ℕ) :
    (highLines N).ncard ≤ 1 + ⌊Real.log (N / 100001) / Real.log (6309 / 5000)⌋₊ := by
  classical
  rcases lt_or_ge N 100001 with hN | hN
  · have : failuresHighUpTo N = ∅ := by
      ext n; simp only [failuresHighUpTo, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    simp [highLines, this]
  have hfin := failuresHighUpTo_finite N
  have hF : (highLines N).ncard = #(hfin.toFinset.image linePoint) := by
    rw [← Set.ncard_coe_finset, coe_image, hfin.coe_toFinset]; rfl
  have hNR : (100001 : ℝ) ≤ N := by exact_mod_cast hN
  have h := card_image_linePoint_le_of_le (le_refl _) hNR hfin.toFinset
    (fun n hn ↦ ((Set.Finite.mem_toFinset _).1 hn).2.2)
    (fun n hn ↦ by exact_mod_cast ((Set.Finite.mem_toFinset _).1 hn).1)
    (fun n hn ↦ by exact_mod_cast ((Set.Finite.mem_toFinset _).1 hn).2.1)
  rw [hF]
  have hk : #(hfin.toFinset.image linePoint) - 1 ≤
      ⌊Real.log (N / 100001) / Real.log (6309 / 5000)⌋₊ := by
    apply Nat.le_floor
    rcases Nat.eq_zero_or_pos #(hfin.toFinset.image linePoint) with h0 | h0
    · rw [h0]; simp only [Nat.zero_sub, Nat.cast_zero]
      exact div_nonneg (Real.log_nonneg ((one_le_div (by norm_num)).2 hNR))
        (Real.log_nonneg (by norm_num))
    · rw [Nat.cast_sub h0, Nat.cast_one]; linarith
  omega

/-- `highLines_ncard_le` with `1/log ρ₀ ≤ 4.3005`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem highLines_ncard_le_num (N : ℕ) :
    (highLines N).ncard ≤ 1 + ⌊4.3005 * Real.log (N / 100001)⌋₊ := by
  refine (highLines_ncard_le N).trans (Nat.add_le_add_left ?_ 1)
  have hρ : 0 < Real.log (6309 / 5000) := Real.log_pos (by norm_num)
  rcases le_or_gt 0 (Real.log (N / 100001)) with hx | hx
  · refine Nat.floor_le_floor ?_
    have := log_rho_ge'
    rw [div_le_iff₀ hρ]
    nlinarith
  · rw [Nat.floor_of_nonpos (div_neg_of_neg_of_pos hx hρ).le]
    exact Nat.zero_le _

/-- **At most `1.05·10⁹` lines** meet `[100001, N]`, for every `N` (Theorem A″). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem highLines_ncard_le_NA (N : ℕ) : (highLines N).ncard ≤ 1050000000 := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ten_rho
  refine (Set.ncard_le_ncard ?_ R.finite_toSet).trans (by rw [Set.ncard_coe_finset]; exact hcard)
  rintro _ ⟨n, ⟨h1, -, hf⟩, rfl⟩
  exact hR n (by omega) hf

/-- The census lines: the exceptions in `[1, 10⁵]` lie on the four lines of `1, 2, 4, 7`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linesUpTo_census_subset (N : ℕ) :
    linePoint '' {n | n ∈ failuresUpTo N ∧ n ≤ 100000} ⊆
      ↑({linePoint 1, linePoint 2, linePoint 4, linePoint 7} : Finset ℚ) := by
  rintro _ ⟨n, ⟨⟨h1, -, hf⟩, hn⟩, rfl⟩
  have hn' : n ∈ failuresUpTo 100000 := ⟨h1, hn, hf⟩
  rw [failuresUpTo_100000_eq] at hn'
  have h23 : linePoint 3 = linePoint 2 := sameTower_two_three.symm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn'
  rcases hn' with rfl | rfl | rfl | rfl | rfl <;> simp [h23]

/-- **The exceptions in `[1, N]` meet at most `4 + #(lines in [100001, N])` lines.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linesUpTo_ncard_le_highLines (N : ℕ) :
    (linesUpTo N).ncard ≤ 4 + (highLines N).ncard := by
  classical
  have hsub : linesUpTo N ⊆ ↑({linePoint 1, linePoint 2, linePoint 4, linePoint 7} : Finset ℚ) ∪
      highLines N := by
    rintro _ ⟨n, hn, rfl⟩
    rcases le_or_gt n 100000 with h | h
    · exact Or.inl (linesUpTo_census_subset N ⟨n, ⟨hn, h⟩, rfl⟩)
    · exact Or.inr ⟨n, ⟨h, hn.2.1, hn.2.2⟩, rfl⟩
  have hfin : (highLines N).Finite := (failuresHighUpTo_finite N).image _
  calc (linesUpTo N).ncard
      ≤ (↑({linePoint 1, linePoint 2, linePoint 4, linePoint 7} : Finset ℚ) ∪
          highLines N).ncard := Set.ncard_le_ncard hsub ((finite_toSet _).union hfin)
    _ ≤ (↑({linePoint 1, linePoint 2, linePoint 4, linePoint 7} : Finset ℚ) : Set ℚ).ncard +
          (highLines N).ncard := Set.ncard_union_le _ _
    _ ≤ 4 + (highLines N).ncard := by
        rw [Set.ncard_coe_finset]
        exact Nat.add_le_add_right (card_le_four) _

/-- **Lines in `[1, N]`: at most `5 + ⌊4.3005 ln(N/100001)⌋`.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linesUpTo_ncard_le_num (N : ℕ) :
    (linesUpTo N).ncard ≤ 5 + ⌊4.3005 * Real.log (N / 100001)⌋₊ := by
  have := highLines_ncard_le_num N
  have := linesUpTo_ncard_le_highLines N
  omega

/-! ### The one-parameter practical bound -/

/-- **`F(N) ≤ 5 + H · #(lines in [100001, N])`**, for `H` bounding the fibres of the slope map
above `10⁵`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem failuresUpTo_ncard_le_highLines (N H : ℕ) (hfib : ∀ r : ℚ, (highFibre' r).ncard ≤ H) :
    (failuresUpTo N).ncard ≤ 5 + H * (highLines N).ncard := by
  have hhigh : (failuresHighUpTo N).ncard ≤ H * (highLines N).ncard := by
    refine Set.ncard_le_mul_ncard_image (failuresHighUpTo_finite N) linePoint H fun r ↦ ?_
    refine (Set.ncard_le_ncard ?_ (lineFibre_finite r |>.subset
      (highFibre'_subset_lineFibre r))).trans (hfib r)
    rintro n ⟨⟨h1, -, hf⟩, rfl⟩
    exact ⟨h1, hf, rfl⟩
  have hsub : failuresUpTo N ⊆ failuresUpTo 100000 ∪ failuresHighUpTo N := by
    rintro n ⟨h1, hN, hf⟩
    rcases le_or_gt n 100000 with h | h
    · exact Or.inl ⟨h1, h, hf⟩
    · exact Or.inr ⟨h, hN, hf⟩
  calc (failuresUpTo N).ncard
      ≤ (failuresUpTo 100000 ∪ failuresHighUpTo N).ncard :=
        Set.ncard_le_ncard hsub ((failuresUpTo_finite _).union (failuresHighUpTo_finite N))
    _ ≤ (failuresUpTo 100000).ncard + (failuresHighUpTo N).ncard := Set.ncard_union_le _ _
    _ ≤ 5 + H * (highLines N).ncard := by rw [failuresUpTo_100000_ncard]; omega

/-- **The one-parameter practical bound**:
`F(N) ≤ 5 + H · min(1.05·10⁹, 1 + ⌊4.3005 ln(N/100001)⌋)`, for every `N`, with the single
height parameter `H` of Theorem B (the fibres of the slope map above `10⁵`). Std3. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem practical_bound_rho (N H : ℕ) (hfib : ∀ r : ℚ, (highFibre' r).ncard ≤ H) :
    (failuresUpTo N).ncard ≤
      5 + H * min 1050000000 (1 + ⌊4.3005 * Real.log (N / 100001)⌋₊) :=
  (failuresUpTo_ncard_le_highLines N H hfib).trans <| Nat.add_le_add_left
    (Nat.mul_le_mul_left H (le_min (highLines_ncard_le_NA N) (highLines_ncard_le_num N))) 5

/-! ### Lines and towers above `7` -/

/-- **A line fibre is a run of consecutive integers**: between two members `a ≤ b`, `a ≥ 3`, of
one line every `n` is an exception on that line. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem mem_lineFibre_of_le {a b n : ℕ} (ha : 3 ≤ a) (han : a ≤ n) (hnb : n ≤ b)
    (hb : b ∈ lineFibre (linePoint a)) : n ∈ lineFibre (linePoint a) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (han.trans hnb)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le han
  obtain ⟨hv, hD⟩ := (mem_lineFibre_add_iff ha e).1 hb
  refine (mem_lineFibre_add_iff ha d).2 ⟨by omega, lt_of_le_of_lt ?_ hD⟩
  have h1 : (2 : ℤ) ^ d ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (0 : ℤ) ≤ |resid 3 2 a| * 2 ^ a := by positivity
  calc 2 ^ d * |resid 3 2 a| * 2 ^ a = 2 ^ d * (|resid 3 2 a| * 2 ^ a) := by ring
    _ ≤ 2 ^ e * (|resid 3 2 a| * 2 ^ a) := mul_le_mul_of_nonneg_right h1 h2
    _ = 2 ^ e * |resid 3 2 a| * 2 ^ a := by ring

/-- **Consecutive indices `n, n + 1` are linked for `n ≥ 7`**: `6 (3/4)ⁿ ≤ 6 (3/4)⁷ < 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linkable_succ {n : ℕ} (hn : 7 ≤ n) : Linkable 3 (3 / 4) n (n + 1) := by
  rw [Linkable, show n + 1 - n = 1 by omega, pow_one]
  have : ((3 : ℝ) / 4) ^ n ≤ (3 / 4) ^ 7 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  push_cast
  nlinarith

/-- **A line fibre above `7` is one chain of linked exceptions**: if `7 ≤ a < b` lie on one
line, every `n ∈ [a, b)` is an exception on that line, linked to `n + 1`. So the relation-tower
of a line whose least member is at least `7` is a single threshold-tower. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem lineFibre_chain {a b n : ℕ} (ha : 7 ≤ a) (han : a ≤ n) (hnb : n < b)
    (hb : b ∈ lineFibre (linePoint a)) :
    n ∈ lineFibre (linePoint a) ∧ n + 1 ∈ lineFibre (linePoint a) ∧
      Linkable 3 (3 / 4) n (n + 1) :=
  ⟨mem_lineFibre_of_le (by omega) han hnb.le hb, mem_lineFibre_of_le (by omega) (by omega) hnb hb,
    linkable_succ (by omega)⟩

/-- Index `0` is linked to nothing: `2 · 3ᵇ > 1`. -/
theorem not_linkable_zero (b : ℕ) : ¬ Linkable 3 (3 / 4) 0 b := by
  rw [Linkable]
  simp only [pow_zero, mul_one, Nat.sub_zero]
  push_cast
  have : (1 : ℝ) ≤ 3 ^ b := one_le_pow₀ (by norm_num)
  linarith

/-- **Least exceptions of lines are tower bases**: an exception `b` with no smaller exception
`a ≥ 1` on its line is linked to no smaller exception (`sameTower_of_linkable`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem isTowerBase_of_least {b : ℕ} (hb : IsFailure 3 2 (3 / 4) b)
    (hmin : ∀ a, 1 ≤ a → a < b → IsFailure 3 2 (3 / 4) a → ¬ SameTower a b) :
    IsTowerBase 3 2 (3 / 4) b := by
  refine ⟨hb, fun a hab ha hl ↦ ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · exact not_linkable_zero b hl
  · exact hmin a ha1 hab ha (sameTower_of_linkable hab ha hb hl)

/-- **Above `7`, the tower bases are the least exceptions of the lines**: for `b ≥ 8`, `b` is a
tower base iff it is an exception with no smaller exception `a ≥ 1` on its line. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem isTowerBase_iff_least {b : ℕ} (hb8 : 8 ≤ b) :
    IsTowerBase 3 2 (3 / 4) b ↔ IsFailure 3 2 (3 / 4) b ∧
      ∀ a, 1 ≤ a → a < b → IsFailure 3 2 (3 / 4) a → ¬ SameTower a b := by
  refine ⟨fun h ↦ ⟨h.1, fun a ha1 hab ha hst ↦ ?_⟩, fun h ↦ isTowerBase_of_least h.1 h.2⟩
  have h2a := sameTower_lt_two_mul ha1 hab h.1 hst
  have hbmem : b ∈ lineFibre (linePoint a) := ⟨by omega, h.1, hst.symm⟩
  have hpred := mem_lineFibre_of_le (n := b - 1) (by omega) (by omega) (by omega) hbmem
  have hlink := linkable_succ (n := b - 1) (by omega)
  rw [show b - 1 + 1 = b by omega] at hlink
  exact h.2 (b - 1) (by omega) hpred.2.1 hlink

/-- **The lines meeting `[1, N]` are at most as many as the tower bases in `[1, N]`**: the least
exception of each line is a tower base (`isTowerBase_of_least`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linesUpTo_ncard_le_towerBases (N : ℕ) :
    (linesUpTo N).ncard ≤ (towerBasesUpTo N).ncard := by
  classical
  have hsub : linesUpTo N ⊆ linePoint '' towerBasesUpTo N := by
    rintro _ ⟨n, ⟨h1, hN, hf⟩, rfl⟩
    have hex : ∃ m, 1 ≤ m ∧ IsFailure 3 2 (3 / 4) m ∧ SameTower m n := ⟨n, h1, hf, rfl⟩
    obtain ⟨hm1, hmf, hmn⟩ := Nat.find_spec hex
    have hle : Nat.find hex ≤ n := Nat.find_min' hex ⟨h1, hf, rfl⟩
    refine ⟨Nat.find hex, ⟨hm1, hle.trans hN, isTowerBase_of_least hmf ?_⟩, hmn⟩
    intro a ha1 hlt ha hst
    exact Nat.find_min hex hlt ⟨ha1, ha, hst.trans hmn⟩
  exact (Set.ncard_le_ncard hsub ((towerBasesUpTo_finite N).image _)).trans
    (Set.ncard_image_le (towerBasesUpTo_finite N))

end BB13
