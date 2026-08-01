/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LineCover

/-!
# Relation-towers: what one line can carry (W3 of plan2-BB13)

The line cover of `BB13/LineCover.lean` bounds the number of *lines*.  To count *failures* one
needs to know how many failures a single line can carry.  This file fixes the vocabulary and
proves what is elementary about the question.

## Two towers, not one

Two notions were conflated in the first version of this development, and the distinction matters:

* a **relation-tower** — a fibre of `linePoint`, i.e. a maximal set of failures whose frame points
  are collinear.  Equivalently (`collinear_scaling`) a maximal scaling family
  `mₐ = 2ᵈμ`, `m_b = 3ᵈμ`;
* a **threshold-tower** — a chain of failures linked by `BB13.Linkable`
  (`2·cᵃ·3ᵇ⁻ᵃ ≤ 1`), the §3 gap-principle notion counted by `BB13.TowerCount`.

`Linkable` is *sufficient* for collinearity, never necessary.  The certified failures `n = 2` and
`n = 3` show the gap is real: `m₂ = 2`, `m₃ = 3`, so their frame points are `(8, 9)` and
`(24, 27) = 3·(8, 9)` — one line, `linePoint 2 = linePoint 3 = 8/9` — while
`2·(3/4)²·3 = 27/8 > 1`, so they are *not* `Linkable`.  The observed relation-tower height in the
certified range is therefore **2**, not 1, and the census `{1}, {2, 3}, {4}, {7}` of
`E ∩ [1, 256]` has four relation-towers against five threshold-towers.

## Confinement

Collinearity is expensive for the upper member: on a line the residues scale, `k_b = 3ᵇ⁻ᵃkₐ`
(`sameTower_resid`), while `|kₐ| ≥ 1` (`resid_ne_zero`, `3ᵃ` odd) and the failure at `b` demands
`|k_b| < (3/2)ᵇ`.  Hence

* `sameTower_gap` — `2ᵇ⁻ᵃ < (3/2)ᵃ`, i.e. `(b − a)·log 2 < a·log(3/2)` (`sameTower_span_lt`):
  a companion sits within `0.58497·a` of its base, so a relation-tower over `a` is confined to
  `[a, a·log₂3)`;
* `sameTower_lt_two_mul` — the crude corollary `b < 2a`, enough for
* `sameTower_fibre_finite` — **every line carries finitely many failures**, with no Diophantine
  input at all, and `sameTower_card_le_of_min` — at most `a` of them over a least element `a`.

What is *not* proved here is a bound uniform in the line: that is the open per-line problem
([BE08] Rem. 7.4, [EF13] p. 6), and it is the hypothesis of the conditional counts in
`BB13/FailureCount.lean`.  A remark on the alternative route: bounding the multiplicity on a line
through `v₂(mₐ)` by a linear form in two logarithms (Baker/Matveev, or Yu `p`-adically) gives a
height `O(b log b)` — *worse* than the elementary `0.585·b + 1` above, so that route is dominated
and is not pursued.

## References

* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008) — Cor. 5.2, and Rem. 7.4 (the per-line
  problem, left open there).
* [EF13] Evertse–Ferretti — counting inside the exceptional subspaces.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* `plans/plan2-BB13.html` (W3).
-/

namespace BB13

open scoped Real

/-! ### The dictionary: slopes versus collinearity -/

/-- Two failures have the same `linePoint` exactly when their frame points are collinear — the
bridge between the Bugeaud–Evertse line cover and the elementary §3 analysis of
`BB13/Subspace.lean`.  (Note `failPoint` lists the coordinates in the order `(3ⁿ, mₙ2ⁿ)`, the
transpose of the `(x, y)` of the approximation system.) -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linePoint_eq_iff_collinear (a b : ℕ) :
    linePoint a = linePoint b ↔ CollinearPts (failPoint 3 2 a) (failPoint 3 2 b) := by
  have hya : ((frameY a : ℤ) : ℚ) ≠ 0 := by rw [frameY]; push_cast; positivity
  have hyb : ((frameY b : ℤ) : ℚ) ≠ 0 := by rw [frameY]; push_cast; positivity
  rw [linePoint, linePoint, div_eq_div_iff hya hyb, ← Int.cast_mul, ← Int.cast_mul, Int.cast_inj]
  simp only [CollinearPts, failPoint, frameX, frameY]
  push_cast
  constructor <;> intro h <;> linarith

/-- **Relation-tower membership**: `a` and `b` lie on one line through the origin. -/
def SameTower (a b : ℕ) : Prop := linePoint a = linePoint b

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_refl (a : ℕ) : SameTower a a := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_symm {a b : ℕ} (h : SameTower a b) : SameTower b a := h.symm

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_trans {a b c : ℕ} (h₁ : SameTower a b) (h₂ : SameTower b c) : SameTower a c :=
  h₁.trans h₂

/-! ### The scaling relation on a line -/

/-- **Residues scale along a line**: `k_b = 3ᵇ⁻ᵃ·kₐ` (`collinear_resid`, in slope vocabulary). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_resid {a b : ℕ} (hab : a ≤ b) (h : SameTower a b) :
    resid 3 2 b = (3 : ℤ) ^ (b - a) * resid 3 2 a := by
  have := collinear_resid 3 2 a b (by norm_num) (by norm_num) hab
    ((linePoint_eq_iff_collinear a b).mp h)
  simpa using this

/-- **`2ᵇ⁻ᵃ ∣ mₐ`**: the base numerator of a relation-tower of span `d` is divisible by `2ᵈ`
(`collinear_scaling`, in slope vocabulary) — the `2`-adic surplus that fuels the stratified
counts of W8. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_dvd {a b : ℕ} (hab : a ≤ b) (h : SameTower a b) :
    (2 : ℤ) ^ (b - a) ∣ Mnum 3 2 a := by
  obtain ⟨μ, hμ, -⟩ := collinear_scaling 3 2 a b (by norm_num) (by norm_num) (by decide) hab
    ((linePoint_eq_iff_collinear a b).mp h)
  exact ⟨μ, by simpa using hμ⟩

/-! ### Confinement -/

/-- The residue of a genuine index never vanishes: `kₐ = 3ᵃ − mₐ2ᵃ` is odd for `a ≥ 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem resid_ne_zero {a : ℕ} (ha : 1 ≤ a) : resid 3 2 a ≠ 0 := by
  intro h
  rw [resid, sub_eq_zero] at h
  have h2 : (2 : ℤ) ∣ ((3 : ℕ) : ℤ) ^ a := by
    rw [h]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
  have := Int.prime_two.dvd_of_dvd_pow h2
  norm_num at this

/-- **The gap principle on a line**, in the form every smallness event can use.  If `a < b` lie on
one line, `a ≥ 1`, and the upper residue obeys `|k_b| < K·(3/2)ᵇ`, then `2ᵇ⁻ᵃ < K·(3/2)ᵃ`: the
residue `kₐ` is amplified by `3ᵇ⁻ᵃ` and must still fit under the bound, while `|kₐ| ≥ 1`.

`K = 1` is a failure of Problem 10.13 (`sameTower_gap`); `K = 4/3` is a Waring event
(`BB13.Waring`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_gap_of_bound {a b : ℕ} {K : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (hkb : |((resid 3 2 b : ℤ) : ℝ)| < K * (3 / 2 : ℝ) ^ b) (h : SameTower a b) :
    (2 : ℝ) ^ (b - a) < K * (3 / 2 : ℝ) ^ a := by
  set d := b - a with hd
  have hb : b = a + d := by omega
  have hk : resid 3 2 b = (3 : ℤ) ^ d * resid 3 2 a := sameTower_resid (le_of_lt hab) h
  have hone : (1 : ℝ) ≤ |((resid 3 2 a : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |resid 3 2 a| := Int.one_le_abs (resid_ne_zero ha)
    have := (Int.cast_le (R := ℝ)).mpr this
    rwa [Int.cast_abs, Int.cast_one] at this
  have hkR : |((resid 3 2 b : ℤ) : ℝ)| = (3 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| := by
    rw [hk]; push_cast; rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have h3d : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  have hstep : (3 : ℝ) ^ d < K * (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by
    have h1 : (3 : ℝ) ^ d ≤ (3 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| := by nlinarith
    have h2 : K * (3 / 2 : ℝ) ^ b = K * (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by
      rw [hb, pow_add]; ring
    rw [hkR] at hkb
    linarith [h2 ▸ hkb]
  have hsplit : (3 : ℝ) ^ d = (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ d := by
    rw [← mul_pow]; norm_num
  have h32d : (0 : ℝ) < (3 / 2 : ℝ) ^ d := by positivity
  rw [hsplit] at hstep
  exact lt_of_mul_lt_mul_left (by linarith [hstep]) (le_of_lt h32d)

/-- **The gap principle on a line** for genuine failures: `2ᵇ⁻ᵃ < (3/2)ᵃ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_gap {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hfb : IsFailure 3 2 (3 / 4) b) (h : SameTower a b) :
    (2 : ℝ) ^ (b - a) < (3 / 2 : ℝ) ^ a := by
  have := sameTower_gap_of_bound (K := 1) ha hab
    (by rw [one_mul]; exact abs_resid_lt_of_isFailure hfb) h
  linarith [this]

/-- **Confinement for a general smallness event**: with `|k_b| < K·(3/2)ᵇ` and `1 ≤ K ≤ 2`, a
companion satisfies `b ≤ 2a`.  (For `K = 4/3`, the Waring case.) -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_le_two_mul_of_bound {a b : ℕ} {K : ℝ} (ha : 1 ≤ a) (hab : a < b) (hK : K ≤ 2)
    (hkb : |((resid 3 2 b : ℤ) : ℝ)| < K * (3 / 2 : ℝ) ^ b) (h : SameTower a b) :
    b ≤ 2 * a := by
  have hgap := sameTower_gap_of_bound ha hab hkb h
  have h32 : (3 / 2 : ℝ) ^ a ≤ (2 : ℝ) ^ a := by
    apply pow_le_pow_left₀ (by norm_num) (by norm_num)
  have h2a : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hlt : (2 : ℝ) ^ (b - a) < (2 : ℝ) ^ (a + 1) := by
    calc (2 : ℝ) ^ (b - a) < K * (3 / 2 : ℝ) ^ a := hgap
      _ ≤ 2 * (2 : ℝ) ^ a := by nlinarith [pow_pos (show (0:ℝ) < 3/2 by norm_num) a]
      _ = (2 : ℝ) ^ (a + 1) := by rw [pow_succ]; ring
  have : b - a < a + 1 := by
    by_contra hcon
    exact absurd (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (not_lt.mp hcon)) (not_le.mpr hlt)
  omega

/-- **Confinement in exact form**: `(b − a)·log 2 < a·log(3/2)`, i.e. a companion of the base `a`
on the same line satisfies `b < a·log₂3 = 1.58496…·a`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_span_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hfb : IsFailure 3 2 (3 / 4) b) (h : SameTower a b) :
    ((b - a : ℕ) : ℝ) * Real.log 2 < (a : ℝ) * Real.log (3 / 2) := by
  have hgap := sameTower_gap ha hab hfb h
  have h1 := Real.log_lt_log (by positivity) hgap
  rwa [Real.log_pow, Real.log_pow] at h1

/-- **The crude corollary** `b < 2a`: a relation-tower over `a` lives inside `[a, 2a)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_lt_two_mul {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hfb : IsFailure 3 2 (3 / 4) b) (h : SameTower a b) :
    b < 2 * a := by
  have hgap := sameTower_gap ha hab hfb h
  have hlt : (3 / 2 : ℝ) ^ a < (2 : ℝ) ^ a := by
    apply pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (b - a) < (2 : ℝ) ^ a := lt_trans hgap hlt
  have : b - a < a := by
    by_contra hcon
    exact absurd (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (not_lt.mp hcon)) (not_le.mpr h2)
  omega

/-! ### Every line carries finitely many failures -/

/-- The failures on the line of slope `r`. -/
def lineFibre (r : ℚ) : Set ℕ := {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}

/-- **A single line carries only finitely many failures** — elementarily, with no Diophantine
input: any member `a` confines the whole fibre to `[0, 2a]` by `sameTower_lt_two_mul`.  This is
what makes the counts of `BB13/FailureCount.lean` independent of the Subspace axiom. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem lineFibre_finite (r : ℚ) : (lineFibre r).Finite := by
  rcases Set.eq_empty_or_nonempty (lineFibre r) with he | ⟨a, ha⟩
  · rw [he]; exact Set.finite_empty
  · apply Set.Finite.subset (Set.finite_Iic (2 * a))
    intro b hb
    rcases le_or_gt b a with hle | hlt
    · exact le_trans hle (by omega)
    · exact le_of_lt (sameTower_lt_two_mul ha.1 hlt hb.2.1 (ha.2.2.trans hb.2.2.symm))

/-- **The height of a relation-tower over its least element `a` is at most `a`** — the fibre sits
in `[a, 2a)`.  (The sharp confinement `sameTower_span_lt` gives the smaller `⌊0.58497·a⌋ + 1`.) -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_card_le_of_min {r : ℚ} {a : ℕ} (ha : a ∈ lineFibre r)
    (hmin : ∀ b ∈ lineFibre r, a ≤ b) : (lineFibre r).ncard ≤ a := by
  have ha1 : 1 ≤ a := ha.1
  have hsub : lineFibre r ⊆ ↑(Finset.Ico a (2 * a)) := by
    intro b hb
    rw [Finset.coe_Ico, Set.mem_Ico]
    refine ⟨hmin b hb, ?_⟩
    rcases eq_or_lt_of_le (hmin b hb) with rfl | hlt
    · omega
    · exact sameTower_lt_two_mul ha.1 hlt hb.2.1 (ha.2.2.trans hb.2.2.symm)
  calc (lineFibre r).ncard
      ≤ (↑(Finset.Ico a (2 * a)) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.Ico a (2 * a)).finite_toSet
    _ = (Finset.Ico a (2 * a)).card := Set.ncard_coe_finset _
    _ = a := by rw [Nat.card_Ico]; omega

end BB13
