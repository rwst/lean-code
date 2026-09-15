/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Cantor
import BB61.Factor
import ForMathlib.Analysis.Equidistribution.ModOne
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Lemma 3 and Proposition 4: the window `K`, and exact confinement

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Lemma 3 and Proposition 4, quadratic case.

`BB61/Splitting.lean` proved the pointwise identity `{ξ αⁿ} = {t_n - S_n}` and
`BB61/Factor.lean` packaged the two halves into the factor map `F`.  Proposition 4 is the
*set-level* consequence, and it is the statement every certificate route consumes: the whole
orbit of every `ξ ∈ C(α)`, at every time, lies in **one compact subset of the circle**,

`X(α) = (C(α) - K) mod 1`,   `K = { ∑_{m≥0} c_m δ_m : δ ∈ {0,1}^ℕ }`,

with **no error term** — the truncated past is a point of `K`, not an approximation to one
(`wVal_padWord`).  So if `X(α) ≠ 𝕋` then 10.61 holds at `α` in the strong form: no
`(ξ αⁿ)` with `ξ ∈ C(α)` is even *dense* mod one.

`continuous_piVal` and `isCompact_cantorSet` (M1 Lemma 1(iii)) live in `BB61/Cantor.lean`,
which this file imports for them.

## Lemma 3, the window

* `windowSet = Set.range wVal` is the note's `K`, and `isCompact_windowSet` says it is
  compact — no closure is needed, it is a continuous image of `{0,1}^ℕ`;
* `wMax`, `wMin` are the note's `P = ∑_{c_m>0} c_m` and `-Q = ∑_{c_m<0} c_m`;
  `windowSet_subset_Icc` is `K ⊆ [-Q, P]` and `wMax_mem_windowSet`, `wMin_mem_windowSet`
  say both endpoints are attained (by the greedy words `wPos`, `wNeg`);
* `tsum_cCoef` — `∑_{m≥0} c_m = -1`, whence `one_le_wMax_sub_wMin`: **`diam K ≥ 1 = d - 1`**,
  the note's lower bound at degree two.  (This is what makes the naive
  "`K` is smaller than the gap" argument fail at every degree `≥ 2`.)

## Proposition 4, exact confinement

The identification that makes the proposition short is that `X(α)` is nothing but the
**range of the factor map**:

* `confSet = Set.range fRaw` and `confSet_eq` — `range F̃ = C(α) - K`, because the two
  halves `ω ↦ (ω⁺, ω⁻)` of a two-sided word are *independent* (`joinW`);
* `confCircle = Set.range fMap` is `X(α)`, and `isCompact_confCircle` its compactness;
* `coe_mul_pow_mem_confCircle` — **Proposition 4**: `{ξ αⁿ} ∈ X(α)` for every `ξ ∈ C(α)`
  and every `n`, exactly.  It is `fMap_iterate_padZ` read as a membership;
* `exists_avoided_interval_of_ne_univ` — if `X(α) ≠ 𝕋` then some open interval
  `J ⊆ (0,1)` is missed by every orbit at every time.  `X(α)` is *closed*, so its
  complement is open, and 1-periodicity carries a witness into `(0,1)`;
* `not_denseModuloOne_of_confCircle_ne_univ`, `not_equidistributed_of_confCircle_ne_univ` —
  the strong form of 10.61 at `α`, from `X(α) ≠ 𝕋` alone.

`BB61/Covering.lean` is the *effective* companion: it never mentions `X(α)`, and certifies
`X(α) ≠ 𝕋` by a finite candidate count.  The note's Cor. 5 — the box-dimension ceiling
`dim_B X(α) ≤ log2/log α + log2/log(1/ρ)`, which is why Route A needs `α > 2^d` — is not
formalised: Mathlib has no box dimension.
-/

namespace BB61

open Set

/-! ## Joining the two halves of a two-sided word

The future and the past of `ω ∈ {0,1}^ℤ` are *independent*: every pair `(w, δ)` of
one-sided words is `(ω⁺, ω⁻)` for exactly one `ω`.  This is what turns the range of the
factor map into a difference set. -/

/-- The two-sided word with future `w` and past `δ`: `ω_k = w_{k-1}` for `k ≥ 1` and
`ω_{-m} = δ_m` for `m ≥ 0`. -/
def joinW (w δ : ℕ → Bool) : Shift := fun k => if 1 ≤ k then w (k - 1).toNat else δ (-k).toNat

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem futures_joinW (w δ : ℕ → Bool) : futures (joinW w δ) = w := by
  funext j
  have h1 : (1 : ℤ) ≤ (j : ℤ) + 1 := by omega
  simp [futures, joinW, h1]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pasts_joinW (w δ : ℕ → Bool) : pasts (joinW w δ) = δ := by
  funext m
  have h1 : ¬ (1 : ℤ) ≤ -(m : ℤ) := by omega
  simp [pasts, joinW, h1]

/-- Every two-sided word is matched on its central block `[-N, N]` by a *shifted zero-padded
one-sided* word: take `n = N+1` and read `ε` off `ω`.  So the orbits of `C(α)` are not a thin
part of the shift space — this is what makes the confinement set of Prop. 4 sharp. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_padZ_agree (ω : Shift) (N : ℕ) :
    ∃ (ε : ℕ → Bool) (n : ℕ), ∀ k : ℤ, |k| ≤ (N : ℤ) → shiftZ^[n] (padZ ε) k = ω k := by
  refine ⟨fun j => ω ((j : ℤ) + 1 - ((N : ℤ) + 1)), N + 1, fun k hk => ?_⟩
  have habs := abs_le.mp hk
  have hcast : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
  have h1 : (1 : ℤ) ≤ k + ((N + 1 : ℕ) : ℤ) := by rw [hcast]; omega
  rw [shiftZ_iterate]
  simp only [padZ, h1, ite_true]
  congr 1
  omega

namespace QuadSetup

variable (P : QuadSetup)

/-! ## M1 Lemma 3: the window `K` -/

/-- The window map is continuous on `{0,1}^ℕ` — the one-sided form of
`continuous_wVal_pasts`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_wVal : Continuous P.wVal := by
  have hβ := P.abs_beta_lt_one
  refine continuous_tsum (fun m => continuous_const.mul (continuous_dR m))
    ((summable_geometric_of_lt_one (abs_nonneg P.β) hβ).mul_left (1 + |P.β|)) fun m δ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |P.cCoef m| * |dR δ m| ≤ ((1 + |P.β|) * |P.β| ^ m) * 1 := by
        refine mul_le_mul (P.abs_cCoef_le m) ?_ (abs_nonneg _) (by positivity)
        rw [abs_of_nonneg (dR_nonneg _ _)]; exact dR_le_one _ _
  _ = (1 + |P.β|) * |P.β| ^ m := mul_one _

/-- **The window `K` of M1 Lemma 3**: the set of all values `∑_{m≥0} c_m δ_m`. -/
noncomputable def windowSet : Set ℝ := Set.range P.wVal

/-- **M1 Lemma 3, compactness.**  `K` is compact — a continuous image of the compact space
`{0,1}^ℕ`.  No closure is taken: the note's point is that `K` is already closed. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isCompact_windowSet : IsCompact P.windowSet := isCompact_range P.continuous_wVal

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_abs_cCoef : Summable fun m : ℕ => |P.cCoef m| := by
  have hβ := P.abs_beta_lt_one
  refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) P.abs_cCoef_le
    ((summable_geometric_of_lt_one (abs_nonneg P.β) hβ).mul_left (1 + |P.β|))

/-- The note's `P = ∑_{c_m>0} c_m`, the top of the window. -/
noncomputable def wMax : ℝ := ∑' m : ℕ, max (P.cCoef m) 0

/-- The note's `-Q = ∑_{c_m<0} c_m`, the bottom of the window. -/
noncomputable def wMin : ℝ := ∑' m : ℕ, min (P.cCoef m) 0

/-- The greedy word taking every positive coefficient and no negative one. -/
noncomputable def wPos : ℕ → Bool := fun m => if 0 < P.cCoef m then true else false

/-- The greedy word taking every negative coefficient and no positive one. -/
noncomputable def wNeg : ℕ → Bool := fun m => if P.cCoef m < 0 then true else false

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wVal_wPos : P.wVal P.wPos = P.wMax := by
  rw [wVal, wMax]
  refine tsum_congr fun m => ?_
  by_cases h : 0 < P.cCoef m
  · rw [max_eq_left h.le]; simp [wPos, dR, h]
  · rw [max_eq_right (not_lt.mp h)]; simp [wPos, dR, h]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wVal_wNeg : P.wVal P.wNeg = P.wMin := by
  rw [wVal, wMin]
  refine tsum_congr fun m => ?_
  by_cases h : P.cCoef m < 0
  · rw [min_eq_left h.le]; simp [wNeg, dR, h]
  · rw [min_eq_right (not_lt.mp h)]; simp [wNeg, dR, h]

/-- **M1 Lemma 3**: the top of the window is attained. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wMax_mem_windowSet : P.wMax ∈ P.windowSet := ⟨P.wPos, P.wVal_wPos⟩

/-- **M1 Lemma 3**: the bottom of the window is attained. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wMin_mem_windowSet : P.wMin ∈ P.windowSet := ⟨P.wNeg, P.wVal_wNeg⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_max_cCoef : Summable fun m : ℕ => max (P.cCoef m) 0 := by
  have h := P.summable_cCoef P.wPos
  refine h.congr fun m => ?_
  by_cases hm : 0 < P.cCoef m
  · rw [max_eq_left hm.le]; simp [wPos, dR, hm]
  · rw [max_eq_right (not_lt.mp hm)]; simp [wPos, dR, hm]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_min_cCoef : Summable fun m : ℕ => min (P.cCoef m) 0 := by
  have h := P.summable_cCoef P.wNeg
  refine h.congr fun m => ?_
  by_cases hm : P.cCoef m < 0
  · rw [min_eq_left hm.le]; simp [wNeg, dR, hm]
  · rw [min_eq_right (not_lt.mp hm)]; simp [wNeg, dR, hm]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cCoef_mul_dR_le (δ : ℕ → Bool) (m : ℕ) :
    P.cCoef m * dR δ m ≤ max (P.cCoef m) 0 := by
  rcases Bool.eq_false_or_eq_true (δ m) with h | h
  · simp [dR, h]
  · simp [dR, h]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem le_cCoef_mul_dR (δ : ℕ → Bool) (m : ℕ) :
    min (P.cCoef m) 0 ≤ P.cCoef m * dR δ m := by
  rcases Bool.eq_false_or_eq_true (δ m) with h | h
  · simp [dR, h]
  · simp [dR, h]

/-- **M1 Lemma 3**: `K ⊆ [-Q, P]`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem windowSet_subset_Icc : P.windowSet ⊆ Set.Icc P.wMin P.wMax := by
  rintro _ ⟨δ, rfl⟩
  refine ⟨?_, ?_⟩
  · exact P.summable_min_cCoef.tsum_le_tsum (P.le_cCoef_mul_dR δ) (P.summable_cCoef δ)
  · exact (P.summable_cCoef δ).tsum_le_tsum (P.cCoef_mul_dR_le δ) P.summable_max_cCoef

/-- `∑_{m≥0} c_m = -1`: the alternating window coefficients sum to `-(d-1)` at degree two.
The note's `∑ c_m = -(d-1)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_cCoef : ∑' m : ℕ, P.cCoef m = -1 := by
  have hβ := P.abs_beta_lt_one
  have hne : (1 : ℝ) - P.β ≠ 0 := by
    rcases abs_lt.mp hβ with ⟨_, h2⟩; linarith
  have hgeom : ∑' m : ℕ, P.β ^ m = (1 - P.β)⁻¹ :=
    tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])
  calc ∑' m : ℕ, P.cCoef m = ∑' m : ℕ, (P.β - 1) * P.β ^ m := by rfl
  _ = (P.β - 1) * ∑' m : ℕ, P.β ^ m := tsum_mul_left
  _ = (P.β - 1) * (1 - P.β)⁻¹ := by rw [hgeom]
  _ = -1 := by field_simp; ring

/-- **M1 Lemma 3, the diameter bound**: `diam K ≥ |∑ c_m| = 1 = d - 1`.  At degree two the
window is at least as wide as the unit interval, which is why no `K`-versus-gap comparison
can ever prove 10.61 — the note's remark that `diam K ≥ d-1 ≥ 1 > g`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_le_wMax_sub_wMin : 1 ≤ P.wMax - P.wMin := by
  have hsub : P.wMax - P.wMin = ∑' m : ℕ, |P.cCoef m| := by
    rw [wMax, wMin, ← P.summable_max_cCoef.tsum_sub P.summable_min_cCoef]
    refine tsum_congr fun m => ?_
    simpa using max_sub_min_eq_abs (P.cCoef m) 0
  have habs : |∑' m : ℕ, P.cCoef m| ≤ ∑' m : ℕ, |P.cCoef m| := by
    have h := norm_tsum_le_tsum_norm (f := fun m : ℕ => P.cCoef m)
      (by simpa [Real.norm_eq_abs] using P.summable_abs_cCoef)
    simpa [Real.norm_eq_abs] using h
  rw [hsub]
  calc (1 : ℝ) = |∑' m : ℕ, P.cCoef m| := by rw [P.tsum_cCoef]; norm_num
  _ ≤ ∑' m : ℕ, |P.cCoef m| := habs

/-! ## M1 Proposition 4: the confinement set -/

/-- The confinement set before reduction mod one: the range of `F̃ = t(ω⁺) - S(ω⁻)`, which
`confSet_eq` identifies with the difference set `C(α) - K`. -/
noncomputable def confSet : Set ℝ := Set.range P.fRaw

/-- **M1 Prop. 4**: `range F̃ = C(α) - K`.  The inclusion `⊆` is the definition of `F̃`; the
converse holds because the two halves of a two-sided word are independent. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confSet_eq :
    P.confSet = Set.image2 (fun t s => t - s) (cantorSet P.α) P.windowSet := by
  ext x
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨piVal P.α (futures ω), ⟨futures ω, rfl⟩, P.wVal (pasts ω), ⟨pasts ω, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, rfl⟩, _, ⟨δ, rfl⟩, rfl⟩
    exact ⟨joinW w δ, by rw [fRaw, futures_joinW, pasts_joinW]⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isCompact_confSet : IsCompact P.confSet := isCompact_range P.continuous_fRaw

/-- **`X(α)` of M1 Prop. 4**: the confinement set `(C(α) - K) mod 1`, equivalently the
range of the factor map `F`. -/
noncomputable def confCircle : Set (AddCircle (1 : ℝ)) := Set.range P.fMap

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_eq_image :
    P.confCircle = (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' P.confSet := by
  rw [confCircle, confSet, ← Set.range_comp]
  rfl

/-- **M1 Prop. 4**: `X(α)` is compact. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isCompact_confCircle : IsCompact P.confCircle := isCompact_range P.continuous_fMap

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isClosed_confCircle : IsClosed P.confCircle := P.isCompact_confCircle.isClosed

/-- **M1 Proposition 4, exact confinement.**  Every fractional part of every orbit lies in
`X(α)`, *with no error term*: the truncated past is a point of `K`, not an approximation to
one.  This is `fMap_iterate_padZ` read as a membership. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_mem_confCircle (ε : ℕ → Bool) (n : ℕ) :
    ((piVal P.α ε * P.α ^ n : ℝ) : AddCircle (1 : ℝ)) ∈ P.confCircle :=
  ⟨shiftZ^[n] (padZ ε), P.fMap_iterate_padZ ε n⟩

/-- **M1 Proposition 4**, for a point of `C(α)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_mul_pow_mem_confCircle {ξ : ℝ} (hξ : ξ ∈ cantorSet P.α) (n : ℕ) :
    ((ξ * P.α ^ n : ℝ) : AddCircle (1 : ℝ)) ∈ P.confCircle := by
  obtain ⟨ε, rfl⟩ := hξ
  exact P.coe_mem_confCircle ε n

end QuadSetup

/-! ## From a missed interval to the two failures -/

/-- Reducing mod one does not move a point of the circle. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_fract (x : ℝ) :
    ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = ((x : ℝ) : AddCircle (1 : ℝ)) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  refine ⟨-⌊x⌋, ?_⟩
  rw [← Int.self_sub_floor]
  simp only [zsmul_eq_mul, mul_one]
  push_cast
  ring

/-- Two reals with the same image in the circle have the same fractional part. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fract_eq_of_coe_eq {a b : ℝ}
    (h : ((a : ℝ) : AddCircle (1 : ℝ)) = ((b : ℝ) : AddCircle (1 : ℝ))) :
    Int.fract a = Int.fract b := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at h
  obtain ⟨k, hk⟩ := h
  refine Int.fract_eq_fract.mpr ⟨k, ?_⟩
  rw [← hk]
  simp

/-- Translating by an integer does not move a point of the circle. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_add_intCast (x : ℝ) (k : ℤ) :
    ((x + (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) = ((x : ℝ) : AddCircle (1 : ℝ)) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  exact ⟨k, by simp only [zsmul_eq_mul, mul_one]; ring⟩

/-- A sequence whose fractional parts avoid a fixed open subinterval of `(0,1)` is not
dense mod one.  (Extracted from `BB61/RouteA.lean`, where it was inlined.) -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_denseModuloOne_of_avoided {s : ℕ → ℝ} {x r : ℝ} (hr : 0 < r)
    (hsub : Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1)
    (havoid : ∀ n : ℕ, Int.fract (s n) ∉ Set.Ioo (x - r) (x + r)) :
    ¬ IsDenseModuloOne s := by
  intro hdense
  have hIccJ : Set.Icc (x - r / 2) (x + r / 2) ⊆ Set.Ioo (x - r) (x + r) := by
    intro y hy
    rw [Set.mem_Icc] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨n, hn⟩ := hdense (x - r / 2) (x + r / 2) (by linarith)
    (fun y hy => Set.Ioo_subset_Icc_self (hsub (hIccJ hy)))
  exact havoid n (hIccJ hn)

/-- A sequence whose fractional parts avoid a fixed open subinterval of `(0,1)` is not
uniformly distributed mod one — a fortiori, since not even dense.  (Extracted from
`BB61/RouteA.lean`.) -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_avoided {s : ℕ → ℝ} {x r : ℝ} (hr : 0 < r)
    (hsub : Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1)
    (havoid : ∀ n : ℕ, Int.fract (s n) ∉ Set.Ioo (x - r) (x + r)) :
    ¬ IsEquidistributedModuloOne s := by
  intro hud
  have hIccJ : Set.Icc (x - r / 2) (x + r / 2) ⊆ Set.Ioo (x - r) (x + r) := by
    intro y hy
    rw [Set.mem_Icc] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := hud (x - r / 2) (x + r / 2) (by linarith)
    (fun y hy => Set.Ioo_subset_Icc_self (hsub (hIccJ hy)))
  have hzero : (fun N : ℕ => (((Finset.range N).filter fun m =>
      Int.fract (s m) ∈ Set.Icc (x - r / 2) (x + r / 2)).card : ℝ) / (N : ℝ))
      = fun _ : ℕ => (0 : ℝ) := by
    funext N
    have hempty : ((Finset.range N).filter fun m =>
        Int.fract (s m) ∈ Set.Icc (x - r / 2) (x + r / 2)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun m _ => fun hmem => havoid m (hIccJ hmem)
    rw [hempty]
    simp
  rw [hzero] at h
  have huniq : (x + r / 2 - (x - r / 2)) / (1 - 0) = 0 :=
    tendsto_nhds_unique h tendsto_const_nhds
  have hr0 : r = 0 := by
    field_simp at huniq
    linarith
  linarith

namespace QuadSetup

variable (P : QuadSetup)

/-- **M1 Proposition 4, the criterion.**  If the confinement set misses a single point of
the circle then it misses a whole interval of `(0,1)`, uniformly in `ξ ∈ C(α)` and `n` —
`X(α)` is *closed*, so its complement is open, and the complement is `1`-periodic, so a
witness can be moved into `(0,1)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_avoided_interval_of_ne_univ (h : P.confCircle ≠ Set.univ) :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ ξ ∈ cantorSet P.α, ∀ n : ℕ,
        Int.fract (ξ * P.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  set U : Set ℝ := (fun y : ℝ => (y : AddCircle (1 : ℝ))) ⁻¹' P.confCircleᶜ with hUdef
  have hUopen : IsOpen U :=
    P.isClosed_confCircle.isOpen_compl.preimage QuotientAddGroup.continuous_mk
  -- a witness in `U`
  obtain ⟨z, hz⟩ : (P.confCircleᶜ).Nonempty := Set.nonempty_compl.mpr h
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) z
  have huU : u ∈ U := by
    rw [hUdef, Set.mem_preimage]
    show ((u : ℝ) : AddCircle (1 : ℝ)) ∈ P.confCircleᶜ
    rwa [hu]
  -- move it into `[0, 1)`
  have hvU : Int.fract u ∈ U := by
    rw [hUdef, Set.mem_preimage, coe_fract]
    exact huU
  -- and then into `(0, 1)`
  have hne : (U ∩ Set.Ioo (0 : ℝ) 1).Nonempty := by
    rcases eq_or_lt_of_le (Int.fract_nonneg u) with h0 | h0
    · obtain ⟨ρ, hρ0, hball⟩ := Metric.isOpen_iff.mp hUopen _ hvU
      refine ⟨min (ρ / 2) (1 / 2), hball ?_, ?_, ?_⟩
      · rw [Real.ball_eq_Ioo, ← h0]
        constructor
        · have : (0 : ℝ) < min (ρ / 2) (1 / 2) := by positivity
          linarith
        · have : min (ρ / 2) (1 / 2) ≤ ρ / 2 := min_le_left _ _
          linarith
      · positivity
      · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    · exact ⟨Int.fract u, hvU, h0, Int.fract_lt_one u⟩
  -- an interval inside `U ∩ (0,1)`
  obtain ⟨y, hy⟩ := hne
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp (hUopen.inter isOpen_Ioo) y hy
  refine ⟨y, r, hr0, fun w hw => ?_, fun ξ hξ n hmem => ?_⟩
  · exact (hball (by rw [Real.ball_eq_Ioo]; exact hw)).2
  · have hfU : Int.fract (ξ * P.α ^ n) ∈ U :=
      (hball (by rw [Real.ball_eq_Ioo]; exact hmem)).1
    rw [hUdef, Set.mem_preimage, coe_fract] at hfU
    exact hfU (P.coe_mul_pow_mem_confCircle hξ n)

/-- **M1 Proposition 4, strong form.**  If `X(α) ≠ 𝕋` then for every `ξ ∈ C(α)` the
sequence `(ξ αⁿ)` is not even *dense* modulo one. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_denseModuloOne_of_confCircle_ne_univ (h : P.confCircle ≠ Set.univ) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsDenseModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := P.exists_avoided_interval_of_ne_univ h
  exact fun ξ hξ => not_denseModuloOne_of_avoided hr hsub (havoid ξ hξ)

/-- **Problem 10.61 at `α`, from confinement alone.**  If `X(α) ≠ 𝕋` then no `(ξ αⁿ)` with
`ξ ∈ C(α)` is uniformly distributed modulo one. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_confCircle_ne_univ (h : P.confCircle ≠ Set.univ) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := P.exists_avoided_interval_of_ne_univ h
  exact fun ξ hξ => not_equidistributed_of_avoided hr hsub (havoid ξ hξ)

/-! ## Sharpness: `X(α)` is the closure of the orbits

Proposition 4 confines every orbit to `X(α)`.  It does not overshoot: `X(α)` is exactly the
closure of the union of all the orbits, so the criterion `X(α) ≠ 𝕋` is not merely sufficient
for "some interval is missed by every orbit at every time" — it is equivalent to it.  The
proof is `exists_padZ_agree` plus the modulus of continuity of `F` (M1 Lemma 6). -/

/-- The union of all the orbits, before reduction mod one. -/
noncomputable def orbitRaw : Set ℝ :=
  {y : ℝ | ∃ (ε : ℕ → Bool) (n : ℕ), y = P.fRaw (shiftZ^[n] (padZ ε))}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem orbitRaw_subset_confSet : P.orbitRaw ⊆ P.confSet := by
  rintro _ ⟨ε, n, rfl⟩
  exact ⟨_, rfl⟩

/-- The agreement bound of M1 Lemma 6 can be made arbitrarily small. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_agreeBound_lt {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, (P.α⁻¹) ^ N + (1 + |P.β|) * |P.β| ^ (N + 1) / (1 - |P.β|) < η := by
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hβ1 := P.abs_beta_lt_one
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  have hc : (0 : ℝ) < (1 + |P.β|) / (1 - |P.β|) := by positivity
  have hi0 : (0 : ℝ) ≤ P.α⁻¹ := (inv_pos_of_one_lt P.one_lt).le
  have hi1 : P.α⁻¹ < 1 := inv_lt_one_of_one_lt P.one_lt
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (half_pos hη) hi1
  obtain ⟨N₂, hN₂⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < η / 2 / ((1 + |P.β|) / (1 - |P.β|)) by positivity) hβ1
  refine ⟨max N₁ N₂, ?_⟩
  have h1 : (P.α⁻¹) ^ max N₁ N₂ < η / 2 :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hi0 hi1.le (le_max_left _ _)) hN₁
  have h2 : |P.β| ^ (max N₁ N₂ + 1) < η / 2 / ((1 + |P.β|) / (1 - |P.β|)) :=
    lt_of_le_of_lt
      (pow_le_pow_of_le_one hβ0 hβ1.le (le_trans (le_max_right _ _) (Nat.le_succ _))) hN₂
  have h3 : (1 + |P.β|) * |P.β| ^ (max N₁ N₂ + 1) / (1 - |P.β|)
      = ((1 + |P.β|) / (1 - |P.β|)) * |P.β| ^ (max N₁ N₂ + 1) := by ring
  rw [h3]
  have h4 : ((1 + |P.β|) / (1 - |P.β|)) * |P.β| ^ (max N₁ N₂ + 1) < η / 2 := by
    rw [← lt_div_iff₀' hc]
    exact h2
  linarith

/-- **Proposition 4 is sharp**: every point of the confinement set is a limit of orbit
points.  Together with `orbitRaw_subset_confSet` this says `X(α)` is the orbit closure. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confSet_subset_closure_orbitRaw : P.confSet ⊆ closure P.orbitRaw := by
  rintro _ ⟨ω, rfl⟩
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨N, hN⟩ := P.exists_agreeBound_lt hη
  obtain ⟨ε, n, hagree⟩ := exists_padZ_agree ω N
  refine ⟨P.fRaw (shiftZ^[n] (padZ ε)), ⟨ε, n, rfl⟩, ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (P.abs_fRaw_sub_le_of_agree fun k hk => (hagree k hk).symm) hN

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem closure_orbitRaw : closure P.orbitRaw = P.confSet :=
  le_antisymm (P.isCompact_confSet.isClosed.closure_subset_iff.mpr P.orbitRaw_subset_confSet)
    P.confSet_subset_closure_orbitRaw

/-- The union of all the orbits, on the circle. -/
noncomputable def orbitCircle : Set (AddCircle (1 : ℝ)) :=
  {z : AddCircle (1 : ℝ) |
    ∃ (ε : ℕ → Bool) (n : ℕ), z = ((piVal P.α ε * P.α ^ n : ℝ) : AddCircle (1 : ℝ))}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_subset_closure_orbitCircle : P.confCircle ⊆ closure P.orbitCircle := by
  rw [P.confCircle_eq_image]
  rintro _ ⟨y, hy, rfl⟩
  have himg : (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' P.orbitRaw ⊆ P.orbitCircle := by
    rintro _ ⟨_, ⟨ε, n, rfl⟩, rfl⟩
    exact ⟨ε, n, P.fMap_iterate_padZ ε n⟩
  refine closure_mono himg ?_
  exact image_closure_subset_closure_image QuotientAddGroup.continuous_mk
    ⟨y, P.confSet_subset_closure_orbitRaw hy, rfl⟩

/-- **The effective criterion certifies the conceptual one.**  If some open subinterval of
`(0,1)` is missed by every orbit at every time — the conclusion of the covering engine of
`BB61/Covering.lean` — then the confinement set of M1 Prop. 4 is not the whole circle.  With
`not_denseModuloOne_of_confCircle_ne_univ` the two criteria are therefore equivalent, and
Route A is exactly a proof that `X(α) ≠ 𝕋`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_ne_univ_of_avoided {x r : ℝ} (hr : 0 < r)
    (hsub : Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1)
    (havoid : ∀ (ε : ℕ → Bool) (n : ℕ),
      Int.fract (piVal P.α ε * P.α ^ n) ∉ Set.Ioo (x - r) (x + r)) :
    P.confCircle ≠ Set.univ := by
  set V : Set (AddCircle (1 : ℝ)) :=
    (fun y : ℝ => (y : AddCircle (1 : ℝ))) '' Set.Ioo (x - r) (x + r) with hV
  have hVopen : IsOpen V := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hVne : V.Nonempty := ⟨_, x, ⟨by linarith, by linarith⟩, rfl⟩
  have hdisj : ∀ z ∈ P.orbitCircle, z ∉ V := by
    rintro _ ⟨ε, n, rfl⟩ ⟨y, hy, hyz⟩
    have hy01 := hsub hy
    have hfr : Int.fract (piVal P.α ε * P.α ^ n) = y := by
      rw [fract_eq_of_coe_eq hyz.symm, Int.fract_eq_self.mpr ⟨hy01.1.le, hy01.2⟩]
    exact havoid ε n (hfr ▸ hy)
  intro huniv
  obtain ⟨z, hzV⟩ := hVne
  have hz : z ∈ closure P.orbitCircle :=
    P.confCircle_subset_closure_orbitCircle (by rw [huniv]; trivial)
  exact closure_minimal hdisj hVopen.isClosed_compl hz hzV

end QuadSetup

end BB61
