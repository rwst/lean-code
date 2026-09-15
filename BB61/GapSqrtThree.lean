/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Raster
import BB61.Bernoulli
import BB61.RouteANormalForm
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The certified gap at `α = 2 + √3`: X8 fires where Route A is blind

Formal companion of `note-1061-M0.html` §6.2 (the headline of M0) and of `note-1061-M2.html` §7
(Proposition 9's converse half).  Together with `BB61/Raster.lean`, which proves
`Route A ⊆ X8`, this file proves the containment **strict**.

M0's sweep found that at `α = 2 + √3` the confinement set `X(α) = (C(α) - K) mod 1` misses two
intervals of length `0.052558`, while Route A does not fire there (`A(α) = 1.0526 > 1`).  The
sweep obtained this at depth `(11, 9)` on `2^21` raster bins.  It is in fact a **depth-`(2,2)`**
fact, exact in `ℤ[√3]`, and that is what is proved here: sixteen closed intervals, nine distinct,
and the gap between two of them.

## Why depth two suffices, and why it is `2 + √3` that allows it

`2 + √3` is the root of `X² - 4X + 1`: norm `+1`, so `β = α⁻¹`.  Hence the window weights
`|c_m| = (1-β)βᵐ` and the Cantor weights `(α-1)α^{-(m+1)}` are the **same sequence**, the
confinement set is `(C + C) mod 1`, and both factors truncate at depth `2` with the *same*
one-sided error `β² = α^{-2} = 7 - 4√3`.  The two depth-2 alphabets are

`{0, 3√3-5, √3-1, 4√3-6}`  (`= {0, w₁, w₂, w₁+w₂}`),

so `x = t_n - S_n` lies in one of the nine intervals `[w₂·p + w₁·q, w₂·p + w₁·q + 2(7-4√3)]`
with `p, q ∈ {0,1,2}`, and reduction mod one leaves the two gaps

`(0.33975, 0.39230)` and `(0.60770, 0.66025)`, both of length `11√3 - 19 = 0.0525589`.

`gapLo = 11 - 6√3` and `gapHi = 5√3 - 8` are the endpoints of the second.  **The certificate has
zero margin at two of the nine intervals**: `w₂·2 + 2(7-4√3) = 12 - 6√3 = 1 + gapLo` and
`w₂·2 + w₁ = 5√3 - 7 = 1 + gapHi` are *equalities*, so the covering touches the gap at both ends
and the openness of the gap is load-bearing.  Nothing here is a numerical tolerance.

## The chain

* `tPart_two_step`, `sPart_two_step` — two turns of the two recursions of `BB61/Splitting.lean`,
  in the exact `ℤ[√3]` form.  The one-sidedness is the point: `BB61/Covering.lean`'s `delta` is
  the two-sided bound `α^{-M} + (1+|β|)|β|^{M'}/(1-|β|)`, which at `M = M' = 2` is `0.1244` and
  would swallow a gap of `0.0526`; the true one-sided error is `β² = 0.0718` on each side.
* `neg_sPart_mem_Icc` — the sharp window bound `S_n ∈ [-1, 0]` at norm `-b = 1`.  This is M2
  Proposition 7's `diam K = d - 1 = 1` in the form the recursion needs, and it is what makes the
  remainder of the past expansion land in `[0, 1]` rather than in `[-√3, √3]`.
* `fract_mem_covThree` — the sixteen-interval covering, `covThree`.
* `covThree_inter_gapIoo_eq_empty` — the certificate: nine intervals times two integer shifts,
  eighteen exact comparisons in `ℤ[√3]`.
* `gap_two_add_sqrt3` — **one open interval, uniform in `ξ ∈ C(2+√3)` and in `n`, that every
  orbit misses at every time**;
* `two_add_sqrt3_not_equidistributed_of_gap` — **Problem 10.61 at `2 + √3`, with no citation and
  no axiom beyond the standard three.**  `BB61/Floor.lean` proves the same statement through the
  entropy floor of `CITED/LedrappierYoung.lean`; this is an independent and axiom-free proof of
  it, and the two agree.
* `exists_zeroRun_two_add_sqrt3` — the same certificate as the **output of the X8 procedure** of
  `BB61/Raster.lean`: at every resolution `G ≥ 100` the raster reports a nonempty run of empty
  bins whose interval misses the orbit.
* `not_routeAExponent_lt_one_twoAddSqrt3`, `routeA_subset_X8_strict` — **`Route A ⊊ X8`**, the
  converse half of M2 Proposition 9.  Route A is blind at `2 + √3` because `A(α) < 1` on the
  quadratic units is exactly `α > 4` (M2 Corollary 6) and `2 + √3 = 3.732`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, CUP 2012,
  Problem 10.61.
-/

noncomputable section

namespace BB61

open Set

/-! ## 1. Two turns of the two recursions -/

/-- Two steps of the Cantor recursion `α t_n = (α-1) ε_n + t_{n+1}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tPart_two_step {α : ℝ} (hα : 1 < α) (ε : ℕ → Bool) (n : ℕ) :
    α ^ 2 * tPart α ε n
      = α * (α - 1) * dR ε n + (α - 1) * dR ε (n + 1) + tPart α ε (n + 2) := by
  have h1 := alpha_mul_tPart hα ε n
  have h2 := alpha_mul_tPart hα ε (n + 1)
  linear_combination α * h1 + h2

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_zero_or_one (ε : ℕ → Bool) (k : ℕ) : dR ε k = 0 ∨ dR ε k = 1 := by
  by_cases h : ε k <;> simp [dR, h]

namespace QuadSetup

variable (P : QuadSetup)

/-- Two steps of the window recursion `S_{n+1} = β S_n + (β-1) ε_n`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sPart_two_step (ε : ℕ → Bool) (n : ℕ) :
    P.sPart ε (n + 2)
      = P.β ^ 2 * P.sPart ε n + P.β * (P.β - 1) * dR ε n + (P.β - 1) * dR ε (n + 1) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, P.sPart_succ, P.sPart_succ]; ring

/-- **The sharp window bound at norm one**: `S_n ∈ [-1, 0]` whenever `0 ≤ β ≤ 1`.  This is
`diam K = d - 1 = 1` of M2 Proposition 7, in recursion form: `|β| + |β - 1| = 1` exactly, so the
interval `[-1, 0]` is invariant.  The generic bound `(1+|β|)/(1-|β|)` of `BB61/Splitting.lean`
is `√3` at `2 + √3` and is far too lossy for a depth-2 certificate. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem neg_sPart_mem_Icc (hβ0 : 0 ≤ P.β) (hβ1 : P.β ≤ 1) (ε : ℕ → Bool) (n : ℕ) :
    0 ≤ -P.sPart ε n ∧ -P.sPart ε n ≤ 1 := by
  induction n with
  | zero => rw [P.sPart_zero]; constructor <;> norm_num
  | succ n ih =>
      rw [P.sPart_succ]
      have hd0 := dR_nonneg ε n
      have hd1 := dR_le_one ε n
      constructor <;> nlinarith [ih.1, ih.2]

end QuadSetup

/-! ## 2. The depth-two data at `2 + √3` -/

namespace GapThree

/-- The depth-2 weight of the *older* digit: `(1-β)β = 3√3 - 5 = 0.196152`. -/
def wOne : ℝ := 3 * Real.sqrt 3 - 5

/-- The depth-2 weight of the *newer* digit: `1-β = √3 - 1 = 0.732051`. -/
def wTwo : ℝ := Real.sqrt 3 - 1

/-- The one-sided depth-2 truncation error, on each of the two sides:
`β² = α^{-2} = 7 - 4√3 = 0.0717968`. -/
def epsTwo : ℝ := 7 - 4 * Real.sqrt 3

/-- The left endpoint of the `(p, q)` interval of the depth-`(2,2)` covering. -/
def lend (p q : ℕ) : ℝ := wTwo * p + wOne * q

/-- The left endpoint of the certified gap: `11 - 6√3 = 0.6076952`. -/
def gapLo : ℝ := 11 - 6 * Real.sqrt 3

/-- The right endpoint of the certified gap: `5√3 - 8 = 0.6602540`.
The gap has length `gapHi - gapLo = 11√3 - 19 = 0.0525589`, M0's `0.052558`. -/
def gapHi : ℝ := 5 * Real.sqrt 3 - 8

/-- **The depth-`(2,2)` covering of the confinement set at `2 + √3`**, reduced mod one: nine
closed intervals of length `2(7-4√3)`, each shifted by an integer.  This is exactly what M0's
X8 procedure rasterises, at `M = M_K = 2`. -/
def covThree : Set ℝ :=
  {y | ∃ p q : ℕ, p ≤ 2 ∧ q ≤ 2 ∧ ∃ m : ℤ,
        lend p q ≤ y + m ∧ y + m ≤ lend p q + 2 * epsTwo}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sq_sqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The future part at depth two: `t_n = w₂ ε_n + w₁ ε_{n+1} + β² t_{n+2}`, with the remainder
in `[0, 1]` — the error is **one-sided**, which is what a `0.0526` gap needs. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tPart_expand (ε : ℕ → Bool) (n : ℕ) :
    ∃ a₁ a₀ : ℕ, a₁ ≤ 1 ∧ a₀ ≤ 1 ∧ ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      tPart (2 + Real.sqrt 3) ε n = wTwo * a₁ + wOne * a₀ + epsTwo * u := by
  have h3 := sq_sqrt3
  have hα : (1 : ℝ) < 2 + Real.sqrt 3 := by linarith [Real.sqrt_nonneg 3]
  have ht := tPart_two_step hα ε n
  refine ⟨if ε n then 1 else 0, if ε (n + 1) then 1 else 0, by split <;> norm_num,
    by split <;> norm_num, tPart (2 + Real.sqrt 3) ε (n + 2),
    piVal_nonneg hα _, piVal_le_one hα _, ?_⟩
  have e1 : ((if ε n then 1 else 0 : ℕ) : ℝ) = dR ε n := by
    unfold dR; split <;> norm_num
  have e0 : ((if ε (n + 1) then 1 else 0 : ℕ) : ℝ) = dR ε (n + 1) := by
    unfold dR; split <;> norm_num
  rw [e1, e0, wTwo, wOne, epsTwo]
  linear_combination (7 - 4 * Real.sqrt 3) * ht
    + ((4 * Real.sqrt 3 + 9) * tPart (2 + Real.sqrt 3) ε n
        - (4 * Real.sqrt 3 + 5) * dR ε n - 4 * dR ε (n + 1)) * h3

/-- The past part at depth two: `-S_n = w₂ δ₁ + w₁ δ₀ + β² v` with `v ∈ [0,1]`.  The three
cases `n = 0, 1, k+2` are the recursion not yet having enough past. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem neg_sPart_expand (P : QuadSetup) (hβ : P.β = 2 - Real.sqrt 3) (ε : ℕ → Bool) (n : ℕ) :
    ∃ c₁ c₀ : ℕ, c₁ ≤ 1 ∧ c₀ ≤ 1 ∧ ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧
      -P.sPart ε n = wTwo * c₁ + wOne * c₀ + epsTwo * v := by
  have h3 := sq_sqrt3
  have hlo := lt_sqrt3
  have hhi := sqrt3_lt
  have hβ0 : 0 ≤ P.β := by rw [hβ]; linarith
  have hβ1 : P.β ≤ 1 := by rw [hβ]; linarith
  match n with
  | 0 =>
      refine ⟨0, 0, by norm_num, by norm_num, 0, le_rfl, zero_le_one, ?_⟩
      rw [P.sPart_zero]; norm_num
  | 1 =>
      refine ⟨if ε 0 then 1 else 0, 0, by split <;> norm_num, by norm_num, 0, le_rfl,
        zero_le_one, ?_⟩
      have e1 : ((if ε 0 then 1 else 0 : ℕ) : ℝ) = dR ε 0 := by unfold dR; split <;> norm_num
      rw [show (1 : ℕ) = 0 + 1 from rfl, P.sPart_succ, P.sPart_zero, e1, hβ, wTwo, wOne, epsTwo]
      ring
  | (k + 2) =>
      obtain ⟨hv0, hv1⟩ := P.neg_sPart_mem_Icc hβ0 hβ1 ε k
      refine ⟨if ε (k + 1) then 1 else 0, if ε k then 1 else 0, by split <;> norm_num,
        by split <;> norm_num, -P.sPart ε k, hv0, hv1, ?_⟩
      have e1 : ((if ε (k + 1) then 1 else 0 : ℕ) : ℝ) = dR ε (k + 1) := by
        unfold dR; split <;> norm_num
      have e0 : ((if ε k then 1 else 0 : ℕ) : ℝ) = dR ε k := by unfold dR; split <;> norm_num
      rw [P.sPart_two_step, e1, e0, hβ, wTwo, wOne, epsTwo]
      linear_combination (-P.sPart ε k - dR ε k) * h3

/-- **The covering.**  Every `{ξ αⁿ}` lies in one of the nine intervals of `covThree`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fract_mem_covThree (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3)
    (hβ : P.β = 2 - Real.sqrt 3) (ε : ℕ → Bool) (n : ℕ) :
    Int.fract (piVal P.α ε * P.α ^ n) ∈ covThree := by
  have hlo := lt_sqrt3
  have hhi := sqrt3_lt
  obtain ⟨a₁, a₀, ha₁, ha₀, u, hu0, hu1, ht⟩ := tPart_expand ε n
  obtain ⟨c₁, c₀, hc₁, hc₀, v, hv0, hv1, hs⟩ := neg_sPart_expand P hβ ε n
  rw [P.fract_split ε n]
  refine ⟨a₁ + c₁, a₀ + c₀, by omega, by omega, ⌊tPart P.α ε n - P.sPart ε n⌋, ?_, ?_⟩ <;>
    rw [Int.fract, sub_add_cancel, hα, lend] <;>
    rw [ht, ← neg_neg (P.sPart ε n), hs] <;> push_cast <;>
    simp only [wTwo, wOne, epsTwo] <;> nlinarith [hu0, hu1, hv0, hv1]

/-- **The certificate**, with zero margin at both ends: the covering misses the open interval
`(11 - 6√3, 5√3 - 8)`.  Eighteen exact comparisons in `ℤ[√3]`; two of them are equalities. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem covThree_inter_gapIoo_eq_empty : Set.Ioo gapLo gapHi ∩ covThree = ∅ := by
  have hlo := lt_sqrt3
  have hhi := sqrt3_lt
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hy, p, q, hp, hq, m, hm1, hm2⟩
  rw [Set.mem_Ioo, gapLo, gapHi] at hy
  simp only [lend, wTwo, wOne, epsTwo] at hm1 hm2
  -- only the shifts `m = 0` and `m = 1` can place `y + m` in `[0, 2]`
  have hmR : (-1 : ℝ) < (m : ℝ) ∧ (m : ℝ) < 2 := by
    constructor
    · have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      have hL : (0 : ℝ) ≤ (Real.sqrt 3 - 1) * p + (3 * Real.sqrt 3 - 5) * q := by
        nlinarith
      nlinarith [hm1, hy.1]
    · have hR : (Real.sqrt 3 - 1) * (p : ℝ) + (3 * Real.sqrt 3 - 5) * q + 2 * (7 - 4 * Real.sqrt 3)
          ≤ 2 := by
        have hp2 : (p : ℝ) ≤ 2 := by exact_mod_cast hp
        have hq2 : (q : ℝ) ≤ 2 := by exact_mod_cast hq
        nlinarith
      nlinarith [hm2, hy.2]
  have hm : m = 0 ∨ m = 1 := by
    have h1 : (-1 : ℤ) < m := by exact_mod_cast hmR.1
    have h2 : m < 2 := by exact_mod_cast hmR.2
    omega
  interval_cases p <;> interval_cases q <;>
    rcases hm with rfl | rfl <;> push_cast at hm1 hm2 <;> linarith

/-! ## 3. Problem 10.61 at `2 + √3`, unconditionally and with no citation -/

variable (P : QuadSetup)

/-- **The avoided interval at `2 + √3`.**  One explicit open interval `J ⊆ (0,1)`, uniform in
`ξ ∈ C(α)` and in `n`, that every orbit misses at every time. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gap_two_add_sqrt3 (hα : P.α = 2 + Real.sqrt 3) (hβ : P.β = 2 - Real.sqrt 3) :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ (ε : ℕ → Bool) (n : ℕ),
        Int.fract (piVal P.α ε * P.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  have hlo := lt_sqrt3
  have hhi := sqrt3_lt
  refine ⟨(3 - Real.sqrt 3) / 2, (11 * Real.sqrt 3 - 19) / 2, by linarith, ?_, ?_⟩
  · intro z hz
    rw [Set.mem_Ioo] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  · intro ε n hz
    have hmem : Int.fract (piVal P.α ε * P.α ^ n) ∈ Set.Ioo gapLo gapHi := by
      rw [Set.mem_Ioo, gapLo, gapHi]
      rw [Set.mem_Ioo] at hz
      constructor <;> linarith [hz.1, hz.2]
    have := covThree_inter_gapIoo_eq_empty
    rw [Set.eq_empty_iff_forall_notMem] at this
    exact this _ ⟨hmem, fract_mem_covThree P hα hβ ε n⟩

/-- No `(ξ αⁿ)` with `ξ ∈ C(2+√3)` is dense modulo one. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_add_sqrt3_not_denseModuloOne_of_gap
    (hα : P.α = 2 + Real.sqrt 3) (hβ : P.β = 2 - Real.sqrt 3) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsDenseModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := gap_two_add_sqrt3 P hα hβ
  rintro ξ ⟨ε, rfl⟩
  exact not_denseModuloOne_of_avoided hr hsub (havoid ε)

/-- **Problem 10.61 at `α = 2 + √3`, axiom-free.**  No `ξ ∈ C(2+√3)` has `(ξ αⁿ)` uniformly
distributed modulo one — a fortiori, since not even dense.

`BB61/Floor.lean` proves the same statement through M3's entropy floor and the cited axiom
`LY.entropyRate_floor` of `CITED/LedrappierYoung.lean`.  This proof consumes no citation and no
axiom beyond the standard three: it is M0 §6.2's support certificate, at depth `(2,2)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_add_sqrt3_not_equidistributed_of_gap
    (hα : P.α = 2 + Real.sqrt 3) (hβ : P.β = 2 - Real.sqrt 3) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := gap_two_add_sqrt3 P hα hβ
  rintro ξ ⟨ε, rfl⟩
  exact not_equidistributed_of_avoided hr hsub (havoid ε)

/-- The certificate read as M1 Proposition 4: the confinement set is not the whole circle. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_ne_univ_two_add_sqrt3
    (hα : P.α = 2 + Real.sqrt 3) (hβ : P.β = 2 - Real.sqrt 3) : P.confCircle ≠ Set.univ := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := gap_two_add_sqrt3 P hα hβ
  exact P.confCircle_ne_univ_of_avoided hr hsub havoid

/-- **Problem 10.61 at `2 + √3`**, on the concrete setup `twoAddSqrt3` (`X² - 4X + 1`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem problem_10_61_two_add_sqrt3_axiom_free :
    ∀ ξ ∈ cantorSet (2 + Real.sqrt 3),
      ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * (2 + Real.sqrt 3) ^ n :=
  two_add_sqrt3_not_equidistributed_of_gap twoAddSqrt3 twoAddSqrt3_alpha twoAddSqrt3_beta

/-! ## 4. `Route A ⊊ X8` -/

/-- **The X8 procedure's output at `2 + √3`.**  At every resolution `G ≥ 100` the raster of
`BB61/Raster.lean`, run on the depth-`(2,2)` covering, reports a nonempty run of empty bins
whose interval misses every orbit point.  This is M0 §6.2's certificate as an object of the
procedure, rather than as an interval. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_zeroRun_two_add_sqrt3 (hα : P.α = 2 + Real.sqrt 3)
    (hβ : P.β = 2 - Real.sqrt 3) {G : ℕ} (hG : 100 ≤ G) :
    ∃ (i : ℤ) (ℓ : ℕ), 0 < ℓ ∧ Raster.ZeroRun G covThree i ℓ ∧
      Raster.runSet G i ℓ ∩ P.orbitFractSet = ∅ := by
  have hlo := lt_sqrt3
  have hhi := sqrt3_lt
  have hG0 : 0 < G := by omega
  have hGR : (100 : ℝ) ≤ (G : ℝ) := by exact_mod_cast hG
  have hXC : P.orbitFractSet ⊆ covThree := by
    rintro _ ⟨ε, n, rfl⟩; exact fract_mem_covThree P hα hβ ε n
  obtain ⟨i, ℓ, hlen, _, hzr, hmiss⟩ :=
    Raster.exists_certified_gap (X := P.orbitFractSet) (Cov := covThree) (Imp := covThree)
      (e := 0) hG0 le_rfl hXC (subset_refl _) (fun y hy => ⟨y, hy, by simp⟩)
      covThree_inter_gapIoo_eq_empty
  refine ⟨i, ℓ, ?_, hzr, hmiss⟩
  have hgap : gapHi - gapLo - 2 * 0 = 11 * Real.sqrt 3 - 19 := by
    rw [gapHi, gapLo]; ring
  rw [hgap] at hlen
  have : (0 : ℝ) < (ℓ : ℝ) := by nlinarith
  exact_mod_cast this

/-- **Route A is blind at `2 + √3`.**  On the quadratic units `A(α) < 1` is exactly `α > 4`
(M2 Corollary 6), and `2 + √3 = 3.7320508…`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_routeAExponent_lt_one_twoAddSqrt3 : ¬ twoAddSqrt3.routeAExponent < 1 := by
  rw [twoAddSqrt3.routeAExponent_lt_one_iff_four_lt (by norm_num [twoAddSqrt3])]
  rw [twoAddSqrt3_alpha]
  push Not
  linarith [sqrt3_lt]

/-- **`Route A ⊊ X8`** (M2 Proposition 9, converse half).  At `2 + √3` the raster certificate
exists — at every resolution `G ≥ 100` — while Route A does not fire.  With
`BB61/Raster.lean`'s `exists_X8Cert_of_cert`, which is the containment, the two criteria are
therefore ordered strictly. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeA_subset_X8_strict :
    ¬ twoAddSqrt3.routeAExponent < 1 ∧
      ∀ G : ℕ, 100 ≤ G → ∃ (i : ℤ) (ℓ : ℕ), 0 < ℓ ∧ Raster.ZeroRun G covThree i ℓ ∧
        Raster.runSet G i ℓ ∩ twoAddSqrt3.orbitFractSet = ∅ :=
  ⟨not_routeAExponent_lt_one_twoAddSqrt3,
    fun _ hG =>
      exists_zeroRun_two_add_sqrt3 twoAddSqrt3 twoAddSqrt3_alpha twoAddSqrt3_beta hG⟩

end GapThree

end BB61
