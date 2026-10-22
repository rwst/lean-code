/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import CITED.MosqueraShmerkin
import CITED.DavenportErdosLeVeque
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Condition (TU) of Isaac (2006) is false — two proofs

Isaac [Isa06] reduces the simple normality of `√s` in base 2 (`s` not a square) to
**Condition (TU)**: writing `ω = .x₁x₂…`, `ν = ω²`, and `f_N(ω) = (x₁ + ⋯ + x_N)/N`, for every
subsequence `(nᵢ)` the quantity `limsupᵢ f_{nᵢ}(√ν)` depends only on the tail of the binary
expansion of `ν`, i.e. is unchanged when a dyadic rational is added to `ν`.  His Theorem 2
((TU) ⇒ Theorem 1) is correct; his proof of (TU) is not (`plans/verdict-isaac2006.html`).
This file records that (TU) is in fact **false**, by the two independent proofs of
`plans/report-sqrtnorm.html` §2.1.  Both refute already the full-sequence form `TUfull`.

* **Proof A** (bootstrap, after [I1 §1.1], with the gap condition corrected; `std3`).  Under
  (TU), Isaac's Section-2 argument applied to `y` with `y²` dyadic — here through the pair
  `ω₁ = y/2 − 1/4`, `ω₂ = 1 − y/8`, whose squares differ by a dyadic rational — gives
  `f_N(y) ≥ 2/5` infinitely often (`frequently_freq_ge`).  Feeding this to
  `yⱼ = √(xⱼ² + 1/4)` for the sparse dyadics `xⱼ = ∑_{i ≤ j} 2^{-nᵢ}`, each `nⱼ₊₁` chosen at a
  zero digit of `yⱼ` past a point where `f(yⱼ) ≥ 2/5`, yields `x = ∑ 2^{-nⱼ}` with
  `f_N(x) → 0` but `f_N(√(x² + 1/4)) ≥ 2/5` infinitely often; `x²` is a Liouville number,
  so irrational.  The pair `(x², x² + 1/4)` violates (TU): contradiction.
  Here `√(4^{n-1} + X²)` is irrational for odd `X < 2^{n-2}` (`not_isSquare_add_four_pow`).
* **Proof B** (Fourier decay; cited).  For a non-atomic homogeneous self-similar measure `μ`,
  the image under the convex map `g(ω) = √(ω²/4 + 1/4)` has power Fourier decay
  ([MS18, Thm 3.1], `CITED/MosqueraShmerkin.lean`), so `g_*μ`-a.e. point is simply normal
  ([DEL63], `CITED/DavenportErdosLeVeque.lean`).  We take `μ = μ₈`, the Cantor measure of
  ratio `1/8`, whose points have binary ones only at multiples of `3` (`cnt_cantor8_le`);
  then `(ω²/4, ω²/4 + 1/4)` violates (TU) for `μ₈`-a.e. `ω`.  This replaces the report's
  Bernoulli(`p`) measure `μ_p` (whose frequency `p ≠ 1/2` needs the strong law) by a measure
  with a deterministic frequency bound `≤ 1/3`; the cited theorem used is the same.

## Conventions

The `k`-th binary digit is `⌊2ᵏ z⌋ mod 2` (`bdig`), which for dyadic `z` picks the terminating
expansion; `f_N` is `freq`.  `SameTail ν ν'` means `ν' − ν ∈ ℤ[1/2]`.

## Main results

* `BB47.Isaac.not_TU_bootstrap`, `not_TUfull_bootstrap` — proof A, standard axioms only.
* `BB47.Isaac.not_TU_fourier`, `not_TUfull_fourier` — proof B, on [MS18] and [DEL63].

## References

* [Isa06] Isaac, R. "On the simple normality to base 2 of `√s`, for `s` not a perfect square."
  arXiv:math/0512404v2 (2006).
* [I1] `isaac1.md` (reviewer file, §1.1), as checked in `plans/report-sqrtnorm.html` §2.1.
* [MS18] Mosquera, C. A., and P. S. Shmerkin, *Ann. Acad. Sci. Fenn. Math.* **43** (2018).
* [DEL63] Davenport, H., P. Erdős, and W. J. LeVeque, *Michigan Math. J.* **10** (1963).
-/

namespace BB47.Isaac

open Filter Topology

/-! ## Binary digits and frequencies -/

/-- The `k`-th binary digit of `z` after the point, `⌊2ᵏ z⌋ mod 2`. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
noncomputable def bdig (z : ℝ) (k : ℕ) : ℤ := ⌊(2 : ℝ) ^ k * z⌋ % 2

/-- The number of ones among the first `N` binary digits of `z`. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
noncomputable def cnt (z : ℝ) (N : ℕ) : ℤ := ∑ k ∈ Finset.range N, bdig z (k + 1)

/-- Isaac's `f_N(z)`: the frequency of ones among the first `N` binary digits. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
noncomputable def freq (z : ℝ) (N : ℕ) : ℝ := (cnt z N : ℝ) / N

lemma bdig_nonneg (z : ℝ) (k : ℕ) : 0 ≤ bdig z k := Int.emod_nonneg _ (by norm_num)

lemma bdig_le_one (z : ℝ) (k : ℕ) : bdig z k ≤ 1 := by
  have := Int.emod_lt_of_pos ⌊(2 : ℝ) ^ k * z⌋ (by norm_num : (0 : ℤ) < 2)
  unfold bdig; omega

lemma cnt_succ (z : ℝ) (N : ℕ) : cnt z (N + 1) = cnt z N + bdig z (N + 1) :=
  Finset.sum_range_succ _ _

lemma cnt_zero (z : ℝ) : cnt z 0 = 0 := rfl

lemma cnt_nonneg (z : ℝ) (N : ℕ) : 0 ≤ cnt z N :=
  Finset.sum_nonneg fun k _ => bdig_nonneg z (k + 1)

lemma cnt_le (z : ℝ) (N : ℕ) : cnt z N ≤ N := by
  induction N with
  | zero => simp [cnt_zero]
  | succ N ih => rw [cnt_succ]; have := bdig_le_one z (N + 1); push_cast; omega

lemma cnt_add_le (z : ℝ) (N s : ℕ) : cnt z N ≤ cnt z (N + s) ∧ cnt z (N + s) ≤ cnt z N + s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← add_assoc, cnt_succ]
    have := bdig_nonneg z (N + s + 1); have := bdig_le_one z (N + s + 1); push_cast; omega

lemma freq_nonneg (z : ℝ) (N : ℕ) : 0 ≤ freq z N :=
  div_nonneg (by exact_mod_cast cnt_nonneg z N) (Nat.cast_nonneg N)

lemma freq_le_one (z : ℝ) (N : ℕ) : freq z N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [freq]
  · rw [freq, div_le_one (by exact_mod_cast hN)]; exact_mod_cast cnt_le z N

lemma isCobounded_freq (z : ℝ) : IsCoboundedUnder (· ≤ ·) atTop (freq z) :=
  isCoboundedUnder_le_of_le atTop (fun N => freq_nonneg z N)

lemma isBounded_freq (z : ℝ) : IsBoundedUnder (· ≤ ·) atTop (freq z) :=
  isBoundedUnder_of ⟨1, fun N => freq_le_one z N⟩

/-- A bounded numerator over `N` tends to `0`. -/
lemma tendsto_div_of_bounded {u : ℕ → ℤ} {C : ℝ} (h : ∀ N, |(u N : ℝ)| ≤ C) :
    Tendsto (fun N : ℕ => (u N : ℝ) / N) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat C)
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (h N) (Nat.cast_nonneg N)

/-- Shifted digit sequences have counts at bounded distance. -/
lemma cnt_shift {a b : ℝ} {s K : ℕ} (h : ∀ k, K ≤ k → bdig a (k + s) = bdig b k) (N : ℕ) :
    |cnt a N - cnt b N| ≤ K + 2 * s := by
  have key : ∀ N, |cnt a (N + s) - cnt b N| ≤ K + s := by
    intro N
    induction N with
    | zero =>
      simp only [zero_add, cnt_zero]
      have := cnt_le a s; have := cnt_nonneg a s
      rw [abs_le]; constructor <;> omega
    | succ N ih =>
      by_cases hN : N + 1 ≤ K
      · have := cnt_le a (N + 1 + s); have := cnt_nonneg a (N + 1 + s)
        have := cnt_le b (N + 1); have := cnt_nonneg b (N + 1)
        rw [abs_le]; push_cast at *; constructor <;> omega
      · have e : N + 1 + s = N + s + 1 := by omega
        rw [e, cnt_succ, cnt_succ, ← h (N + 1) (by omega), show N + 1 + s = N + s + 1 by omega]
        rw [abs_le] at *; constructor <;> omega
  have h1 := key N; have h2 := cnt_add_le a N s
  rw [abs_le] at *; constructor <;> omega

/-- Complemented shifted digit sequences: counts add up to `N` up to a bounded error. -/
lemma cnt_shift_compl {a b : ℝ} {s K : ℕ} (h : ∀ k, K ≤ k → bdig a (k + s) = 1 - bdig b k)
    (N : ℕ) : |cnt a N + cnt b N - N| ≤ K + 2 * s := by
  have key : ∀ N, |cnt a (N + s) + cnt b N - N| ≤ K + s := by
    intro N
    induction N with
    | zero =>
      simp only [zero_add, cnt_zero]
      have := cnt_le a s; have := cnt_nonneg a s
      rw [abs_le]; constructor <;> omega
    | succ N ih =>
      by_cases hN : N + 1 ≤ K
      · have := cnt_le a (N + 1 + s); have := cnt_nonneg a (N + 1 + s)
        have := cnt_le b (N + 1); have := cnt_nonneg b (N + 1)
        rw [abs_le]; push_cast at *; constructor <;> omega
      · have e : N + 1 + s = N + s + 1 := by omega
        rw [e, cnt_succ, cnt_succ, ← e, h (N + 1) (by omega)]
        rw [abs_le] at *; constructor <;> omega
  have h1 := key N; have h2 := cnt_add_le a N s
  rw [abs_le] at *; constructor <;> omega

lemma tendsto_freq_sub {a b : ℝ} {s K : ℕ} (h : ∀ k, K ≤ k → bdig a (k + s) = bdig b k) :
    Tendsto (fun N => freq a N - freq b N) atTop (𝓝 0) := by
  have := tendsto_div_of_bounded (u := fun N => cnt a N - cnt b N) (C := K + 2 * s)
    (fun N => by exact_mod_cast cnt_shift h N)
  refine this.congr fun N => ?_
  simp only [freq]; push_cast; ring

lemma tendsto_freq_add {a b : ℝ} {s K : ℕ} (h : ∀ k, K ≤ k → bdig a (k + s) = 1 - bdig b k) :
    Tendsto (fun N => freq a N + freq b N) atTop (𝓝 1) := by
  have h0 := tendsto_div_of_bounded (u := fun N => cnt a N + cnt b N - N) (C := K + 2 * s)
    (fun N => by exact_mod_cast cnt_shift_compl h N)
  have h1 : Tendsto (fun N : ℕ => (((cnt a N + cnt b N - N : ℤ) : ℝ) / N) + 1) atTop (𝓝 1) := by
    simpa using h0.add_const 1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : (N : ℝ) ≠ 0 := by positivity
  simp only [freq]; push_cast; field_simp; ring

/-! ### Floors at consecutive scales -/

lemma floor_two_mul (t : ℝ) : ⌊2 * t⌋ = 2 * ⌊t⌋ + ⌊2 * t⌋ % 2 := by
  have h1 : 2 * ⌊t⌋ ≤ ⌊2 * t⌋ := Int.le_floor.2 (by push_cast; linarith [Int.floor_le t])
  have h2 : ⌊2 * t⌋ < 2 * ⌊t⌋ + 2 :=
    Int.floor_lt.2 (by push_cast; linarith [Int.lt_floor_add_one t])
  omega

lemma floor_succ (t : ℝ) (k : ℕ) :
    ⌊(2 : ℝ) ^ (k + 1) * t⌋ = 2 * ⌊(2 : ℝ) ^ k * t⌋ + bdig t (k + 1) := by
  unfold bdig
  rw [show (2 : ℝ) ^ (k + 1) * t = 2 * ((2 : ℝ) ^ k * t) by ring]
  exact floor_two_mul _

/-- If the floors at scale `m` differ by at most one and the smaller is even, all coarser floors
agree. -/
lemma floor_agree {z w : ℝ} {m : ℕ} (hz : bdig z m = 0)
    (h1 : ⌊(2 : ℝ) ^ m * z⌋ ≤ ⌊(2 : ℝ) ^ m * w⌋) (h2 : ⌊(2 : ℝ) ^ m * w⌋ ≤ ⌊(2 : ℝ) ^ m * z⌋ + 1) :
    ∀ k < m, ⌊(2 : ℝ) ^ k * w⌋ = ⌊(2 : ℝ) ^ k * z⌋ := by
  have key : ∀ d, d < m → ⌊(2 : ℝ) ^ (m - 1 - d) * w⌋ = ⌊(2 : ℝ) ^ (m - 1 - d) * z⌋ := by
    intro d
    induction d with
    | zero =>
      intro hm
      have ew := floor_succ w (m - 1); have ez := floor_succ z (m - 1)
      rw [show m - 1 + 1 = m by omega] at ew ez
      have := bdig_nonneg w m; have := bdig_le_one w m
      rw [hz] at ez; simp only [Nat.sub_zero]; omega
    | succ d ih =>
      intro hm
      have ew := floor_succ w (m - 1 - (d + 1)); have ez := floor_succ z (m - 1 - (d + 1))
      rw [show m - 1 - (d + 1) + 1 = m - 1 - d by omega] at ew ez
      have := ih (by omega)
      have := bdig_nonneg w (m - 1 - d); have := bdig_le_one w (m - 1 - d)
      have := bdig_nonneg z (m - 1 - d); have := bdig_le_one z (m - 1 - d)
      omega
  intro k hk
  have := key (m - 1 - k) (by omega)
  rwa [show m - 1 - (m - 1 - k) = k by omega] at this

lemma cnt_agree {z w : ℝ} {m : ℕ} (h : ∀ k < m, ⌊(2 : ℝ) ^ k * w⌋ = ⌊(2 : ℝ) ^ k * z⌋) :
    ∀ N < m, cnt w N = cnt z N := by
  intro N hN
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [bdig, h (k + 1) (by simp at hk; omega)]

/-! ## Condition (TU) -/

/-- `ν` and `ν'` have the same tail: they differ by a dyadic rational. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
def SameTail (ν ν' : ℝ) : Prop := ∃ (a : ℤ) (m : ℕ), ν' - ν = a / 2 ^ m

/-- Isaac's Condition (TU) [Isa06, §1]: for every subsequence `(nᵢ)`, `limsupᵢ f_{nᵢ}(√ν)` is a
tail function of `ν`. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
def TU : Prop :=
  ∀ ν ν' : ℝ, 0 < ν → ν < 1 → 0 < ν' → ν' < 1 → Irrational ν → SameTail ν ν' →
    ∀ n : ℕ → ℕ, StrictMono n →
      limsup (fun i => freq (√ν) (n i)) atTop = limsup (fun i => freq (√ν') (n i)) atTop

/-- (TU) for the full sequence `nᵢ = i` only; both refutations below refute this weaker form. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
def TUfull : Prop :=
  ∀ ν ν' : ℝ, 0 < ν → ν < 1 → 0 < ν' → ν' < 1 → Irrational ν → SameTail ν ν' →
    limsup (freq (√ν)) atTop = limsup (freq (√ν')) atTop

@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
lemma TU.full (h : TU) : TUfull := fun ν ν' h1 h2 h3 h4 h5 h6 =>
  h ν ν' h1 h2 h3 h4 h5 h6 id strictMono_id

/-! ## Digits under the affine maps used -/

lemma bdig_half (z : ℝ) (k : ℕ) : bdig (z / 2) (k + 1) = bdig z k := by
  unfold bdig; rw [show (2 : ℝ) ^ (k + 1) * (z / 2) = 2 ^ k * z by ring]

lemma bdig_omega1 (y : ℝ) (k : ℕ) (hk : 2 ≤ k) : bdig (y / 2 - 1 / 4) (k + 1) = bdig y k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  unfold bdig
  have e : (2 : ℝ) ^ (j + 2 + 1) * (y / 2 - 1 / 4) = 2 ^ (j + 2) * y - ((2 * 2 ^ j : ℤ) : ℝ) := by
    push_cast; ring
  rw [e, Int.floor_sub_intCast]
  omega

lemma bdig_omega2 {y : ℝ} (hy : Irrational y) (k : ℕ) :
    bdig (1 - y / 8) (k + 3) = 1 - bdig y k := by
  unfold bdig
  have hirr : Irrational ((2 : ℝ) ^ k * y) := by
    have := hy.natCast_mul (m := 2 ^ k) (by positivity); push_cast at this; exact this
  have e : (2 : ℝ) ^ (k + 3) * (1 - y / 8) = ((8 * 2 ^ k : ℤ) : ℝ) + -((2 : ℝ) ^ k * y) := by
    push_cast; ring
  rw [e, Int.floor_intCast_add, Int.floor_neg]
  have hc : ⌈(2 : ℝ) ^ k * y⌉ = ⌊(2 : ℝ) ^ k * y⌋ + 1 := by
    rw [Int.ceil_eq_iff]; push_cast
    have h1 : (⌊(2 : ℝ) ^ k * y⌋ : ℝ) < 2 ^ k * y :=
      lt_of_le_of_ne (Int.floor_le _) (fun h => hirr.ne_int _ h.symm)
    exact ⟨by linarith, (Int.lt_floor_add_one _).le⟩
  rw [hc]; omega

lemma bdig_dyadic (X n k : ℕ) (hk : n < k) : bdig ((X : ℝ) / 2 ^ n) k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = n + j + 1 := ⟨k - n - 1, by omega⟩
  unfold bdig
  have e : (2 : ℝ) ^ (n + j + 1) * ((X : ℝ) / 2 ^ n) = ((2 * (X * 2 ^ j) : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e, Int.floor_natCast]; push_cast; exact Int.mul_emod_right _ _

lemma bdig_zero (k : ℕ) : bdig 0 k = 0 := by simp [bdig]

lemma cnt_zero_real (N : ℕ) : cnt 0 N = 0 := by simp [cnt, bdig_zero]

lemma bdig_add_pow_gt (z : ℝ) {n k : ℕ} (hk : n < k) : bdig (z + 1 / 2 ^ n) k = bdig z k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = n + j + 1 := ⟨k - n - 1, by omega⟩
  unfold bdig
  have e : (2 : ℝ) ^ (n + j + 1) * (z + 1 / 2 ^ n) = 2 ^ (n + j + 1) * z + ((2 * 2 ^ j : ℤ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e, Int.floor_add_intCast]; omega

/-- Setting a zero digit to one raises the count by at most one. -/
lemma cnt_add_pow {z : ℝ} {n : ℕ} (hz : bdig z n = 0) (N : ℕ) :
    cnt (z + 1 / 2 ^ n) N ≤ cnt z N + 1 := by
  set w := z + 1 / 2 ^ n
  have hF : ⌊(2 : ℝ) ^ n * w⌋ = ⌊(2 : ℝ) ^ n * z⌋ + 1 := by
    rw [show (2 : ℝ) ^ n * w = 2 ^ n * z + 1 by simp only [w]; field_simp]
    exact Int.floor_add_one _
  have hag := cnt_agree (floor_agree (z := z) (w := w) hz (by rw [hF]; omega) (by rw [hF]))
  have : ∀ N, cnt w N ≤ cnt z N + 1 ∧ (N < n → cnt w N = cnt z N) := by
    intro N
    induction N with
    | zero => simp [cnt_zero]
    | succ N ih =>
      refine ⟨?_, fun h => hag _ h⟩
      rcases lt_trichotomy (N + 1) n with h | h | h
      · rw [hag _ h]; omega
      · rw [cnt_succ, cnt_succ, ih.2 (by omega), h, hz]
        have := bdig_le_one w n; omega
      · rw [cnt_succ, cnt_succ, bdig_add_pow_gt z h]; have := ih.1; omega
  exact (this N).1

/-! ## Every binary expansion has infinitely many zeros -/

lemma exists_zero_after (z : ℝ) (M : ℕ) : ∃ k, M < k ∧ bdig z k = 0 := by
  by_contra hcon
  push Not at hcon
  have hone : ∀ k, M < k → bdig z k = 1 := fun k hk => by
    have := hcon k hk; have := bdig_nonneg z k; have := bdig_le_one z k; omega
  have hrec : ∀ t, ⌊(2 : ℝ) ^ (M + t) * z⌋ + 1 = 2 ^ t * (⌊(2 : ℝ) ^ M * z⌋ + 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [← add_assoc, floor_succ, hone _ (by omega), pow_succ]; linarith
  set F := ⌊(2 : ℝ) ^ M * z⌋
  set δ := (F : ℝ) + 1 - 2 ^ M * z
  have hδ : 0 < δ := by have := Int.lt_floor_add_one ((2 : ℝ) ^ M * z); simp only [δ, F]; linarith
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (1 / δ) (by norm_num : (1 : ℝ) < 2)
  have h1 := Int.floor_le ((2 : ℝ) ^ (M + t) * z)
  have h2 : ((⌊(2 : ℝ) ^ (M + t) * z⌋ : ℤ) : ℝ) = 2 ^ t * ((F : ℝ) + 1) - 1 := by
    have := congrArg (fun x : ℤ => (x : ℝ)) (hrec t); push_cast at this; linarith
  rw [h2, pow_add] at h1
  have e : (2 : ℝ) ^ t * δ = 2 ^ t * ((F : ℝ) + 1) - 2 ^ M * 2 ^ t * z := by simp only [δ]; ring
  have : 1 < 2 ^ t * δ := by rw [div_lt_iff₀ hδ] at ht; linarith
  linarith

lemma ones_run {z : ℝ} {M : ℕ} : ∀ t, (∀ k, M < k → k ≤ M + t → bdig z k = 1) →
    cnt z (M + t) = cnt z M + t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    intro h
    rw [← add_assoc, cnt_succ, ih (fun k h1 h2 => h k h1 (by omega)), h (M + t + 1) (by omega) (by omega)]
    push_cast; ring

/-- After any position `M` there is a zero digit `m` with `f_{m-1} ≥ f_M`. -/
lemma exists_zero_freq (z : ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ m, M < m ∧ bdig z m = 0 ∧ freq z M ≤ freq z (m - 1) := by
  classical
  have hex := exists_zero_after z M
  obtain ⟨hm1, hm2⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hm1, hm2, ?_⟩
  set m := Nat.find hex
  set t := m - 1 - M
  have hrun : ∀ k, M < k → k ≤ M + t → bdig z k = 1 := by
    intro k hk1 hk2
    have hmin := Nat.find_min hex (show k < m by omega)
    have := bdig_nonneg z k; have := bdig_le_one z k
    by_contra hne; exact hmin ⟨hk1, by omega⟩
  have hc := ones_run t hrun
  rw [show m - 1 = M + t by omega]
  have hcM := cnt_le z M; have hc0 := cnt_nonneg z M
  simp only [freq, hc]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (cnt z M : ℝ) ≤ M := by exact_mod_cast hcM
  push_cast; nlinarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]

/-! ## (TU) forces upper frequency `≥ 1/2` at `y` whenever `y²` is dyadic (Isaac's §2) -/

/-- [Isa06, Theorem 2], localised: under (TU), if `1/2 < y < 1` is irrational with `y²` dyadic,
then `f_N(y) ≥ 2/5` for infinitely many `N`.  The pair is `ω₁ = y/2 - 1/4`, `ω₂ = 1 - y/8`:
`ω₂² - ω₁²` is dyadic, `ω₁` carries the digits of `y`, `ω₂` their complements. -/
@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
lemma frequently_freq_ge (hTU : TUfull) {y : ℝ} (hy : Irrational y) (hy1 : 1 / 2 < y)
    (hy2 : y < 1) {a : ℤ} {m : ℕ} (hsq : y ^ 2 = a / 2 ^ m) :
    ∃ᶠ N in atTop, (2 : ℝ) / 5 ≤ freq y N := by
  have h1 : Tendsto (fun N => freq (y / 2 - 1 / 4) N - freq y N) atTop (𝓝 0) :=
    tendsto_freq_sub (s := 1) (K := 2) (fun k hk => bdig_omega1 y k hk)
  have h2 : Tendsto (fun N => freq (1 - y / 8) N + freq y N) atTop (𝓝 1) :=
    tendsto_freq_add (s := 3) (K := 0) (fun k _ => bdig_omega2 hy k)
  have hw1 : 0 < y / 2 - 1 / 4 := by linarith
  have hw2 : 0 < 1 - y / 8 := by linarith
  have key := hTU ((y / 2 - 1 / 4) ^ 2) ((1 - y / 8) ^ 2) (by positivity) (by nlinarith)
    (by positivity) (by nlinarith) ?irr ?tail
  case irr =>
    rintro ⟨q, hq⟩
    apply hy
    refine ⟨(a : ℚ) / 2 ^ m + 1 / 4 - 4 * q, ?_⟩
    push_cast; rw [hq, ← hsq]; ring
  case tail =>
    refine ⟨15 * 2 ^ (m + 2) - 15 * a, m + 6, ?_⟩
    rw [show (1 - y / 8) ^ 2 - (y / 2 - 1 / 4) ^ 2 = 15 / 16 - 15 / 64 * y ^ 2 by ring, hsq]
    push_cast; field_simp; ring
  rw [Real.sqrt_sq hw1.le, Real.sqrt_sq hw2.le] at key
  by_contra hcon
  rw [not_frequently] at hcon
  have e1 := h1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 20 by norm_num))
  have e2 := h2.eventually (lt_mem_nhds (show (19 / 20 : ℝ) < 1 by norm_num))
  have L1 : limsup (freq (y / 2 - 1 / 4)) atTop ≤ 9 / 20 :=
    limsup_le_of_le (isCobounded_freq _) (by
      filter_upwards [hcon, e1] with N h h'; push Not at h; linarith)
  have L2 : 11 / 20 ≤ limsup (freq (1 - y / 8)) atTop :=
    le_limsup_of_frequently_le (by
      refine Eventually.frequently ?_
      filter_upwards [hcon, e2] with N h h'; push Not at h; linarith) (isBounded_freq _)
  rw [key] at L1; linarith

/-! ## Proof A: the bootstrap [I1 §1.1] -/

/-- `y(x) = √(x² + 1/4)`, so that `y(x)²` and `x²` have the same tail. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
noncomputable def ysq (x : ℝ) : ℝ := √(x ^ 2 + 1 / 4)

lemma ysq_sq (x : ℝ) : ysq x ^ 2 = x ^ 2 + 1 / 4 := Real.sq_sqrt (by positivity)

lemma half_lt_ysq {x : ℝ} (hx : 0 < x) : 1 / 2 < ysq x :=
  Real.lt_sqrt (by norm_num) |>.2 (by nlinarith)

lemma ysq_lt_one {x : ℝ} (hx0 : 0 < x) (hx : x < 1 / 4) : ysq x < 1 :=
  (Real.sqrt_lt' one_pos).2 (by nlinarith)

lemma ysq_mono {x x' : ℝ} (h0 : 0 ≤ x) (h : x ≤ x') : ysq x ≤ ysq x' :=
  Real.sqrt_le_sqrt (by nlinarith)

/-- `X² + 4^q` is not a square when `X` is odd and `X < 2^{q-1}`. -/
@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
lemma not_isSquare_add_four_pow (q X : ℕ) (hq : 2 ≤ q) (hX : Odd X) (hXlt : X < 2 ^ (q - 1)) :
    ¬ IsSquare (X ^ 2 + 4 ^ q) := by
  rintro ⟨Z, hZ⟩
  rw [show (4 : ℕ) ^ q = 2 ^ (2 * q) by rw [pow_mul]; norm_num] at hZ
  have hpos : 0 < 2 ^ (2 * q) := by positivity
  have hXZ : X < Z := by nlinarith
  have hprod : (Z - X) * (Z + X) = 2 ^ (2 * q) := by
    have hZ' : (X : ℤ) ^ 2 + 2 ^ (2 * q) = Z * Z := by exact_mod_cast hZ
    zify [hXZ.le]; linear_combination -hZ'
  obtain ⟨a, -, hA⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hprod)
  obtain ⟨b, -, hB⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hprod)
  rw [hA, hB, ← pow_add] at hprod
  have hab := Nat.pow_right_injective le_rfl hprod
  obtain ⟨r, hr⟩ := hX
  rcases a with _ | _ | a
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [pow_succ] at hB; simp at hA; omega
  · obtain ⟨c, rfl⟩ : ∃ c, b = 2 * (q - 1) + 1 := ⟨0, by omega⟩
    rw [pow_succ, pow_mul] at hB
    simp only [zero_add, pow_one] at hA
    have hP : 2 ≤ 2 ^ (q - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, show (4 : ℕ) ^ (q - 1) = 2 ^ (q - 1) * 2 ^ (q - 1) by
      rw [← mul_pow]; norm_num] at hB
    have : X + 1 = 2 ^ (q - 1) * 2 ^ (q - 1) := by omega
    nlinarith
  · rcases b with _ | _ | b
    · simp at hB; rw [pow_succ, pow_succ] at hA; omega
    · simp at hB; rw [pow_succ, pow_succ] at hA; omega
    · rw [pow_succ, pow_succ] at hA hB; omega

@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
lemma ysq_dyadic_irrational (n X : ℕ) (hn : 3 ≤ n) (hX : Odd X) (hXlt : X < 2 ^ (n - 2)) :
    Irrational (ysq ((X : ℝ) / 2 ^ n)) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  have hns := not_isSquare_add_four_pow q X (by omega) hX (by rwa [show q + 1 - 2 = q - 1 by omega] at hXlt)
  have hirr := (irrational_sqrt_natCast_iff.2 hns).div_natCast (m := 2 ^ (q + 1)) (by positivity)
  convert hirr using 1
  unfold ysq
  have e : ((X : ℝ) / 2 ^ (q + 1)) ^ 2 + 1 / 4 =
      ((X ^ 2 + 4 ^ q : ℕ) : ℝ) / ((2 : ℝ) ^ (q + 1)) ^ 2 := by
    push_cast
    rw [show (4 : ℝ) ^ q = (2 ^ q) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    field_simp; ring
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  push_cast; rfl

/-- One step of the bootstrap: under (TU), past any bound `B` there is a zero digit `m` of
`y(X/2ⁿ)` with `f_{m-1} ≥ 2/5`. -/
@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
lemma bootstrap_step (hTU : TUfull) (n X B : ℕ) (hn : 3 ≤ n) (hX : Odd X)
    (hXlt : X < 2 ^ (n - 2)) :
    ∃ m, B ≤ m ∧ bdig (ysq ((X : ℝ) / 2 ^ n)) m = 0 ∧
      (2 : ℝ) / 5 ≤ freq (ysq ((X : ℝ) / 2 ^ n)) (m - 1) := by
  set x := (X : ℝ) / 2 ^ n
  have hx0 : 0 < x := by
    have : 0 < X := hX.pos
    positivity
  have hx1 : x < 1 / 4 := by
    have h4 : (2 : ℝ) ^ n = 2 ^ (n - 2) * 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have : (X : ℝ) < 2 ^ (n - 2) := by exact_mod_cast hXlt
    simp only [x]; rw [div_lt_iff₀ (by positivity), h4]; linarith
  have hfr := frequently_freq_ge hTU (ysq_dyadic_irrational n X hn hX hXlt) (half_lt_ysq hx0)
    (ysq_lt_one hx0 hx1) (a := 4 * X ^ 2 + 2 ^ (2 * n)) (m := 2 * n + 2) (by
      rw [ysq_sq]; push_cast; field_simp; ring)
  obtain ⟨M, hM, hfM⟩ := Filter.frequently_atTop.1 hfr (B + 1)
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_zero_freq (ysq x) (show 0 < M by omega)
  exact ⟨m, by omega, hm2, hfM.trans hm3⟩

lemma two_div_pow_le {a b : ℕ} (h : b + 1 ≤ a) : (2 : ℝ) / 2 ^ a ≤ 1 / 2 ^ b := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (2 : ℝ) ^ (b + 1) ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) h
  rw [pow_succ] at this; linarith

section Construction

/-- The sparse sequence `(nⱼ, Xⱼ)`, `xⱼ = Xⱼ/2^{nⱼ} = ∑_{i ≤ j} 2^{-nᵢ}`, driven by a choice
function `nxt` for the next position. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
def seqA (nxt : ℕ → ℕ → ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | j + 1 =>
    (nxt (seqA nxt j).1 (seqA nxt j).2 (4 * (j + 1) * (seqA nxt j).1 + 4),
     (seqA nxt j).2 *
       2 ^ (nxt (seqA nxt j).1 (seqA nxt j).2 (4 * (j + 1) * (seqA nxt j).1 + 4) - (seqA nxt j).1)
       + 1)

/-- `nⱼ`. -/
def nn (nxt : ℕ → ℕ → ℕ → ℕ) (j : ℕ) : ℕ := (seqA nxt j).1

/-- `Xⱼ`. -/
def XX (nxt : ℕ → ℕ → ℕ → ℕ) (j : ℕ) : ℕ := (seqA nxt j).2

variable {nxt : ℕ → ℕ → ℕ → ℕ}
  (hnB : ∀ n X B, 3 ≤ n → Odd X → X < 2 ^ (n - 2) → B ≤ nxt n X B)
include hnB


omit hnB in
lemma nn_succ (j : ℕ) : (nn nxt (j + 1)) = nxt (nn nxt j) (XX nxt j) (4 * (j + 1) * (nn nxt j) + 4) := rfl

omit hnB in
lemma XX_succ (j : ℕ) : (XX nxt (j + 1)) = (XX nxt j) * 2 ^ ((nn nxt (j + 1)) - nn nxt j) + 1 := rfl

lemma inv_seq (j : ℕ) : 3 ≤ (nn nxt j) ∧ Odd (XX nxt j) ∧ (XX nxt j) < 2 ^ ((nn nxt j) - 2) := by
  induction j with
  | zero => simp [nn, XX, seqA]
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hm := hnB _ _ (4 * (j + 1) * (nn nxt j) + 4) h1 h2 h3
    rw [← nn_succ (nxt := nxt) j] at hm
    set n := nn nxt j; set m := nn nxt (j + 1); set X := XX nxt j
    rw [XX_succ]
    have hmn : n + 2 ≤ m := by
      have : n ≤ 4 * (j + 1) * n := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    have hp : 2 ^ (n - 2) * 2 ^ (m - n) = 2 ^ (m - 2) := by rw [← pow_add]; congr 1; omega
    have h2' : 2 ≤ 2 ^ (m - n) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m - n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_, by nlinarith [Nat.mul_le_mul_right (2 ^ (m - n)) (show X + 1 ≤ 2 ^ (n - 2) from h3)]⟩
    exact (((Nat.even_pow.2 ⟨even_two, by omega⟩).mul_left X)).add_one

lemma nn_succ_ge (j : ℕ) : 4 * (j + 1) * (nn nxt j) + 4 ≤ (nn nxt (j + 1)) := by
  obtain ⟨h1, h2, h3⟩ := inv_seq hnB j
  exact hnB _ _ _ h1 h2 h3

lemma nn_add_two_le (j : ℕ) : nn nxt j + 2 ≤ nn nxt (j + 1) := by
  have h := nn_succ_ge hnB j
  have : nn nxt j ≤ 4 * (j + 1) * nn nxt j := Nat.le_mul_of_pos_left _ (by positivity)
  omega

lemma nn_ge (j : ℕ) : 3 * 4 ^ j ≤ (nn nxt j) := by
  induction j with
  | zero => simp [nn, seqA]
  | succ j ih => have := nn_succ_ge hnB j; rw [pow_succ]; nlinarith

/-- `xⱼ = Xⱼ / 2^{nⱼ}`. -/
noncomputable def xs (nxt : ℕ → ℕ → ℕ → ℕ) (j : ℕ) : ℝ := (XX nxt j : ℝ) / 2 ^ nn nxt j

omit hnB in
lemma xs_zero : xs nxt 0 = 0 + 1 / 2 ^ 3 := by simp [xs, nn, XX, seqA]

lemma xs_succ (j : ℕ) : xs nxt (j + 1) = xs nxt j + 1 / 2 ^ (nn nxt (j + 1)) := by
  have := nn_add_two_le hnB j
  unfold xs; rw [XX_succ]; push_cast
  rw [show (2 : ℝ) ^ (nn nxt (j + 1)) = 2 ^ (nn nxt j) * 2 ^ ((nn nxt (j + 1)) - nn nxt j) by
    rw [← pow_add]; congr 1; omega]
  field_simp

lemma xs_pos (j : ℕ) : 0 < xs nxt j := by
  have := (inv_seq hnB j).2.1.pos; unfold xs; positivity

lemma xs_lt (j : ℕ) : xs nxt j < 1 / 4 := by
  obtain ⟨h1, -, h3⟩ := inv_seq hnB j
  have h4 : (2 : ℝ) ^ (nn nxt j) = 2 ^ ((nn nxt j) - 2) * 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have : ((XX nxt j : ℕ) : ℝ) < 2 ^ ((nn nxt j) - 2) := by exact_mod_cast h3
  unfold xs; rw [div_lt_iff₀ (by positivity), h4]; linarith

lemma xs_mono : Monotone (xs nxt) :=
  monotone_nat_of_le_succ fun j => by rw [xs_succ hnB]; have : (0 : ℝ) < 1 / 2 ^ (nn nxt (j + 1)) := by positivity
                                      linarith

lemma xs_tail (j : ℕ) : ∀ i, j ≤ i →
    xs nxt i ≤ xs nxt j + 2 / 2 ^ (nn nxt (j + 1)) - 2 / 2 ^ (nn nxt (i + 1)) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => linarith
  | succ i hi ih =>
    rw [xs_succ hnB]
    have := two_div_pow_le (a := nn nxt (i + 1 + 1)) (b := nn nxt (i + 1)) (by
      have := nn_add_two_le hnB (i + 1); omega)
    have e : (2 : ℝ) / 2 ^ (nn nxt (i + 1)) = 2 * (1 / 2 ^ (nn nxt (i + 1))) := by ring
    linarith

/-- The limit point `x = sup xⱼ = ∑ 2^{-nⱼ}`. -/
noncomputable def xlim (nxt : ℕ → ℕ → ℕ → ℕ) : ℝ := ⨆ j, xs nxt j

lemma bdd_xs : BddAbove (Set.range (xs nxt)) := ⟨1 / 4, by rintro _ ⟨j, rfl⟩; exact (xs_lt hnB j).le⟩

lemma xs_le_xlim (j : ℕ) : xs nxt j ≤ xlim nxt := le_ciSup (bdd_xs hnB) j

lemma xs_lt_xlim (j : ℕ) : xs nxt j < xlim nxt := by
  have := xs_le_xlim hnB (j + 1); rw [xs_succ hnB] at this
  have : (0 : ℝ) < 1 / 2 ^ (nn nxt (j + 1)) := by positivity
  linarith

lemma xlim_sub_le (j : ℕ) : xlim nxt - xs nxt j ≤ (3 / 2) / 2 ^ (nn nxt (j + 1)) := by
  have hb : xlim nxt ≤ xs nxt (j + 1) + 2 / 2 ^ (nn nxt (j + 1 + 1)) := by
    refine ciSup_le fun i => ?_
    rcases le_total i (j + 1) with h | h
    · have := xs_mono hnB h; have : (0 : ℝ) < 2 / 2 ^ (nn nxt (j + 1 + 1)) := by positivity
      linarith
    · have := xs_tail hnB (j + 1) i h; have : (0 : ℝ) < 2 / 2 ^ (nn nxt (i + 1)) := by positivity
      linarith
  rw [xs_succ hnB] at hb
  have h2 := two_div_pow_le (a := nn nxt (j + 1 + 1)) (b := (nn nxt (j + 1)) + 1) (by
    have := nn_add_two_le hnB (j + 1); omega)
  have e : (1 : ℝ) / 2 ^ ((nn nxt (j + 1)) + 1) = (1 / 2) / 2 ^ (nn nxt (j + 1)) := by
    rw [pow_succ]; field_simp
  rw [e] at h2
  have e2 : (3 / 2 : ℝ) / 2 ^ (nn nxt (j + 1)) = 1 / 2 ^ (nn nxt (j + 1)) + (1 / 2) / 2 ^ (nn nxt (j + 1)) := by
    ring
  linarith

lemma xlim_pos : 0 < xlim nxt := (xs_pos hnB 0).trans (xs_lt_xlim hnB 0)

lemma xlim_lt : xlim nxt < 1 / 4 := by
  have h := xlim_sub_le hnB 0
  have h1 : (2 : ℝ) ^ 8 ≤ 2 ^ (nn nxt (0 + 1)) :=
    pow_le_pow_right₀ (by norm_num) (by have := nn_succ_ge hnB 0; have := (inv_seq hnB 0).1; omega)
  have h2 : (3 / 2 : ℝ) / 2 ^ (nn nxt (0 + 1)) ≤ (3 / 2) / 2 ^ 8 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
  have h3 : xs nxt 0 = 1 / 8 := by rw [xs_zero]; norm_num
  linarith

lemma sq_xlim_sub (j : ℕ) : xlim nxt ^ 2 - xs nxt j ^ 2 ≤ (3 / 4) / 2 ^ (nn nxt (j + 1)) := by
  have h1 := xlim_sub_le hnB j; have h2 := xs_lt_xlim hnB j
  have h3 := xlim_lt hnB; have h4 := xs_lt hnB j; have h5 := xs_pos hnB j
  have e : xlim nxt ^ 2 - xs nxt j ^ 2 = (xlim nxt - xs nxt j) * (xlim nxt + xs nxt j) := by ring
  have e2 : (3 / 4 : ℝ) / 2 ^ (nn nxt (j + 1)) = (3 / 2) / 2 ^ (nn nxt (j + 1)) * (1 / 2) := by ring
  rw [e, e2]
  exact mul_le_mul h1 (by linarith) (by linarith) (by positivity)

/-- `x²` is a Liouville number, hence irrational. -/
@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
lemma liouville_sq_xlim : Liouville (xlim nxt ^ 2) := by
  intro k
  have hn3 := (inv_seq hnB k).1
  refine ⟨((XX nxt k) ^ 2 : ℕ), 2 ^ (2 * nn nxt k), ?_, ?_, ?_⟩
  · have : (2 : ℤ) ^ 1 ≤ 2 ^ (2 * nn nxt k) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  · have h := xs_lt_xlim hnB k; have h0 := xs_pos hnB k
    have e : (((XX nxt k) ^ 2 : ℕ) : ℤ) / ((2 ^ (2 * nn nxt k) : ℤ) : ℝ) = xs nxt k ^ 2 := by
      unfold xs; push_cast; ring
    rw [e]; intro h'; nlinarith
  · have e : (((XX nxt k) ^ 2 : ℕ) : ℤ) / ((2 ^ (2 * nn nxt k) : ℤ) : ℝ) = xs nxt k ^ 2 := by
      unfold xs; push_cast; ring
    rw [e]
    have h := xs_lt_xlim hnB k; have h0 := xs_pos hnB k
    rw [abs_of_pos (by nlinarith)]
    have hs := sq_xlim_sub hnB k
    have hge : 2 * k * (nn nxt k) ≤ (nn nxt (k + 1)) := by have := nn_succ_ge hnB k; nlinarith
    have : (1 : ℝ) / 2 ^ (nn nxt (k + 1)) ≤ 1 / (((2 ^ (2 * nn nxt k) : ℤ) : ℝ)) ^ k := by
      push_cast; rw [← pow_mul]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by nlinarith))
    have : (3 / 4 : ℝ) / 2 ^ (nn nxt (k + 1)) < 1 / 2 ^ (nn nxt (k + 1)) :=
      div_lt_div_of_pos_right (by norm_num) (by positivity)
    linarith

lemma cnt_xs_le (j N : ℕ) : cnt (xs nxt j) N ≤ j + 1 := by
  induction j generalizing N with
  | zero => rw [xs_zero]; have := cnt_add_pow (bdig_zero 3) N; rw [cnt_zero_real] at this; simpa
  | succ j ih =>
    rw [xs_succ hnB]
    have hz : bdig (xs nxt j) (nn nxt (j + 1)) = 0 :=
      bdig_dyadic _ _ _ (by have := nn_succ_ge hnB j; nlinarith)
    have := cnt_add_pow hz N; have := ih N; push_cast; omega

lemma cnt_xlim_eq (j N : ℕ) (hN : N < (nn nxt (j + 1)) - 1) : cnt (xlim nxt) N = cnt (xs nxt j) N := by
  have hge := nn_succ_ge hnB j
  set m := (nn nxt (j + 1)) - 1
  have hz : bdig (xs nxt j) m = 0 := bdig_dyadic _ _ _ (by have := nn_add_two_le hnB j; omega)
  refine cnt_agree (floor_agree hz ?_ ?_) N hN
  · exact Int.floor_mono (mul_le_mul_of_nonneg_left (xs_le_xlim hnB j) (by positivity))
  · rw [← Int.floor_add_one]
    refine Int.floor_mono ?_
    have h := xlim_sub_le hnB j
    have e : (2 : ℝ) ^ (nn nxt (j + 1)) = 2 ^ m * 2 := by rw [← pow_succ]; congr 1; omega
    rw [e] at h
    have : (2 : ℝ) ^ m * ((3 / 2) / (2 ^ m * 2)) = 3 / 4 := by field_simp; ring
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]

omit hnB in
lemma succ_sq_le (j : ℕ) : (j + 1) ^ 2 ≤ 3 * 4 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    calc (j + 1 + 1) ^ 2 ≤ (2 * (j + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (j + 1) ^ 2 := by ring
      _ ≤ 4 * (3 * 4 ^ j) := by omega
      _ = 3 * 4 ^ (j + 1) := by ring

lemma cnt_xlim_sq_le (N : ℕ) : cnt (xlim nxt) N ^ 2 ≤ N + 1 := by
  classical
  have hex : ∃ j, N < (nn nxt (j + 1)) - 1 := ⟨N, by
    have := nn_ge hnB (N + 1); have : N + 2 ≤ 4 ^ (N + 1) := by
      have := Nat.lt_pow_self (n := N + 1) (show 1 < 4 by norm_num); omega
    omega⟩
  have hj := Nat.find_spec hex
  rw [cnt_xlim_eq hnB _ _ hj]
  have hc := cnt_xs_le hnB (Nat.find hex) N
  have hc0 := cnt_nonneg (xs nxt (Nat.find hex)) N
  rcases hfind : Nat.find hex with _ | j
  · rw [hfind] at hc hc0; simp at hc; nlinarith
  · rw [hfind] at hc hc0
    have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    have h1 := nn_ge hnB (j + 1); have h2 := succ_sq_le (j + 1)
    have : ((j + 1 + 1 : ℕ) : ℤ) ^ 2 ≤ N + 1 := by exact_mod_cast (by omega : (j + 1 + 1) ^ 2 ≤ N + 1)
    push_cast at this hc
    nlinarith

@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
lemma tendsto_freq_xlim : Tendsto (freq (xlim nxt)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => √(2 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).sqrt
  refine squeeze_zero' (Eventually.of_forall fun N => freq_nonneg _ N) ?_ hs
  filter_upwards [eventually_ge_atTop 1] with N hN
  apply Real.le_sqrt_of_sq_le
  have hc := cnt_xlim_sq_le hnB N
  have hc' : ((cnt (xlim nxt) N : ℤ) : ℝ) ^ 2 ≤ N + 1 := by exact_mod_cast hc
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold freq
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
lemma frequently_freq_ylim (hnz : ∀ n X B : ℕ, 3 ≤ n → Odd X → X < 2 ^ (n - 2) →
      bdig (ysq ((X : ℝ) / 2 ^ n)) (nxt n X B) = 0)
    (hnf : ∀ n X B : ℕ, 3 ≤ n → Odd X → X < 2 ^ (n - 2) →
      (2 : ℝ) / 5 ≤ freq (ysq ((X : ℝ) / 2 ^ n)) (nxt n X B - 1)) :
    ∃ᶠ N in atTop, (2 : ℝ) / 5 ≤ freq (ysq (xlim nxt)) N := by
  refine Filter.frequently_atTop.2 fun M => ⟨(nn nxt (M + 1)) - 1, ?_, ?_⟩
  · have := nn_ge hnB (M + 1)
    have : M + 2 ≤ 4 ^ (M + 1) := by
      have := Nat.lt_pow_self (n := M + 1) (show 1 < 4 by norm_num); omega
    omega
  obtain ⟨h1, h2, h3⟩ := inv_seq hnB M
  have hz := hnz _ _ (4 * (M + 1) * (nn nxt M) + 4) h1 h2 h3
  have hf := hnf _ _ (4 * (M + 1) * (nn nxt M) + 4) h1 h2 h3
  rw [← nn_succ (nxt := nxt) M] at hz hf
  change bdig (ysq (xs nxt M)) _ = 0 at hz
  change _ ≤ freq (ysq (xs nxt M)) _ at hf
  set m := nn nxt (M + 1)
  have hge : 1 ≤ m := by have := nn_succ_ge hnB M; omega
  have hle : ysq (xs nxt M) ≤ ysq (xlim nxt) := ysq_mono (xs_pos hnB M).le (xs_le_xlim hnB M)
  have hdiff : ysq (xlim nxt) - ysq (xs nxt M) ≤ (3 / 4) / 2 ^ m := by
    have hs := sq_xlim_sub hnB M
    have e : ysq (xlim nxt) ^ 2 - ysq (xs nxt M) ^ 2 = xlim nxt ^ 2 - xs nxt M ^ 2 := by
      rw [ysq_sq, ysq_sq]; ring
    have hy1 := half_lt_ysq (xlim_pos hnB); have hy2 := half_lt_ysq (xs_pos hnB M)
    nlinarith
  have ha : ⌊(2 : ℝ) ^ m * ysq (xs nxt M)⌋ ≤ ⌊(2 : ℝ) ^ m * ysq (xlim nxt)⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_left hle (by positivity))
  have hb : ⌊(2 : ℝ) ^ m * ysq (xlim nxt)⌋ ≤ ⌊(2 : ℝ) ^ m * ysq (xs nxt M)⌋ + 1 := by
    rw [← Int.floor_add_one]; refine Int.floor_mono ?_
    have : (2 : ℝ) ^ m * ((3 / 4) / 2 ^ m) = 3 / 4 := by field_simp
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
  have hag := cnt_agree (floor_agree hz ha hb) (m - 1) (by omega)
  simp only [freq] at hf ⊢; rwa [hag]

end Construction

/-- **(TU) is false** — proof A, the bootstrap of [I1 §1.1] as corrected in the report
(`plans/report-sqrtnorm.html` §2.1).  Already the full-sequence form fails. -/
@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
theorem not_TUfull_bootstrap : ¬ TUfull := by
  intro hTU
  choose! nxt hnB hnz hnf using bootstrap_step hTU
  set x := xlim nxt
  have hx0 := xlim_pos hnB; have hx1 := xlim_lt hnB
  have key := hTU (x ^ 2) (x ^ 2 + 1 / 4) (by positivity) (by nlinarith) (by positivity)
    (by nlinarith) (liouville_sq_xlim hnB).irrational ⟨1, 2, by norm_num⟩
  rw [Real.sqrt_sq hx0.le, (tendsto_freq_xlim hnB).limsup_eq] at key
  have h := le_limsup_of_frequently_le (frequently_freq_ylim hnB hnz hnf) (isBounded_freq _)
  change _ ≤ limsup (freq (√(x ^ 2 + 1 / 4))) atTop at h
  rw [← key] at h; norm_num at h

/-- **(TU) is false** (proof A). -/
@[category research solved, AMS 11, ref "Isa06", group "isaac_tu"]
theorem not_TU_bootstrap : ¬ TU := fun h => not_TUfull_bootstrap h.full

/-! ## Proof B: Fourier decay of a nonlinear image of a self-similar measure -/

section ProofB

open MeasureTheory

/-- The fair coin on `Fin 2`. -/
noncomputable def coin : Measure (Fin 2) := (PMF.uniformOfFintype (Fin 2)).toMeasure

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

lemma coin_singleton (i : Fin 2) : coin {i} = 2⁻¹ := by
  rw [coin, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
    PMF.uniformOfFintype_apply]
  simp

/-- `ι ↦ ∑ ιₖ 8^{-(k+1)}`: the points whose binary digits are `0` off the multiples of `3`. -/
noncomputable def cantor8 (ι : ℕ → Fin 2) : ℝ := ∑' k, ((ι k : ℕ) : ℝ) * (1 / 8 : ℝ) ^ (k + 1)

/-- The Cantor measure of ratio `1/8` (fair coin weights), a homogeneous self-similar measure
`μ^p_{a,t}` with `a = 1/8`, `t = (0, 1)`, `p = (1/2, 1/2)`. -/
@[category API, AMS 11 28, ref "MS18", group "isaac_tu"]
noncomputable abbrev mu8 : Measure ℝ := MS.ssMeasure coin (fun i => ((i : ℕ) : ℝ)) (1 / 8)

lemma mu8_eq : mu8 = (Measure.infinitePi (fun _ : ℕ => coin)).map cantor8 := rfl

lemma fin2_le_one (i : Fin 2) : ((i : ℕ) : ℝ) ≤ 1 := by
  have := i.isLt; exact_mod_cast (by omega : (i : ℕ) ≤ 1)

lemma summable_geom8 : Summable (fun k : ℕ => (1 / 8 : ℝ) ^ (k + 1)) :=
  (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))

lemma tsum_geom8 : ∑' k : ℕ, (1 / 8 : ℝ) ^ (k + 1) = 1 / 7 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

lemma summable_c8 (ι : ℕ → Fin 2) : Summable (fun k => ((ι k : ℕ) : ℝ) * (1 / 8 : ℝ) ^ (k + 1)) :=
  Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => by have := fin2_le_one (ι k); nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 8) (k + 1)])
    summable_geom8

lemma measurable_coord (k : ℕ) : Measurable (fun ι : ℕ → Fin 2 => ((ι k : ℕ) : ℝ)) :=
  (measurable_of_finite (fun i : Fin 2 => ((i : ℕ) : ℝ))).comp (measurable_pi_apply k)

lemma measurable_cantor8 : Measurable cantor8 := by
  have hm : ∀ n, Measurable
      (fun ι : ℕ → Fin 2 => ∑ k ∈ Finset.range n, ((ι k : ℕ) : ℝ) * (1 / 8 : ℝ) ^ (k + 1)) :=
    fun n => Finset.measurable_sum _ fun k _ => (measurable_coord k).mul_const _
  have hl : Tendsto
      (fun n (ι : ℕ → Fin 2) => ∑ k ∈ Finset.range n, ((ι k : ℕ) : ℝ) * (1 / 8 : ℝ) ^ (k + 1))
      atTop (𝓝 cantor8) :=
    tendsto_pi_nhds.2 fun ι => (summable_c8 ι).hasSum.tendsto_sum_nat
  exact measurable_of_tendsto_metrizable hm hl

/-- Integer part of `8ᵐ · cantor8 ι`. -/
def A8 (ι : ℕ → Fin 2) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 8 * A8 ι m + ι m

/-- Fractional remainder of `8ᵐ · cantor8 ι`. -/
noncomputable def T8 (ι : ℕ → Fin 2) (m : ℕ) : ℝ :=
  ∑' k, ((ι (m + k) : ℕ) : ℝ) * (1 / 8 : ℝ) ^ (k + 1)

lemma T8_nonneg (ι : ℕ → Fin 2) (m : ℕ) : 0 ≤ T8 ι m := tsum_nonneg fun k => by positivity

lemma T8_le (ι : ℕ → Fin 2) (m : ℕ) : T8 ι m ≤ 1 / 7 := by
  rw [T8, ← tsum_geom8]
  exact Summable.tsum_le_tsum (fun k => by
    have := fin2_le_one (ι (m + k)); nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 8) (k + 1)])
    (summable_c8 (fun k => ι (m + k))) summable_geom8

lemma pow8_cantor8 (ι : ℕ → Fin 2) (m : ℕ) : (8 : ℝ) ^ m * cantor8 ι = A8 ι m + T8 ι m := by
  induction m with
  | zero => simp [A8, T8, cantor8]
  | succ m ih =>
    have hs : T8 ι m = ((ι m : ℕ) : ℝ) * (1 / 8) + 1 / 8 * T8 ι (m + 1) := by
      rw [T8, (summable_c8 (fun k => ι (m + k))).tsum_eq_zero_add, T8, ← tsum_mul_left]
      congr 1
      · simp
      · congr 1; ext k; rw [show m + (k + 1) = m + 1 + k by ring]; ring
    rw [pow_succ, A8]; push_cast
    linear_combination 8 * ih + 8 * hs

lemma floor_cantor8 (ι : ℕ → Fin 2) (m r : ℕ) (hr : r ≤ 2) :
    ⌊(2 : ℝ) ^ (3 * m + r) * cantor8 ι⌋ = 2 ^ r * A8 ι m := by
  have e : (2 : ℝ) ^ (3 * m + r) * cantor8 ι = 2 ^ r * A8 ι m + 2 ^ r * T8 ι m := by
    rw [pow_add, pow_mul, show (2 : ℝ) ^ 3 = 8 by norm_num, mul_comm ((8 : ℝ) ^ m),
      mul_assoc, pow8_cantor8]; ring
  have h4 : (2 : ℝ) ^ r ≤ 4 := by
    calc (2 : ℝ) ^ r ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hr
      _ = 4 := by norm_num
  have := T8_nonneg ι m; have := T8_le ι m
  rw [e, Int.floor_eq_iff]; push_cast
  constructor
  · nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) r]
  · nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) r]

lemma bdig_cantor8_off (ι : ℕ → Fin 2) (m r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    bdig (cantor8 ι) (3 * m + r) = 0 := by
  unfold bdig; rw [floor_cantor8 ι m r hr2]
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ, mul_comm ((2 : ℤ) ^ r') 2, mul_assoc]; exact Int.mul_emod_right _ _

/-- At most a third of the binary digits of `cantor8 ι` are ones. -/
@[category API, AMS 11, ref "Isa06", group "isaac_tu"]
lemma cnt_cantor8_le (ι : ℕ → Fin 2) (N : ℕ) : cnt (cantor8 ι) N ≤ ((N / 3 : ℕ) : ℤ) := by
  induction N with
  | zero => simp [cnt_zero]
  | succ N ih =>
    rw [cnt_succ]
    rcases (by omega : (N + 1) % 3 = 0 ∨ (N + 1) % 3 = 1 ∨ (N + 1) % 3 = 2) with h | h | h
    · have := bdig_le_one (cantor8 ι) (N + 1); push_cast at ih ⊢; omega
    · rw [show N + 1 = 3 * ((N + 1) / 3) + 1 by omega, bdig_cantor8_off ι _ 1 le_rfl (by norm_num)]
      push_cast at ih ⊢; omega
    · rw [show N + 1 = 3 * ((N + 1) / 3) + 2 by omega, bdig_cantor8_off ι _ 2 (by norm_num) le_rfl]
      push_cast at ih ⊢; omega

lemma cantor8_injective : Function.Injective cantor8 := by
  intro ι ι' h
  have hA : ∀ m, A8 ι m = A8 ι' m := fun m => by
    have h1 := floor_cantor8 ι m 0 (by norm_num); have h2 := floor_cantor8 ι' m 0 (by norm_num)
    rw [h] at h1; rw [h1] at h2; simpa using h2
  funext m; apply Fin.ext
  have := hA (m + 1); simp only [A8, hA m] at this; omega

lemma infinitePi_coin_singleton (ι₀ : ℕ → Fin 2) :
    Measure.infinitePi (fun _ : ℕ => coin) {ι₀} = 0 := by
  have h : ∀ n : ℕ, Measure.infinitePi (fun _ : ℕ => coin) {ι₀} ≤ (2⁻¹ : ENNReal) ^ n := by
    intro n
    calc Measure.infinitePi (fun _ : ℕ => coin) {ι₀}
        ≤ Measure.infinitePi (fun _ : ℕ => coin)
            (Set.pi (Finset.range n : Set ℕ) (fun k => {ι₀ k})) :=
          measure_mono (by intro ι hι; rw [Set.mem_singleton_iff] at hι; subst hι; simp)
      _ = ∏ k ∈ Finset.range n, coin {ι₀ k} :=
          Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)
      _ = (2⁻¹ : ENNReal) ^ n := by simp [coin_singleton]
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_iff.2 (by norm_num)) h)
    (by simp)

@[category API, AMS 11 28, ref "MS18", group "isaac_tu"]
lemma mu8_singleton (a : ℝ) : mu8 {a} = 0 := by
  rw [mu8_eq, Measure.map_apply measurable_cantor8 (measurableSet_singleton a)]
  by_cases h : ∃ ι₀, cantor8 ι₀ = a
  · obtain ⟨ι₀, rfl⟩ := h
    exact measure_mono_null (fun ι hι => cantor8_injective hι) (infinitePi_coin_singleton ι₀)
  · push Not at h
    convert measure_empty (μ := Measure.infinitePi (fun _ : ℕ => coin))
    ext ι; simp [h ι]

instance : IsProbabilityMeasure mu8 := by
  rw [mu8_eq]; infer_instance

/-- `g(ω) = y(ω/2) = √(ω²/4 + 1/4)`, the smooth convex map of the report's Proof B. -/
noncomputable def gB (x : ℝ) : ℝ := ysq (x / 2)

/-- `g'`. -/
noncomputable def gB' (x : ℝ) : ℝ := x / 2 / (2 * gB x)

/-- `g''`. -/
noncomputable def gB'' (x : ℝ) : ℝ := (1 / 2 * (2 * gB x) - x / 2 * (2 * gB' x)) / (2 * gB x) ^ 2

lemma gB_pos (x : ℝ) : 0 < gB x := Real.sqrt_pos.2 (by positivity)

lemma continuous_gB : Continuous gB :=
  Real.continuous_sqrt.comp (by fun_prop)

lemma continuous_gB' : Continuous gB' :=
  (continuous_id.div_const 2).div (continuous_const.mul continuous_gB)
    (fun x => (mul_pos two_pos (gB_pos x)).ne')

lemma hasDerivAt_gB (x : ℝ) : HasDerivAt gB (gB' x) x := by
  have hf : HasDerivAt (fun y : ℝ => (y / 2) ^ 2 + 1 / 4) (x / 2) x := by
    have := (((hasDerivAt_id' x).div_const 2).pow 2).add_const (1 / 4 : ℝ)
    convert this using 1; ring
  exact hf.sqrt (by positivity)

lemma hasDerivAt_gB' (x : ℝ) : HasDerivAt gB' (gB'' x) x :=
  HasDerivAt.div ((hasDerivAt_id' x).div_const 2) ((hasDerivAt_gB x).const_mul 2)
    (mul_pos two_pos (gB_pos x)).ne'

lemma continuous_gB'' : Continuous gB'' :=
  ((continuous_const.mul (continuous_const.mul continuous_gB)).sub
    ((continuous_id.div_const 2).mul (continuous_const.mul continuous_gB'))).div
    ((continuous_const.mul continuous_gB).pow 2)
    (fun x => (pow_pos (mul_pos two_pos (gB_pos x)) 2).ne')

lemma gB''_pos (x : ℝ) : 0 < gB'' x := by
  have hg := gB_pos x
  have hg2 : gB x ^ 2 = (x / 2) ^ 2 + 1 / 4 := ysq_sq _
  have e : 1 / 2 * (2 * gB x) - x / 2 * (2 * gB' x) = 1 / (4 * gB x) := by
    rw [gB']; field_simp; linear_combination 16 * hg2
  rw [gB'', e]; positivity

/-- **(TU) is false** — proof B of `plans/report-sqrtnorm.html` §2.1, with the Cantor measure of
ratio `1/8` in place of the Bernoulli(`p`) measure `μ_p`: the frequency `p < 1/2` of ones is
replaced by the deterministic bound `≤ 1/3`, so the strong law is not needed.  For `μ₈`-almost
every `ω`, `√((ω/2)² + 1/4)` is simply normal ([MS18, Thm 3.1] + [DEL63]) while `f_N(ω/2) ≤ 1/3
+ 2/N`. -/
@[category research solved, AMS 11 42, ref "Isa06" "MS18" "DEL63", group "isaac_tu"]
theorem not_TUfull_fourier : ¬ TUfull := by
  intro hTU
  obtain ⟨σ, hσ, C, hdec⟩ := MS.fourierDecay_smoothImage coin
    (fun i => by rw [coin_singleton]; norm_num) (fun i => ((i : ℕ) : ℝ)) (1 / 8) (by norm_num)
    (by norm_num) mu8_singleton gB gB' gB'' hasDerivAt_gB hasDerivAt_gB' continuous_gB''
    gB''_pos
  have hDEL := DEL.ae_simplyNormal_of_fourierDecay (mu8.map gB) σ hσ C hdec
  have h1 : ∀ᵐ ω ∂mu8, Tendsto (freq (gB ω)) atTop (𝓝 (1 / 2)) :=
    ae_of_ae_map continuous_gB.measurable.aemeasurable hDEL
  have h2 : ∀ᵐ ω ∂mu8, Irrational (ω ^ 2) := by
    rw [ae_iff]
    refine measure_mono_null (t := ⋃ q : ℚ, ({√(q : ℝ)} ∪ {-√(q : ℝ)})) ?_
      (measure_iUnion_null fun q => measure_union_null (mu8_singleton _) (mu8_singleton _))
    intro ω hω
    change ¬ Irrational (ω ^ 2) at hω
    simp only [Irrational, not_not, Set.mem_range] at hω
    obtain ⟨q, hq⟩ := hω
    have habs : |ω| = √(q : ℝ) := by rw [hq, Real.sqrt_sq_eq_abs]
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff]
    refine ⟨q, ?_⟩
    rcases abs_eq (Real.sqrt_nonneg _) |>.1 habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  rw [mu8_eq] at h1 h2
  have h1' := ae_of_ae_map measurable_cantor8.aemeasurable h1
  have h2' := ae_of_ae_map measurable_cantor8.aemeasurable h2
  have : (ae (Measure.infinitePi (fun _ : ℕ => coin))).NeBot :=
    ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨ι, hn, hirr⟩ := (h1'.and h2').exists
  set ω := cantor8 ι
  have hω0 : 0 ≤ ω := by
    have := pow8_cantor8 ι 0; have := T8_nonneg ι 0; simp [A8] at *; linarith
  have hω1 : ω ≤ 1 / 7 := by
    have := pow8_cantor8 ι 0; have := T8_le ι 0; simp [A8] at *; linarith
  have hωpos : 0 < ω := by
    rcases hω0.lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by rw [← h]; simp⟩ hirr
  have key := hTU ((ω / 2) ^ 2) ((ω / 2) ^ 2 + 1 / 4) (by positivity) (by nlinarith)
    (by positivity) (by nlinarith) (by
      have := hirr.div_natCast (m := 4) (by norm_num)
      convert this using 1; push_cast; ring) ⟨1, 2, by norm_num⟩
  rw [Real.sqrt_sq (by positivity)] at key
  change _ = limsup (freq (gB ω)) atTop at key
  rw [hn.limsup_eq] at key
  have hb : ∀ N : ℕ, 30 ≤ N → freq (ω / 2) N ≤ 2 / 5 := by
    intro N hN
    have hs := cnt_shift (a := ω / 2) (b := ω) (s := 1) (K := 0) (fun k _ => bdig_half ω k) N
    have hc : cnt ω N ≤ ((N / 3 : ℕ) : ℤ) := cnt_cantor8_le ι N
    have h3 : ((N / 3 : ℕ) : ℝ) ≤ (N : ℝ) / 3 := by exact_mod_cast Nat.cast_div_le
    have hc' : (cnt (ω / 2) N : ℝ) ≤ N / 3 + 2 := by
      have : cnt (ω / 2) N ≤ ((N / 3 : ℕ) : ℤ) + 2 := by rw [abs_le] at hs; push_cast at hs; omega
      have : (cnt (ω / 2) N : ℝ) ≤ ((N / 3 : ℕ) : ℝ) + 2 := by
        have h := (Int.cast_le (R := ℝ)).2 this; push_cast at h; exact h
      linarith
    have hN' : (30 : ℝ) ≤ N := by exact_mod_cast hN
    unfold freq; rw [div_le_iff₀ (by linarith)]; linarith
  have hL : limsup (freq (ω / 2)) atTop ≤ 2 / 5 :=
    limsup_le_of_le (isCobounded_freq _) (eventually_atTop.2 ⟨30, hb⟩)
  rw [key] at hL; norm_num at hL

/-- **(TU) is false** (proof B, from [MS18, Thm 3.1] and [DEL63]). -/
@[category research solved, AMS 11 42, ref "Isa06" "MS18" "DEL63", group "isaac_tu"]
theorem not_TU_fourier : ¬ TU := fun h => not_TUfull_fourier h.full

end ProofB

end BB47.Isaac
