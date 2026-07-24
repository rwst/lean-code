/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Tails of a real power series with bounded coefficients

For `0 ≤ r < 1` and a bounded coefficient sequence `a : ℕ → ℝ`, the series `∑ⱼ a_{n+j} rʲ`
converges for every `n`.  The resulting function `n ↦ tailSeries r a n` is the fixed point of
the *backward* recursion `T n = a n + r · T (n+1)`, and this is the shape in which such series
arise in symbolic dynamics: `a` is an infinite word over a finite alphabet, `r` is a contraction
ratio, and `tailSeries r a n` is the value read off the word from position `n` on.

The API below is deliberately organised around that recursion rather than around `tsum`:

* two-sided bounds from bounds on the letters (`tailSeries_le`, `le_tailSeries`);
* transfer of *any* uniform bound on the partial sums (`tailSeries_le_of_partialTail_le`),
  which lets an inductive invariant on the finite truncations — the standard way to exploit
  cancellation, e.g. sign-alternating words — be pushed to the limit;
* **rigidity**: the extreme values `c/(1-r)` of the two bounds are attained only by the
  constant word `c` (`eq_of_tailSeries_eq_le`, `eq_of_tailSeries_eq_ge`).

## Main definitions

* `ForMathlib.tailSeries r a n` — the sum `∑ⱼ a_{n+j} rʲ`.
* `ForMathlib.partialTail r a n N` — its `N`-th partial sum.

## Main results

* `ForMathlib.tailSeries_succ` — the backward recursion `T n = a n + r · T (n+1)`.
* `ForMathlib.tailSeries_le` / `ForMathlib.le_tailSeries` — `a m ∈ [c₁, c₂]` for `m ≥ n` forces
  `tailSeries r a n ∈ [c₁/(1-r), c₂/(1-r)]`.
* `ForMathlib.eq_of_tailSeries_eq_ge` / `ForMathlib.eq_of_tailSeries_eq_le` — equality in either
  bound forces `a` to be constant from `n` on.
-/

namespace ForMathlib

open Filter Topology

variable {r c M : ℝ} {a : ℕ → ℝ} {n : ℕ}

/-- The `n`-th tail of the power series with coefficients `a`, read from position `n`:
`tailSeries r a n = ∑_{j ≥ 0} a_{n+j} rʲ`. -/
noncomputable def tailSeries (r : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑' j : ℕ, a (n + j) * r ^ j

/-- The `N`-th partial sum of `tailSeries r a n`. -/
noncomputable def partialTail (r : ℝ) (a : ℕ → ℝ) (n N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, a (n + j) * r ^ j

/-! ## Convergence -/

/-- A power series with bounded coefficients converges for `0 ≤ r < 1`. -/
theorem summable_tailSeries (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : ∀ k, |a k| ≤ M) (n : ℕ) :
    Summable fun j : ℕ => a (n + j) * r ^ j := by
  have hgeo : Summable fun j : ℕ => M * r ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left M
  refine Summable.of_norm_bounded hgeo fun j => ?_
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact mul_le_mul_of_nonneg_right (ha _) (by positivity)

theorem tendsto_partialTail (hsum : Summable fun j : ℕ => a (n + j) * r ^ j) :
    Tendsto (partialTail r a n) atTop (𝓝 (tailSeries r a n)) :=
  hsum.hasSum.tendsto_sum_nat

/-! ## The backward recursion -/

/-- Peeling off the first letter, at the level of partial sums. -/
theorem partialTail_succ (r : ℝ) (a : ℕ → ℝ) (n N : ℕ) :
    partialTail r a n (N + 1) = a n + r * partialTail r a (n + 1) N := by
  have key : ∀ j : ℕ, a (n + (j + 1)) * r ^ (j + 1) = r * (a (n + 1 + j) * r ^ j) := by
    intro j
    have hj : n + (j + 1) = n + 1 + j := by omega
    rw [hj, pow_succ]
    ring
  rw [partialTail, partialTail, Finset.sum_range_succ', Finset.mul_sum]
  simp only [key, pow_zero, mul_one, Nat.add_zero]
  ring

/-- The tail series is the fixed point of the backward recursion `T n = a n + r · T (n+1)`. -/
theorem tailSeries_succ (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : ∀ k, |a k| ≤ M) (n : ℕ) :
    tailSeries r a n = a n + r * tailSeries r a (n + 1) := by
  have h1 : Tendsto (fun N => partialTail r a n (N + 1)) atTop (𝓝 (tailSeries r a n)) :=
    (tendsto_partialTail (summable_tailSeries hr0 hr1 ha n)).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N => partialTail r a n (N + 1)) atTop
      (𝓝 (a n + r * tailSeries r a (n + 1))) := by
    simp only [partialTail_succ]
    exact ((tendsto_partialTail (summable_tailSeries hr0 hr1 ha (n + 1))).const_mul r).const_add _
  exact tendsto_nhds_unique h1 h2

/-! ## Bounds -/

/-- Any uniform upper bound on the partial sums passes to the limit.  This is the entry point
for inductive invariants on finite truncations. -/
theorem tailSeries_le_of_partialTail_le (hsum : Summable fun j : ℕ => a (n + j) * r ^ j)
    (h : ∀ N, partialTail r a n N ≤ c) : tailSeries r a n ≤ c :=
  le_of_tendsto (tendsto_partialTail hsum) (Eventually.of_forall h)

/-- Any uniform lower bound on the partial sums passes to the limit. -/
theorem le_tailSeries_of_le_partialTail (hsum : Summable fun j : ℕ => a (n + j) * r ^ j)
    (h : ∀ N, c ≤ partialTail r a n N) : c ≤ tailSeries r a n :=
  ge_of_tendsto (tendsto_partialTail hsum) (Eventually.of_forall h)

/-- The constant word `c` has tail value `c/(1-r)`. -/
theorem tailSeries_const (hr0 : 0 ≤ r) (hr1 : r < 1) (c : ℝ) (n : ℕ) :
    tailSeries r (fun _ => c) n = c / (1 - r) := by
  rw [tailSeries, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- Letters bounded above by `c` from position `n` on force `tailSeries r a n ≤ c/(1-r)`. -/
theorem tailSeries_le (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : ∀ k, |a k| ≤ M)
    (h : ∀ m, n ≤ m → a m ≤ c) : tailSeries r a n ≤ c / (1 - r) := by
  have hgeo : Summable fun j : ℕ => c * r ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  have := Summable.tsum_le_tsum (f := fun j : ℕ => a (n + j) * r ^ j) (g := fun j : ℕ => c * r ^ j)
    (fun j => mul_le_mul_of_nonneg_right (h _ (Nat.le_add_right _ _)) (by positivity))
    (summable_tailSeries hr0 hr1 ha n) hgeo
  rwa [← tailSeries, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, ← div_eq_mul_inv] at this

/-- Letters bounded below by `c` from position `n` on force `c/(1-r) ≤ tailSeries r a n`. -/
theorem le_tailSeries (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : ∀ k, |a k| ≤ M)
    (h : ∀ m, n ≤ m → c ≤ a m) : c / (1 - r) ≤ tailSeries r a n := by
  have hgeo : Summable fun j : ℕ => c * r ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  have := Summable.tsum_le_tsum (f := fun j : ℕ => c * r ^ j) (g := fun j : ℕ => a (n + j) * r ^ j)
    (fun j => mul_le_mul_of_nonneg_right (h _ (Nat.le_add_right _ _)) (by positivity))
    hgeo (summable_tailSeries hr0 hr1 ha n)
  rwa [← tailSeries, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, ← div_eq_mul_inv] at this

/-! ## Rigidity of the extreme values -/

/-- **Rigidity at the lower bound.**  If the letters are `≥ c` from position `n` on and the tail
attains the extreme value `c/(1-r)`, then the word is constant equal to `c` from `n` on. -/
theorem eq_of_tailSeries_eq_ge (hr0 : 0 < r) (hr1 : r < 1) (ha : ∀ k, |a k| ≤ M)
    (h : ∀ m, n ≤ m → c ≤ a m) (heq : tailSeries r a n = c / (1 - r)) :
    ∀ m, n ≤ m → a m = c := by
  have hgeo : Summable fun j : ℕ => c * r ^ j :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left c
  have hsum := summable_tailSeries hr0.le hr1 ha n
  have hdiff : Summable fun j : ℕ => a (n + j) * r ^ j - c * r ^ j := hsum.sub hgeo
  have hnn : ∀ j : ℕ, 0 ≤ a (n + j) * r ^ j - c * r ^ j := by
    intro j
    have := mul_le_mul_of_nonneg_right (h (n + j) (Nat.le_add_right _ _))
      (pow_nonneg hr0.le j)
    linarith
  have hzero : ∑' j : ℕ, (a (n + j) * r ^ j - c * r ^ j) = 0 := by
    rw [hsum.tsum_sub hgeo, ← tailSeries, heq, tsum_mul_left,
      tsum_geometric_of_lt_one hr0.le hr1, ← div_eq_mul_inv, sub_self]
  intro m hm
  obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
  have hle := hdiff.le_tsum j fun i _ => hnn i
  rw [hzero] at hle
  have : a (n + j) * r ^ j - c * r ^ j = 0 := le_antisymm hle (hnn j)
  have hrj : (r : ℝ) ^ j ≠ 0 := by positivity
  have : (a (n + j) - c) * r ^ j = 0 := by linarith [this]
  rcases mul_eq_zero.mp this with h' | h'
  · linarith
  · exact absurd h' hrj

theorem tailSeries_neg (r : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    tailSeries r (fun k => -a k) n = -tailSeries r a n := by
  rw [tailSeries, tailSeries, ← tsum_neg]
  exact tsum_congr fun j => by ring

/-- **Rigidity at the upper bound.**  If the letters are `≤ c` from position `n` on and the tail
attains the extreme value `c/(1-r)`, then the word is constant equal to `c` from `n` on. -/
theorem eq_of_tailSeries_eq_le (hr0 : 0 < r) (hr1 : r < 1) (ha : ∀ k, |a k| ≤ M)
    (h : ∀ m, n ≤ m → a m ≤ c) (heq : tailSeries r a n = c / (1 - r)) :
    ∀ m, n ≤ m → a m = c := by
  have key := eq_of_tailSeries_eq_ge (r := r) (a := fun k => -a k) (c := -c) (M := M) hr0 hr1
    (fun k => by rw [abs_neg]; exact ha k) (fun m hm => neg_le_neg (h m hm)) ?_
  · intro m hm
    have := key m hm
    simpa using congrArg Neg.neg this
  · rw [tailSeries_neg, heq, neg_div]

end ForMathlib
