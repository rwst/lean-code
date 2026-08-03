/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# Memory loss for sequential (time-dependent) dynamical systems

A **sequential** dynamical system is a family of maps `S : ι → α → α` together with a *word*
`w : ℕ → ι` prescribing which map to apply at each time; `Dynamics.seqOrbit S w x n` is the state
after `n` steps.  This file proves, for a **uniformly expanding** family, that the word determines
the orbit up to an exponentially small error:

> two points driven by the same word whose orbits stay within distance `D` of each other are within
> `D / Λⁿ` — for every `n`.

Consequently the Birkhoff sums of a Lipschitz observable along two such orbits differ by a bound
*independent of the number of terms*, so their averages differ by `O(1/N)`: in the limit, the
empirical distribution of a confined sequential orbit is a functional of its word alone.

## Main results

* `Dynamics.IsUniformlyExpanding.le_dist_seqOrbit` — expansion along a common word: distances grow
  by at least `Λⁿ`.
* `Dynamics.IsUniformlyExpanding.dist_le_of_forall_dist_le` — **memory loss**, and its convenience
  form `dist_le_of_forall_mem` for orbits confined to a bounded set (`D = diam K`).
* `Dynamics.IsUniformlyExpanding.eq_of_forall_dist_le` — the coding is injective: a word followed
  forever by two confined orbits determines the point.
* `Dynamics.IsUniformlyExpanding.abs_sum_sub_sum_le` — the Birkhoff sums of a `C`-Lipschitz
  observable along the two orbits differ by at most `C * D / (Λ - 1)`, *for every number of terms*;
  `abs_average_sub_le` divides by `N`.
* `Dynamics.seqOrbit_affine` — for an affine family `x ↦ a * x + b i` the state is an explicit
  affine functional of the word, `aⁿ * (x + ∑_{k<n} b (w k) / a^{k+1})`: geometric weights, the most
  recent symbol weighted most.
* `Dynamics.dist_le_mul_two_thirds_pow`, `Dynamics.abs_sum_sub_sum_le_of_mem_Ico` — the case
  `x ↦ (3 * x + c) / 2` with rate `(2/3)ⁿ`, and, for orbits confined to `[0, 1)`, the empirical form
  with the explicit constant `2 * C`.
* `Dynamics.seqOrbit_threeHalvesStep_fract`, `Dynamics.fract_eq_fract_of_word_eq` — the hypotheses
  are not vacuous: the fractional parts of `(3/2)ⁿ ξ` are exactly such an orbit, driven by the word
  `cₙ = 3⌊(3/2)ⁿ ξ⌋ - 2⌊(3/2)ⁿ⁺¹ ξ⌋`, and that word determines `Int.fract ξ`.

## The direction of "memory loss", and what is *not* proved here

The name is standard, but the mechanism here runs *backwards* and it is worth saying so plainly.
Two points driven by the same word do not approach each other — the maps are expanding, so they
separate.  What the confinement hypothesis says is that they cannot separate, and the only way out
is that they were exponentially close to begin with.  Memory of the initial condition is lost not
because the dynamics contracts it, but because the symbolic record leaves it no room.

This is the elementary, "weak" form of loss of memory, and it needs no transfer operators: no
densities, no bounded variation, no Lasota–Yorke inequality, no spectral gap.  The
sequential-transfer-operator theorems of Ott–Stenlund–Young and Conze–Raugi (listed below for
orientation) prove a *different*, much stronger statement — that two arbitrary initial *densities*
pushed forward along a common composition of expanding maps converge to each other in `L¹`,
exponentially fast — and **none of that is used or reproved here**.  Everything below is about
points with a common itinerary.

## References

* Ott, William; Stenlund, Mikko; Young, Lai-Sang. *Memory loss for time-dependent dynamical
  systems.* Math. Res. Lett. **16** (2009), 463–475.
* Conze, Jean-Pierre; Raugi, Albert. *Limit theorems for sequential expanding dynamical systems on
  [0,1].* Contemp. Math. **430** (2007), 89–121.
-/

open Filter Topology

namespace Dynamics

variable {α ι : Type*}

/-- The state of the sequential system `S` after `n` steps along the word `w`, started at `x`:
`seqOrbit S w x (n + 1) = S (w n) (seqOrbit S w x n)`. -/
def seqOrbit (S : ι → α → α) (w : ℕ → ι) (x : α) : ℕ → α
  | 0 => x
  | n + 1 => S (w n) (seqOrbit S w x n)

@[simp]
theorem seqOrbit_zero (S : ι → α → α) (w : ℕ → ι) (x : α) : seqOrbit S w x 0 = x := rfl

@[simp]
theorem seqOrbit_succ (S : ι → α → α) (w : ℕ → ι) (x : α) (n : ℕ) :
    seqOrbit S w x (n + 1) = S (w n) (seqOrbit S w x n) := rfl

/-- Running `m + n` steps is running `n` steps of the *shifted* word from the state at time `m`. -/
theorem seqOrbit_add (S : ι → α → α) (w : ℕ → ι) (x : α) (m n : ℕ) :
    seqOrbit S w x (m + n) = seqOrbit S (fun k => w (m + k)) (seqOrbit S w x m) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, seqOrbit_succ, ih, seqOrbit_succ]

/-- Only the first `n` symbols of the word matter for the state at time `n`. -/
theorem seqOrbit_congr {S : ι → α → α} {w w' : ℕ → ι} (x : α) {n : ℕ} (h : ∀ k < n, w k = w' k) :
    seqOrbit S w x n = seqOrbit S w' x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [seqOrbit_succ, seqOrbit_succ, ih fun k hk => h k (hk.trans (Nat.lt_succ_self n)),
      h n (Nat.lt_succ_self n)]

/-- The tail of a geometric series, in the form needed for the Birkhoff estimate. -/
private theorem geom_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, r ^ (j + 1) ≤ r / (1 - r) := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have hsum : ∑ j ∈ Finset.range N, r ^ (j + 1) = r * ∑ j ∈ Finset.range N, r ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hgeom : ∑ j ∈ Finset.range N, r ^ j ≤ (1 - r)⁻¹ := by
    rw [geom_sum_eq hr1.ne, show (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) by
      rw [← neg_sub r 1, ← neg_sub (r ^ N) 1, neg_div_neg_eq], inv_eq_one_div]
    gcongr
    exact sub_le_self 1 (pow_nonneg hr0 N)
  calc ∑ j ∈ Finset.range N, r ^ (j + 1) = r * ∑ j ∈ Finset.range N, r ^ j := hsum
    _ ≤ r * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeom hr0
    _ = r / (1 - r) := (div_eq_mul_inv _ _).symm

section Expanding

variable [PseudoMetricSpace α]

/-- A family of maps is **uniformly expanding** with factor `Λ` if every member expands distances by
at least `Λ`.  Only `1 < Λ` is interesting, but the definition does not assume it. -/
def IsUniformlyExpanding (S : ι → α → α) (Λ : ℝ) : Prop :=
  ∀ i x y, Λ * dist x y ≤ dist (S i x) (S i y)

namespace IsUniformlyExpanding

variable {S : ι → α → α} {Λ D : ℝ} {w : ℕ → ι} {x y : α}

/-- **Expansion along a common word.**  Distances between two orbits driven by the same word grow by
a factor of at least `Λ` per step. -/
theorem le_dist_seqOrbit (hS : IsUniformlyExpanding S Λ) (hΛ : 0 ≤ Λ) (w : ℕ → ι) (x y : α)
    (n : ℕ) : Λ ^ n * dist x y ≤ dist (seqOrbit S w x n) (seqOrbit S w y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc Λ ^ (n + 1) * dist x y = Λ * (Λ ^ n * dist x y) := by ring
      _ ≤ Λ * dist (seqOrbit S w x n) (seqOrbit S w y n) := mul_le_mul_of_nonneg_left ih hΛ
      _ ≤ dist (seqOrbit S w x (n + 1)) (seqOrbit S w y (n + 1)) := hS _ _ _

/-- **Memory loss, basic form.**  If two orbits along the same word are still within `D` of each
other at time `n`, then their starting points were within `D / Λⁿ`. -/
theorem dist_le_of_dist_seqOrbit_le (hS : IsUniformlyExpanding S Λ) (hΛ : 0 < Λ) {n : ℕ}
    (hD : dist (seqOrbit S w x n) (seqOrbit S w y n) ≤ D) : dist x y ≤ D / Λ ^ n :=
  (le_div_iff₀' (by positivity)).2 ((hS.le_dist_seqOrbit hΛ.le w x y n).trans hD)

/-- **Memory loss.**  Two points driven by the same word whose orbits stay within `D` of each other
are within `D / Λⁿ` — for *every* `n`.  The initial condition is remembered by the word only to
within an exponentially small error. -/
theorem dist_le_of_forall_dist_le (hS : IsUniformlyExpanding S Λ) (hΛ : 0 < Λ)
    (hD : ∀ n, dist (seqOrbit S w x n) (seqOrbit S w y n) ≤ D) (n : ℕ) : dist x y ≤ D / Λ ^ n :=
  hS.dist_le_of_dist_seqOrbit_le hΛ (hD n)

/-- Memory loss for orbits confined to a bounded set: the ambient bound is its diameter. -/
theorem dist_le_of_forall_mem (hS : IsUniformlyExpanding S Λ) (hΛ : 0 < Λ) {K : Set α}
    (hK : Bornology.IsBounded K) (hx : ∀ n, seqOrbit S w x n ∈ K) (hy : ∀ n, seqOrbit S w y n ∈ K)
    (n : ℕ) : dist x y ≤ Metric.diam K / Λ ^ n :=
  hS.dist_le_of_forall_dist_le hΛ (fun m => Metric.dist_le_diam_of_mem hK (hx m) (hy m)) n

/-- The same bound at an intermediate time: the state at time `k` is determined by the word to
within `D / Λᵐ` for every `m` — in particular to within `D / Λ^(N-k)` if the word is known only up
to time `N`.  This is the "exponential transient decay" of the normal form. -/
theorem dist_seqOrbit_le (hS : IsUniformlyExpanding S Λ) (hΛ : 0 < Λ)
    (hD : ∀ n, dist (seqOrbit S w x n) (seqOrbit S w y n) ≤ D) (k m : ℕ) :
    dist (seqOrbit S w x k) (seqOrbit S w y k) ≤ D / Λ ^ m := by
  refine hS.dist_le_of_dist_seqOrbit_le (w := fun j => w (k + j)) hΛ (n := m) ?_
  rw [← seqOrbit_add, ← seqOrbit_add]
  exact hD _

/-- **The empirical distribution is a functional of the word alone.**  For a `C`-Lipschitz
observable, the Birkhoff *sums* along two orbits driven by the same word (and staying within `D` of
each other) differ by at most `C * D / (Λ - 1)`: a bound independent of the number of terms. -/
theorem abs_sum_sub_sum_le (hS : IsUniformlyExpanding S Λ) (hΛ : 1 < Λ) (hD0 : 0 ≤ D)
    (hD : ∀ n, dist (seqOrbit S w x n) (seqOrbit S w y n) ≤ D) {φ : α → ℝ} {C : NNReal}
    (hφ : LipschitzWith C φ) (N : ℕ) :
    |∑ n ∈ Finset.range N, φ (seqOrbit S w x n) - ∑ n ∈ Finset.range N, φ (seqOrbit S w y n)|
      ≤ C * D / (Λ - 1) := by
  have hΛ0 : (0 : ℝ) < Λ := one_pos.trans hΛ
  have hinv : (Λ : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hΛ
  -- termwise, via the intermediate-time bound with `m = N - n`
  have hterm : ∀ n ∈ Finset.range N,
      |φ (seqOrbit S w x n) - φ (seqOrbit S w y n)| ≤ C * D * (Λ⁻¹) ^ (N - n) := by
    intro n _
    have h1 : dist (φ (seqOrbit S w x n)) (φ (seqOrbit S w y n)) ≤ C * (D / Λ ^ (N - n)) :=
      hφ.dist_le_mul_of_le (hS.dist_seqOrbit_le hΛ0 hD n (N - n))
    rw [Real.dist_eq] at h1
    calc |φ (seqOrbit S w x n) - φ (seqOrbit S w y n)| ≤ C * (D / Λ ^ (N - n)) := h1
      _ = C * D * (Λ⁻¹) ^ (N - n) := by rw [inv_pow, div_eq_mul_inv]; ring
  -- reindex the geometric tail
  have hreindex : ∑ n ∈ Finset.range N, (Λ⁻¹ : ℝ) ^ (N - n)
      = ∑ j ∈ Finset.range N, (Λ⁻¹ : ℝ) ^ (j + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 1
    omega
  have hval : (Λ⁻¹ : ℝ) / (1 - Λ⁻¹) = (Λ - 1)⁻¹ := by
    have h1 : (1 : ℝ) - Λ⁻¹ = (Λ - 1) / Λ := by field_simp
    rw [h1, div_div_eq_mul_div, inv_mul_cancel₀ hΛ0.ne', one_div]
  calc |∑ n ∈ Finset.range N, φ (seqOrbit S w x n) - ∑ n ∈ Finset.range N, φ (seqOrbit S w y n)|
      = |∑ n ∈ Finset.range N, (φ (seqOrbit S w x n) - φ (seqOrbit S w y n))| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ Finset.range N, |φ (seqOrbit S w x n) - φ (seqOrbit S w y n)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, C * D * (Λ⁻¹) ^ (N - n) := Finset.sum_le_sum hterm
    _ = C * D * ∑ n ∈ Finset.range N, (Λ⁻¹ : ℝ) ^ (N - n) := by rw [Finset.mul_sum]
    _ ≤ C * D * (Λ - 1)⁻¹ := by
        rw [hreindex, ← hval]
        exact mul_le_mul_of_nonneg_left (geom_tail_le (by positivity) hinv N) (by positivity)
    _ = C * D / (Λ - 1) := (div_eq_mul_inv _ _).symm

/-- The Birkhoff *averages* of a Lipschitz observable along two orbits driven by the same word
differ by `O(1/N)`, with an explicit constant. -/
theorem abs_average_sub_le (hS : IsUniformlyExpanding S Λ) (hΛ : 1 < Λ) (hD0 : 0 ≤ D)
    (hD : ∀ n, dist (seqOrbit S w x n) (seqOrbit S w y n) ≤ D) {φ : α → ℝ} {C : NNReal}
    (hφ : LipschitzWith C φ) (N : ℕ) :
    |(∑ n ∈ Finset.range N, φ (seqOrbit S w x n)) / N
        - (∑ n ∈ Finset.range N, φ (seqOrbit S w y n)) / N| ≤ C * D / (Λ - 1) / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_sub_div_same, abs_div, abs_of_pos hN0]
  gcongr
  exact hS.abs_sum_sub_sum_le hΛ hD0 hD hφ N

end IsUniformlyExpanding

end Expanding

section Injectivity

variable [MetricSpace α] {S : ι → α → α} {Λ D : ℝ} {w : ℕ → ι} {x y : α}

/-- **The coding is injective.**  A word followed forever by two orbits that stay within a fixed
distance of each other determines the point: there is at most one starting point per itinerary. -/
theorem IsUniformlyExpanding.eq_of_forall_dist_le (hS : IsUniformlyExpanding S Λ) (hΛ : 1 < Λ)
    (hD : ∀ n, dist (seqOrbit S w x n) (seqOrbit S w y n) ≤ D) : x = y := by
  have hΛ0 : (0 : ℝ) < Λ := one_pos.trans hΛ
  have hlim : Tendsto (fun n : ℕ => D / Λ ^ n) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (Λ⁻¹ : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (by rw [inv_lt_one_iff₀]; right; exact hΛ)
    have h' := h.const_mul D
    rw [mul_zero] at h'
    exact h'.congr fun n => by rw [inv_pow, ← div_eq_mul_inv]
  have hle : dist x y ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun n => hS.dist_le_of_forall_dist_le hΛ0 hD n)
  exact dist_le_zero.1 hle

/-- The same, for orbits confined to a bounded set. -/
theorem IsUniformlyExpanding.eq_of_forall_mem (hS : IsUniformlyExpanding S Λ) (hΛ : 1 < Λ)
    {K : Set α} (hK : Bornology.IsBounded K) (hx : ∀ n, seqOrbit S w x n ∈ K)
    (hy : ∀ n, seqOrbit S w y n ∈ K) : x = y :=
  hS.eq_of_forall_dist_le hΛ fun n => Metric.dist_le_diam_of_mem hK (hx n) (hy n)

end Injectivity

/-! ### Affine families: the explicit normal form -/

section Affine

variable {a : ℝ}

/-- An affine family with slope `a ≥ 0` is uniformly expanding with factor `a` — with equality in
the defining inequality, so the rate is exact. -/
theorem isUniformlyExpanding_affine (ha : 0 ≤ a) (b : ι → ℝ) :
    IsUniformlyExpanding (fun i x => a * x + b i) a := by
  intro i x y
  rw [Real.dist_eq, Real.dist_eq, show a * x + b i - (a * y + b i) = a * (x - y) by ring, abs_mul,
    abs_of_nonneg ha]

/-- **The affine normal form.**  Along an affine family the state at time `n` is an explicit affine
functional of the word: the symbols enter with geometric weights, the most recent weighted most, and
the initial condition enters with weight `aⁿ`. -/
theorem seqOrbit_affine (ha : a ≠ 0) (b : ι → ℝ) (w : ℕ → ι) (x : ℝ) (n : ℕ) :
    seqOrbit (fun i x => a * x + b i) w x n
      = a ^ n * (x + ∑ k ∈ Finset.range n, b (w k) / a ^ (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [seqOrbit_succ, ih, Finset.sum_range_succ]
    field_simp
    ring

end Affine

/-! ### The `(3/2)ⁿ` step maps -/

/-- The step maps of the `(3/2)ⁿ` normal form: `ε ↦ (3 ε + c) / 2`, where `c` is the combined
bit/recentring symbol at that time. -/
noncomputable def threeHalvesStep (c : ℝ) (x : ℝ) : ℝ := (3 * x + c) / 2

theorem threeHalvesStep_eq_affine :
    threeHalvesStep = fun (c : ℝ) (x : ℝ) => (3 / 2 : ℝ) * x + c / 2 := by
  funext c x
  rw [threeHalvesStep]
  ring

theorem isUniformlyExpanding_threeHalvesStep :
    IsUniformlyExpanding threeHalvesStep (3 / 2 : ℝ) := by
  rw [threeHalvesStep_eq_affine]
  exact isUniformlyExpanding_affine (by norm_num) _

/-- **Weak memory loss for the `(3/2)ⁿ` normal form.**  Two points driven by the same
bit/recentring word, whose orbits stay within `D` of each other, are within `D * (2/3)ⁿ` — for every
`n`. -/
theorem dist_le_mul_two_thirds_pow {w : ℕ → ℝ} {x y D : ℝ}
    (hD : ∀ n, dist (seqOrbit threeHalvesStep w x n) (seqOrbit threeHalvesStep w y n) ≤ D)
    (n : ℕ) : dist x y ≤ D * (2 / 3 : ℝ) ^ n := by
  have h := isUniformlyExpanding_threeHalvesStep.dist_le_of_forall_dist_le (by norm_num) hD n
  have h32 : ((3 : ℝ) / 2) ^ n = (((2 : ℝ) / 3) ^ n)⁻¹ := by
    rw [← inv_pow]
    norm_num
  rwa [h32, div_eq_mul_inv, inv_inv] at h

/-- The bit/recentring word of a confined orbit of `x ↦ (3x + c)/2` determines the orbit. -/
theorem eq_of_seqOrbit_threeHalvesStep_dist_le {w : ℕ → ℝ} {x y D : ℝ}
    (hD : ∀ n, dist (seqOrbit threeHalvesStep w x n) (seqOrbit threeHalvesStep w y n) ≤ D) :
    x = y :=
  isUniformlyExpanding_threeHalvesStep.eq_of_forall_dist_le (by norm_num) hD

/-- Orbits confined to `[0, 1)` stay within distance `1` of each other. -/
theorem dist_le_one_of_mem_Ico {u v : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1)
    (hv : v ∈ Set.Ico (0 : ℝ) 1) : dist u v ≤ 1 := by
  rw [Real.dist_eq, abs_le]
  constructor <;> [linarith [hu.1, hv.2]; linarith [hu.2, hv.1]]

/-- **The normal-form box, as a theorem.**  For orbits of the `(3/2)ⁿ` step maps confined to
`[0, 1)`, the Birkhoff sums of a `C`-Lipschitz observable along two orbits with the *same*
bit/recentring word differ by at most `2 * C`, whatever the number of terms — so the empirical
averages differ by at most `2 * C / N`.  Initial data and transients are irrelevant to the empirical
distribution; only the word matters. -/
theorem abs_sum_sub_sum_le_of_mem_Ico {w : ℕ → ℝ} {x y : ℝ} {φ : ℝ → ℝ} {C : NNReal}
    (hφ : LipschitzWith C φ) (hx : ∀ n, seqOrbit threeHalvesStep w x n ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ n, seqOrbit threeHalvesStep w y n ∈ Set.Ico (0 : ℝ) 1) (N : ℕ) :
    |∑ n ∈ Finset.range N, φ (seqOrbit threeHalvesStep w x n)
        - ∑ n ∈ Finset.range N, φ (seqOrbit threeHalvesStep w y n)| ≤ 2 * C := by
  have h := isUniformlyExpanding_threeHalvesStep.abs_sum_sub_sum_le (by norm_num) zero_le_one
    (fun n => dist_le_one_of_mem_Ico (hx n) (hy n)) hφ N
  norm_num at h
  linarith

/-! ### The `(3/2)ⁿ` orbit itself

The hypotheses above are not vacuous: the fractional parts of `(3/2)ⁿ ξ` *are* a sequential orbit of
`threeHalvesStep`, confined to `[0, 1)`, driven by the integer word `cₙ = 3 mₙ - 2 mₙ₊₁` built from
the integer parts `mₙ = ⌊(3/2)ⁿ ξ⌋`.  (The orbit is genuinely sequential and not an autonomous map of
the fractional part: `(3/2) mₙ` is an integer only when `mₙ` is even, so the symbol `cₙ` carries the
parity of `mₙ` as well as the recentring — which is why it is called the bit/recentring word.) -/

/-- The fractional parts of `(3/2)ⁿ ξ` form a sequential orbit of `threeHalvesStep` along the word
`cₙ = 3⌊(3/2)ⁿ ξ⌋ - 2⌊(3/2)ⁿ⁺¹ ξ⌋`. -/
theorem seqOrbit_threeHalvesStep_fract (ξ : ℝ) (n : ℕ) :
    seqOrbit threeHalvesStep
        (fun k => ((3 * ⌊(3 / 2 : ℝ) ^ k * ξ⌋ - 2 * ⌊(3 / 2 : ℝ) ^ (k + 1) * ξ⌋ : ℤ) : ℝ))
        (Int.fract ξ) n = Int.fract ((3 / 2 : ℝ) ^ n * ξ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [seqOrbit_succ, ih, threeHalvesStep, Int.fract, Int.fract]
    push_cast
    ring

/-- **Only the word matters, for the actual `(3/2)ⁿ` orbit.**  If two reals have the same
bit/recentring word at every time, their fractional parts coincide. -/
theorem fract_eq_fract_of_word_eq {ξ η : ℝ}
    (hw : ∀ k : ℕ, (3 * ⌊(3 / 2 : ℝ) ^ k * ξ⌋ - 2 * ⌊(3 / 2 : ℝ) ^ (k + 1) * ξ⌋ : ℤ)
      = 3 * ⌊(3 / 2 : ℝ) ^ k * η⌋ - 2 * ⌊(3 / 2 : ℝ) ^ (k + 1) * η⌋) :
    Int.fract ξ = Int.fract η := by
  have hwfun : (fun k => ((3 * ⌊(3 / 2 : ℝ) ^ k * ξ⌋ - 2 * ⌊(3 / 2 : ℝ) ^ (k + 1) * ξ⌋ : ℤ) : ℝ))
      = fun k => ((3 * ⌊(3 / 2 : ℝ) ^ k * η⌋ - 2 * ⌊(3 / 2 : ℝ) ^ (k + 1) * η⌋ : ℤ) : ℝ) := by
    funext k
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (hw k)
  refine eq_of_seqOrbit_threeHalvesStep_dist_le (D := 1)
    (w := fun k => ((3 * ⌊(3 / 2 : ℝ) ^ k * ξ⌋ - 2 * ⌊(3 / 2 : ℝ) ^ (k + 1) * ξ⌋ : ℤ) : ℝ))
    fun n => ?_
  rw [seqOrbit_threeHalvesStep_fract, hwfun, seqOrbit_threeHalvesStep_fract]
  exact dist_le_one_of_mem_Ico ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

end Dynamics
