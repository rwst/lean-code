/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Positivity

/-!
# Natural (asymptotic) density of a set of naturals

The **natural density** of `A ⊆ ℕ` is the limit, if it exists, of `|A ∩ [0, n)| / n`.  Mathlib
has Schnirelmann density (`Mathlib/Combinatorics/Schnirelmann.lean`) and lists the asymptotic
densities as a TODO there; `Mathlib/MeasureTheory/Function/Intersectivity.lean` carries a
"once we have a natural density API" TODO of its own.  This file is that missing piece, in the
minimal form the statement "the proportion of … tends to `d`" needs.

## Main definitions

* `natDensityCount A n` — the counting function `|A ∩ [0, n)|`, as a `Finset.card`;
* `HasNatDensity A d` — `A` has natural density `d`, i.e. `natDensityCount A n / n → d`.  This is
  the workhorse: it asserts *both* that the limit exists and its value;
* `natDensity A` — the value, defined as a `limUnder` and therefore junk when the limit does not
  exist.  Use `HasNatDensity` in hypotheses and conclusions; `HasNatDensity.natDensity_eq`
  converts.

## Main statements

* `HasNatDensity.unique`, `HasNatDensity.natDensity_eq`;
* `hasNatDensity_empty`, `hasNatDensity_univ`, `HasNatDensity.nonneg`, `HasNatDensity.le_one`,
  `HasNatDensity.compl`;
* `hasNatDensity_iff_ratCast` — a rational density value may be tested in `ℚ` rather than `ℝ`,
  which is what a statement phrased with rational partial ratios needs.

Following `schnirelmannDensity`, the definitions take a `DecidablePred (· ∈ A)` instance
argument, so that they compute in explicit cases; the value does not depend on the instance.

## TODO

Upper and lower densities (as a `limsup`/`liminf`), invariance under finite symmetric difference,
and additivity on disjoint unions.
-/

open Filter Topology Finset

variable {A B : Set ℕ}

/-- The counting function of `A ⊆ ℕ`: the number of elements of `A` below `n`. -/
def natDensityCount (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  #{a ∈ range n | a ∈ A}

section Count

variable [DecidablePred (· ∈ A)]

@[simp] theorem natDensityCount_zero : natDensityCount A 0 = 0 := by
  simp [natDensityCount]

theorem natDensityCount_succ (n : ℕ) :
    natDensityCount A (n + 1) = natDensityCount A n + if n ∈ A then 1 else 0 := by
  unfold natDensityCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem natDensityCount_le (n : ℕ) : natDensityCount A n ≤ n := by
  unfold natDensityCount
  simpa using Finset.card_filter_le (range n) (· ∈ A)

/-- The elements of `A` below `n` and those of `Aᶜ` below `n` together make up all of `[0, n)`. -/
theorem natDensityCount_add_compl (n : ℕ) [DecidablePred (· ∈ Aᶜ)] :
    natDensityCount A n + natDensityCount Aᶜ n = n := by
  unfold natDensityCount
  have h : ({a ∈ range n | a ∈ Aᶜ} : Finset ℕ) = {a ∈ range n | ¬ a ∈ A} :=
    Finset.filter_congr fun a _ => by simp [Set.mem_compl_iff]
  rw [h]
  simpa using Finset.card_filter_add_card_filter_not (s := range n) (p := (· ∈ A))

end Count

/-- `A ⊆ ℕ` has natural (asymptotic) density `d`: the proportion of elements of `A` below `n`
tends to `d` as `n → ∞`. -/
def HasNatDensity (A : Set ℕ) [DecidablePred (· ∈ A)] (d : ℝ) : Prop :=
  Tendsto (fun n => (natDensityCount A n : ℝ) / n) atTop (𝓝 d)

/-- The natural density of `A ⊆ ℕ`.  This is junk unless `A` has a density; the `Prop`-valued
`HasNatDensity` is the statement to use. -/
noncomputable def natDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  limUnder atTop fun n => (natDensityCount A n : ℝ) / n

section Density

variable [DecidablePred (· ∈ A)] {d d₁ d₂ : ℝ}

theorem HasNatDensity.unique (h₁ : HasNatDensity A d₁) (h₂ : HasNatDensity A d₂) : d₁ = d₂ :=
  tendsto_nhds_unique h₁ h₂

theorem HasNatDensity.natDensity_eq (h : HasNatDensity A d) : natDensity A = d :=
  h.limUnder_eq

theorem hasNatDensity_empty : HasNatDensity (∅ : Set ℕ) 0 := by
  have h : ∀ n : ℕ, ((natDensityCount (∅ : Set ℕ) n : ℝ) / n) = 0 := by
    intro n; simp [natDensityCount]
  simp [HasNatDensity, h]

theorem hasNatDensity_univ : HasNatDensity (Set.univ : Set ℕ) 1 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp [natDensityCount, div_self hne]

theorem HasNatDensity.nonneg (h : HasNatDensity A d) : 0 ≤ d :=
  ge_of_tendsto h <| Eventually.of_forall fun n => by positivity

theorem HasNatDensity.le_one (h : HasNatDensity A d) : d ≤ 1 := by
  refine le_of_tendsto h <| Eventually.of_forall fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast natDensityCount_le n

/-- Complementation: if `A` has density `d`, then `Aᶜ` has density `1 - d`. -/
theorem HasNatDensity.compl [DecidablePred (· ∈ Aᶜ)] (h : HasNatDensity A d) :
    HasNatDensity Aᶜ (1 - d) := by
  refine (tendsto_const_nhds.sub h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum : (natDensityCount A n : ℝ) + (natDensityCount Aᶜ n : ℝ) = n := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (natDensityCount_add_compl (A := A) n)
  field_simp
  linarith

/-- A rational density value may be tested in `ℚ`: `ℚ` carries the topology induced from `ℝ`. -/
theorem hasNatDensity_iff_ratCast (q : ℚ) :
    HasNatDensity A (q : ℝ) ↔
      Tendsto (fun n => (natDensityCount A n : ℚ) / n) atTop (𝓝 q) := by
  have hcast : ∀ n : ℕ,
      (((natDensityCount A n : ℚ) / n : ℚ) : ℝ) = (natDensityCount A n : ℝ) / n := by
    intro n; push_cast; ring
  constructor
  · intro h
    rw [Rat.isUniformEmbedding_coe_real.isEmbedding.tendsto_nhds_iff]
    exact h.congr fun n => (hcast n).symm
  · intro h
    exact ((Rat.isUniformEmbedding_coe_real.isEmbedding.tendsto_nhds_iff).mp h).congr hcast

end Density
