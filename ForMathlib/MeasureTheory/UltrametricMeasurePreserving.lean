/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic

@[expose] public section

/-!
# Surjective isometries of ultrametric groups preserve left-invariant measures

In an ultrametric (non-archimedean) space the closed balls of positive radius are **clopen**
(`IsUltrametricDist.isClopen_closedBall`) and pairwise **nested-or-disjoint**, so the collection of
all of them is simultaneously a topological basis and a `π`-system. This makes them an ideal
generating family for measure-uniqueness arguments.

For a second-countable ultrametric *normed additive group* `X` carrying a finite left-invariant
measure `μ`, any two closed balls of the same radius have the same measure (translation invariance),
and a surjective isometry `Φ : X → X` maps each closed ball onto a closed ball of the same radius.
Hence `Φ` preserves the measure of every ball, and by `π`-system uniqueness on the generating basis
it preserves `μ` itself.

The motivating example is the ring of `p`-adic integers `ℤ_[p]` with its additive Haar measure: any
solenoidal homeomorphism (equivalently, `p`-adic isometry) of `ℤ_[p]` is measure-preserving.

## Main statements

* `IsUltrametricDist.isPiSystem_closedBalls`: the closed balls of positive radius form a `π`-system.
* `IsUltrametricDist.isTopologicalBasis_closedBalls`: they form a topological basis.
* `MeasureTheory.measurePreserving_of_surjective_isometry`: a continuous surjective isometry of a
  second-countable ultrametric normed additive group preserves every finite left-invariant measure.
-/

open Metric Set TopologicalSpace MeasureTheory

namespace IsUltrametricDist

/-- The collection of all closed balls of *positive* radius in a (pseudo)metric space. In an
ultrametric space this is both a topological basis (`isTopologicalBasis_closedBalls`) and a
`π`-system (`isPiSystem_closedBalls`). -/
def closedBalls (X : Type*) [PseudoMetricSpace X] : Set (Set X) :=
  {B | ∃ (c : X) (r : ℝ), 0 < r ∧ B = closedBall c r}

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

/-- In an ultrametric space, two closed balls that meet are nested: if `r ≤ r'` and the balls
`closedBall c r`, `closedBall c' r'` share a point, then the former is contained in the latter.
This is the strong triangle inequality `dist x z ≤ max (dist x y) (dist y z)`. -/
theorem closedBall_subset_closedBall_of_mem {c c' : X} {r r' : ℝ} (hrr : r ≤ r')
    {z : X} (hz : z ∈ closedBall c r) (hz' : z ∈ closedBall c' r') :
    closedBall c r ⊆ closedBall c' r' := by
  rw [mem_closedBall] at hz hz'
  intro w hw
  rw [mem_closedBall] at hw ⊢
  have h1 : dist w z ≤ r := by
    refine (IsUltrametricDist.dist_triangle_max w c z).trans ?_
    rw [max_le_iff]; exact ⟨hw, by rw [dist_comm]; exact hz⟩
  refine (IsUltrametricDist.dist_triangle_max w z c').trans ?_
  rw [max_le_iff]; exact ⟨h1.trans hrr, hz'⟩

/-- **The closed balls of positive radius form a `π`-system in an ultrametric space.** Two such
balls are nested-or-disjoint, so a nonempty intersection equals the smaller ball. -/
theorem isPiSystem_closedBalls : IsPiSystem (closedBalls X) := by
  rintro s ⟨c, r, hr, rfl⟩ t ⟨c', r', hr', rfl⟩ hst
  obtain ⟨z, hz⟩ := hst
  rcases le_total r r' with h | h
  · rw [inter_eq_left.mpr (closedBall_subset_closedBall_of_mem h hz.1 hz.2)]
    exact ⟨c, r, hr, rfl⟩
  · rw [inter_eq_right.mpr (closedBall_subset_closedBall_of_mem h hz.2 hz.1)]
    exact ⟨c', r', hr', rfl⟩

/-- **The closed balls of positive radius form a topological basis in an ultrametric space.** Each is
open (closed balls are clopen here), and every open set is a neighbourhood union of them: a metric
ball `ball a ε ⊆ u` contains the clopen `closedBall a (ε/2) ∋ a`. -/
theorem isTopologicalBasis_closedBalls : IsTopologicalBasis (closedBalls X) := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => ?_) (fun a u ha hu => ?_)
  · obtain ⟨c, r, hr, rfl⟩ := hu
    exact IsUltrametricDist.isOpen_closedBall c (ne_of_gt hr)
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu a ha
    refine ⟨closedBall a (ε / 2), ⟨a, ε / 2, by positivity, rfl⟩,
      by simp [mem_closedBall, le_of_lt, hε], ?_⟩
    exact (closedBall_subset_ball (by linarith)).trans hball

end IsUltrametricDist

namespace MeasureTheory

open IsUltrametricDist

/-- **A surjective isometry of a second-countable ultrametric normed additive group preserves every
finite left-invariant measure.**

The closed balls of positive radius generate the Borel `σ`-algebra (they form a topological basis)
and form a `π`-system, so by measure-uniqueness it suffices that `Φ` preserves the measure of each
ball. Two balls of equal radius have equal measure by left-invariance (translation), and the
isometry `Φ` maps `closedBall (Φ a) r` back to `closedBall a r`; combined with surjectivity this
shows `(Measure.map Φ μ) (closedBall c r) = μ (closedBall c r)` for every ball.

For `X = ℤ_[p]` with additive Haar measure this says every `p`-adic isometry is measure-preserving. -/
theorem measurePreserving_of_surjective_isometry
    {X : Type*} [NormedAddCommGroup X] [IsUltrametricDist X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    {Φ : X → X} (hcont : Continuous Φ) (hisom : Isometry Φ) (hsurj : Function.Surjective Φ) :
    MeasurePreserving Φ μ μ := by
  have hΦmeas : Measurable Φ := hcont.measurable
  -- All closed balls of a given radius have the same measure (translation invariance).
  have hball_eq : ∀ (c c' : X) (r : ℝ), μ (closedBall c r) = μ (closedBall c' r) := by
    intro c c' r
    have hpre : (fun h => (c' - c) + h) ⁻¹' closedBall c' r = closedBall c r := by
      ext x; simp only [Set.mem_preimage, mem_closedBall, dist_eq_norm]
      rw [show (c' - c) + x - c' = x - c by abel]
    have := measure_preimage_add μ (c' - c) (closedBall c' r)
    rw [hpre] at this; exact this
  -- The isometry pulls a ball back to a ball of the same radius.
  have hΦpre : ∀ (a : X) (r : ℝ), Φ ⁻¹' closedBall (Φ a) r = closedBall a r := by
    intro a r; ext x; simp only [Set.mem_preimage, mem_closedBall]
    rw [hisom.dist_eq]
  -- The balls generate the Borel σ-algebra.
  have hgen : (‹MeasurableSpace X› = MeasurableSpace.generateFrom (closedBalls X)) := by
    rw [BorelSpace.measurable_eq (α := X)]
    exact isTopologicalBasis_closedBalls.borel_eq_generateFrom
  refine ⟨hΦmeas, ?_⟩
  symm
  refine ext_of_generate_finite (closedBalls X) hgen isPiSystem_closedBalls ?_ ?_
  · rintro s ⟨c, r, hr, rfl⟩
    obtain ⟨a, ha⟩ := hsurj c
    rw [Measure.map_apply hΦmeas measurableSet_closedBall, ← ha, hΦpre a r]
    exact hball_eq (Φ a) a r
  · rw [Measure.map_apply hΦmeas MeasurableSet.univ, Set.preimage_univ]

end MeasureTheory
