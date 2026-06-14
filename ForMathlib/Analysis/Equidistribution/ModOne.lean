/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Real.Cardinality

@[expose] public section

open scoped Topology

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is said to be equidistributed on
an interval `[a, b]` if for every subinterval `[c, d]` of `[a, b]` we have
`lim_{n→ ∞} |{s_1, ..., s_n} ∩ [c, d]| / n = (d - c)/(b-a)`
-/
def IsEquidistributed (a b : ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ c d, c ≤ d → Set.Icc c d ⊆ Set.Icc a b →
  Filter.atTop.Tendsto (fun n => ((Finset.range n).filter
    fun m => s m ∈ Set.Icc c d).card / (n : ℝ)) (𝓝 <| (d - c) / (b - a))

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is said to be equidistributed
modulo 1 or uniformly distributed modulo 1 if the sequence of the fractional parts of
`a_n`, denoted by `(a_n)` or by `a_n − ⌊a_n⌋`, is equidistributed in the interval `[0, 1]`.
-/
def IsEquidistributedModuloOne (s : ℕ → ℝ) : Prop :=
  IsEquidistributed 0 1 (fun n => Int.fract (s n))

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is *dense modulo one* if every interval of
positive length contained in `[0, 1]` contains at least one fractional part `Int.fract (s n)` —
equivalently, the fractional parts `(Int.fract (s n))` are dense in `[0, 1]` (Mathlib's `Dense`).
It is the companion of `IsEquidistributedModuloOne`; uniform distribution implies, and is strictly
stronger than, density modulo one.
-/
def IsDenseModuloOne (s : ℕ → ℝ) : Prop :=
  ∀ c d : ℝ, c < d → Set.Icc c d ⊆ Set.Icc (0 : ℝ) 1 → ∃ n, Int.fract (s n) ∈ Set.Icc c d

/--
`IsDenseModuloOne s` holds iff the fractional parts `Int.fract (s n)` are dense in `[0, 1]`, i.e.
`[0, 1]` is contained in the closure of their range. This links the interval-hitting definition to
Mathlib's topological `closure`. (The fractional parts lie in `[0, 1)`, so they are never dense in all
of `ℝ`; density is *in `[0, 1]`*, not `Dense (Set.range …)`.)
-/
theorem isDenseModuloOne_iff_subset_closure (s : ℕ → ℝ) :
    IsDenseModuloOne s ↔ Set.Icc (0 : ℝ) 1 ⊆ closure (Set.range (fun n => Int.fract (s n))) := by
  constructor
  · intro hdense x hx
    obtain ⟨hx0, hx1⟩ := hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hsub : Set.Icc (max 0 (x - ε / 2)) (min 1 (x + ε / 2)) ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hcd : max 0 (x - ε / 2) < min 1 (x + ε / 2) := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    obtain ⟨n, hn⟩ := hdense _ _ hcd hsub
    rw [Set.mem_Icc] at hn
    have hlb : x - ε / 2 ≤ max 0 (x - ε / 2) := le_max_right _ _
    have hub : min 1 (x + ε / 2) ≤ x + ε / 2 := min_le_right _ _
    refine ⟨Int.fract (s n), Set.mem_range_self n, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hn.1, hn.2]
  · intro hclosure c d hcd hsub
    have hm : (c + d) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
      hsub (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    obtain ⟨y, ⟨n, hyn⟩, hdist⟩ :=
      (Metric.mem_closure_iff.mp (hclosure hm)) ((d - c) / 2) (by linarith)
    have hfy : Int.fract (s n) = y := hyn
    rw [Real.dist_eq, abs_lt] at hdist
    refine ⟨n, Set.mem_Icc.mpr ?_⟩
    rw [hfy]
    exact ⟨by linarith [hdist.2], by linarith [hdist.1]⟩
