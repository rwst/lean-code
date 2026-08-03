/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

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
Half-open counting. `IsEquidistributed` is stated with *closed* subintervals, but the natural
targets of an equidistribution statement (digit blocks, arcs of a partition) are half-open: they
tile without overlapping. For `0 ≤ c ≤ d ≤ 1` the proportion of indices `n < N` with
`Int.fract (s n) ∈ [c, d)` tends to `d - c` as well.

The two counts differ by the indices with `Int.fract (s n) = d`, and those are counted by the
*degenerate* closed interval `[d, d]`, whose density the hypothesis says is `d - d = 0`. So no
approximation argument is needed — the boundary is killed by an instance of the same hypothesis.
-/
theorem IsEquidistributedModuloOne.tendsto_count_Ico {s : ℕ → ℝ}
    (h : IsEquidistributedModuloOne s) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    Filter.atTop.Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Int.fract (s n) ∈ Set.Ico c d).card : ℝ) / N)
      (𝓝 (d - c)) := by
  have hIcc := h c d hcd (Set.Icc_subset_Icc hc hd)
  have hpt := h d d le_rfl (Set.Icc_subset_Icc (hc.trans hcd) hd)
  simp only [sub_zero, div_one, sub_self] at hIcc hpt
  -- monotonicity of `· / N` on the nonnegative counts
  have key : ∀ (u v N : ℕ), u ≤ v → (u : ℝ) / N ≤ (v : ℝ) / N := by
    intro u v N huv
    have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    have huv' : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
    calc (u : ℝ) / N = (u : ℝ) * (1 / (N : ℝ)) := by ring
      _ ≤ (v : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right huv' hN
      _ = (v : ℝ) / N := by ring
  have hle : ∀ N : ℕ,
      ((Finset.range N).filter fun n => Int.fract (s n) ∈ Set.Ico c d).card
        ≤ ((Finset.range N).filter fun n => Int.fract (s n) ∈ Set.Icc c d).card := by
    intro N
    refine Finset.card_le_card fun n hn => ?_
    simp only [Finset.mem_filter, Set.mem_Ico, Set.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.le⟩
  have hge : ∀ N : ℕ,
      ((Finset.range N).filter fun n => Int.fract (s n) ∈ Set.Icc c d).card
        ≤ ((Finset.range N).filter fun n => Int.fract (s n) ∈ Set.Ico c d).card
          + ((Finset.range N).filter fun n => Int.fract (s n) ∈ Set.Icc d d).card := by
    intro N
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_union, Set.mem_Ico, Set.mem_Icc] at hn ⊢
    rcases lt_or_eq_of_le hn.2.2 with hlt | heq
    · exact Or.inl ⟨hn.1, hn.2.1, hlt⟩
    · exact Or.inr ⟨hn.1, heq.ge, heq.le⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using hIcc.sub hpt) hIcc
    (fun N => ?_) (fun N => hle N |> key _ _ N)
  have h1 := key _ _ N (hge N)
  rw [Nat.cast_add, add_div] at h1
  linarith

/--
**Weyl's criterion** condition for a real sequence `(xₙ)`: the exponential sums
`(1/N) Σ_{n<N} e^{2πi h xₙ}` vanish in the limit, for every non-zero integer `h`.

Weyl's theorem is that this is equivalent to `IsEquidistributedModuloOne` — in this development,
`Bertin.uniformlyDistributedModOne_iff_weylCriterion` chained with
`Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne`, or directly
`Bugeaud.theorem_1_2_weyl`.

This definition is shared: it is the single home for the notion used by both the `BertinPisot`
development (Bertin, Theorem 4.3.2) and the `Bugeaud` chapters (Bugeaud, Theorem 1.2), which
formerly each carried a character-for-character identical private copy.

References: Weyl, H. "Über die Gleichverteilung von Zahlen mod. Eins." *Math. Ann.* 77 (1916),
313–352; Kuipers, L. and Niederreiter, H. *Uniform Distribution of Sequences*, Wiley 1974,
Theorem 1.2.1; Bertin, M.-J. et al. *Pisot and Salem Numbers*, Birkhäuser 1992, Theorem 4.3.2;
Bugeaud, Y. *Distribution Modulo One and Diophantine Approximation*, CUP 2012, Theorem 1.2.
-/
noncomputable def WeylCriterion (x : ℕ → ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Filter.Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * h * x n)) / N)
      Filter.atTop (𝓝 0)

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
