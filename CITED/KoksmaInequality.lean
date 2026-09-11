/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Koksma's inequality (KN74 Ch. 2, Thm 5.1)

The classical bridge between *discrepancy* and *integration error*:

> **Theorem 5.1 (Koksma's inequality).**  Let `f` be a function on `I = [0,1]` of bounded
> variation `V(f)`, and let `x₁, …, x_N ∈ I` have star discrepancy `D*_N`.  Then
> `|N⁻¹ ∑ f(xₙ) − ∫₀¹ f| ≤ V(f) · D*_N`.

The proof in [KN74] is half a page: Lemma 5.1 is the Abel-summation identity
`N⁻¹∑f(xₙ) − ∫₀¹f = ∑_{n=0}^{N} ∫_{xₙ}^{x_{n+1}} (t − n/N)\,df(t)` (with `x₀ = 0`, `x_{N+1} = 1`),
and Theorem 5.1 follows because `|t − n/N| ≤ D*_N` on each subinterval, by that chapter's
Theorem 1.4.  It is recorded here as a cited `axiom` rather than proved, because Mathlib has no
star discrepancy at all: the definition below is new, and a formal proof would need the
Riemann–Stieltjes half of `eVariationOn` as well.

## What is here

* `starDiscrepancy` — `D*_N(x) = sup_{0 ≤ a ≤ 1} |N⁻¹ #{n < N : {xₙ} ∈ [0,a)} − a|`, together
  with `starDiscrepancy_nonneg`, `starDiscrepancy_le_one` and `starDiscrepancy_fract` (the
  definition already reduces mod one, so it is unchanged by reducing the input);
* `abs_average_sub_integral_le` — **Koksma's inequality**, the cited `axiom`, for points in
  `[0,1)`;
* `abs_average_sub_integral_le_of_periodic` — [KN74]'s own remark after Theorem 5.1, that the
  inequality holds for *arbitrary* real `xₙ` as soon as `f` is 1-periodic.  Proved from the
  axiom, since `f(xₙ) = f({xₙ})` and `D*` does not see the reduction.  **This is the form that
  a sequence `(ξαⁿ)` needs**, its terms being nowhere near `[0,1]`.

## The consumer

The step to a discrepancy *lower* bound out of a Weyl-sum lower bound — the shape used by
`note-1061-M5.html` Corollary 4, `liminf D*_N ≥ max_h |G_p(h)|/(4√2 h)` — needs one more
ingredient, the total variation of the characters, `V(cos 2πhx) = V(sin 2πhx) = 4h` on `[0,1]`.
That is **proved**, not assumed, in `ForMathlib/Analysis/BoundedVariation/Trigonometric.lean`
(Mathlib knows a monotone function has bounded variation but not what it is), and
`BB61/DiscrepancyFloor.lean` assembles the two into the floor.  So `abs_average_sub_integral_le`
below is the *only* thing that chain takes on citation.

What is **not** here is the companion equivalence "`(xₙ)` is u.d. mod one iff `D*_N → 0`"
([KN74] Ch. 2, §1), which nothing in the repository needs.

Note that "Koksma" is overloaded in this repository: `BertinPisot/KoksmasTheorem.lean` is
Koksma's *metric* theorem (Bertin §4.5) and `[Kok45]` in `DistributionModOne/` is his 1945
metric-approximation paper.  The inequality is a third, unrelated result.

## References
* [KN74] Kuipers, L. and Niederreiter, H. *Uniform Distribution of Sequences.* Wiley, 1974 —
  Ch. 2, §5, Lemma 5.1 and Theorem 5.1 (Koksma's inequality); the multidimensional
  Koksma–Hlawka inequality is Theorem 5.5 of the same section.
* [Kok43] Koksma, J. F. "Een algemeene stelling uit de theorie der gelijkmatige verdeeling
  modulo 1." *Mathematica B (Zutphen)* **11** (1942/43), 7–11 — the original.
-/

open scoped Classical

namespace Koksma

/-- The set of local discrepancies `|N⁻¹ #{n < N : {xₙ} < a} − a|` over `a ∈ [0,1]`, whose
supremum is the star discrepancy. -/
@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
def discSet (x : ℕ → ℝ) (N : ℕ) : Set ℝ :=
  {d : ℝ | ∃ a ∈ Set.Icc (0 : ℝ) 1,
    d = |(((Finset.range N).filter fun n => Int.fract (x n) < a).card : ℝ) / N - a|}

/-- **The star discrepancy** `D*_N` of the first `N` terms of a real sequence, taken modulo one:
`D*_N = sup_{0 ≤ a ≤ 1} |N⁻¹ #{n < N : {xₙ} ∈ [0,a)} − a|`.  Mathlib has no discrepancy. -/
@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
noncomputable def starDiscrepancy (x : ℕ → ℝ) (N : ℕ) : ℝ := sSup (discSet x N)

@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
theorem zero_mem_discSet (x : ℕ → ℝ) (N : ℕ) : (0 : ℝ) ∈ discSet x N := by
  refine ⟨0, Set.left_mem_Icc.mpr zero_le_one, ?_⟩
  have hempty : ((Finset.range N).filter fun n => Int.fract (x n) < (0 : ℝ)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun n _ => not_lt.mpr (Int.fract_nonneg _)
  rw [hempty]
  simp

@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
theorem discSet_le_one {x : ℕ → ℝ} {N : ℕ} {d : ℝ} (hd : d ∈ discSet x N) : d ≤ 1 := by
  obtain ⟨a, ha, rfl⟩ := hd
  have hcard : (((Finset.range N).filter fun n => Int.fract (x n) < a).card : ℝ) ≤ N := by
    have := Finset.card_filter_le (Finset.range N) fun n => Int.fract (x n) < a
    rw [Finset.card_range] at this
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      Nat.cast_zero, div_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg ha.1]
    exact ha.2
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h0 : (0 : ℝ) ≤ (((Finset.range N).filter fun n => Int.fract (x n) < a).card : ℝ) / N :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hNpos)
    have h1 : (((Finset.range N).filter fun n => Int.fract (x n) < a).card : ℝ) / N ≤ 1 :=
      (div_le_one hNpos).mpr hcard
    rw [abs_le]
    constructor <;> [linarith [ha.2]; linarith [ha.1]]

@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
theorem discSet_bddAbove (x : ℕ → ℝ) (N : ℕ) : BddAbove (discSet x N) :=
  ⟨1, fun _ hd => discSet_le_one hd⟩

@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
theorem starDiscrepancy_nonneg (x : ℕ → ℝ) (N : ℕ) : 0 ≤ starDiscrepancy x N :=
  le_csSup (discSet_bddAbove x N) (zero_mem_discSet x N)

@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
theorem starDiscrepancy_le_one (x : ℕ → ℝ) (N : ℕ) : starDiscrepancy x N ≤ 1 := by
  exact csSup_le ⟨0, zero_mem_discSet x N⟩ fun _ hd => discSet_le_one hd

/-- The discrepancy reduces its input mod one already, so reducing beforehand changes nothing. -/
@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
theorem starDiscrepancy_fract (x : ℕ → ℝ) (N : ℕ) :
    starDiscrepancy (fun n => Int.fract (x n)) N = starDiscrepancy x N := by
  simp only [starDiscrepancy, discSet, Int.fract_fract]

/-- **Koksma's inequality** ([KN74] Ch. 2, Thm 5.1).  For `f` of bounded variation on `[0,1]`
and points `xₙ ∈ [0,1)`, the error of the equal-weight quadrature rule is at most the total
variation times the star discrepancy.  A cited `axiom`: the proof is Abel summation against the
Stieltjes measure `df`, and neither the discrepancy nor that integration by parts is in
Mathlib. -/
@[category research solved, AMS 11, ref "KN74", group "koksma_inequality"]
axiom abs_average_sub_integral_le {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) {x : ℕ → ℝ}
    (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1) (N : ℕ) :
    |(∑ n ∈ Finset.range N, f (x n)) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ (eVariationOn f (Set.Icc (0 : ℝ) 1)).toReal * starDiscrepancy x N

/-- A 1-periodic function does not see the reduction mod one. -/
@[category API, AMS 11, ref "KN74", group "koksma_inequality"]
theorem periodic_fract {f : ℝ → ℝ} (hper : Function.Periodic f 1) (y : ℝ) :
    f (Int.fract y) = f y := by
  have h := hper.sub_int_mul_eq (x := y) ⌊y⌋
  rw [mul_one] at h
  rw [Int.fract]
  exact h

/-- **Koksma's inequality for a periodic integrand** ([KN74], the remark after Thm 5.1): for
1-periodic `f` the points `xₙ` need not lie in `[0,1]` at all.  This is the form an orbit
`(ξαⁿ)` needs.  Proved from the axiom: `f(xₙ) = f({xₙ})` and the discrepancy is unchanged. -/
@[category research solved, AMS 11, ref "KN74", group "koksma_inequality"]
theorem abs_average_sub_integral_le_of_periodic {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) (hper : Function.Periodic f 1)
    (x : ℕ → ℝ) (N : ℕ) :
    |(∑ n ∈ Finset.range N, f (x n)) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ (eVariationOn f (Set.Icc (0 : ℝ) 1)).toReal * starDiscrepancy x N := by
  have hmem : ∀ n, Int.fract (x n) ∈ Set.Ico (0 : ℝ) 1 :=
    fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have h := abs_average_sub_integral_le hf hmem N
  rw [starDiscrepancy_fract] at h
  simpa only [periodic_fract hper] using h

end Koksma
