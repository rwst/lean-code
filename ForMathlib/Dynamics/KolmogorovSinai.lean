/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Subadditive
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# Kolmogorov–Sinai (measure-theoretic) entropy

Mathlib carries *topological* entropy (`Mathlib/Dynamics/TopologicalEntropy/`) but no
measure-theoretic entropy.  This file supplies the missing definitions and the cheap lemmas around
them, for a measure-preserving map `T` of a probability space:

* `MeasureTheory.partitionEntropy μ f` — the Shannon entropy `H_μ(P) = ∑_A -μ(A) log μ(A)` of a
  finite measurable partition `P`;
* `MeasureTheory.joinIter T f n` — the dynamical join `P ∨ T⁻¹P ∨ ⋯ ∨ T^{-(n-1)}P`;
* `MeasureTheory.entropyRate T μ f` — the entropy `h_μ(T, P)` of `T` relative to `P`, i.e. the
  Fekete limit of `H_μ(⋁_{i<n} T^{-i}P) / n`;
* `MeasureTheory.kolmogorovSinai T μ` — the entropy `h_μ(T) = sup_P h_μ(T, P)`.

## Two design decisions

**Partitions are finite-valued observables.**  A finite measurable partition of `α` is recorded here
as a map `f : α → ι` into a `Fintype`, the partition being the family of fibers `f⁻¹{i}` (empty
fibers are allowed and cost nothing, since `negMulLog 0 = 0`).  This is not a restriction — every
finite partition arises this way — and it buys a great deal: fibers are automatically pairwise
disjoint and cover `α`, so no partition axioms have to be carried around; measurability is the
single hypothesis `∀ i, MeasurableSet (f ⁻¹' {i})`; and the join of two partitions is simply the
pair map `x ↦ (f x, g x)`, whose fiber over `(i, j)` is `f⁻¹{i} ∩ g⁻¹{j}` by `rfl`-level reasoning.

**`kolmogorovSinai` takes values in `ℝ≥0∞`.**  The supremum over *all* finite partitions is
genuinely `[0, ∞]`-valued (already for a Bernoulli shift on an infinite alphabet), so `ℝ` is not a
total codomain: `sSup` of an unbounded set of reals would silently return the junk value `0`.  The
entropy of a *fixed* partition, by contrast, is a finite real, so `partitionEntropy` and
`entropyRate` are `ℝ`-valued and the coercion `ENNReal.ofReal` happens only at the supremum.

## Main results

* `partitionEntropy_nonneg`, `partitionEntropy_le_log_card` — `0 ≤ H_μ(P) ≤ log |P|`.
* `partitionEntropy_comp_le` — entropy is monotone under refinement: a coarsening `φ ∘ f` of `f`
  has smaller entropy.
* `partitionEntropy_pair_le` — subadditivity `H_μ(P ∨ Q) ≤ H_μ(P) + H_μ(Q)`.  This is the engine:
  applied along the orbit it makes `n ↦ H_μ(⋁_{i<n} T^{-i}P)` a subadditive sequence, so Fekete's
  lemma (`Subadditive.tendsto_lim`) gives the limit defining `entropyRate`.
* `tendsto_partitionEntropy_joinIter_div` — `H_μ(⋁_{i<n} T^{-i}P) / n → h_μ(T, P)`.
* `entropyRate_comp`, `kolmogorovSinai_of_measurableEquiv` — both are isomorphism invariants: they
  transfer along a measure-preserving (measurable) equivalence intertwining the two maps.
* `partitionEntropy_const`, `entropyRate_const` — the trivial partition has zero entropy.

The combinatorial core of subadditivity is stated separately for a finite joint distribution and its
marginals, `Real.sum_negMulLog_le_add_of_marginals`, on top of two pointwise lemmas
(`Real.negMulLog_add_mul_log_le`, the `log x ≤ x - 1` form of Gibbs' inequality, and
`Real.negMulLog_sum_le_sum_negMulLog`, superadditivity under grouping).  All three are stated in
terms of `Real.negMulLog` alone and belong upstream in
`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`.

Note that no *lower* bound on `h_μ(T)` is proved here for any particular system: the only entropy
computed is the trivial partition's.  Positivity of entropy for a given map is exactly the kind of
statement this file is meant to let its users state, not one it can supply.

## Deliberately out of scope

Generators and the Kolmogorov–Sinai generator theorem, conditional entropy, the variational
principle, and affinity of `μ ↦ h_μ(T)` in `μ`.  Those are substantial theorems rather than
definitions; nothing here depends on them, and this file is not the place to start them.

## References

* Kolmogorov, A. N. *A new metric invariant of transient dynamical systems and automorphisms of
  Lebesgue spaces.* Dokl. Akad. Nauk SSSR **119** (1958), 861–864.
* Sinai, Ya. G. *On the concept of entropy for a dynamic system.* Dokl. Akad. Nauk SSSR **124**
  (1959), 768–771.
* Walters, Peter. *An Introduction to Ergodic Theory.* GTM 79, Springer, 1982, Chapter 4.
* Petersen, Karl. *Ergodic Theory.* Cambridge Univ. Press, 1983, Chapter 5.
* Einsiedler, Manfred and Ward, Thomas. *Ergodic Theory with a view towards Number Theory.* GTM
  259, Springer, 2011, Chapter 4.
-/

open Filter Topology
open scoped ENNReal

namespace Real

/-- **Gibbs' inequality, pointwise.**  For `0 ≤ r ≤ s` (more precisely: `r, s ≥ 0` with `s > 0`
whenever `r > 0`), `r log(s/r) ≤ s - r`.  Summing this over a pair of probability vectors is the
standard proof both of `H ≤ log n` and of subadditivity of Shannon entropy; the `r = 0` case is
where Mathlib's junk value `log 0 = 0` is absorbed. -/
theorem negMulLog_add_mul_log_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : 0 < r → 0 < s) :
    negMulLog r + r * log s ≤ s - r := by
  rcases hr.eq_or_lt with h | hr0
  · subst h; simpa using hs
  · have hs0 : 0 < s := hrs hr0
    have h1 : log (s / r) ≤ s / r - 1 := log_le_sub_one_of_pos (div_pos hs0 hr0)
    have h2 : r * log (s / r) ≤ r * (s / r - 1) := mul_le_mul_of_nonneg_left h1 hr
    rw [log_div hs0.ne' hr0.ne', mul_sub, show r * (s / r - 1) = s - r by field_simp] at h2
    have e : negMulLog r + r * log s = r * log s - r * log r := by
      show -r * log r + r * log s = _
      ring
    rw [e]
    exact h2

/-- **Grouping decreases entropy, pointwise.**  Lumping the cells of a partition together can only
decrease Shannon entropy: `negMulLog` is superadditive on nonnegative reals. -/
theorem negMulLog_sum_le_sum_negMulLog {ι : Type*} {s : Finset ι} {p : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) : negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, negMulLog (p i) := by
  have hP0 : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg hp
  rcases hP0.eq_or_lt with h | hPpos
  · have hzero : ∀ i ∈ s, p i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hp).1 h.symm
    have h1 : negMulLog (∑ i ∈ s, p i) = 0 := by rw [← h, negMulLog_zero]
    have h2 : ∑ i ∈ s, negMulLog (p i) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hzero i hi, negMulLog_zero]
    rw [h1, h2]
  · have step : ∀ i ∈ s, -(p i * log (∑ k ∈ s, p k)) ≤ negMulLog (p i) := by
      intro i hi
      have hmul : p i * log (p i) ≤ p i * log (∑ k ∈ s, p k) := by
        rcases (hp i hi).eq_or_lt with h0 | h0
        · simp [← h0]
        · exact mul_le_mul_of_nonneg_left (log_le_log h0 (Finset.single_le_sum hp hi)) (hp i hi)
      have e : negMulLog (p i) = -(p i * log (p i)) := by show -p i * log (p i) = _; ring
      rw [e]
      exact neg_le_neg hmul
    calc negMulLog (∑ i ∈ s, p i) = ∑ i ∈ s, -(p i * log (∑ k ∈ s, p k)) := by
          rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
          show -(∑ i ∈ s, p i) * log (∑ k ∈ s, p k) = _
          ring
      _ ≤ ∑ i ∈ s, negMulLog (p i) := Finset.sum_le_sum step

/-- **Subadditivity of Shannon entropy**, for a finite joint distribution `r` with marginals `p`
and `q`: the entropy of `r` is at most the sum of the entropies of its marginals.  This is the
combinatorial core of `MeasureTheory.partitionEntropy_pair_le`; the proof is the classical one, a
summed form of `Real.negMulLog_add_mul_log_le` comparing `r` with the product `p ⊗ q`. -/
theorem sum_negMulLog_le_add_of_marginals {ι κ : Type*} [Fintype ι] [Fintype κ] {r : ι → κ → ℝ}
    {p : ι → ℝ} {q : κ → ℝ} (hr0 : ∀ i j, 0 ≤ r i j) (hp : ∀ i, ∑ j, r i j = p i)
    (hq : ∀ j, ∑ i, r i j = q j) (h1 : ∑ i, p i = 1) :
    ∑ i, ∑ j, negMulLog (r i j) ≤ (∑ i, negMulLog (p i)) + ∑ j, negMulLog (q j) := by
  have hrp : ∀ i j, r i j ≤ p i := fun i j => by
    rw [← hp i]
    exact Finset.single_le_sum (fun j _ => hr0 i j) (Finset.mem_univ j)
  have hrq : ∀ i j, r i j ≤ q j := fun i j => by
    rw [← hq j]
    exact Finset.single_le_sum (fun i _ => hr0 i j) (Finset.mem_univ i)
  have hq1 : ∑ j, q j = 1 := by
    rw [← h1, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => (hq j).symm,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hp i).symm, Finset.sum_comm]
  -- the pointwise Gibbs inequality, at every cell of the join
  have key : ∀ i j, negMulLog (r i j) + r i j * (log (p i) + log (q j)) ≤ p i * q j - r i j := by
    intro i j
    rcases (hr0 i j).eq_or_lt with h0 | h0
    · rw [← h0]
      have hpq : 0 ≤ p i * q j :=
        mul_nonneg ((hr0 i j).trans (hrp i j)) ((hr0 i j).trans (hrq i j))
      simpa using hpq
    · have hpi : 0 < p i := h0.trans_le (hrp i j)
      have hqj : 0 < q j := h0.trans_le (hrq i j)
      rw [← log_mul hpi.ne' hqj.ne']
      exact negMulLog_add_mul_log_le (hr0 i j) (by positivity) fun _ => by positivity
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key i j
  have expand : ∀ i j, negMulLog (r i j) + r i j * (log (p i) + log (q j))
      = negMulLog (r i j) + r i j * log (p i) + r i j * log (q j) := fun i j => by ring
  have hL : ∑ i, ∑ j, (negMulLog (r i j) + r i j * (log (p i) + log (q j)))
      = (∑ i, ∑ j, negMulLog (r i j)) + (∑ i, ∑ j, r i j * log (p i))
        + ∑ i, ∑ j, r i j * log (q j) := by
    simp only [expand, Finset.sum_add_distrib]
  have hB : ∑ i, ∑ j, r i j * log (p i) = ∑ i, p i * log (p i) :=
    Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hp i]
  have hC : ∑ i, ∑ j, r i j * log (q j) = ∑ j, q j * log (q j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hq j]
  have hR : ∑ i, ∑ j, (p i * q j - r i j) = 0 := by
    have step : ∀ i, ∑ j, (p i * q j - r i j) = p i * (∑ j, q j) - p i := fun i => by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp i]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => step i, hq1]
    simp
  have hEp : ∑ i, p i * log (p i) = -∑ i, negMulLog (p i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by show _ = -(-p i * log (p i)); ring
  have hEq : ∑ j, q j * log (q j) = -∑ j, negMulLog (q j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by show _ = -(-q j * log (q j)); ring
  rw [hL, hB, hC, hR, hEp, hEq] at hsum
  linarith

end Real

namespace MeasureTheory

open Real

variable {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Measures of the fibers of a finite-valued map -/

/-- The fibers of a finite-valued map cut any measurable set into finitely many disjoint pieces. -/
theorem sum_measure_inter_fiber [Fintype κ] {g : α → κ} (hg : ∀ j, MeasurableSet (g ⁻¹' {j}))
    (μ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    ∑ j : κ, μ (s ∩ g ⁻¹' {j}) = μ s := by
  have hcover : s = ⋃ j, s ∩ g ⁻¹' {j} := by ext x; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun j => s ∩ g ⁻¹' {j}) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hx hx' => hij ?_
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    exact hx.2.symm.trans hx'.2
  conv_rhs => rw [hcover]
  rw [measure_iUnion hdisj fun j => hs.inter (hg j), tsum_fintype]

/-- The measures of the fibers of a finite-valued map add up to the total mass. -/
theorem sum_measure_fiber [Fintype ι] {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i}))
    (μ : Measure α) : ∑ i : ι, μ (f ⁻¹' {i}) = μ Set.univ := by
  simpa using sum_measure_inter_fiber hf μ MeasurableSet.univ

theorem sum_measure_inter_fiber_toReal [Fintype κ] {μ : Measure α} [IsFiniteMeasure μ] {g : α → κ}
    (hg : ∀ j, MeasurableSet (g ⁻¹' {j})) {s : Set α} (hs : MeasurableSet s) :
    ∑ j : κ, (μ (s ∩ g ⁻¹' {j})).toReal = (μ s).toReal := by
  rw [← ENNReal.toReal_sum fun j _ => measure_ne_top μ _, sum_measure_inter_fiber hg μ hs]

theorem sum_measure_fiber_toReal [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ι}
    (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) : ∑ i : ι, (μ (f ⁻¹' {i})).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun i _ => measure_ne_top μ _, sum_measure_fiber hf, measure_univ,
    ENNReal.toReal_one]

theorem measure_fiber_toReal_le_one {μ : Measure α} [IsProbabilityMeasure μ] (s : Set α) :
    (μ s).toReal ≤ 1 := by
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-! ### Shannon entropy of a finite measurable partition -/

/-- The **Shannon entropy** `H_μ(P) = ∑_A -μ(A) log μ(A)` of the finite measurable partition `P`
given by the fibers of `f : α → ι`. -/
noncomputable def partitionEntropy [Fintype ι] (μ : Measure α) (f : α → ι) : ℝ :=
  ∑ i : ι, negMulLog (μ (f ⁻¹' {i})).toReal

theorem partitionEntropy_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] (f : α → ι) :
    0 ≤ partitionEntropy μ f :=
  Finset.sum_nonneg fun _ _ =>
    negMulLog_nonneg ENNReal.toReal_nonneg (measure_fiber_toReal_le_one _)

/-- The trivial partition `{α}` has zero entropy. -/
@[simp]
theorem partitionEntropy_const [Fintype ι] [DecidableEq ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (i₀ : ι) : partitionEntropy μ (fun _ : α => i₀) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i = i₀
  · subst h
    rw [show (fun _ : α => i) ⁻¹' {i} = Set.univ by ext x; simp, measure_univ,
      ENNReal.toReal_one, negMulLog_one]
  · rw [show (fun _ : α => i₀) ⁻¹' {i} = (∅ : Set α) by ext x; simp [Ne.symm h], measure_empty,
      ENNReal.toReal_zero, negMulLog_zero]

/-- **Entropy is at most the logarithm of the number of cells.** -/
theorem partitionEntropy_le_log_card [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) :
    partitionEntropy μ f ≤ log (Fintype.card ι) := by
  have hsum : ∑ i : ι, (μ (f ⁻¹' {i})).toReal = 1 := sum_measure_fiber_toReal hf
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsum
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have key : ∀ i : ι, negMulLog (μ (f ⁻¹' {i})).toReal
      + (μ (f ⁻¹' {i})).toReal * log ((Fintype.card ι : ℝ)⁻¹)
      ≤ (Fintype.card ι : ℝ)⁻¹ - (μ (f ⁻¹' {i})).toReal := fun i =>
    negMulLog_add_mul_log_le ENNReal.toReal_nonneg (by positivity) fun _ => by positivity
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hsum, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne',
    log_inv] at h
  have : partitionEntropy μ f - log (Fintype.card ι) ≤ 1 - 1 := by
    simpa [partitionEntropy, sub_eq_add_neg] using h
  linarith

/-- Entropy is unchanged by an injective relabelling of the cells. -/
theorem partitionEntropy_comp_injective [Fintype ι] [Fintype κ] {μ : Measure α} (f : α → ι)
    {e : ι → κ} (he : Function.Injective e) :
    partitionEntropy μ (e ∘ f) = partitionEntropy μ f := by
  symm
  refine Fintype.sum_of_injective e he _ _ (fun k hk => ?_) fun i => ?_
  · have hempty : (e ∘ f) ⁻¹' {k} = ∅ := by
      ext x
      simp only [Function.comp_apply, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => hk ⟨f x, h⟩
    rw [hempty, measure_empty, ENNReal.toReal_zero, negMulLog_zero]
  · have : (e ∘ f) ⁻¹' {e i} = f ⁻¹' {i} := by
      ext x
      simp [he.eq_iff]
    rw [this]

/-- Entropy is unchanged by pulling a partition back along a measure-preserving map. -/
theorem partitionEntropy_comp [Fintype ι] {μ : Measure α} {ν : Measure β} {T : α → β}
    (hT : MeasurePreserving T μ ν) {f : β → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) :
    partitionEntropy μ (f ∘ T) = partitionEntropy ν f :=
  Finset.sum_congr rfl fun i _ => by
    rw [show (f ∘ T) ⁻¹' {i} = T ⁻¹' (f ⁻¹' {i}) from rfl,
      hT.measure_preimage (hf i).nullMeasurableSet]

/-- **Entropy is monotone under refinement**: a coarsening `φ ∘ f` of the partition `f` has no more
entropy than `f` itself. -/
theorem partitionEntropy_comp_le [Fintype ι] [Fintype κ] [DecidableEq κ] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) (φ : ι → κ) :
    partitionEntropy μ (φ ∘ f) ≤ partitionEntropy μ f := by
  have hfiber : ∀ k : κ, (μ ((φ ∘ f) ⁻¹' {k})).toReal
      = ∑ i ∈ Finset.univ.filter fun i => φ i = k, (μ (f ⁻¹' {i})).toReal := by
    intro k
    have hset : (φ ∘ f) ⁻¹' {k} = ⋃ i ∈ Finset.univ.filter fun i => φ i = k, f ⁻¹' {i} := by
      ext x
      simp
    have hdisj : (↑(Finset.univ.filter fun i => φ i = k) : Set ι).PairwiseDisjoint
        fun i => f ⁻¹' {i} := by
      intro i _ j _ hij
      refine Set.disjoint_left.mpr fun x hx hx' => hij ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
      exact hx.symm.trans hx'
    rw [hset, measure_biUnion_finset hdisj fun i _ => hf i,
      ENNReal.toReal_sum fun i _ => measure_ne_top μ _]
  calc partitionEntropy μ (φ ∘ f)
      = ∑ k : κ, negMulLog (∑ i ∈ Finset.univ.filter fun i => φ i = k,
          (μ (f ⁻¹' {i})).toReal) := Finset.sum_congr rfl fun k _ => by rw [hfiber k]
    _ ≤ ∑ k : κ, ∑ i ∈ Finset.univ.filter fun i => φ i = k,
          negMulLog (μ (f ⁻¹' {i})).toReal :=
        Finset.sum_le_sum fun k _ =>
          negMulLog_sum_le_sum_negMulLog fun i _ => ENNReal.toReal_nonneg
    _ = partitionEntropy μ f := Finset.sum_fiberwise _ _ _

/-! ### The join of two partitions -/

omit [MeasurableSpace α] in
theorem preimage_pair (f : α → ι) (g : α → κ) (i : ι) (j : κ) :
    (fun x => (f x, g x)) ⁻¹' {(i, j)} = f ⁻¹' {i} ∩ g ⁻¹' {j} := by
  ext x
  simp [Prod.ext_iff]

theorem measurableSet_pair_fiber {f : α → ι} {g : α → κ} (hf : ∀ i, MeasurableSet (f ⁻¹' {i}))
    (hg : ∀ j, MeasurableSet (g ⁻¹' {j})) (z : ι × κ) :
    MeasurableSet ((fun x => (f x, g x)) ⁻¹' {z}) := by
  rw [show z = (z.1, z.2) from rfl, preimage_pair]
  exact (hf z.1).inter (hg z.2)

/-- **Subadditivity of Shannon entropy**: `H_μ(P ∨ Q) ≤ H_μ(P) + H_μ(Q)`, where the join `P ∨ Q` is
the partition into the sets `f⁻¹{i} ∩ g⁻¹{j}`, i.e. the fibers of the pair map. -/
theorem partitionEntropy_pair_le [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ι} {g : α → κ} (hf : ∀ i, MeasurableSet (f ⁻¹' {i}))
    (hg : ∀ j, MeasurableSet (g ⁻¹' {j})) :
    partitionEntropy μ (fun x => (f x, g x)) ≤ partitionEntropy μ f + partitionEntropy μ g := by
  have hmarg₁ : ∀ i, ∑ j, (μ (f ⁻¹' {i} ∩ g ⁻¹' {j})).toReal = (μ (f ⁻¹' {i})).toReal := fun i =>
    sum_measure_inter_fiber_toReal hg (hf i)
  have hmarg₂ : ∀ j, ∑ i, (μ (f ⁻¹' {i} ∩ g ⁻¹' {j})).toReal = (μ (g ⁻¹' {j})).toReal := by
    intro j
    rw [← sum_measure_inter_fiber_toReal (μ := μ) hf (hg j)]
    exact Finset.sum_congr rfl fun i _ => by rw [Set.inter_comm]
  have htot : ∑ i, (μ (f ⁻¹' {i})).toReal = 1 := sum_measure_fiber_toReal hf
  have hjoint : partitionEntropy μ (fun x => (f x, g x))
      = ∑ i, ∑ j, negMulLog (μ (f ⁻¹' {i} ∩ g ⁻¹' {j})).toReal := by
    rw [partitionEntropy, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [preimage_pair]
  rw [hjoint]
  exact Real.sum_negMulLog_le_add_of_marginals (fun _ _ => ENNReal.toReal_nonneg) hmarg₁ hmarg₂
    htot

/-! ### The dynamical join and the entropy of a partition relative to `T` -/

/-- The **dynamical join** `P ∨ T⁻¹P ∨ ⋯ ∨ T^{-(n-1)}P`, recorded as the observable
`x ↦ (f x, f (T x), …, f (T^{n-1} x))`. -/
def joinIter (T : α → α) (f : α → ι) (n : ℕ) : α → Fin n → ι := fun x i => f (T^[i] x)

omit [MeasurableSpace α] in
theorem joinIter_one (T : α → α) (f : α → ι) : joinIter T f 1 = (fun i (_ : Fin 1) => i) ∘ f := by
  funext x k
  simp [joinIter, Fin.val_eq_zero]

omit [MeasurableSpace α] in
theorem joinIter_add (T : α → α) (f : α → ι) (m n : ℕ) (x : α) :
    joinIter T f (m + n) x = Fin.append (joinIter T f m x) (joinIter T f n (T^[m] x)) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp [joinIter, Fin.append_left]
  · simp only [joinIter, Fin.append_right, Fin.val_natAdd, ← Function.iterate_add_apply]
    rw [add_comm]

theorem measurableSet_joinIter_fiber {T : α → α} (hT : Measurable T) {f : α → ι}
    (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) (n : ℕ) (w : Fin n → ι) :
    MeasurableSet (joinIter T f n ⁻¹' {w}) := by
  have : joinIter T f n ⁻¹' {w} = ⋂ i : Fin n, T^[i] ⁻¹' (f ⁻¹' {w i}) := by
    ext x
    simp [joinIter, funext_iff]
  rw [this]
  exact MeasurableSet.iInter fun i => (hT.iterate i) (hf (w i))

/-- The map `(u, v) ↦ Fin.append u v` is injective. -/
theorem _root_.Fin.append_pair_injective {m n : ℕ} :
    Function.Injective fun uv : (Fin m → ι) × (Fin n → ι) => Fin.append uv.1 uv.2 := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  simp only at h
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simpa [Fin.append_left] using congrFun h (Fin.castAdd n i)
  · simpa [Fin.append_right] using congrFun h (Fin.natAdd m i)

/-- **The entropy of the dynamical join is subadditive in the length of the window.**  This is the
input to Fekete's lemma. -/
theorem partitionEntropy_joinIter_add_le [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i}))
    (m n : ℕ) :
    partitionEntropy μ (joinIter T f (m + n))
      ≤ partitionEntropy μ (joinIter T f m) + partitionEntropy μ (joinIter T f n) := by
  have hsplit : joinIter T f (m + n)
      = (fun uv : (Fin m → ι) × (Fin n → ι) => Fin.append uv.1 uv.2)
        ∘ fun x => (joinIter T f m x, joinIter T f n (T^[m] x)) := by
    funext x
    exact joinIter_add T f m n x
  rw [hsplit, partitionEntropy_comp_injective _ Fin.append_pair_injective]
  have hiter : MeasurePreserving T^[m] μ μ := hT.iterate m
  calc partitionEntropy μ (fun x => (joinIter T f m x, joinIter T f n (T^[m] x)))
      ≤ partitionEntropy μ (joinIter T f m)
        + partitionEntropy μ (joinIter T f n ∘ T^[m]) :=
        partitionEntropy_pair_le (measurableSet_joinIter_fiber hT.measurable hf m)
          fun w => hiter.measurable (measurableSet_joinIter_fiber hT.measurable hf n w)
    _ = partitionEntropy μ (joinIter T f m) + partitionEntropy μ (joinIter T f n) := by
        rw [partitionEntropy_comp hiter (measurableSet_joinIter_fiber hT.measurable hf n)]

theorem subadditive_partitionEntropy_joinIter [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) :
    Subadditive fun n => partitionEntropy μ (joinIter T f n) := fun m n =>
  partitionEntropy_joinIter_add_le hT hf m n

/-- The **entropy of `T` relative to the partition `P`**, `h_μ(T, P)`: the Fekete limit of
`H_μ(⋁_{i<n} T^{-i}P) / n`, defined unconditionally as the infimum of that sequence (the two agree
whenever `T` preserves the probability measure `μ` and `P` is measurable, by
`tendsto_partitionEntropy_joinIter_div`). -/
noncomputable def entropyRate [Fintype ι] (T : α → α) (μ : Measure α) (f : α → ι) : ℝ :=
  sInf ((fun n : ℕ => partitionEntropy μ (joinIter T f n) / n) '' Set.Ici 1)

theorem entropyRate_eq_subadditiveLim [Fintype ι] {μ : Measure α} {T : α → α} {f : α → ι}
    (h : Subadditive fun n => partitionEntropy μ (joinIter T f n)) :
    h.lim = entropyRate T μ f := by
  rw [Subadditive.lim]
  rfl

private theorem bddBelow_partitionEntropy_joinIter_div [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} {f : α → ι} :
    BddBelow (Set.range fun n : ℕ => partitionEntropy μ (joinIter T f n) / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (partitionEntropy_nonneg _) (Nat.cast_nonneg n)

private theorem bddBelow_image_partitionEntropy_joinIter_div [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} {f : α → ι} :
    BddBelow ((fun n : ℕ => partitionEntropy μ (joinIter T f n) / n) '' Set.Ici 1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, -, rfl⟩
  exact div_nonneg (partitionEntropy_nonneg _) (Nat.cast_nonneg n)

/-- **Fekete's lemma for entropy**: `H_μ(⋁_{i<n} T^{-i}P) / n → h_μ(T, P)`. -/
theorem tendsto_partitionEntropy_joinIter_div [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) :
    Tendsto (fun n : ℕ => partitionEntropy μ (joinIter T f n) / n) atTop
      (𝓝 (entropyRate T μ f)) := by
  have hsub := subadditive_partitionEntropy_joinIter hT hf
  have := hsub.tendsto_lim bddBelow_partitionEntropy_joinIter_div
  rwa [entropyRate_eq_subadditiveLim hsub] at this

theorem entropyRate_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] (T : α → α)
    (f : α → ι) : 0 ≤ entropyRate T μ f := by
  refine le_csInf ⟨_, ⟨1, le_refl 1, rfl⟩⟩ ?_
  rintro x ⟨n, -, rfl⟩
  exact div_nonneg (partitionEntropy_nonneg _) (Nat.cast_nonneg n)

theorem entropyRate_le_partitionEntropy [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (T : α → α) (f : α → ι) : entropyRate T μ f ≤ partitionEntropy μ f := by
  have h : entropyRate T μ f ≤ partitionEntropy μ (joinIter T f 1) / (1 : ℕ) :=
    csInf_le bddBelow_image_partitionEntropy_joinIter_div ⟨1, le_refl 1, rfl⟩
  rw [joinIter_one, partitionEntropy_comp_injective _ fun a b hab => congrFun hab 0] at h
  simpa using h

/-- `T` has zero entropy relative to the trivial partition. -/
@[simp]
theorem entropyRate_const [Fintype ι] [DecidableEq ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (T : α → α) (i₀ : ι) : entropyRate T μ (fun _ : α => i₀) = 0 :=
  le_antisymm (by simpa using entropyRate_le_partitionEntropy (μ := μ) T fun _ : α => i₀)
    (entropyRate_nonneg T _)

theorem entropyRate_le_log_card [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] (T : α → α)
    {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) :
    entropyRate T μ f ≤ log (Fintype.card ι) :=
  (entropyRate_le_partitionEntropy T f).trans (partitionEntropy_le_log_card hf)

theorem entropyRate_comp_injective [Fintype ι] [Fintype κ] (T : α → α) (μ : Measure α) (f : α → ι)
    {e : ι → κ} (he : Function.Injective e) :
    entropyRate T μ (e ∘ f) = entropyRate T μ f := by
  have hjoin : ∀ n : ℕ, joinIter T (e ∘ f) n = (fun w : Fin n → ι => e ∘ w) ∘ joinIter T f n :=
    fun n => rfl
  have hinj : ∀ n : ℕ, Function.Injective fun w : Fin n → ι => e ∘ w := fun n w w' h =>
    funext fun k => he (congrFun h k)
  have hfun : (fun n : ℕ => partitionEntropy μ (joinIter T (e ∘ f) n) / n)
      = fun n : ℕ => partitionEntropy μ (joinIter T f n) / n := by
    funext n
    rw [hjoin n, partitionEntropy_comp_injective _ (hinj n)]
  rw [entropyRate, entropyRate, hfun]

/-- **`h_μ(T, P)` is an isomorphism invariant.**  If `e` is measure preserving and intertwines `T`
with `S`, then `T` relative to the pullback of `P` has the same entropy as `S` relative to `P`. -/
theorem entropyRate_comp [Fintype ι] {μ : Measure α} {ν : Measure β} {T : α → α} {S : β → β}
    {e : α → β} (he : MeasurePreserving e μ ν) (hsc : Function.Semiconj e T S) (hS : Measurable S)
    {f : β → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) :
    entropyRate T μ (f ∘ e) = entropyRate S ν f := by
  have hjoin : ∀ n : ℕ, joinIter T (f ∘ e) n = joinIter S f n ∘ e := by
    intro n
    funext x k
    simp only [joinIter, Function.comp_apply]
    rw [hsc.iterate_right k x]
  have hfun : (fun n : ℕ => partitionEntropy μ (joinIter T (f ∘ e) n) / n)
      = fun n : ℕ => partitionEntropy ν (joinIter S f n) / n := by
    funext n
    rw [hjoin n, partitionEntropy_comp he (measurableSet_joinIter_fiber hS hf n)]
  rw [entropyRate, entropyRate, hfun]

/-! ### Kolmogorov–Sinai entropy -/

/-- The **Kolmogorov–Sinai entropy** `h_μ(T) = sup_P h_μ(T, P)`, the supremum being over all finite
measurable partitions `P` of the space.  It is genuinely `[0, ∞]`-valued, whence the codomain
`ℝ≥0∞`; partitions are enumerated as measurable maps `α → Fin n`, which is no loss of generality. -/
noncomputable def kolmogorovSinai (T : α → α) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (f : α → Fin n) (_ : ∀ i, MeasurableSet (f ⁻¹' {i})), ENNReal.ofReal (entropyRate T μ f)

theorem le_kolmogorovSinai {T : α → α} {μ : Measure α} {n : ℕ} {f : α → Fin n}
    (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) :
    ENNReal.ofReal (entropyRate T μ f) ≤ kolmogorovSinai T μ :=
  le_iSup_of_le n (le_iSup_of_le f (le_iSup_of_le hf le_rfl))

/-- Every finite measurable partition, with cells indexed by an arbitrary `Fintype`, is dominated by
the Kolmogorov–Sinai entropy. -/
theorem ofReal_entropyRate_le_kolmogorovSinai [Fintype ι] {T : α → α} {μ : Measure α} {f : α → ι}
    (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) :
    ENNReal.ofReal (entropyRate T μ f) ≤ kolmogorovSinai T μ := by
  classical
  set e := Fintype.equivFin ι
  have hfib : ∀ k, MeasurableSet ((e ∘ f) ⁻¹' {k}) := by
    intro k
    have : (e ∘ f) ⁻¹' {k} = f ⁻¹' {e.symm k} := by
      ext x
      simp [Equiv.eq_symm_apply]
    rw [this]
    exact hf _
  rw [← entropyRate_comp_injective T μ f e.injective]
  exact le_kolmogorovSinai hfib

theorem kolmogorovSinai_le_of_semiconj {μ : Measure α} {ν : Measure β} {T : α → α} {S : β → β}
    {e : α → β} (hme : Measurable e) (he : MeasurePreserving e μ ν)
    (hsc : Function.Semiconj e T S) (hS : Measurable S) :
    kolmogorovSinai S ν ≤ kolmogorovSinai T μ := by
  refine iSup_le fun n => iSup_le fun f => iSup_le fun hf => ?_
  rw [← entropyRate_comp he hsc hS hf]
  exact le_kolmogorovSinai fun i => hme (hf i)

/-- **Kolmogorov–Sinai entropy is an isomorphism invariant.**  It transfers along a
measure-preserving measurable equivalence intertwining the two maps. -/
theorem kolmogorovSinai_of_measurableEquiv {μ : Measure α} {ν : Measure β} {T : α → α} {S : β → β}
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (hsc : Function.Semiconj e T S)
    (hT : Measurable T) (hS : Measurable S) : kolmogorovSinai T μ = kolmogorovSinai S ν := by
  refine le_antisymm ?_ (kolmogorovSinai_le_of_semiconj e.measurable he hsc hS)
  have hsc' : Function.Semiconj (e.symm : β → α) S T := by
    intro y
    have h1 : e (T (e.symm y)) = S y := by rw [hsc (e.symm y), e.apply_symm_apply]
    calc (e.symm : β → α) (S y) = e.symm (e (T (e.symm y))) := by rw [h1]
      _ = T (e.symm y) := e.symm_apply_apply _
  exact kolmogorovSinai_le_of_semiconj e.symm.measurable (he.symm e) hsc' hT

end MeasureTheory
