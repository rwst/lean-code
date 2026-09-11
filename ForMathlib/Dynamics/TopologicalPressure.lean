/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.Asymptotics.ExpGrowth
public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
-- Not used by any proof here.  It fixes which `NormedSpace ℝ ℝ` instance the Bochner
-- integral below elaborates to (`InnerProductSpace.toNormedSpace`, not
-- `NormedField.toNormedSpace`), so that this statement agrees constant-for-constant with a
-- flat comparator challenge, whose import union necessarily contains
-- `Analysis.Fourier.AddCircle`.  See the paper repo's `COMPARATOR.md`.
public import Mathlib.Analysis.InnerProductSpace.Basic
public import ForMathlib.Dynamics.KolmogorovSinai

@[expose] public section

/-!
# Topological pressure relative to a partition, and the variational inequality

Mathlib carries topological entropy (`Mathlib/Dynamics/TopologicalEntropy/`) and
`ForMathlib/Dynamics/KolmogorovSinai.lean` supplies measure-theoretic entropy, but neither carries
the **topological pressure** `P(T, φ)` of a potential `φ`, which is what turns an entropy statement
into a computable certificate.  This file supplies the *combinatorial* half of that theory: the
pressure computed along a finite partition, and the inequality relating it to Kolmogorov–Sinai
entropy.

## Main definitions

* `Dynamics.partitionSum T φ f n` — the `n`-th **partition sum**
  `Z_n(φ, P) = ∑_{A ∈ ⋁_{i<n} T^{-i}P} exp (sup_A S_n φ)`, where `S_n φ = ∑_{i<n} φ ∘ T^i` is the
  Birkhoff sum (`birkhoffSum`) and `P` is the partition given by the fibers of `f : α → ι`.  It is
  `ℝ≥0∞`-valued: the supremum over an *empty* cell is `0`, which is exactly the convention that
  makes empty cells cost nothing, and no boundedness hypothesis is needed to state it.
* `Dynamics.partitionPressure T φ f` — the **pressure of `φ` relative to `P`**,
  `P(T, φ, P) = limsup_n (1/n) log Z_n(φ, P)`, as an `EReal`.  For a symbolic system and `P` the
  time-zero coordinate partition this is the topological pressure on the full shift.

## Main results

* `Real.sum_mul_add_negMulLog_le_log_sum_exp` — **the Gibbs variational bound**
  `∑ᵢ (pᵢ aᵢ + negMulLog pᵢ) ≤ log ∑ᵢ exp aᵢ` for a probability vector `p`.  This is the one
  inequality behind the whole variational principle, and it belongs upstream next to
  `Real.negMulLog_add_mul_log_le`.
* `MeasureTheory.partitionEntropy_add_integral_le` — its measure-theoretic form: for a finite
  measurable partition `P` and a bound `g ≤ M i` on the `i`-th cell,
  `H_μ(P) + ∫ g ∂μ ≤ log ∑ᵢ exp (M i)`.
* `MeasureTheory.entropyRate_add_integral_le_partitionPressure` — **the easy half of the
  variational principle, relative to a partition**: for `T` preserving the probability measure `μ`
  and a potential `φ` bounded above,
  `h_μ(T, P) + ∫ φ ∂μ ≤ P(T, φ, P)`.
* `Dynamics.partitionPressure_zero` — `P(T, 0, P)` is the topological entropy
  `Dynamics.partitionTopEntropy T P` along `P`, the growth rate of the number of nonempty cells.
* `Dynamics.partitionPressure_mono`, `Dynamics.partitionPressure_add_const` — the pressure is
  monotone in `φ` and satisfies `P(φ + c) = P(φ) + c`; hence the sandwich
  `Dynamics.le_partitionPressure`, `Dynamics.partitionPressure_le`:
  `h_top + inf φ ≤ P(φ) ≤ h_top + sup φ`.
* `MeasureTheory.entropyRate_le_partitionPressure_of_integral_eq_zero` — the **certificate** form:
  a potential integrating to zero against `μ` forces `h_μ(T, P) ≤ P(T, φ, P)`, so a pressure below
  an entropy floor rules `μ` out.
* `MeasureTheory.le_integral_of_partitionPressure_le` — the **pressure sandwich**: for `β > 0`,
  `-P(T, -β g, P)/β ≤ ∫ g ∂μ` for every invariant `μ`.  With the trivial upper bound
  `P(T, -β g, P) ≤ h_top - β inf g` this brackets `inf_μ ∫ g ∂μ` to within `h_top/β`, which is what
  makes a search for a positive lower bound terminate.

## Auxiliary results

* `MeasureTheory.integral_eq_sum_setIntegral_fiber` — splitting an integral along a finite
  measurable partition.
* `MeasureTheory.integral_birkhoffSum`, `MeasureTheory.integrable_birkhoffSum`,
  `MeasureTheory.integral_comp_of_measurePreserving` — `∫ S_n φ ∂μ = n ∫ φ ∂μ` for invariant `μ`.
* `Dynamics.expGrowthSup_ofReal_exp`, `Dynamics.expGrowthInf_ofReal_exp` — the exponential growth
  rate of `n ↦ exp (n c)` is `c`, from above and from below.

## Deliberately out of scope

The *hard* half of the variational principle (`P(T, φ) ≤ sup_μ (h_μ(T) + ∫φ)`), Bowen's definition
of the pressure by dynamical covers of a uniform space, the Kolmogorov–Sinai generator theorem
(which identifies `h_μ(T, P)` with `h_μ(T)` for a generating `P`), equilibrium states, and the
Ruelle–Perron–Frobenius theorem.  Each is a substantial theorem in its own right; nothing here
depends on any of them.

## References

* Walters, P. *An Introduction to Ergodic Theory*, GTM 79, Springer 1982, Chapter 9.
* Bowen, R. *Equilibrium States and the Ergodic Theory of Anosov Diffeomorphisms*, LNM 470, 1975.
-/

open Filter Topology MeasureTheory
open scoped ENNReal

namespace Real

/-- **The Gibbs variational bound.**  For a probability vector `p` supported on a finite set `s`
and any reals `a i`,
`∑ᵢ (pᵢ · aᵢ - pᵢ log pᵢ) ≤ log (∑ᵢ exp aᵢ)`,
with equality exactly at the Gibbs measure `pᵢ ∝ exp aᵢ`.  Together with
`Real.negMulLog_add_mul_log_le`, of which it is the summed form, this is the whole analytic content
of the easy half of the variational principle for the topological pressure.

This belongs upstream in `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`. -/
theorem sum_mul_add_negMulLog_le_log_sum_exp {ι : Type*} {s : Finset ι} {p a : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, (p i * a i + negMulLog (p i)) ≤ log (∑ i ∈ s, exp (a i)) := by
  have hs : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · rw [h] at hsum; simp at hsum
    · exact h
  set C := ∑ i ∈ s, exp (a i) with hCdef
  have hCpos : 0 < C := Finset.sum_pos (fun i _ => exp_pos (a i)) hs
  -- pointwise Gibbs inequality against the normalised weights `exp (a i) / C`
  have key : ∀ i ∈ s, p i * a i + negMulLog (p i) - p i * log C ≤ exp (a i) / C - p i := by
    intro i hi
    have hq : (0 : ℝ) < exp (a i) / C := div_pos (exp_pos _) hCpos
    have h := negMulLog_add_mul_log_le (hp i hi) hq.le fun _ => hq
    rw [log_div (exp_pos _).ne' hCpos.ne', log_exp] at h
    nlinarith [h]
  have hle := Finset.sum_le_sum key
  have hL : ∑ i ∈ s, (p i * a i + negMulLog (p i) - p i * log C)
      = (∑ i ∈ s, (p i * a i + negMulLog (p i))) - log C := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hR : ∑ i ∈ s, (exp (a i) / C - p i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, ← Finset.sum_div, ← hCdef, div_self hCpos.ne']
    ring
  rw [hL, hR] at hle
  linarith

end Real

namespace MeasureTheory

open Real

variable {α ι : Type*} [MeasurableSpace α]

/-! ### Splitting an integral along a finite measurable partition -/

/-- The integral of `g` is the sum of its integrals over the cells of a finite measurable
partition. -/
theorem integral_eq_sum_setIntegral_fiber [Fintype ι] {μ : Measure α} {f : α → ι}
    (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) {g : α → ℝ} (hg : Integrable g μ) :
    ∫ x, g x ∂μ = ∑ i, ∫ x in f ⁻¹' {i}, g x ∂μ := by
  classical
  have hpt : ∀ x, ∑ i, (f ⁻¹' {i}).indicator g x = g x := by
    intro x
    rw [Finset.sum_eq_single (f x)]
    · exact Set.indicator_of_mem (Set.mem_preimage.mpr rfl) g
    · intro b _ hb
      exact Set.indicator_of_notMem (by simpa using fun h => hb h.symm) g
    · intro h; exact absurd (Finset.mem_univ (f x)) h
  calc ∫ x, g x ∂μ = ∫ x, ∑ i, (f ⁻¹' {i}).indicator g x ∂μ := by simp_rw [hpt]
    _ = ∑ i, ∫ x, (f ⁻¹' {i}).indicator g x ∂μ :=
        integral_finsetSum _ fun i _ => hg.indicator (hf i)
    _ = ∑ i, ∫ x in f ⁻¹' {i}, g x ∂μ :=
        Finset.sum_congr rfl fun i _ => integral_indicator (hf i)

/-! ### The Gibbs bound for a partition -/

/-- **The Gibbs bound for a finite measurable partition.**  If `g ≤ M i` on the `i`-th cell of the
partition given by the fibers of `f`, and every cell outside the finite set `s` is *empty*, then
`H_μ(P) + ∫ g ∂μ ≤ log (∑_{i ∈ s} exp (M i))`.

This is the single step that produces the variational inequality: applied to the dynamical join
`⋁_{i<n} T^{-i}P` and the Birkhoff sum `S_n φ`, it says that entropy plus energy is at most the
logarithm of the partition function. -/
theorem partitionEntropy_add_integral_le [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i})) {g : α → ℝ} (hg : Integrable g μ)
    {s : Finset ι} {M : ι → ℝ} (hs : ∀ i ∉ s, f ⁻¹' {i} = ∅)
    (hM : ∀ i ∈ s, ∀ x ∈ f ⁻¹' {i}, g x ≤ M i) :
    partitionEntropy μ f + ∫ x, g x ∂μ ≤ log (∑ i ∈ s, exp (M i)) := by
  classical
  have hzero : ∀ i ∉ s, (μ (f ⁻¹' {i})).toReal = 0 := fun i hi => by simp [hs i hi]
  -- the cell weights form a probability vector supported on `s`
  have hsum : ∑ i ∈ s, (μ (f ⁻¹' {i})).toReal = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ s) fun i _ hi => hzero i hi]
    exact sum_measure_fiber_toReal hf
  -- the entropy only sees `s`
  have hent : partitionEntropy μ f = ∑ i ∈ s, negMulLog (μ (f ⁻¹' {i})).toReal := by
    refine (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => ?_).symm
    rw [hzero i hi, negMulLog_zero]
  -- the integral is dominated by the cellwise bounds
  have hint : ∫ x, g x ∂μ ≤ ∑ i ∈ s, (μ (f ⁻¹' {i})).toReal * M i := by
    rw [integral_eq_sum_setIntegral_fiber hf hg,
      ← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by rw [hs i hi]; simp)]
    refine Finset.sum_le_sum fun i hi => ?_
    calc ∫ x in f ⁻¹' {i}, g x ∂μ ≤ ∫ _ in f ⁻¹' {i}, M i ∂μ :=
          setIntegral_mono_on hg.integrableOn (integrable_const (M i)).integrableOn
            (hf i) (hM i hi)
      _ = (μ (f ⁻¹' {i})).toReal * M i := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def]
  calc partitionEntropy μ f + ∫ x, g x ∂μ
      ≤ ∑ i ∈ s, negMulLog (μ (f ⁻¹' {i})).toReal
        + ∑ i ∈ s, (μ (f ⁻¹' {i})).toReal * M i := by rw [hent]; linarith
    _ = ∑ i ∈ s, ((μ (f ⁻¹' {i})).toReal * M i + negMulLog (μ (f ⁻¹' {i})).toReal) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ log (∑ i ∈ s, exp (M i)) :=
        sum_mul_add_negMulLog_le_log_sum_exp (fun i _ => ENNReal.toReal_nonneg) hsum

end MeasureTheory

namespace Dynamics

open Real MeasureTheory ExpGrowth

variable {α ι : Type*} [MeasurableSpace α]

/-! ### The partition sum and the pressure relative to a partition -/

/-- The **cell weight** `exp (sup_A S_n φ)` of the cell `A` of `⋁_{i<n} T^{-i}P` indexed by the word
`w`, as an element of `ℝ≥0∞`.  Taking the supremum in `ℝ≥0∞` rather than in `ℝ` makes the empty
cell weigh `0` — the right convention — and needs no boundedness hypothesis. -/
noncomputable def cellWeight [Fintype ι] (T : α → α) (φ : α → ℝ) (f : α → ι) (n : ℕ)
    (w : Fin n → ι) : ℝ≥0∞ :=
  ⨆ x ∈ joinIter T f n ⁻¹' {w}, ENNReal.ofReal (exp (birkhoffSum T φ n x))

/-- The **`n`-th partition sum** (partition function)
`Z_n(φ, P) = ∑_{A ∈ ⋁_{i<n} T^{-i}P} exp (sup_A S_n φ)`. -/
noncomputable def partitionSum [Fintype ι] (T : α → α) (φ : α → ℝ) (f : α → ι) (n : ℕ) : ℝ≥0∞ :=
  ∑ w : Fin n → ι, cellWeight T φ f n w

/-- The **pressure of `φ` relative to the partition `P`**,
`P(T, φ, P) = limsup_n (1/n) log Z_n(φ, P)`.

For a symbolic system `ι^ℕ` (or `ι^ℤ`) with `T` the shift and `P` the time-zero coordinate
partition, this is the topological pressure of `φ`; in general it is the pressure computed along
`P`, which is what `MeasureTheory.entropyRate_add_integral_le_partitionPressure` bounds. -/
noncomputable def partitionPressure [Fintype ι] (T : α → α) (φ : α → ℝ) (f : α → ι) : EReal :=
  expGrowthSup (partitionSum T φ f)

variable [Fintype ι] {T : α → α} {φ ψ : α → ℝ} {f : α → ι}

omit [MeasurableSpace α] in
theorem cellWeight_le_of_le {C : ℝ} (hC : ∀ x, φ x ≤ C) (n : ℕ) (w : Fin n → ι) :
    cellWeight T φ f n w ≤ ENNReal.ofReal (exp (n * C)) := by
  refine iSup₂_le fun x _ => ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)
  calc birkhoffSum T φ n x = ∑ k ∈ Finset.range n, φ (T^[k] x) := rfl
    _ ≤ ∑ _k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hC _
    _ = n * C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [MeasurableSpace α] in
theorem cellWeight_ne_top {C : ℝ} (hC : ∀ x, φ x ≤ C) (n : ℕ) (w : Fin n → ι) :
    cellWeight T φ f n w ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (cellWeight_le_of_le hC n w)

omit [MeasurableSpace α] in
theorem partitionSum_ne_top {C : ℝ} (hC : ∀ x, φ x ≤ C) (n : ℕ) :
    partitionSum T φ f n ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun w _ => cellWeight_ne_top hC n w

omit [MeasurableSpace α] in
theorem cellWeight_pos_of_mem {n : ℕ} {w : Fin n → ι} {x : α} (hx : joinIter T f n x = w) :
    0 < cellWeight T φ f n w :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.2 (exp_pos _)) (le_iSup₂ (f := fun x (_ : x ∈ _) =>
    ENNReal.ofReal (exp (birkhoffSum T φ n x))) x hx)

omit [MeasurableSpace α] in
theorem partitionSum_pos [Nonempty α] (n : ℕ) : 0 < partitionSum T φ f n :=
  lt_of_lt_of_le (cellWeight_pos_of_mem (T := T) (φ := φ) (f := f) (x := Classical.arbitrary α) rfl)
    (Finset.single_le_sum (f := fun w => cellWeight T φ f n w)
      (fun _ _ => zero_le) (Finset.mem_univ _))

omit [MeasurableSpace α] in
theorem partitionSum_ne_zero [Nonempty α] (n : ℕ) : partitionSum T φ f n ≠ 0 :=
  (partitionSum_pos n).ne'

/-! ### The calculus of the pressure -/

/-- The exponential growth of `n ↦ exp (n c)`: the `limsup` and the `liminf` both equal `c`,
because the sequence `log (exp (n c)) / n` is *constantly* `c` from `n = 1` on. -/
theorem log_ofReal_exp_div_eventually_eq (c : ℝ) : ∀ᶠ n : ℕ in atTop,
    ENNReal.log (ENNReal.ofReal (Real.exp (n * c))) / (n : EReal) = (c : EReal) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
    ← EReal.coe_coe_eq_natCast, ← EReal.coe_div, mul_comm, mul_div_assoc, div_self hn0, mul_one]

theorem expGrowthSup_ofReal_exp (c : ℝ) :
    expGrowthSup (fun n : ℕ => ENNReal.ofReal (Real.exp (n * c))) = (c : EReal) := by
  rw [expGrowthSup, Filter.limsup_congr (log_ofReal_exp_div_eventually_eq c), Filter.limsup_const]

theorem expGrowthInf_ofReal_exp (c : ℝ) :
    expGrowthInf (fun n : ℕ => ENNReal.ofReal (Real.exp (n * c))) = (c : EReal) := by
  rw [expGrowthInf, Filter.liminf_congr (log_ofReal_exp_div_eventually_eq c), Filter.liminf_const]

/-- The number of *nonempty* cells of the dynamical join `⋁_{i<n} T^{-i}P`. -/
noncomputable def partitionCard (T : α → α) (f : α → ι) (n : ℕ) : ℕ :=
  {w : Fin n → ι | (joinIter T f n ⁻¹' {w}).Nonempty}.ncard

/-- The **topological entropy of `T` along `P`**: the exponential growth rate of the number of
nonempty cells of `⋁_{i<n} T^{-i}P`.  It is the pressure of the zero potential
(`partitionPressure_zero`). -/
noncomputable def partitionTopEntropy (T : α → α) (f : α → ι) : EReal :=
  expGrowthSup fun n => (partitionCard T f n : ℝ≥0∞)

variable {c C : ℝ}

omit [MeasurableSpace α] in
theorem cellWeight_zero_of_nonempty {n : ℕ} {w : Fin n → ι}
    (h : (joinIter T f n ⁻¹' {w}).Nonempty) : cellWeight T (0 : α → ℝ) f n w = 1 := by
  obtain ⟨x, hx⟩ := h
  have hb : ∀ y : α, birkhoffSum T (0 : α → ℝ) n y = 0 := fun y => by simp [birkhoffSum]
  simp only [cellWeight, hb, Real.exp_zero, ENNReal.ofReal_one]
  exact le_antisymm (iSup₂_le fun _ _ => le_rfl)
    (le_iSup₂ (f := fun _ (_ : _ ∈ _) => (1 : ℝ≥0∞)) x hx)

omit [MeasurableSpace α] in
theorem cellWeight_of_eq_empty {n : ℕ} {w : Fin n → ι} (h : joinIter T f n ⁻¹' {w} = ∅) :
    cellWeight T φ f n w = 0 := by
  simp [cellWeight, h]

omit [MeasurableSpace α] in
theorem partitionSum_zero (n : ℕ) : partitionSum T (0 : α → ℝ) f n = partitionCard T f n := by
  classical
  have hc : ∀ w : Fin n → ι, cellWeight T (0 : α → ℝ) f n w
      = if (joinIter T f n ⁻¹' {w}).Nonempty then 1 else 0 := by
    intro w
    split_ifs with h
    · exact cellWeight_zero_of_nonempty h
    · exact cellWeight_of_eq_empty (Set.not_nonempty_iff_eq_empty.1 h)
  simp only [partitionSum, hc, Finset.sum_boole, partitionCard, Set.ncard_eq_toFinset_card',
    Set.toFinset_ofPred]

omit [MeasurableSpace α] in
/-- **The pressure of the zero potential is the entropy along the partition.** -/
theorem partitionPressure_zero : partitionPressure T (0 : α → ℝ) f = partitionTopEntropy T f :=
  congrArg expGrowthSup (funext fun n => partitionSum_zero n)

omit [MeasurableSpace α] in
theorem cellWeight_mono (h : ∀ x, φ x ≤ ψ x) (n : ℕ) (w : Fin n → ι) :
    cellWeight T φ f n w ≤ cellWeight T ψ f n w :=
  iSup₂_mono fun _ _ => ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.2 (Finset.sum_le_sum fun _ _ => h _))

omit [MeasurableSpace α] in
theorem partitionSum_mono (h : ∀ x, φ x ≤ ψ x) (n : ℕ) :
    partitionSum T φ f n ≤ partitionSum T ψ f n :=
  Finset.sum_le_sum fun w _ => cellWeight_mono h n w

omit [MeasurableSpace α] in
/-- The pressure is monotone in the potential. -/
theorem partitionPressure_mono (h : ∀ x, φ x ≤ ψ x) :
    partitionPressure T φ f ≤ partitionPressure T ψ f :=
  expGrowthSup_monotone fun n => partitionSum_mono h n

omit [MeasurableSpace α] in
theorem cellWeight_add_const (n : ℕ) (w : Fin n → ι) :
    cellWeight T (fun x => φ x + c) f n w
      = ENNReal.ofReal (Real.exp (n * c)) * cellWeight T φ f n w := by
  have hb : ∀ x : α, birkhoffSum T (fun x => φ x + c) n x = birkhoffSum T φ n x + n * c :=
    fun x => by
      simp only [birkhoffSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
  simp only [cellWeight, hb, ENNReal.mul_iSup]
  refine iSup_congr fun x => iSup_congr fun _ => ?_
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

omit [MeasurableSpace α] in
theorem partitionSum_add_const (n : ℕ) :
    partitionSum T (fun x => φ x + c) f n
      = ENNReal.ofReal (Real.exp (n * c)) * partitionSum T φ f n := by
  simp only [partitionSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => cellWeight_add_const n w

omit [MeasurableSpace α] in
/-- **Translating the potential by a constant translates the pressure by that constant.** -/
theorem partitionPressure_add_const :
    partitionPressure T (fun x => φ x + c) f = partitionPressure T φ f + (c : EReal) := by
  have hmul : partitionSum T (fun x => φ x + c) f
      = partitionSum T φ f * fun n : ℕ => ENNReal.ofReal (Real.exp (n * c)) :=
    funext fun n => by rw [partitionSum_add_const, Pi.mul_apply, mul_comm]
  rw [partitionPressure, partitionPressure, hmul]
  refine le_antisymm ?_ ?_
  · calc expGrowthSup (partitionSum T φ f * fun n : ℕ => ENNReal.ofReal (Real.exp (n * c)))
        ≤ expGrowthSup (partitionSum T φ f)
          + expGrowthSup fun n : ℕ => ENNReal.ofReal (Real.exp (n * c)) :=
          expGrowthSup_mul_le
            (Or.inr (by rw [expGrowthSup_ofReal_exp]; exact EReal.coe_ne_top c))
            (Or.inr (by rw [expGrowthSup_ofReal_exp]; exact EReal.coe_ne_bot c))
      _ = expGrowthSup (partitionSum T φ f) + (c : EReal) := by rw [expGrowthSup_ofReal_exp]
  · calc expGrowthSup (partitionSum T φ f) + (c : EReal)
        = expGrowthSup (partitionSum T φ f)
          + expGrowthInf fun n : ℕ => ENNReal.ofReal (Real.exp (n * c)) := by
          rw [expGrowthInf_ofReal_exp]
      _ ≤ _ := le_expGrowthSup_mul

omit [MeasurableSpace α] in
/-- The pressure of a potential bounded above by `C` is at most the entropy plus `C`. -/
theorem partitionPressure_le (hC : ∀ x, φ x ≤ C) :
    partitionPressure T φ f ≤ partitionTopEntropy T f + (C : EReal) := by
  have h1 : partitionPressure T φ f ≤ partitionPressure T (fun x => (0 : α → ℝ) x + C) f :=
    partitionPressure_mono fun x => by simpa using hC x
  rw [partitionPressure_add_const, partitionPressure_zero] at h1
  exact h1

omit [MeasurableSpace α] in
/-- The pressure of a potential bounded below by `c` is at least the entropy plus `c`. -/
theorem le_partitionPressure (hc : ∀ x, c ≤ φ x) :
    partitionTopEntropy T f + (c : EReal) ≤ partitionPressure T φ f := by
  have h1 : partitionPressure T (fun x => (0 : α → ℝ) x + c) f ≤ partitionPressure T φ f :=
    partitionPressure_mono fun x => by simpa using hc x
  rw [partitionPressure_add_const, partitionPressure_zero] at h1
  exact h1

end Dynamics

namespace MeasureTheory

open Real Dynamics ExpGrowth

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {φ : α → ℝ}

/-! ### Birkhoff sums of an invariant measure -/

/-- Composition with a measure-preserving self-map does not change an integral. -/
theorem integral_comp_of_measurePreserving {S : α → α} (hS : MeasurePreserving S μ μ)
    (hφ : AEStronglyMeasurable φ μ) : ∫ x, φ (S x) ∂μ = ∫ x, φ x ∂μ := by
  have h := integral_map (μ := μ) (φ := S) (f := φ) hS.measurable.aemeasurable
    (by rwa [hS.map_eq])
  rw [hS.map_eq] at h
  exact h.symm

/-- The integral of the `n`-th Birkhoff sum of an invariant measure is `n` times the integral. -/
theorem integral_birkhoffSum (hT : MeasurePreserving T μ μ) (hφ : Integrable φ μ) (n : ℕ) :
    ∫ x, birkhoffSum T φ n x ∂μ = n * ∫ x, φ x ∂μ := by
  have hint : ∀ k ∈ Finset.range n, Integrable (fun x => φ (T^[k] x)) μ := fun k _ =>
    (hT.iterate k).integrable_comp_of_integrable hφ
  calc ∫ x, birkhoffSum T φ n x ∂μ = ∫ x, ∑ k ∈ Finset.range n, φ (T^[k] x) ∂μ := rfl
    _ = ∑ k ∈ Finset.range n, ∫ x, φ (T^[k] x) ∂μ := integral_finsetSum _ hint
    _ = ∑ _k ∈ Finset.range n, ∫ x, φ x ∂μ :=
        Finset.sum_congr rfl fun k _ =>
          integral_comp_of_measurePreserving (hT.iterate k) hφ.aestronglyMeasurable
    _ = n * ∫ x, φ x ∂μ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem integrable_birkhoffSum (hT : MeasurePreserving T μ μ) (hφ : Integrable φ μ) (n : ℕ) :
    Integrable (birkhoffSum T φ n) μ :=
  integrable_finsetSum _ fun k _ => (hT.iterate k).integrable_comp_of_integrable hφ

/-! ### The variational inequality -/

/-- **The easy half of the variational principle, relative to a partition.**  For a map `T`
preserving a probability measure `μ`, a finite measurable partition `P`, and a potential `φ`
bounded above,
`h_μ(T, P) + ∫ φ ∂μ ≤ P(T, φ, P)`.

The whole proof is the Gibbs bound `MeasureTheory.partitionEntropy_add_integral_le` applied to the
dynamical join `⋁_{i<n} T^{-i}P` and the Birkhoff sum `S_n φ`, divided by `n`; no ergodic theorem
and no compactness are used.  Combined with the Kolmogorov–Sinai generator theorem — which is *not*
proved here — the left-hand side becomes `h_μ(T) + ∫ φ ∂μ` whenever `P` generates. -/
theorem entropyRate_add_integral_le_partitionPressure [Fintype ι] [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i}))
    (hφ : Integrable φ μ) {C : ℝ} (hC : ∀ x, φ x ≤ C) :
    ((entropyRate T μ f + ∫ x, φ x ∂μ : ℝ) : EReal) ≤ partitionPressure T φ f := by
  classical
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : μ Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr h] at h1
    simp at h1
  -- Step 1: the finite-`n` inequality, in `ℝ`
  have key : ∀ n : ℕ, partitionEntropy μ (joinIter T f n) + n * ∫ x, φ x ∂μ
      ≤ Real.log ((partitionSum T φ f n).toReal) := by
    intro n
    set S : Finset (Fin n → ι) :=
      Finset.univ.filter fun w => (joinIter T f n ⁻¹' {w}).Nonempty with hSdef
    set M : (Fin n → ι) → ℝ := fun w => Real.log ((cellWeight T φ f n w).toReal) with hMdef
    have hcell_top : ∀ w, cellWeight T φ f n w ≠ ⊤ := fun w => cellWeight_ne_top hC n w
    have hemp : ∀ w ∉ S, joinIter T f n ⁻¹' {w} = ∅ := by
      intro w hw
      rw [hSdef, Finset.mem_filter] at hw
      exact Set.not_nonempty_iff_eq_empty.1 fun h => hw ⟨Finset.mem_univ w, h⟩
    have hpos : ∀ w ∈ S, 0 < (cellWeight T φ f n w).toReal := by
      intro w hw
      rw [hSdef, Finset.mem_filter] at hw
      obtain ⟨x, hx⟩ := hw.2
      exact ENNReal.toReal_pos (cellWeight_pos_of_mem hx).ne' (hcell_top w)
    have hbound : ∀ w ∈ S, ∀ x ∈ joinIter T f n ⁻¹' {w}, birkhoffSum T φ n x ≤ M w := by
      intro w _ x hx
      have hle : ENNReal.ofReal (exp (birkhoffSum T φ n x)) ≤ cellWeight T φ f n w :=
        le_iSup₂ (f := fun x (_ : x ∈ joinIter T f n ⁻¹' {w}) =>
          ENNReal.ofReal (exp (birkhoffSum T φ n x))) x hx
      have hle' : exp (birkhoffSum T φ n x) ≤ (cellWeight T φ f n w).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (hcell_top w)).1 hle
      calc birkhoffSum T φ n x = Real.log (exp (birkhoffSum T φ n x)) := (Real.log_exp _).symm
        _ ≤ M w := Real.log_le_log (exp_pos _) hle'
    have hgibbs := partitionEntropy_add_integral_le
      (measurableSet_joinIter_fiber hT.measurable hf n) (integrable_birkhoffSum hT hφ n)
      hemp hbound
    rw [integral_birkhoffSum hT hφ n] at hgibbs
    refine hgibbs.trans (le_of_eq (congrArg Real.log ?_))
    have h1 : ∑ w ∈ S, exp (M w) = ∑ w ∈ S, (cellWeight T φ f n w).toReal :=
      Finset.sum_congr rfl fun w hw => by rw [hMdef]; exact Real.exp_log (hpos w hw)
    have h2 : ∑ w ∈ S, (cellWeight T φ f n w).toReal
        = ∑ w : Fin n → ι, (cellWeight T φ f n w).toReal := by
      refine Finset.sum_subset (Finset.subset_univ S) fun w _ hw => ?_
      rw [cellWeight, hemp w hw]
      simp
    rw [h1, h2, partitionSum, ENNReal.toReal_sum fun w _ => hcell_top w]
  -- Step 2: divide by `n` and pass to the `EReal` limsup
  have hne0 : ∀ n : ℕ, partitionSum T φ f n ≠ 0 := fun n => partitionSum_ne_zero n
  have hnetop : ∀ n : ℕ, partitionSum T φ f n ≠ ⊤ := fun n => partitionSum_ne_top hC n
  have hstep : ∀ n : ℕ, 1 ≤ n →
      ((partitionEntropy μ (joinIter T f n) / n + ∫ x, φ x ∂μ : ℝ) : EReal)
        ≤ ENNReal.log (partitionSum T φ f n) / (n : EReal) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hreal : partitionEntropy μ (joinIter T f n) / n + ∫ x, φ x ∂μ
        ≤ Real.log ((partitionSum T φ f n).toReal) / n := by
      rw [div_add' _ _ _ hn0.ne', div_le_div_iff_of_pos_right hn0]
      calc partitionEntropy μ (joinIter T f n) + (∫ x, φ x ∂μ) * n
          = partitionEntropy μ (joinIter T f n) + n * ∫ x, φ x ∂μ := by ring
        _ ≤ _ := key n
    rw [ENNReal.log_pos_real (hne0 n) (hnetop n)]
    calc ((partitionEntropy μ (joinIter T f n) / n + ∫ x, φ x ∂μ : ℝ) : EReal)
        ≤ ((Real.log ((partitionSum T φ f n).toReal) / n : ℝ) : EReal) := EReal.coe_le_coe hreal
      _ = (Real.log ((partitionSum T φ f n).toReal) : EReal) / (n : EReal) := by
          rw [EReal.coe_div]; norm_cast
  have hlim : Tendsto
      (fun n : ℕ => ((partitionEntropy μ (joinIter T f n) / n + ∫ x, φ x ∂μ : ℝ) : EReal)) atTop
      (𝓝 (((entropyRate T μ f + ∫ x, φ x ∂μ : ℝ) : EReal))) :=
    EReal.tendsto_coe.2 ((tendsto_partitionEntropy_joinIter_div hT hf).add tendsto_const_nhds)
  calc ((entropyRate T μ f + ∫ x, φ x ∂μ : ℝ) : EReal)
      = limsup
        (fun n : ℕ => ((partitionEntropy μ (joinIter T f n) / n + ∫ x, φ x ∂μ : ℝ) : EReal))
        atTop := hlim.limsup_eq.symm
    _ ≤ limsup (fun n : ℕ => ENNReal.log (partitionSum T φ f n) / (n : EReal)) atTop :=
        limsup_le_limsup (Filter.eventually_atTop.2 ⟨1, fun n hn => hstep n hn⟩)
    _ = partitionPressure T φ f := rfl

/-! ### Two consequences: certificates and the pressure sandwich -/

/-- **A pressure certificate bounds the entropy of every measure the potential annihilates.**  If
`∫ φ ∂μ = 0` then `h_μ(T, P) ≤ P(T, φ, P)`.

This is the shape in which the pressure is used as a *certificate*: exhibiting one potential `φ`
that integrates to zero against every measure of interest and whose pressure is below an entropy
floor rules those measures out. -/
theorem entropyRate_le_partitionPressure_of_integral_eq_zero [Fintype ι] [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i}))
    (hφ : Integrable φ μ) {C : ℝ} (hC : ∀ x, φ x ≤ C) (hzero : ∫ x, φ x ∂μ = 0) :
    ((entropyRate T μ f : ℝ) : EReal) ≤ partitionPressure T φ f := by
  have h := entropyRate_add_integral_le_partitionPressure hT hf hφ hC
  rwa [hzero, add_zero] at h

/-- **The pressure sandwich, lower half.**  For `β > 0`, the pressure of `-β g` bounds the integral
of `g` against *every* invariant measure from below:
`-P(T, -β g, P)/β ≤ ∫ g ∂μ`.

Together with the trivial upper bound `P(T, -β g, P) ≤ h_top + β·(-inf g)` this brackets
`inf_μ ∫ g ∂μ` to within `h_top/β`, which is what makes a search for a positive lower bound on
`inf_μ ∫ g ∂μ` terminate. -/
theorem le_integral_of_partitionPressure_le [Fintype ι] [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : α → ι} (hf : ∀ i, MeasurableSet (f ⁻¹' {i}))
    {g : α → ℝ} (hg : Integrable g μ) {D : ℝ} (hD : ∀ x, D ≤ g x) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (h : partitionPressure T (fun x => -(β * g x)) f ≤ (c : EReal)) :
    -c / β ≤ ∫ x, g x ∂μ := by
  have hint : Integrable (fun x => -(β * g x)) μ := (hg.const_mul β).neg
  have hbdd : ∀ x, -(β * g x) ≤ -(β * D) := fun x => neg_le_neg (by nlinarith [hD x])
  have hmain := (entropyRate_add_integral_le_partitionPressure hT hf hint hbdd).trans h
  rw [EReal.coe_le_coe_iff] at hmain
  have hI : ∫ x, -(β * g x) ∂μ = -(β * ∫ x, g x ∂μ) := by
    rw [integral_neg, integral_const_mul]
  rw [hI] at hmain
  have hpos : 0 ≤ entropyRate T μ f := entropyRate_nonneg T f
  rw [div_le_iff₀ hβ]
  nlinarith [hmain, hpos]

end MeasureTheory
