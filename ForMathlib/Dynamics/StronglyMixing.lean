/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Measure.MeasuredSets

@[expose] public section

/-!
# Strong mixing, its consequences, and the Bernoulli shift

A measure-preserving system `(f, μ)` is **strongly mixing** if `μ (f⁻ⁿ A ∩ B) → μ A · μ B` for all
measurable `A, B`. This file collects the general theory needed to transfer mixing to the `3x+1` map
(`BL`):

* `IsStronglyMixing` — the predicate (bundling measure preservation).
* `IsStronglyMixing.ergodic` — strong mixing implies ergodicity.
* `IsStronglyMixing.of_measurableEquiv` — strong mixing is an isomorphism invariant: it transfers
  along a measure-preserving measurable equivalence intertwining the two maps.
* `isStronglyMixing_infinitePi_shift` — **any (one-sided) Bernoulli shift is strongly mixing.** For an
  i.i.d. product measure on `ℕ → α`, the coordinate shift is strongly mixing. This is the classical
  fact [Quas09], here given a complete proof: cylinder sets (`measurableCylinders`) form a generating
  set-ring, so an arbitrary measurable set is approximated in symmetric difference by a cylinder
  (`exists_measure_symmDiff_lt_of_generateFrom_isSetRing`); two cylinders whose coordinate blocks are
  far enough apart are *exactly* independent under the shift (the coordinates are independent,
  `iIndepFun_infinitePi`, and disjoint blocks stay independent, `iIndepFun.indepFun_finset`); an
  `ε/4` argument then yields the limit for general sets.

Combined with `IsStronglyMixing.of_measurableEquiv`, the last item gives strong mixing for any system
*isomorphic* to a Bernoulli shift — e.g. the doubling map, and (in `BL`) the `3x+1` map `T₂`, which is
Bernoulli via the conjugacy `Φ`.

## References
* [Quas09] Quas, Anthony. *Ergodicity and Mixing Properties.* In *Encyclopedia of Complexity and
  Systems Science* (2009), 2918–2933. (Any Bernoulli shift is strong-mixing; the doubling map, being
  measure-theoretically isomorphic to a one-sided Bernoulli shift, is therefore strong-mixing.)
-/

namespace MeasureTheory

open Filter Topology ProbabilityTheory
open scoped ENNReal symmDiff

variable {α : Type*} [MeasurableSpace α]

/-- A measure-preserving system `(f, μ)` is **strongly mixing** if `μ (f⁻ⁿ A ∩ B) → μ A · μ B` for all
measurable `A, B` (this bundles measure preservation). -/
def IsStronglyMixing (f : α → α) (μ : Measure α) : Prop :=
  MeasurePreserving f μ μ ∧ ∀ A B, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n => μ (f^[n] ⁻¹' A ∩ B)) atTop (𝓝 (μ A * μ B))

/-- **Strong mixing implies ergodicity.** For an invariant set `s` (`f⁻¹ s = s`), mixing with
`A = B = s` gives `μ s = μ s · μ s`, forcing `μ s ∈ {0, 1}`. -/
theorem IsStronglyMixing.ergodic {f : α → α} {μ : Measure α} [IsProbabilityMeasure μ]
    (h : IsStronglyMixing f μ) : Ergodic f μ := by
  refine ⟨h.1, ⟨fun s hs hinv => ?_⟩⟩
  have hiter : ∀ n, f^[n] ⁻¹' s = s := by
    intro n; induction n with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ', Set.preimage_comp, hinv, ih]
  have hmix := h.2 s s hs hs
  have hconst : (fun n => μ (f^[n] ⁻¹' s ∩ s)) = fun _ => μ s := by
    funext n; rw [hiter n, Set.inter_self]
  rw [hconst] at hmix
  have huniq : μ s = μ s * μ s := tendsto_nhds_unique tendsto_const_nhds hmix
  have hdich : μ s = 0 ∨ μ s = 1 := by
    rcases eq_or_ne (μ s) 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ((ENNReal.mul_eq_left h0 (measure_ne_top μ s)).mp huniq.symm)
  rw [eventuallyConst_set]
  rcases hdich with h0 | hs1
  · exact Or.inr (by rw [ae_iff]; simpa using h0)
  · exact Or.inl (by rw [ae_iff, show {a | a ∉ s} = sᶜ from rfl,
      measure_compl hs (measure_ne_top μ s), measure_univ, hs1, tsub_self])

/-- **Strong mixing is an isomorphism invariant.** If `e : α ≃ᵐ β` is measure-preserving and
intertwines `f` with `g` (`Function.Semiconj e f g`), then `f` is strongly mixing whenever `g` is.
Iterating gives `f^[n] = e⁻¹ ∘ g^[n] ∘ e`, so `μ (f⁻ⁿ A ∩ B) = ν (g⁻ⁿ A' ∩ B')` with
`A' = e⁻¹·' A`, `B' = e⁻¹·' B` and `ν A' = μ A`, `ν B' = μ B`. -/
theorem IsStronglyMixing.of_measurableEquiv {β : Type*} [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → α} {g : β → β} (e : α ≃ᵐ β)
    (he : MeasurePreserving ⇑e μ ν) (hsc : Function.Semiconj ⇑e f g) (hg : IsStronglyMixing g ν) :
    IsStronglyMixing f μ := by
  have hesymm : MeasurePreserving ⇑e.symm ν μ := he.symm e
  have hf : f = ⇑e.symm ∘ g ∘ ⇑e := by
    funext x; simp only [Function.comp_apply]; rw [← hsc x, e.symm_apply_apply]
  have hfmeas : Measurable f := by
    rw [hf]; exact e.symm.measurable.comp (hg.1.measurable.comp e.measurable)
  refine ⟨by rw [hf]; exact hesymm.comp (hg.1.comp he), fun A B hA hB => ?_⟩
  have hmix := hg.2 _ _ (e.symm.measurable hA) (e.symm.measurable hB)
  have hAν : ν (⇑e.symm ⁻¹' A) = μ A := hesymm.measure_preimage hA.nullMeasurableSet
  have hBν : ν (⇑e.symm ⁻¹' B) = μ B := hesymm.measure_preimage hB.nullMeasurableSet
  rw [← hAν, ← hBν]
  have key : ∀ n, μ (f^[n] ⁻¹' A ∩ B) = ν (g^[n] ⁻¹' (⇑e.symm ⁻¹' A) ∩ (⇑e.symm ⁻¹' B)) := by
    intro n
    have hpt : ∀ y, f^[n] (⇑e.symm y) = ⇑e.symm (g^[n] y) := by
      intro y
      have hi := (hsc.iterate_right n) (e.symm y)
      rw [e.apply_symm_apply] at hi
      rw [← hi, e.symm_apply_apply]
    have hseteq : ⇑e.symm ⁻¹' (f^[n] ⁻¹' A ∩ B)
        = g^[n] ⁻¹' (⇑e.symm ⁻¹' A) ∩ (⇑e.symm ⁻¹' B) := by
      ext y; simp only [Set.mem_preimage, Set.mem_inter_iff, hpt y]
    have hmeas : MeasurableSet (f^[n] ⁻¹' A ∩ B) := ((hfmeas.iterate n) hA).inter hB
    rw [← hesymm.measure_preimage hmeas.nullMeasurableSet, hseteq]
  simp_rw [key]
  exact hmix

/-! ### Any Bernoulli shift is strongly mixing

We now prove `isStronglyMixing_infinitePi_shift`. The two general set-theoretic facts below feed the
`ε/4` estimate; everything else is specific to the one-sided shift on `ℕ → α`. -/

/-- The symmetric difference of two intersections is contained in the union of the
coordinatewise symmetric differences. -/
private lemma inter_symmDiff_inter_subset {Ω : Type*} (s t b b' : Set Ω) :
    (s ∩ b) ∆ (t ∩ b') ⊆ (s ∆ t) ∪ (b ∆ b') := by
  intro x hx
  simp only [Set.mem_union, Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
  tauto

/-- The real-valued measure is `1`-Lipschitz for the symmetric-difference distance. -/
private lemma abs_measureReal_sub_le_symmDiff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (s t : Set Ω) : |μ.real s - μ.real t| ≤ μ.real (s ∆ t) := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have hsub : s ⊆ t ∪ (s ∆ t) := by
      intro x hx; simp only [Set.mem_union, Set.mem_symmDiff]; tauto
    have h1 := measureReal_mono (μ := μ) hsub
    have h2 := measureReal_union_le (μ := μ) t (s ∆ t)
    linarith
  · have hsub : t ⊆ s ∪ (s ∆ t) := by
      intro x hx; simp only [Set.mem_union, Set.mem_symmDiff]; tauto
    have h1 := measureReal_mono (μ := μ) hsub
    have h2 := measureReal_union_le (μ := μ) s (s ∆ t)
    linarith

/-- The one-sided (left) shift on sequences `ℕ → α`: `seqShift x = (n ↦ x (n+1))` drops the `0`th
coordinate. The dynamics of `(seqShift, Measure.infinitePi (fun _ => ν))` is the **Bernoulli shift**
over the single-coordinate law `ν`. -/
def seqShift (x : ℕ → α) : ℕ → α := fun n => x (n + 1)

set_option linter.unusedSectionVars false in
/-- Iterating the shift `n` times drops the first `n` coordinates. -/
private lemma seqShift_iterate (m : ℕ) : ∀ (x : ℕ → α) (k : ℕ), seqShift^[m] x k = x (k + m) := by
  induction m with
  | zero => intro x k; simp
  | succ p ih =>
    intro x k
    rw [Function.iterate_succ, Function.comp_apply, ih (seqShift x) k]
    rfl

variable (ν : Measure α) [IsProbabilityMeasure ν]

/-- The shift preserves the i.i.d. product measure: it is the coordinate reindexing along the
injection `· + 1`, which `Measure.map_infinitePi_infinitePi_of_inj` sends to the same product. -/
private lemma seqShift_measurePreserving :
    MeasurePreserving seqShift (Measure.infinitePi (fun _ : ℕ => ν))
      (Measure.infinitePi (fun _ : ℕ => ν)) := by
  refine ⟨measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1), ?_⟩
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν) (add_left_injective 1)
  exact h

/-- **Exact independence of far-apart cylinders.** If the coordinate block of `cylinder I S` shifted
by `n` is disjoint from the block of `cylinder J R` (which holds once `n > sup J`), then the shifted
cylinder and the cylinder are independent events. -/
private lemma seqShift_eventually_indep (I J : Finset ℕ) (S : Set (∀ _ : I, α)) (R : Set (∀ _ : J, α))
    (hS : MeasurableSet S) (hR : MeasurableSet R) (n : ℕ) (hn : J.sup id < n) :
    Measure.infinitePi (fun _ : ℕ => ν) (seqShift^[n] ⁻¹' cylinder I S ∩ cylinder J R)
      = Measure.infinitePi (fun _ : ℕ => ν) (cylinder I S)
        * Measure.infinitePi (fun _ : ℕ => ν) (cylinder J R) := by
  classical
  -- The index block of `cylinder I S`, shifted by `n`.
  let e : ℕ ↪ ℕ := ⟨(· + n), add_left_injective n⟩
  let K : Finset ℕ := I.map e
  have hmemK : ∀ i : I, (i : ℕ) + n ∈ K := fun i => Finset.mem_map_of_mem e i.2
  -- Reindexing the cylinder set from `K` back to `I`.
  let ρ : (∀ _ : K, α) → (∀ _ : I, α) := fun g i => g ⟨(i : ℕ) + n, hmemK i⟩
  have hρ : Measurable ρ := measurable_pi_lambda _ fun i => measurable_pi_apply _
  -- The shifted cylinder is the `K`-block cylinder over `ρ ⁻¹' S`.
  have hset : seqShift^[n] ⁻¹' cylinder I S = cylinder K (ρ ⁻¹' S) := by
    ext x
    simp only [Set.mem_preimage, mem_cylinder, Set.mem_preimage]
    have heq : I.restrict (seqShift^[n] x) = ρ (K.restrict x) := by
      funext i; exact seqShift_iterate n x (i : ℕ)
    rw [heq]
  -- The two coordinate blocks are disjoint, hence independent.
  have hdisj : Disjoint K J := by
    rw [Finset.disjoint_left]
    rintro a ha haJ
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 ha
    have hle : (i + n : ℕ) ≤ J.sup id := Finset.le_sup (f := id) haJ
    omega
  have hcoind : iIndepFun (fun (i : ℕ) (ω : ℕ → α) => ω i)
      (Measure.infinitePi (fun _ : ℕ => ν)) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => id) fun _ => measurable_id
  have hKJ : IndepFun K.restrict J.restrict (Measure.infinitePi (fun _ : ℕ => ν)) :=
    hcoind.indepFun_finset K J hdisj fun i => measurable_pi_apply i
  -- Independence, stated for the cylinders (defeq to the block preimages).
  have hmul : Measure.infinitePi (fun _ : ℕ => ν) (cylinder K (ρ ⁻¹' S) ∩ cylinder J R)
      = Measure.infinitePi (fun _ : ℕ => ν) (cylinder K (ρ ⁻¹' S))
        * Measure.infinitePi (fun _ : ℕ => ν) (cylinder J R) :=
    hKJ.measure_inter_preimage_eq_mul (ρ ⁻¹' S) R (hρ hS) hR
  have hPK : Measure.infinitePi (fun _ : ℕ => ν) (cylinder K (ρ ⁻¹' S))
      = Measure.infinitePi (fun _ : ℕ => ν) (cylinder I S) := by
    rw [← hset]
    exact ((seqShift_measurePreserving ν).iterate n).measure_preimage hS.cylinder.nullMeasurableSet
  rw [hset, hmul, hPK]

/-- Eventual exact independence, packaged for cylinders given as elements of `measurableCylinders`. -/
private lemma seqShift_eventually_indep_mem (A' B' : Set (ℕ → α))
    (hA' : A' ∈ measurableCylinders (fun _ : ℕ => α))
    (hB' : B' ∈ measurableCylinders (fun _ : ℕ => α)) :
    ∀ᶠ n in atTop, Measure.infinitePi (fun _ : ℕ => ν) (seqShift^[n] ⁻¹' A' ∩ B')
      = Measure.infinitePi (fun _ : ℕ => ν) A' * Measure.infinitePi (fun _ : ℕ => ν) B' := by
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders A').mp hA'
  obtain ⟨J, R, hR, rfl⟩ := (mem_measurableCylinders B').mp hB'
  rw [eventually_atTop]
  exact ⟨J.sup id + 1, fun n hn => seqShift_eventually_indep ν I J S R hS hR n (by omega)⟩

/-- **(Quas 2009.) Any one-sided Bernoulli shift is strongly mixing.** For a probability measure `ν`
on `α`, the coordinate shift `x ↦ (n ↦ x (n+1))` on `ℕ → α`, equipped with the i.i.d. product measure
`Measure.infinitePi (fun _ => ν)`, is strongly mixing. The proof realises the standard
cylinder-approximation argument; see [Quas09] and the module docstring. -/
theorem isStronglyMixing_infinitePi_shift :
    IsStronglyMixing (seqShift (α := α)) (Measure.infinitePi fun _ => ν) := by
  refine ⟨seqShift_measurePreserving ν, fun A B hA hB => ?_⟩
  show Tendsto (fun n => Measure.infinitePi (fun _ : ℕ => ν) (seqShift^[n] ⁻¹' A ∩ B)) atTop
    (𝓝 (Measure.infinitePi (fun _ : ℕ => ν) A * Measure.infinitePi (fun _ : ℕ => ν) B))
  set μ := Measure.infinitePi (fun _ : ℕ => ν) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hfin : ∀ s : Set (ℕ → α), μ s ≠ ⊤ := fun s => measure_ne_top μ s
  have hmp : MeasurePreserving seqShift μ μ := by rw [hμ]; exact seqShift_measurePreserving ν
  have hev : ∀ A' B' : Set (ℕ → α), A' ∈ measurableCylinders (fun _ : ℕ => α) →
      B' ∈ measurableCylinders (fun _ : ℕ => α) →
      ∀ᶠ n in atTop, μ (seqShift^[n] ⁻¹' A' ∩ B') = μ A' * μ B' := by
    intro A' B' hA' hB'; rw [hμ]; exact seqShift_eventually_indep_mem ν A' B' hA' hB'
  -- Reduce to convergence of the real-valued measures.
  rw [show (μ A * μ B) = ENNReal.ofReal (μ.real A * μ.real B) by
        rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def, measureReal_def,
          ENNReal.ofReal_toReal (hfin A), ENNReal.ofReal_toReal (hfin B)]]
  rw [show (fun n => μ (seqShift^[n] ⁻¹' A ∩ B))
        = fun n => ENNReal.ofReal (μ.real (seqShift^[n] ⁻¹' A ∩ B)) from by
      funext n; rw [measureReal_def, ENNReal.ofReal_toReal (hfin _)]]
  apply ENNReal.tendsto_ofReal
  -- The `ε/4` argument for the real-valued limit.
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / 4 with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨A', hA'mem, hA'⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ)
    isSetRing_measurableCylinders
    ⟨{Set.univ}, Set.countable_singleton _, by
        rw [Set.singleton_subset_iff]; exact univ_mem_measurableCylinders _, by
        rw [Set.sUnion_singleton, Set.compl_univ, measure_empty]⟩
    generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.mpr hδpos)
  obtain ⟨B', hB'mem, hB'⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ)
    isSetRing_measurableCylinders
    ⟨{Set.univ}, Set.countable_singleton _, by
        rw [Set.singleton_subset_iff]; exact univ_mem_measurableCylinders _, by
        rw [Set.sUnion_singleton, Set.compl_univ, measure_empty]⟩
    generateFrom_measurableCylinders.symm hB (ENNReal.ofReal_pos.mpr hδpos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev A' B' hA'mem hB'mem)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hA'm : MeasurableSet A' := MeasurableSet.of_mem_measurableCylinders hA'mem
  have hB'm : MeasurableSet B' := MeasurableSet.of_mem_measurableCylinders hB'mem
  -- The middle term is exact.
  have hmid : μ.real (seqShift^[n] ⁻¹' A' ∩ B') = μ.real A' * μ.real B' := by
    rw [measureReal_def, hN n hn, ENNReal.toReal_mul]; rfl
  -- Symmetric-difference bounds, converted to `ℝ` and to `δ`.
  have hAA' : μ.real (A ∆ A') < δ := by
    rw [measureReal_def, symmDiff_comm]
    calc (μ (A' ∆ A)).toReal < (ENNReal.ofReal δ).toReal :=
          (ENNReal.toReal_lt_toReal (hfin _) ENNReal.ofReal_ne_top).mpr hA'
      _ = δ := ENNReal.toReal_ofReal hδpos.le
  have hBB' : μ.real (B ∆ B') < δ := by
    rw [measureReal_def, symmDiff_comm]
    calc (μ (B' ∆ B)).toReal < (ENNReal.ofReal δ).toReal :=
          (ENNReal.toReal_lt_toReal (hfin _) ENNReal.ofReal_ne_top).mpr hB'
      _ = δ := ENNReal.toReal_ofReal hδpos.le
  have hAA'' : |μ.real A' - μ.real A| ≤ μ.real (A ∆ A') := by
    rw [symmDiff_comm]; exact abs_measureReal_sub_le_symmDiff μ A' A
  have hBB'' : |μ.real B' - μ.real B| ≤ μ.real (B ∆ B') := by
    rw [symmDiff_comm]; exact abs_measureReal_sub_le_symmDiff μ B' B
  -- First term: continuity of `μ` under the cylinder approximation.
  have h1 : |μ.real (seqShift^[n] ⁻¹' A ∩ B) - μ.real (seqShift^[n] ⁻¹' A' ∩ B')|
      ≤ μ.real (A ∆ A') + μ.real (B ∆ B') := by
    calc |μ.real (seqShift^[n] ⁻¹' A ∩ B) - μ.real (seqShift^[n] ⁻¹' A' ∩ B')|
        ≤ μ.real ((seqShift^[n] ⁻¹' A ∩ B) ∆ (seqShift^[n] ⁻¹' A' ∩ B')) :=
          abs_measureReal_sub_le_symmDiff μ _ _
      _ ≤ μ.real (((seqShift^[n] ⁻¹' A) ∆ (seqShift^[n] ⁻¹' A')) ∪ (B ∆ B')) :=
          measureReal_mono (μ := μ) (inter_symmDiff_inter_subset _ _ _ _)
      _ ≤ μ.real ((seqShift^[n] ⁻¹' A) ∆ (seqShift^[n] ⁻¹' A')) + μ.real (B ∆ B') :=
          measureReal_union_le (μ := μ) _ _
      _ = μ.real (seqShift^[n] ⁻¹' (A ∆ A')) + μ.real (B ∆ B') := by rw [← Set.preimage_symmDiff]
      _ = μ.real (A ∆ A') + μ.real (B ∆ B') := by
          rw [(hmp.iterate n).measureReal_preimage (hA.symmDiff hA'm).nullMeasurableSet]
  -- Third term: continuity of multiplication.
  have h3 : |μ.real A' * μ.real B' - μ.real A * μ.real B| ≤ μ.real (A ∆ A') + μ.real (B ∆ B') := by
    have e : μ.real A' * μ.real B' - μ.real A * μ.real B
        = (μ.real A' - μ.real A) * μ.real B' + μ.real A * (μ.real B' - μ.real B) := by ring
    calc |μ.real A' * μ.real B' - μ.real A * μ.real B|
        = |(μ.real A' - μ.real A) * μ.real B' + μ.real A * (μ.real B' - μ.real B)| := by rw [e]
      _ ≤ |(μ.real A' - μ.real A) * μ.real B'| + |μ.real A * (μ.real B' - μ.real B)| :=
            abs_add_le _ _
      _ = |μ.real A' - μ.real A| * |μ.real B'| + |μ.real A| * |μ.real B' - μ.real B| := by
            rw [abs_mul, abs_mul]
      _ ≤ μ.real (A ∆ A') * 1 + 1 * μ.real (B ∆ B') := by
            apply add_le_add
            · exact mul_le_mul hAA''
                (by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
                (abs_nonneg _) measureReal_nonneg
            · exact mul_le_mul
                (by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
                hBB'' (abs_nonneg _) zero_le_one
      _ = μ.real (A ∆ A') + μ.real (B ∆ B') := by ring
  calc |μ.real (seqShift^[n] ⁻¹' A ∩ B) - μ.real A * μ.real B|
      ≤ |μ.real (seqShift^[n] ⁻¹' A ∩ B) - μ.real (seqShift^[n] ⁻¹' A' ∩ B')|
        + |μ.real (seqShift^[n] ⁻¹' A' ∩ B') - μ.real A * μ.real B| := abs_sub_le _ _ _
    _ = |μ.real (seqShift^[n] ⁻¹' A ∩ B) - μ.real (seqShift^[n] ⁻¹' A' ∩ B')|
        + |μ.real A' * μ.real B' - μ.real A * μ.real B| := by rw [hmid]
    _ ≤ (μ.real (A ∆ A') + μ.real (B ∆ B')) + (μ.real (A ∆ A') + μ.real (B ∆ B')) :=
        add_le_add h1 h3
    _ < ε := by linarith

end MeasureTheory
