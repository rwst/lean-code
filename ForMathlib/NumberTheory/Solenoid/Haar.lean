/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import ForMathlib.NumberTheory.PadicHaar
public import ForMathlib.NumberTheory.Solenoid.Basic

@[expose] public section

/-!
# Haar measure on the `S`-adic solenoid

`Σ_S` is a compact group, so it carries a normalized Haar probability measure `haar S`.  This
file identifies it concretely:

> **`haar S` is Lebesgue × ∏_{p ∈ S} Haar(`ℤ_p`) read on the fundamental domain
> `D_S = [0,1) × ∏_{p ∈ S} ℤ_p`** (`haar_eq`, `haar_apply`),

and deduces the cell masses `(b - a) ∏_{p ∈ S} p^{-k_p}` (`haar_cell`).

* `ambientMeasure S` is Lebesgue measure times the product of the `p`-adic Haar measures, each
  normalized on `ℤ_p` (`ForMathlib/NumberTheory/PadicHaar.lean`); `D_S` has mass `1`.
* `isAddFundamentalDomain_D`: `D_S` is a fundamental domain for `Δ_S` in Mathlib's sense — the
  theorem `exists_unique_fundamental` of `Ambient.lean`, rephrased.
* `measureD S = map mk (ambientMeasure S |_ D_S)` is translation invariant (translate the
  fundamental domain, not the set: `IsAddFundamentalDomain.measure_set_eq`) and a probability
  measure, so uniqueness of Haar measure identifies it with `haar S`.

Invariance under every `σ_u` follows from uniqueness as well (`map_smulAut_haar`).

## Main declarations

* `Solenoid.ambientMeasure`, `ambientMeasure_prod`, `ambientMeasure_D`,
  `isAddFundamentalDomain_D`.
* `Solenoid.haar`, `haar_eq`, `haar_apply`, `measurePreserving_mk`.
* `Solenoid.map_smulAut_haar`, `measurePreserving_smulAut`.
* `Solenoid.haar_mk_image_of_isOpen`, `Solenoid.cell`, `haar_cell`, `haar_cell_single`,
  `haar_cell_pos`.

## Implementation notes

The quotient σ-algebra is the one inherited from `QuotientAddGroup.measurableSpace`; see
`Basic.lean`.  The route avoids `Mathlib/MeasureTheory/Measure/Haar/Quotient.lean`, which works
with right cosets (`Δ.op`) and would need the fundamental domain re-proved for the opposite
action.  For `S = {2, 3}` this file specialises to `TH/Solenoid/Haar.lean`.

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer (2011),
  Chapter 8.
-/

namespace Solenoid

open Metric Set MeasureTheory MeasureTheory.Measure TopologicalSpace Rat
open scoped Pointwise ENNReal

variable (S : Finset Nat.Primes)

/-! ### The ambient Haar measure -/

/-- The Haar measure of `G_S = ℝ × ∏_{p ∈ S} ℚ_p`: Lebesgue measure times the `p`-adic Haar
measures, each normalized so that `ℤ_p` has mass `1`.  The fundamental domain then has mass `1`
(`ambientMeasure_D`). -/
noncomputable def ambientMeasure : Measure (ambient S) :=
  (volume : Measure ℝ).prod (Measure.pi fun p : S ↦ Padic.haarMeasure ((p : Nat.Primes) : ℕ))

instance instSigmaFiniteAmbientMeasure : SigmaFinite (ambientMeasure S) :=
  inferInstanceAs (SigmaFinite ((volume : Measure ℝ).prod
    (Measure.pi fun p : S ↦ Padic.haarMeasure ((p : Nat.Primes) : ℕ))))

instance instIsAddLeftInvariantAmbientMeasure : (ambientMeasure S).IsAddLeftInvariant :=
  inferInstanceAs (((volume : Measure ℝ).prod
    (Measure.pi fun p : S ↦ Padic.haarMeasure ((p : Nat.Primes) : ℕ))).IsAddLeftInvariant)

variable {S}

/-- The measure of a box is the product of the coordinate measures. -/
theorem ambientMeasure_prod (I : Set ℝ) (s : (p : S) → Set ℚ_[((p : Nat.Primes) : ℕ)]) :
    ambientMeasure S (I ×ˢ univ.pi s) =
      volume I * ∏ p : S, Padic.haarMeasure ((p : Nat.Primes) : ℕ) (s p) := by
  rw [ambientMeasure, Measure.prod_prod, Measure.pi_pi]

/-- **The fundamental domain is a probability box.** -/
theorem ambientMeasure_D : ambientMeasure S (D S) = 1 := by
  rw [D, ambientMeasure_prod, Real.volume_Ico]
  simp [Padic.haarMeasure_closedBall_one]

theorem measurableSet_D : MeasurableSet (D S) :=
  measurableSet_Ico.prod (MeasurableSet.univ_pi fun _ ↦ measurableSet_closedBall)

/-- The lattice is countable: it is the image of a subring of `ℚ`. -/
instance instCountableLattice : Countable (lattice S) := by
  refine Function.Surjective.countable
    (f := fun q : sIntegers S ↦ (⟨diag S q, diag_mem_lattice q.2⟩ : lattice S)) ?_
  rintro ⟨g, hg⟩
  obtain ⟨q, hq, rfl⟩ := mem_lattice.mp hg
  exact ⟨⟨q, hq⟩, rfl⟩

/-- **`D_S` is a fundamental domain in Mathlib's sense.** -/
theorem isAddFundamentalDomain_D : IsAddFundamentalDomain (lattice S) (D S) (ambientMeasure S) := by
  refine IsAddFundamentalDomain.mk' measurableSet_D.nullMeasurableSet fun x ↦ ?_
  obtain ⟨d, ⟨hdD, hd⟩, huniq⟩ := exists_unique_fundamental x
  refine ⟨⟨-(x - d), neg_mem hd⟩, ?_, ?_⟩
  · change -(x - d) + x ∈ D S
    simpa using hdD
  · rintro ⟨γ, hγ⟩ (hxD : γ + x ∈ D S)
    have hx : x - (γ + x) ∈ lattice S := by
      rw [show x - (γ + x) = -γ by abel]
      exact neg_mem hγ
    apply Subtype.ext
    change γ = -(x - d)
    rw [← huniq (γ + x) ⟨hxD, hx⟩]
    abel

/-! ### The quotient measure and Haar measure on `Σ_S` -/

theorem measurable_mk : Measurable (QuotientAddGroup.mk (s := lattice S)) :=
  QuotientAddGroup.continuous_mk.measurable

variable (S) in
/-- The measure on `Σ_S` obtained by reading `ambientMeasure S` on the fundamental domain. -/
noncomputable def measureD : Measure (Solenoid S) :=
  Measure.map (QuotientAddGroup.mk (s := lattice S)) ((ambientMeasure S).restrict (D S))

theorem measureD_apply {A : Set (Solenoid S)} (hA : MeasurableSet A) :
    measureD S A = ambientMeasure S (QuotientAddGroup.mk ⁻¹' A ∩ D S) := by
  rw [measureD, Measure.map_apply measurable_mk hA, Measure.restrict_apply (measurable_mk hA)]

instance instIsProbabilityMeasureMeasureD : IsProbabilityMeasure (measureD S) :=
  ⟨by rw [measureD_apply MeasurableSet.univ, Set.preimage_univ, Set.univ_inter, ambientMeasure_D]⟩

/-- The preimage of any set under the projection is `Δ_S`-invariant. -/
theorem preimage_mk_vadd_invariant (A : Set (Solenoid S)) (γ : lattice S) :
    (fun x ↦ γ +ᵥ x) ⁻¹' (QuotientAddGroup.mk ⁻¹' A) = QuotientAddGroup.mk ⁻¹' A := by
  ext u
  have hmk : (QuotientAddGroup.mk ((γ : ambient S) + u) : Solenoid S) = QuotientAddGroup.mk u := by
    rw [QuotientAddGroup.eq]
    simp
  change (QuotientAddGroup.mk ((γ : ambient S) + u) : Solenoid S) ∈ A ↔ _
  rw [hmk]
  rfl

/-- **`measureD S` is translation invariant.**  The proof moves the fundamental domain, not the
set: a `Δ_S`-invariant set has the same mass in every fundamental domain. -/
instance instIsAddLeftInvariantMeasureD : (measureD S).IsAddLeftInvariant := by
  constructor
  intro x
  ext A hA
  rw [Measure.map_apply (measurable_const_add x) hA, measureD_apply hA,
    measureD_apply (measurable_const_add x hA)]
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  set T : Set (ambient S) := QuotientAddGroup.mk ⁻¹' A with hT
  have hTmeas : MeasurableSet T := measurable_mk hA
  have hpre : QuotientAddGroup.mk ⁻¹' ((fun y ↦ QuotientAddGroup.mk g + y) ⁻¹' A)
      = (fun u ↦ g + u) ⁻¹' T := by
    ext u
    simp only [Set.mem_preimage, hT]
    rw [← QuotientAddGroup.mk_add]
  rw [hpre]
  have hstep : (fun u ↦ g + u) ⁻¹' T ∩ D S = (fun u ↦ g + u) ⁻¹' (T ∩ (g +ᵥ D S)) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_vadd_set, vadd_eq_add]
    exact and_congr_right' ⟨fun h ↦ ⟨u, h, rfl⟩, fun ⟨y, hy, hyu⟩ ↦ add_left_cancel hyu ▸ hy⟩
  rw [hstep, measure_preimage_add]
  exact (isAddFundamentalDomain_D.measure_set_eq (isAddFundamentalDomain_D.vadd_of_comm g)
    hTmeas (preimage_mk_vadd_invariant A)).symm

variable (S) in
/-- **The normalized Haar probability measure of the solenoid.** -/
noncomputable def haar : Measure (Solenoid S) := Measure.addHaarMeasure ⊤

noncomputable instance instIsAddHaarMeasureHaar : (haar S).IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure (⊤ : PositiveCompacts (Solenoid S))).IsAddHaarMeasure)

/-- **The product form of Haar measure**: the abstract Haar measure of `Σ_S` is
Lebesgue × ∏ Haar(`ℤ_p`) read on the fundamental domain. -/
theorem haar_eq : haar S = measureD S :=
  (Measure.addHaarMeasure_eq_iff ⊤ (measureD S)).mpr (by
    change measureD S univ = 1
    exact measure_univ)

instance instIsProbabilityMeasureHaar : IsProbabilityMeasure (haar S) := by
  rw [haar_eq]; infer_instance

/-- **The product form, in coordinates.**  The Haar mass of a Borel set of `Σ_S` is the ambient
mass of its representatives in `D_S`. -/
theorem haar_apply {A : Set (Solenoid S)} (hA : MeasurableSet A) :
    haar S A = ambientMeasure S (QuotientAddGroup.mk ⁻¹' A ∩ D S) := by
  rw [haar_eq, measureD_apply hA]

/-- The projection is measure preserving from the fundamental domain onto the solenoid. -/
theorem measurePreserving_mk :
    MeasurePreserving (QuotientAddGroup.mk (s := lattice S)) ((ambientMeasure S).restrict (D S))
      (haar S) :=
  ⟨measurable_mk, haar_eq.symm⟩

/-! ### Invariance under the `S`-units -/

variable {u : ℚ}

theorem measurable_smulAut (hu : IsSUnit S u) : Measurable (smulAut hu) :=
  (smulAut hu).continuous.measurable

/-- **Haar measure is invariant under every `σ_u`.**  The pushforward is again a Haar probability
measure, and there is only one. -/
theorem map_smulAut_haar (hu : IsSUnit S u) : Measure.map (smulAut hu) (haar S) = haar S := by
  have huniv : Measure.map (smulAut hu) (haar S) univ = 1 := by
    rw [Measure.map_apply (measurable_smulAut hu) MeasurableSet.univ, Set.preimage_univ,
      measure_univ]
  have : (Measure.map (smulAut hu) (haar S)).IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map (haar S) (smulAut hu)
  exact ((Measure.addHaarMeasure_eq_iff ⊤ _).mpr huniv).symm

theorem measurePreserving_smulAut (hu : IsSUnit S u) :
    MeasurePreserving (smulAut hu) (haar S) (haar S) :=
  ⟨measurable_smulAut hu, map_smulAut_haar hu⟩

theorem haar_preimage_smulAut (hu : IsSUnit S u) {A : Set (Solenoid S)} (hA : MeasurableSet A) :
    haar S (smulAut hu ⁻¹' A) = haar S A :=
  (measurePreserving_smulAut hu).measure_preimage hA.nullMeasurableSet

/-! ### Cells -/

/-- A subset of the fundamental domain is a set of unique representatives. -/
theorem preimage_image_inter_D {R : Set (ambient S)} (hR : R ⊆ D S) :
    QuotientAddGroup.mk (s := lattice S) ⁻¹' (QuotientAddGroup.mk '' R) ∩ D S = R := by
  ext v
  constructor
  · rintro ⟨⟨r, hr, hrv⟩, hvD⟩
    have hsub : v - r ∈ lattice S := by
      have h := QuotientAddGroup.eq.mp hrv
      rwa [neg_add_eq_sub] at h
    obtain ⟨d, _, huniq⟩ := exists_unique_fundamental v
    have h1 : v = d := huniq v ⟨hvD, by simp⟩
    have h2 : r = d := huniq r ⟨hR hr, hsub⟩
    rwa [h1.trans h2.symm]
  · exact fun hv ↦ ⟨⟨v, hv, rfl⟩, hR hv⟩

/-- **No folding on open subsets of the fundamental domain**: the Haar mass of the image of an
open `R ⊆ D_S` is its ambient mass. -/
theorem haar_mk_image_of_isOpen {R : Set (ambient S)} (hRD : R ⊆ D S) (hR : IsOpen R) :
    haar S (QuotientAddGroup.mk '' R) = ambientMeasure S R := by
  rw [haar_apply ((QuotientAddGroup.isOpenMap_coe (N := lattice S) R hR).measurableSet),
    preimage_image_inter_D hRD]

variable (S) in
/-- The **cell** over the interval `(a, b)` at levels `k : S → ℕ`: fractional part in `(a, b)` and,
for each `p ∈ S`, the `p`-adic coordinate congruent to `c p` modulo `p^{k p}`. -/
noncomputable def cell (a b : ℝ) (k : S → ℕ) (c : (p : S) → ℚ_[((p : Nat.Primes) : ℕ)]) :
    Set (Solenoid S) :=
  QuotientAddGroup.mk '' (Ioo a b ×ˢ univ.pi fun p ↦ Padic.residueBall _ (k p) (c p))

/-- **The cell masses.**  A cell over an interval of length `b - a` at levels `k` has Haar mass
`(b - a) ∏_{p ∈ S} p^{-k_p}`: the fractional part and the residues at the primes of `S` are
independent and uniform. -/
theorem haar_cell {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (k : S → ℕ)
    {c : (p : S) → ℚ_[((p : Nat.Primes) : ℕ)]} (hc : ∀ p, ‖c p‖ ≤ 1) :
    haar S (cell S a b k c) =
      ENNReal.ofReal (b - a) * ∏ p : S, (((p : Nat.Primes) : ℕ) ^ k p : ℝ≥0∞)⁻¹ := by
  have hsub : Ioo a b ×ˢ univ.pi (fun p ↦ Padic.residueBall _ (k p) (c p)) ⊆ D S := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    refine ⟨⟨ha.trans hx.1.le, hx.2.trans_le hb⟩, fun p _ ↦ ?_⟩
    exact Padic.residueBall_subset_unitBall (hc p) (k p) (hy p trivial)
  have hopen : IsOpen (Ioo a b ×ˢ univ.pi fun p ↦ Padic.residueBall _ (k p) (c p)) :=
    isOpen_Ioo.prod (isOpen_set_pi finite_univ fun p _ ↦ Padic.isOpen_residueBall (k p) (c p))
  rw [cell, haar_mk_image_of_isOpen hsub hopen, ambientMeasure_prod, Real.volume_Ioo]
  simp only [Padic.haarMeasure_residueBall]

/-- A cell over a nondegenerate interval has positive mass. -/
theorem haar_cell_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (k : S → ℕ)
    {c : (p : S) → ℚ_[((p : Nat.Primes) : ℕ)]} (hc : ∀ p, ‖c p‖ ≤ 1) :
    0 < haar S (cell S a b k c) := by
  rw [haar_cell ha hb k hc]
  refine ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by linarith)).ne' ?_
  exact Finset.prod_ne_zero_iff.mpr fun p _ ↦ ENNReal.inv_ne_zero.mpr
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

/-- **The pure `p`-adic cylinder**: the residue mod `p^k` at one prime `p₀ ∈ S` is uniform, each
class having Haar mass `p₀^{-k}`. -/
theorem haar_cell_single (p₀ : S) (k : ℕ) {c : (p : S) → ℚ_[((p : Nat.Primes) : ℕ)]}
    (hc : ∀ p, ‖c p‖ ≤ 1) :
    haar S (cell S 0 1 (Pi.single p₀ k) c) = (((p₀ : Nat.Primes) : ℕ) ^ k : ℝ≥0∞)⁻¹ := by
  rw [haar_cell le_rfl le_rfl _ hc, Finset.prod_eq_single p₀ (fun p _ hp ↦ by simp [hp])
    (by simp)]
  simp

end Solenoid

/-! ### Examples -/

section Examples

open Solenoid MeasureTheory
open scoped ENNReal

private def two : Nat.Primes := ⟨2, Nat.prime_two⟩

private def three : Nat.Primes := ⟨3, Nat.prime_three⟩

private theorem primesOf_six : Nat.primesOf 6 = {two, three} := by
  ext ℓ
  rw [Nat.mem_primesOf_iff_dvd (by norm_num), Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hle : (ℓ : ℕ) ≤ 6 := Nat.le_of_dvd (by norm_num) h
    have hp := ℓ.2
    have h23 : (ℓ : ℕ) = 2 ∨ (ℓ : ℕ) = 3 := by
      interval_cases (ℓ : ℕ) <;> first | omega | exact absurd hp Nat.not_prime_zero |
        exact absurd hp Nat.not_prime_one | exact absurd hp (by decide)
    rcases h23 with h2 | h3
    · exact Or.inl (Subtype.ext h2)
    · exact Or.inr (Subtype.ext h3)
  · rintro (rfl | rfl)
    · change 2 ∣ 6; norm_num
    · change 3 ∣ 6; norm_num

/-- For `S = {2, 3}` the cell masses are `(b - a) 2⁻ᵏ 3⁻ʲ`, the values of `TH.S6.haar_cell`. -/
example {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (k j : ℕ)
    {c : (p : Nat.primesOf 6) → ℚ_[((p : Nat.Primes) : ℕ)]} (hc : ∀ p, ‖c p‖ ≤ 1) :
    haar _ (cell (Nat.primesOf 6) a b (fun p ↦ if ((p : Nat.Primes) : ℕ) = 2 then k else j) c) =
      ENNReal.ofReal (b - a) * (((2 : ℝ≥0∞) ^ k)⁻¹ * ((3 : ℝ≥0∞) ^ j)⁻¹) := by
  rw [haar_cell ha hb _ hc, Finset.prod_coe_sort (Nat.primesOf 6)
    (fun p : Nat.Primes ↦ (((p : ℕ) : ℝ≥0∞) ^ (if (p : ℕ) = 2 then k else j))⁻¹),
    primesOf_six, Finset.prod_pair (fun h ↦ by simpa [two, three] using congrArg Subtype.val h)]
  simp [two, three]

end Examples
