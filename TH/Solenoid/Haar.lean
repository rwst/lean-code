/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ForMathlib.NumberTheory.PadicHaar
import TH.Solenoid.Sigma6
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Haar measure on the solenoid `Σ₆`, its invariance, and the cell masses

This is work package W2 of plan-A1+ (§4, L2).  `Σ₆` is a compact group (W1), so it carries a
normalized Haar probability measure `haar`; the content of this file is *what that measure is*:

> **`haar` is Lebesgue × Haar(`ℤ₂`) × Haar(`ℤ₃`) read on the fundamental domain
> `D = [0,1) × ℤ₂ × ℤ₃`** (`haar_eq_μD`, `haar_apply`),

and hence the finite-level cell masses `2⁻ᵏ 3⁻ʲ (b-a)` (`haar_cell`) which are the objects of
`Z32/Dictionary.lean`: fractional part in an interval, floor residue mod `2ᵏ`, floor residue mod
`3ʲ`.  The route is:

* `μ6`, the ambient Haar measure on `G₆ = ℝ × ℚ₂ × ℚ₃`, a product of Lebesgue measure and the two
  `p`-adic Haar measures normalized on `ℤ_[p]` (`ForMathlib/NumberTheory/PadicHaar.lean`);
  it gives the fundamental domain mass `1` (`μ6_D`).
* `isAddFundamentalDomain_D`: `D` *is* a fundamental domain for `Δ₆` in Mathlib's sense — this is
  just `exists_unique_fundamental` of W1 rephrased through `IsAddFundamentalDomain.mk'`.
* `μD := map mk (μ6.restrict D)` is then translation-invariant (the one real proof here: translate
  the fundamental domain rather than the set, and use that `μ6` does not see which fundamental
  domain a `Δ₆`-invariant set is measured against), and it is a probability measure, so
  uniqueness of Haar measure identifies it with `haar`.

Invariance under the `ℤ²`-action is then immediate from uniqueness in the same form: the
pushforward of `haar` under any `solAut` is again a Haar probability measure
(`map_solAut_haar`), in particular `haar` is `σ₂`-, `σ₃`- and `T`-invariant.  This is the
statement the entropy side of the plan consumes: the diagonal `T = ×(3/2)` is a measure-preserving
transformation of `(Σ₆, haar)` (`measurePreserving_T32`).

*σ-algebra note (correcting W1).*  `Σ₆` is **not** given a declared `borel _` σ-algebra: it
already has `QuotientAddGroup.measurableSpace` (the pushforward σ-algebra), and
`QuotientAddGroup.borelSpace` proves that this *is* the Borel σ-algebra for a quotient of a Polish
group by a closed normal subgroup.  W1's declared instance has therefore been removed (see
`Sigma6.lean`): it was a genuine diamond, and it also placed `Σ₆` outside
`Mathlib/MeasureTheory/Measure/Haar/Quotient.lean`, whose `…MeasureEqMeasurePreimage` layer takes
no `MeasurableSpace (G ⧸ Γ)` variable and so is stated for the pushforward σ-algebra only.  That
layer is now applicable in principle; it is not used here because it is routed through the
*opposite* subgroup `Δ₆.op` (right cosets), which would have to be re-proved a fundamental domain
(Mathlib duplicates that proof for `AddCircle`), while the direct route through
`IsAddFundamentalDomain.measure_set_eq` — translate the fundamental domain, not the set — is
twenty lines.

## Main statements

* `μ6_D`, `isAddFundamentalDomain_D` — the ambient measure and the fundamental domain.
* `haar_eq_μD`, `haar_apply` — **the product form**: `haar A = μ6 (mk ⁻¹' A ∩ D)`.
* `map_solAut_haar`, `map_T32_haar`, `measurePreserving_T32` — invariance under the action.
* `haar_cell`, `haar_cell_twoAdic` — **the cell masses** `2⁻ᵏ 3⁻ʲ (b-a)`.

## References

Plan A1+ §4 (L2) and §6.1.  The general statement behind `haar_eq_μD` is the standard
"Haar downstairs = Haar upstairs restricted to a fundamental domain" of [EW11, Ch. 8]; here it is
proved directly, at the concrete `S = {∞, 2, 3}` solenoid.
-/

namespace TH.S6

open Metric Set MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Pointwise ENNReal

/-! ### The ambient Haar measure on `G₆` -/

/-- The Haar measure of `G₆ = ℝ × ℚ₂ × ℚ₃`: Lebesgue measure times the two `p`-adic Haar
measures, each normalized so that `ℤ_[p]` has mass `1`.  With this normalization the fundamental
domain has mass `1` (`μ6_D`). -/
noncomputable def μ6 : Measure G6 :=
  (volume : Measure ℝ).prod ((Padic.haarMeasure 2).prod (Padic.haarMeasure 3))

instance instSFiniteμ6 : SFinite μ6 :=
  inferInstanceAs (SFinite ((volume : Measure ℝ).prod
    ((Padic.haarMeasure 2).prod (Padic.haarMeasure 3))))

instance instSigmaFiniteμ6 : SigmaFinite μ6 :=
  inferInstanceAs (SigmaFinite ((volume : Measure ℝ).prod
    ((Padic.haarMeasure 2).prod (Padic.haarMeasure 3))))

instance instIsAddLeftInvariantμ6 : μ6.IsAddLeftInvariant :=
  inferInstanceAs (((volume : Measure ℝ).prod
    ((Padic.haarMeasure 2).prod (Padic.haarMeasure 3))).IsAddLeftInvariant)

instance instIsAddRightInvariantμ6 : μ6.IsAddRightInvariant :=
  inferInstanceAs (((volume : Measure ℝ).prod
    ((Padic.haarMeasure 2).prod (Padic.haarMeasure 3))).IsAddRightInvariant)

/-- The measure of a box is the product of the three coordinate measures. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem μ6_prod (I : Set ℝ) (S : Set ℚ_[2]) (T : Set ℚ_[3]) :
    μ6 (I ×ˢ (S ×ˢ T)) = volume I * (Padic.haarMeasure 2 S * Padic.haarMeasure 3 T) := by
  rw [μ6, Measure.prod_prod, Measure.prod_prod]

/-- **The fundamental domain is a probability box.**  This is what fixes the normalization of
`μ6`, and hence makes the quotient measure a probability measure. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem μ6_D : μ6 D = 1 := by
  rw [D, μ6_prod, Real.volume_Ico, Padic.haarMeasure_closedBall_one,
    Padic.haarMeasure_closedBall_one]
  norm_num

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem measurableSet_D : MeasurableSet D :=
  measurableSet_Ico.prod (measurableSet_closedBall.prod measurableSet_closedBall)

/-- The lattice is countable: it is the image of the countable ring `ℤ[1/6] ⊆ ℚ`. -/
instance instCountableΔ₆ : Countable Δ₆ := by
  refine Function.Surjective.countable (f := fun q : Z16 => (⟨diag q, diag_mem_Δ₆ q.2⟩ : Δ₆)) ?_
  rintro ⟨g, hg⟩
  obtain ⟨q, hq, rfl⟩ := mem_Δ₆.mp hg
  exact ⟨⟨q, hq⟩, rfl⟩

/-- **`D` is a fundamental domain in Mathlib's sense.**  This is `exists_unique_fundamental` of
W1, transposed from "the representative in `D`" to "the lattice element that moves a point into
`D`". -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem isAddFundamentalDomain_D : IsAddFundamentalDomain Δ₆ D μ6 := by
  refine IsAddFundamentalDomain.mk' measurableSet_D.nullMeasurableSet ?_
  intro x
  obtain ⟨d, ⟨hdD, hd⟩, huniq⟩ := exists_unique_fundamental x
  refine ⟨⟨-(x - d), AddSubgroup.neg_mem _ hd⟩, ?_, ?_⟩
  · show -(x - d) + x ∈ D
    simpa using hdD
  · rintro ⟨γ, hγ⟩ hmem
    have hxD : γ + x ∈ D := hmem
    have hx : x - (γ + x) ∈ Δ₆ := by
      have hrw : x - (γ + x) = -γ := by abel
      rw [hrw]
      exact AddSubgroup.neg_mem _ hγ
    have huniq' := huniq (γ + x) ⟨hxD, hx⟩
    apply Subtype.ext
    show γ = -(x - d)
    rw [← huniq']
    abel

/-! ### The quotient measure and Haar measure on `Σ₆` -/

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem measurable_mk : Measurable (QuotientAddGroup.mk (s := Δ₆)) :=
  QuotientAddGroup.continuous_mk.measurable

/-- The measure of `Σ₆` obtained by reading `μ6` on the fundamental domain. -/
noncomputable def μD : Measure S6 := Measure.map (QuotientAddGroup.mk (s := Δ₆)) (μ6.restrict D)

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem μD_apply {A : Set S6} (hA : MeasurableSet A) :
    μD A = μ6 (QuotientAddGroup.mk ⁻¹' A ∩ D) := by
  rw [μD, Measure.map_apply measurable_mk hA, Measure.restrict_apply (measurable_mk hA)]

instance instIsProbabilityMeasureμD : IsProbabilityMeasure μD :=
  ⟨by rw [μD_apply MeasurableSet.univ, Set.preimage_univ, Set.univ_inter, μ6_D]⟩

/-- The preimage of any set under the projection is `Δ₆`-invariant. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem preimage_mk_vadd_invariant (A : Set S6) (γ : Δ₆) :
    (fun x => γ +ᵥ x) ⁻¹' (QuotientAddGroup.mk ⁻¹' A) = QuotientAddGroup.mk ⁻¹' A := by
  ext u
  have hmk : (QuotientAddGroup.mk ((γ : G6) + u) : S6) = QuotientAddGroup.mk u := by
    rw [QuotientAddGroup.eq]
    simp
  show (QuotientAddGroup.mk ((γ : G6) + u) : S6) ∈ A ↔ _
  rw [hmk]
  exact Iff.rfl

/-- **`μD` is translation-invariant.**  The proof does not move the set: it moves the fundamental
domain, and uses that a `Δ₆`-invariant set has the same `μ6`-mass in any fundamental domain
(`IsAddFundamentalDomain.measure_set_eq`). -/
instance instIsAddLeftInvariantμD : μD.IsAddLeftInvariant := by
  constructor
  intro x
  ext A hA
  rw [Measure.map_apply (measurable_const_add x) hA, μD_apply hA,
    μD_apply (measurable_const_add x hA)]
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  set S : Set G6 := QuotientAddGroup.mk ⁻¹' A with hS
  have hSmeas : MeasurableSet S := measurable_mk hA
  have hpre : QuotientAddGroup.mk ⁻¹' ((fun y => QuotientAddGroup.mk g + y) ⁻¹' A)
      = (fun u => g + u) ⁻¹' S := by
    ext u
    simp only [Set.mem_preimage, hS]
    show (QuotientAddGroup.mk g + QuotientAddGroup.mk u : S6) ∈ A ↔ _
    rw [← QuotientAddGroup.mk_add]
  rw [hpre]
  have hstep : (fun u => g + u) ⁻¹' S ∩ D = (fun u => g + u) ⁻¹' (S ∩ (g +ᵥ D)) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_vadd_set]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨u, h2, rfl⟩⟩
    · rintro ⟨h1, ⟨v, hv, hvu⟩⟩
      refine ⟨h1, ?_⟩
      have hvu' : v = u := by simpa using add_left_cancel hvu
      rwa [hvu'] at hv
  rw [hstep, measure_preimage_add μ6 g]
  exact (isAddFundamentalDomain_D.measure_set_eq (isAddFundamentalDomain_D.vadd_of_comm g)
    hSmeas (preimage_mk_vadd_invariant A)).symm

/-- **The normalized Haar probability measure of the solenoid.** -/
noncomputable def haar : Measure S6 := Measure.addHaarMeasure ⊤

noncomputable instance instIsAddHaarMeasureHaar : haar.IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure (⊤ : PositiveCompacts S6)).IsAddHaarMeasure)

/-- **The product form of Haar measure.**  Haar measure of `Σ₆` is the ambient
Lebesgue × Haar(`ℤ₂`) × Haar(`ℤ₃`) read on the fundamental domain — the identification of the
abstract Haar measure with a concrete product. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem haar_eq_μD : haar = μD :=
  (Measure.addHaarMeasure_eq_iff ⊤ μD).mpr (by show μD Set.univ = 1; simp)

instance instIsProbabilityMeasureHaar : IsProbabilityMeasure haar := by
  rw [haar_eq_μD]; infer_instance

/-- **The product form, in coordinates.**  For every Borel set of the solenoid, its Haar mass is
the `μ6`-mass of its representatives in `D = [0,1) × ℤ₂ × ℤ₃`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem haar_apply {A : Set S6} (hA : MeasurableSet A) :
    haar A = μ6 (QuotientAddGroup.mk ⁻¹' A ∩ D) := by
  rw [haar_eq_μD, μD_apply hA]

/-- The projection is measure-preserving from the fundamental domain onto the solenoid: the form
in which the product structure transports integrals (for W3/W4). -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem measurePreserving_mk :
    MeasurePreserving (QuotientAddGroup.mk (s := Δ₆)) (μ6.restrict D) haar :=
  ⟨measurable_mk, haar_eq_μD.symm⟩

/-! ### Invariance under the `ℤ²`-action -/

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem measurable_solAut {q : ℚ} (hq : IsZ16Unit q) : Measurable (solAut hq : S6 → S6) :=
  (solAut hq).continuous.measurable

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem map_solAut_univ {q : ℚ} (hq : IsZ16Unit q) :
    Measure.map (solAut hq) haar Set.univ = 1 := by
  rw [Measure.map_apply (measurable_solAut hq) MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- **Haar measure is invariant under every automorphism `solAut`.**  The pushforward is again a
Haar probability measure, and there is only one. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem map_solAut_haar {q : ℚ} (hq : IsZ16Unit q) : Measure.map (solAut hq) haar = haar := by
  haveI : IsProbabilityMeasure (Measure.map (solAut hq) haar) := ⟨map_solAut_univ hq⟩
  haveI : (Measure.map (solAut hq) haar).IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map haar (solAut hq)
  exact ((Measure.addHaarMeasure_eq_iff ⊤ (Measure.map (solAut hq) haar)).mpr
    (map_solAut_univ hq)).symm

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem measurePreserving_solAut {q : ℚ} (hq : IsZ16Unit q) :
    MeasurePreserving (solAut hq) haar haar :=
  ⟨measurable_solAut hq, map_solAut_haar hq⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem map_σ2_haar : Measure.map σ2 haar = haar := map_solAut_haar isZ16Unit_two

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem map_σ3_haar : Measure.map σ3 haar = haar := map_solAut_haar isZ16Unit_three

/-- **Haar measure is `T`-invariant**: `(Σ₆, haar, ×3/2)` is a measure-preserving system, the
object whose orbits are the sequences `(3/2)ⁿ ξ`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem map_T32_haar : Measure.map T32 haar = haar := map_solAut_haar isZ16Unit_threeHalves

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem measurePreserving_T32 : MeasurePreserving T32 haar haar :=
  measurePreserving_solAut isZ16Unit_threeHalves

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem measurePreserving_σ2 : MeasurePreserving σ2 haar haar :=
  measurePreserving_solAut isZ16Unit_two

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem measurable_T32 : Measurable (T32 : S6 → S6) := measurable_solAut isZ16Unit_threeHalves

@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem haar_preimage_T32 {A : Set S6} (hA : MeasurableSet A) : haar (T32 ⁻¹' A) = haar A := by
  conv_rhs => rw [← map_T32_haar]
  rw [Measure.map_apply measurable_T32 hA]

/-! ### Cells -/

/-- A subset of the fundamental domain is a set of unique representatives: no two of its points
are congruent, and no point of `D` outside it is congruent to one of its points. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem preimage_image_inter_D {R : Set G6} (hR : R ⊆ D) :
    (QuotientAddGroup.mk (s := Δ₆)) ⁻¹' ((QuotientAddGroup.mk (s := Δ₆)) '' R) ∩ D = R := by
  ext u
  constructor
  · rintro ⟨⟨r, hr, hru⟩, huD⟩
    have hsub : u - r ∈ Δ₆ := by
      have h := QuotientAddGroup.eq.mp hru
      rwa [neg_add_eq_sub] at h
    obtain ⟨d, _, huniq⟩ := exists_unique_fundamental u
    have h1 : u = d := huniq u ⟨huD, by simp⟩
    have h2 : r = d := huniq r ⟨hR hr, hsub⟩
    rwa [show u = r from h1.trans h2.symm]
  · intro hu
    exact ⟨⟨u, hu, rfl⟩, hR hu⟩

/-- **The mass of a box of representatives.**  For an *open* subset of the fundamental domain, the
Haar mass of its image in `Σ₆` is its ambient mass: no folding occurs. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem haar_mk_image_of_isOpen {R : Set G6} (hRD : R ⊆ D) (hR : IsOpen R) :
    haar (QuotientAddGroup.mk '' R) = μ6 R := by
  rw [haar_apply ((QuotientAddGroup.isOpenMap_coe (N := Δ₆) R hR).measurableSet),
    preimage_image_inter_D hRD]

/-- The level-`(k, j)` **cell** over the interval `(a, b)`: fractional part in `(a, b)`, `2`-adic
coordinate congruent to `c` mod `2ᵏ`, `3`-adic coordinate congruent to `d` mod `3ʲ`.  These are
the finite-level objects of `Z32/Dictionary.lean` (fractional part and floor residues), seen
inside `Σ₆`. -/
noncomputable def cell (a b : ℝ) (k : ℕ) (c : ℚ_[2]) (j : ℕ) (d : ℚ_[3]) : Set S6 :=
  QuotientAddGroup.mk '' (Ioo a b ×ˢ (Padic.residueBall 2 k c ×ˢ Padic.residueBall 3 j d))

/-- **The cell masses.**  A level-`(k, j)` cell over an interval of length `b - a` has Haar mass
`(b - a) · 2⁻ᵏ · 3⁻ʲ`: the fractional part and the two floor-residue coordinates are independent
and uniform.  This is the finite-level dictionary between Haar measure on `Σ₆` and the cell
counts of `Z32/Dictionary.lean`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem haar_cell {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (k : ℕ) {c : ℚ_[2]} (hc : ‖c‖ ≤ 1)
    (j : ℕ) {d : ℚ_[3]} (hd : ‖d‖ ≤ 1) :
    haar (cell a b k c j d)
      = ENNReal.ofReal (b - a) * (((2 : ℝ≥0∞) ^ k)⁻¹ * ((3 : ℝ≥0∞) ^ j)⁻¹) := by
  have hsub : (Ioo a b ×ˢ (Padic.residueBall 2 k c ×ˢ Padic.residueBall 3 j d)) ⊆ D := by
    rintro ⟨x, y, z⟩ ⟨hx, hy, hz⟩
    exact ⟨⟨ha.trans hx.1.le, hx.2.trans_le hb⟩,
      Padic.residueBall_subset_unitBall hc k hy, Padic.residueBall_subset_unitBall hd j hz⟩
  have hopen : IsOpen (Ioo a b ×ˢ (Padic.residueBall 2 k c ×ˢ Padic.residueBall 3 j d)) :=
    isOpen_Ioo.prod ((Padic.isOpen_residueBall k c).prod (Padic.isOpen_residueBall j d))
  rw [cell, haar_mk_image_of_isOpen hsub hopen, μ6_prod, Real.volume_Ioo,
    Padic.haarMeasure_residueBall, Padic.haarMeasure_residueBall]
  norm_num

/-- The pure `2`-adic cylinder: the floor residue mod `2ᵏ` is uniform, each value having Haar mass
`2⁻ᵏ`.  This is the input to the entropy bookkeeping of plan-A1+ L8 (the `σ₂`-joins of the
level-`1` partition are the level-`n` cells). -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem haar_cell_twoAdic (k : ℕ) {c : ℚ_[2]} (hc : ‖c‖ ≤ 1) :
    haar (cell 0 1 k c 0 0) = ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [haar_cell le_rfl le_rfl k hc 0 (by simp)]
  norm_num

/-- Cells are non-null: every level-`(k, j)` cell over a nondegenerate interval carries positive
Haar mass, so the partition into cells is a genuine partition. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_haar"]
theorem haar_cell_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) {c : ℚ_[2]}
    (hc : ‖c‖ ≤ 1) (j : ℕ) {d : ℚ_[3]} (hd : ‖d‖ ≤ 1) : 0 < haar (cell a b k c j d) := by
  rw [haar_cell ha hb k hc j hd]
  have h1 : (0 : ℝ≥0∞) < ENNReal.ofReal (b - a) := by
    simp only [ENNReal.ofReal_pos]
    linarith
  have h2 : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞) ^ k)⁻¹ := by simp [ENNReal.inv_pos]
  have h3 : (0 : ℝ≥0∞) < ((3 : ℝ≥0∞) ^ j)⁻¹ := by simp [ENNReal.inv_pos]
  exact ENNReal.mul_pos h1.ne' (ENNReal.mul_pos h2.ne' h3.ne').ne'

end TH.S6
