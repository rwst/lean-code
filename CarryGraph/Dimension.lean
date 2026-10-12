/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Cover
import ForMathlib.Topology.MetricSpace.BoxDimension

/-!
# Dimension bounds from covers ([Fal03] ch. 3)

Let a finite carry graph `X` cover a system `(S, f, adm)` on a pseudo-emetric space through `ρ`,
and let `K` be a set of points that are admissible for arbitrarily many steps.  Suppose the
itinerary localises: two points of `K` in one `ρ v` that follow the same word of length `n` are
within `c · rⁿ` of each other (`r < 1`).  Then `K` is covered by one ball of radius `c · rⁿ` per
word of length `n`, so by `ntot n` balls, and

  `dim_B K ≤ entropy X / log r⁻¹`,   `dim_H K ≤ entropy X / log r⁻¹`

(`Cover.upperBoxDim_le`, `Cover.dimH_le`).  For a piecewise expanding system with expansion
`λ = r⁻¹` this is the classical "dimension ≤ entropy / log λ" ([Fal03] §3.2 for the counting).
The localisation hypothesis follows from expansion along the run (`edist_le_of_follows`) and a
bound on the distance of the run endpoints (`Cover.upperBoxDim_le_of_expanding`).

This is the generic form of `DubC2.Gen.upperBoxDim_avoiders_le`; the affine instance is in
`CarryGraph/Affine.lean` (`affine_dimH_le`).

## References

* [Fal03] K. Falconer, *Fractal Geometry*, 2nd ed., Wiley, 2003.
-/

open Filter ENNReal ExpGrowth Metric
open scoped NNReal

namespace CarryGraph

variable {V S A : Type*} {X : CarryGraph V A} {f : A → S → S} {adm : S → A → Prop}
  {ρ : V → Set S}

section metric

variable [PseudoEMetricSpace S]

/-- **Expansion along a run**: if each admissible step expands distances by at least `r⁻¹`,
two points following the same word of length `n` are `rⁿ`-close to their run endpoints'
distance. -/
@[category API, AMS 37 28, ref "Fal03", group "carry_dimension"]
theorem edist_le_of_follows {r : ℝ≥0∞}
    (hexp : ∀ a x y, adm x a → adm y a → edist x y ≤ r * edist (f a x) (f a y)) :
    ∀ {x y : S} {w : List A}, Follows f adm x w → Follows f adm y w →
      edist x y ≤ r ^ w.length * edist (run f x w) (run f y w)
  | x, y, [], _, _ => by simp [run]
  | x, y, a :: w, ⟨hx, hxw⟩, ⟨hy, hyw⟩ => by
    calc edist x y ≤ r * edist (f a x) (f a y) := hexp a x y hx hy
      _ ≤ r * (r ^ w.length * edist (run f (f a x) w) (run f (f a y) w)) :=
          mul_le_mul_right (edist_le_of_follows hexp hxw hyw) r
      _ = r ^ (a :: w).length * edist (run f x (a :: w)) (run f y (a :: w)) := by
          simp only [List.length_cons, run, pow_succ]; ring

variable [Fintype V] [Fintype A] [DecidableEq A]

/-- One centre per itinerary: the covering number at scale `c · rⁿ` is at most `ntot n`. -/
@[category textbook, AMS 37 28, ref "Fal03", group "carry_dimension"]
theorem Cover.externalCoveringNumber_le (h : Cover X f adm ρ) {K : Set S}
    (hK : ∀ x ∈ K, (∃ v, x ∈ ρ v) ∧ ∀ n, ∃ w : List A, w.length = n ∧ Follows f adm x w)
    {ε : ℝ≥0} {n : ℕ}
    (hloc : ∀ v (w : List A) x y, x ∈ K → y ∈ K → x ∈ ρ v → y ∈ ρ v → w.length = n →
      Follows f adm x w → Follows f adm y w → edist x y ≤ ε) :
    externalCoveringNumber ε K ≤ X.ntot n := by
  classical
  let D : Finset (V × List A) := Finset.univ.biUnion fun v => (X.words v n).image fun w => (v, w)
  let P : V × List A → Prop := fun d => ∃ x ∈ K, x ∈ ρ d.1 ∧ Follows f adm x d.2
  let E := D.filter P
  let ctr : E → S := fun d => Classical.choose (Finset.mem_filter.1 d.2).2
  have hctr : ∀ d : E, ctr d ∈ K ∧ ctr d ∈ ρ d.1.1 ∧ Follows f adm (ctr d) d.1.2 := fun d =>
    Classical.choose_spec (Finset.mem_filter.1 d.2).2
  let T : Finset S := E.attach.image ctr
  have hcov : IsCover ε K (T : Set S) := by
    intro x hx
    obtain ⟨⟨v, hv⟩, hw⟩ := hK x hx
    obtain ⟨w, hl, hf⟩ := hw n
    have hD : (v, w) ∈ D := Finset.mem_biUnion.2
      ⟨v, Finset.mem_univ _, Finset.mem_image.2 ⟨w, mem_words.2 ⟨hl, h.isWord hv hf⟩, rfl⟩⟩
    have hE : (v, w) ∈ E := Finset.mem_filter.2 ⟨hD, x, hx, hv, hf⟩
    obtain ⟨hyK, hyv, hyf⟩ := hctr ⟨(v, w), hE⟩
    exact ⟨ctr ⟨(v, w), hE⟩, Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, Finset.mem_attach _ _, rfl⟩),
      hloc v w x _ hx hyK hv hyv hl hf hyf⟩
  have hT : T.card ≤ X.ntot n :=
    calc T.card ≤ E.attach.card := Finset.card_image_le
      _ = E.card := Finset.card_attach
      _ ≤ D.card := Finset.card_filter_le _ _
      _ ≤ ∑ v, ((X.words v n).image fun w => (v, w)).card := Finset.card_biUnion_le
      _ ≤ ∑ v, X.npaths v n := Finset.sum_le_sum fun v _ =>
          Finset.card_image_le.trans (card_words_le_npaths v n)
  refine hcov.externalCoveringNumber_le_encard.trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast hT

/-- **Box dimension ≤ entropy / log r⁻¹.** -/
@[category textbook, AMS 37 28, ref "Fal03", group "carry_dimension"]
theorem Cover.upperBoxDim_le (h : Cover X f adm ρ) {K : Set S}
    (hK : ∀ x ∈ K, (∃ v, x ∈ ρ v) ∧ ∀ n, ∃ w : List A, w.length = n ∧ Follows f adm x w)
    {r c : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c)
    (hloc : ∀ v (w : List A) x y, x ∈ K → y ∈ K → x ∈ ρ v → y ∈ ρ v →
      Follows f adm x w → Follows f adm y w → edist x y ≤ c * r ^ w.length) :
    upperBoxDim K ≤ X.entropy / ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
  have hN : ∀ n, (externalCoveringNumber (c * r ^ n) K : ℝ≥0∞) ≤ (X.ntot n : ℝ≥0∞) := fun n => by
    have := h.externalCoveringNumber_le hK (ε := c * r ^ n) (n := n)
      fun v w x y hx hy hxv hyv hl hxf hyf => by
        have := hloc v w x y hx hy hxv hyv hxf hyf
        rw [hl] at this
        exact_mod_cast this
    exact_mod_cast ENat.toENNReal_mono this
  have hG : coveringGrowth r K ≤ X.entropy := by
    rw [← coveringGrowth_const_mul hr1 hc K]
    exact expGrowthSup_monotone hN
  have hlog : (0 : EReal) ≤ ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
    have h0 : (0 : ℝ) < r := hr0
    have h1 : (r : ℝ) < 1 := hr1
    exact_mod_cast (Real.log_pos (one_lt_inv_iff₀.2 ⟨h0, h1⟩)).le
  rw [upperBoxDim_eq_upperBoxDimWith hr0 hr1]
  exact EReal.div_le_div_right_of_nonneg hlog hG

/-- **Box dimension for an expanding system**: every admissible step expands by `r⁻¹`, and
the run endpoints of two points of `K` in one `ρ v` that follow the same word are `c`-close. -/
@[category textbook, AMS 37 28, ref "Fal03", group "carry_dimension"]
theorem Cover.upperBoxDim_le_of_expanding (h : Cover X f adm ρ) {K : Set S}
    (hK : ∀ x ∈ K, (∃ v, x ∈ ρ v) ∧ ∀ n, ∃ w : List A, w.length = n ∧ Follows f adm x w)
    {r c : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c)
    (hexp : ∀ a x y, adm x a → adm y a → edist x y ≤ r * edist (f a x) (f a y))
    (hend : ∀ v (w : List A) x y, x ∈ K → y ∈ K → x ∈ ρ v → y ∈ ρ v →
      Follows f adm x w → Follows f adm y w → edist (run f x w) (run f y w) ≤ c) :
    upperBoxDim K ≤ X.entropy / ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
  refine h.upperBoxDim_le hK hr0 hr1 hc fun v w x y hx hy hxv hyv hxf hyf => ?_
  calc edist x y ≤ (r : ℝ≥0∞) ^ w.length * edist (run f x w) (run f y w) :=
        edist_le_of_follows hexp hxf hyf
    _ ≤ (r : ℝ≥0∞) ^ w.length * c := mul_le_mul_right (hend v w x y hx hy hxv hyv hxf hyf) _
    _ = ((c * r ^ w.length : ℝ≥0) : ℝ≥0∞) := by push_cast; ring

end metric

/-- **Hausdorff dimension ≤ entropy / log r⁻¹.** -/
@[category textbook, AMS 37 28, ref "Fal03", group "carry_dimension"]
theorem Cover.dimH_le [EMetricSpace S] [MeasurableSpace S] [BorelSpace S] [Fintype V]
    [Fintype A] [DecidableEq A] (h : Cover X f adm ρ) {K : Set S} (hne : K.Nonempty)
    (hK : ∀ x ∈ K, (∃ v, x ∈ ρ v) ∧ ∀ n, ∃ w : List A, w.length = n ∧ Follows f adm x w)
    {r c : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c)
    (hloc : ∀ v (w : List A) x y, x ∈ K → y ∈ K → x ∈ ρ v → y ∈ ρ v →
      Follows f adm x w → Follows f adm y w → edist x y ≤ c * r ^ w.length) :
    (dimH K : EReal) ≤ X.entropy / ((Real.log (r : ℝ)⁻¹ : ℝ) : EReal) := by
  exact (dimH_le_upperBoxDim hne).trans (h.upperBoxDim_le hK hr0 hr1 hc hloc)

end CarryGraph
