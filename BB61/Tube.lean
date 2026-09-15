/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.BoxDim
import BB61.FullSupport
import ForMathlib.Topology.Algebra.DenseCover
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.MetricSpace.Thickening
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M3 Proposition 1: the tube criterion is vacuous

`note-1061-M3.html` §3 audits the three moves of Route B of `plans/plan-1061.html`.  This file
formalises the third one, which the note kills outright:

> **Proposition 1 (the tube criterion is vacuous).**  Let `B ⊆ ℝ^{d-1}` have non-empty
> interior and put `T_B := {x ∈ ℝ^d : (x_2,…,x_d) ∈ B}`.  Then the image of `T_B` in `𝕋^d_Λ`
> is *all* of `𝕋^d_Λ`.  In particular `Haar(T_K) = 1` for every window `K`, in every degree,
> for every Pisot `α`.

The plan's Route B was to "kill `τ_*λ = Leb` whenever the tube `T_K := {(u,w) : w ∈ K_δ}`
is not all of `𝕋^d_Σ` in measure — a much weaker condition than Route A's", with the
B-criterion `Haar(T_K) < 1` read "morally" as `Leb_{d-1}(K)` small against the covolume of the
lattice.  Proposition 1 says that criterion has no instances.

## What is proved here

The tube is unrestricted in the first coordinate, so covering the torus by it is a question
about the *second* coordinate alone.  That is `tube_add_eq_univ_iff`, and it is pure algebra —
no topology, no discreteness of `Λ`, any degree:

`T_B + Λ = ℝ^d  ⟺  B + shadow Λ = ℝ^{d-1}`,   `shadow Λ := Prod.snd '' Λ`.

`image_mk_tube_eq_univ_iff` transports it to the torus through
`QuotientAddGroup.image_mk_eq_univ_iff`.  Proposition 1 is then the one-line
`image_mk_tube_eq_univ`: a set with non-empty interior plus a dense set is everything
(`add_dense_eq_univ`), so the whole content is the density of `shadow Λ`, which is where the
number theory sits.

At degree two `Λ = ι(ℤ[α]) = {(u + vα, u + vβ)}` (`lattice`) and `shadow Λ = ℤ + βℤ`
(`mem_shadow_lattice`).  Its density needs no duality and no irrationality lemma: `β ≠ 0`
(equivalently `b ≠ 0`, since `αβ = -b`) makes `β^n ∈ ℤ + βℤ` a sequence of non-zero elements
tending to `0`, so `0` is not isolated (`dense_shadow`).  `prop1` and `measure_prop1` are the
two forms of the conclusion, `prop1_thickening` is the note's "for every window `K`" — the
plan's tube is over the *fattened* window `K_δ`, which is open and non-empty for every
`δ > 0`, so nothing about `K` is needed at all.

`no_tube_criterion` is the audit verdict: no `B` with non-empty interior has a tube of measure
`< 1`.  `exists_tube_small_shadow` is the sharp form aimed at the plan's "morally
`Leb_{d-1}(K)/covolume`": for every `ε > 0` there is a tube whose shadow has Lebesgue measure
below `ε · covol` and whose image is still everything, so no bound on the size of the window
can ever produce a margin.

## The dichotomy at `δ = 0`

`tube_window_dichotomy` is what makes the vacuity sharp rather than accidental.  On the
family the plan expected to cover — quadratic Pisot `α` with `|β| < 1/2`, "in particular every
`X² - aX ± 1`, including the first genuinely hard case `α = 1 + √2`" — the *exact* window `K`
is a Cantor set of upper box dimension `log 2 / log|β|⁻¹ < 1`, hence Lebesgue-null
(`volume_windowSet_eq_zero`, on `BB61/BoxDim.lean`'s M1 Lemma 3), and a null `B` never covers
(`image_mk_tube_ne_univ_of_volume_zero`).  So

`δ > 0 ⟹ image of T_{K_δ} is everything`,  `image of T_K is not`.

The function `δ ↦ Haar(T_{K_δ})` is identically `1` on `δ > 0` and drops to `0` at `δ = 0`; it
takes no value in between, and no kernel can concentrate on a null set.  There is therefore no
`δ` at which a margin exists, which is the precise reason the plan's continuous-looking
quantity `Leb₁(K)/covol` is not the Haar measure of anything.

## What is not proved here

* **Degree `> 2` needs its density input.**  Everything before `namespace QuadSetup` is stated
  for an arbitrary lattice in `G × E`; only `Dense (shadow Λ)` is assumed.  At degree `d` that
  is the density of `{(σ₂(x),…,σ_d(x)) : x ∈ ℤ[α]}` in `ℝ^{d-1}`, which is true but is not
  formalised: the note gets it from Pontryagin duality on `𝕋^d_Λ`, which Mathlib does not
  have, and the contraction argument used here at `d = 2` gives only non-discreteness once
  `d - 1 > 1`.  The abstract statements are therefore the general-degree theorem *modulo* that
  one input.
* **No Haar measure on the torus is constructed.**  `measure_prop1` and `no_tube_criterion`
  are stated for an arbitrary probability measure on `(ℝ × ℝ) ⧸ Λ`, which is all the
  conclusion `= 1` needs, and the `δ = 0` half is stated as a set identity plus the
  one-dimensional Lebesgue statement `volume (K + shadow Λ) = 0`, not as a Haar measure.
* **`Ω ⊆ T_K` is not restated.**  That `λ = Φ_*μ` lives on the tube over the window is M1
  (`BB61/Confinement.lean`); Proposition 1 does not use it and neither does this file.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M3.html` §3, Proposition 1 and the paragraph after it; `plans/plan-1061.html`
  Route B, the B-criterion box.  Numerics `BB61/m3_prop1_lean.py`.
-/

noncomputable section

namespace BB61

open Set Pointwise Topology MeasureTheory

/-! ## The tube and its shadow -/

section Abstract

variable {G E : Type*}

/-- **The tube over `B`**: the points of `G × E` whose second coordinate lies in `B`, with the
first coordinate — the `τ̄` direction of the note — unrestricted.  At degree `d` this is the
note's `T_B = {x ∈ ℝ^d : (x_2,…,x_d) ∈ B}` with `G = ℝ` and `E = ℝ^{d-1}`. -/
def tube (G : Type*) {E : Type*} (B : Set E) : Set (G × E) := {p | p.2 ∈ B}

@[simp]
theorem mem_tube {B : Set E} {p : G × E} : p ∈ tube G B ↔ p.2 ∈ B := Iff.rfl

variable [AddCommGroup G] [AddCommGroup E]

/-- **The shadow of the lattice**: its image under the second projection.  At degree `d` this
is `{(σ₂(x),…,σ_d(x)) : x ∈ ℤ[α]}`, the conjugate coordinates of `Λ` alone. -/
def shadow (Λ : AddSubgroup (G × E)) : AddSubgroup E := Λ.map (AddMonoidHom.snd G E)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_shadow {Λ : AddSubgroup (G × E)} {x : E} :
    x ∈ shadow Λ ↔ ∃ g ∈ Λ, g.2 = x := by
  simp [shadow, AddSubgroup.mem_map]

/-- **The tube criterion is one-dimensional.**  A tube covers `ℝ^d` modulo `Λ` exactly when
its base covers the conjugate space modulo the shadow of `Λ`: the first coordinate is free, so
it can always absorb the first coordinate of the lattice vector one needs.

This is pure algebra.  No topology, no discreteness of `Λ`, and no restriction on the degree
enter; in particular the covering property of a tube has nothing to do with the *size* of `B`
relative to the covolume. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tube_add_eq_univ_iff (Λ : AddSubgroup (G × E)) (B : Set E) :
    tube G B + (Λ : Set (G × E)) = Set.univ ↔ B + (shadow Λ : Set E) = Set.univ := by
  constructor
  · intro h
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨u, hu, g, hg, hsum⟩ := Set.mem_add.mp (h ▸ Set.mem_univ ((0 : G), x))
    refine Set.mem_add.mpr ⟨u.2, hu, g.2, mem_shadow.mpr ⟨g, hg, rfl⟩, ?_⟩
    have := congrArg Prod.snd hsum
    simpa using this
  · intro h
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨b, hb, y, hy, hsum⟩ := Set.mem_add.mp (h ▸ Set.mem_univ z.2)
    obtain ⟨g, hg, hg2⟩ := mem_shadow.mp hy
    refine Set.mem_add.mpr ⟨z - g, ?_, g, hg, by abel⟩
    show (z - g).2 ∈ B
    have hz2 : (z - g).2 = b := by
      show z.2 - g.2 = b
      rw [← hsum, hg2]; abel
    rw [hz2]; exact hb

/-- The same criterion in the torus `𝕋^d_Λ = ℝ^d / Λ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem image_mk_tube_eq_univ_iff (Λ : AddSubgroup (G × E)) (B : Set E) :
    (QuotientAddGroup.mk '' tube G B : Set ((G × E) ⧸ Λ)) = Set.univ
      ↔ B + (shadow Λ : Set E) = Set.univ :=
  (QuotientAddGroup.image_mk_eq_univ_iff Λ (tube G B)).trans (tube_add_eq_univ_iff Λ B)

variable [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- **M3 Proposition 1**, in any degree, modulo the density of the shadow: if the conjugate
coordinates of the lattice are dense, then the image of `T_B` in `𝕋^d_Λ` is all of `𝕋^d_Λ`
whenever `B` has non-empty interior. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem image_mk_tube_eq_univ (Λ : AddSubgroup (G × E)) (hΛ : Dense (shadow Λ : Set E))
    {B : Set E} (hB : (interior B).Nonempty) :
    (QuotientAddGroup.mk '' tube G B : Set ((G × E) ⧸ Λ)) = Set.univ :=
  (image_mk_tube_eq_univ_iff Λ B).mpr (add_dense_eq_univ hB hΛ)

/-- **`Haar(T_B) = 1`.**  Stated for an arbitrary probability measure on the torus, which is
all the conclusion needs: the set is everything, so no Haar measure has to be built. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measure_image_mk_tube {Λ : AddSubgroup (G × E)} (hΛ : Dense (shadow Λ : Set E))
    {B : Set E} (hB : (interior B).Nonempty) [MeasurableSpace ((G × E) ⧸ Λ)]
    (ν : Measure ((G × E) ⧸ Λ)) [IsProbabilityMeasure ν] :
    ν (QuotientAddGroup.mk '' tube G B) = 1 := by
  rw [image_mk_tube_eq_univ Λ hΛ hB, measure_univ]

end Abstract

/-! ## The lattice `ι(ℤ[α]) ⊂ ℝ²` and its shadow `ℤ + βℤ` -/

namespace QuadSetup

variable (P : QuadSetup)

/-- The Minkowski embedding at degree two, on coordinates: `(u, v) ↦ (u + vα, u + vβ)`. -/
def emb : (ℤ × ℤ) →+ (ℝ × ℝ) where
  toFun z := (((z.1 : ℝ) + (z.2 : ℝ) * P.α), ((z.1 : ℝ) + (z.2 : ℝ) * P.β))
  map_zero' := by simp
  map_add' := by
    intro x y
    have h1 : ((x + y).1 : ℤ) = x.1 + y.1 := rfl
    have h2 : ((x + y).2 : ℤ) = x.2 + y.2 := rfl
    simp only [h1, h2, Prod.mk_add_mk, Prod.ext_iff]
    constructor <;> (push_cast; ring)

/-- **The lattice `Λ = ι(ℤ[α]) ⊂ ℝ²`.**  Discreteness is never used: only the density of its
shadow matters for Proposition 1. -/
def lattice : AddSubgroup (ℝ × ℝ) := P.emb.range

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_lattice {p : ℝ × ℝ} :
    p ∈ P.lattice ↔ ∃ u v : ℤ, p = ((u : ℝ) + v * P.α, (u : ℝ) + v * P.β) := by
  simp only [lattice, AddMonoidHom.mem_range, emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z.1, z.2, hz.symm⟩
  · rintro ⟨u, v, hp⟩; exact ⟨(u, v), hp.symm⟩

/-- **The shadow is `ℤ[β] = ℤ + βℤ`.** -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_shadow_lattice {x : ℝ} :
    x ∈ shadow P.lattice ↔ ∃ u v : ℤ, x = (u : ℝ) + v * P.β := by
  rw [mem_shadow]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨u, v, rfl⟩ := P.mem_lattice.mp hg
    exact ⟨u, v, rfl⟩
  · rintro ⟨u, v, rfl⟩
    exact ⟨((u : ℝ) + v * P.α, (u : ℝ) + v * P.β), P.mem_lattice.mpr ⟨u, v, rfl⟩, rfl⟩

/-- `αβ = -b`: the norm of the quadratic, read off `α² = aα + b` and `β = a - α`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_mul_beta : P.α * P.β = -(P.b : ℝ) := by
  have h := P.root
  unfold β
  linear_combination -h

/-- The conjugate vanishes exactly in the degenerate integer case `b = 0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_ne_zero_of_b (hb : P.b ≠ 0) : P.β ≠ 0 := by
  intro h
  have hab := P.alpha_mul_beta
  rw [h, mul_zero] at hab
  exact hb (by exact_mod_cast (neg_eq_zero.mp hab.symm))

/-- `βⁿ ∈ ℤ + βℤ`, by `β² = aβ + b`.  This is the whole arithmetic input to the density of
the shadow. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_pow_mem_shadow (n : ℕ) : P.β ^ n ∈ shadow P.lattice := by
  induction n with
  | zero => exact P.mem_shadow_lattice.mpr ⟨1, 0, by norm_num⟩
  | succ n ih =>
      obtain ⟨u, v, huv⟩ := P.mem_shadow_lattice.mp ih
      refine P.mem_shadow_lattice.mpr ⟨v * P.b, u + v * P.a, ?_⟩
      have hr := P.beta_root
      rw [pow_succ, huv]
      push_cast
      linear_combination (v : ℝ) * hr

/-- **The shadow is dense.**  `0` is not isolated in `ℤ + βℤ`: the powers `βⁿ` lie in it, are
non-zero because `b ≠ 0`, and tend to `0` because `|β| < 1`.

This replaces the note's Pontryagin-duality argument (that a character is trivial on the image
of the line `ℝ × {0}` only if it is trivial), which is not available in Mathlib.  At degree two
the contraction does the whole job; at higher degree it gives only non-discreteness. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dense_shadow (hb : P.b ≠ 0) : Dense ((shadow P.lattice : AddSubgroup ℝ) : Set ℝ) := by
  refine AddSubgroup.dense_of_not_isolated_zero _ fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε P.abs_beta_lt_one
  refine ⟨|P.β ^ n|, ?_, ?_, ?_⟩
  · rcases abs_choice (P.β ^ n) with h | h
    · rw [h]; exact P.beta_pow_mem_shadow n
    · rw [h]; exact neg_mem (P.beta_pow_mem_shadow n)
  · exact abs_pos.mpr (pow_ne_zero _ (P.beta_ne_zero_of_b hb))
  · rw [abs_pow]; exact hn

/-! ## Proposition 1 at degree two -/

/-- **M3 Proposition 1.**  The image of the tube `T_B` in `𝕋²_Λ` is all of `𝕋²_Λ`, for every
`B ⊆ ℝ` with non-empty interior. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem prop1 (hb : P.b ≠ 0) {B : Set ℝ} (hB : (interior B).Nonempty) :
    (QuotientAddGroup.mk '' tube ℝ B : Set ((ℝ × ℝ) ⧸ P.lattice)) = Set.univ :=
  image_mk_tube_eq_univ P.lattice (P.dense_shadow hb) hB

/-- **`Haar(T_B) = 1`** at degree two. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measure_prop1 (hb : P.b ≠ 0) {B : Set ℝ} (hB : (interior B).Nonempty)
    [MeasurableSpace ((ℝ × ℝ) ⧸ P.lattice)] (ν : Measure ((ℝ × ℝ) ⧸ P.lattice))
    [IsProbabilityMeasure ν] :
    ν (QuotientAddGroup.mk '' tube ℝ B) = 1 := by
  rw [P.prop1 hb hB, measure_univ]

/-- **"for every window `K`".**  The plan's tube is over the fattened window `K_δ`, and a
thickening is open and non-empty for every `δ > 0`, so no property of `K` beyond
non-emptiness is used. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem prop1_thickening (hb : P.b ≠ 0) {K : Set ℝ} (hK : K.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    (QuotientAddGroup.mk '' tube ℝ (Metric.thickening δ K) : Set ((ℝ × ℝ) ⧸ P.lattice))
      = Set.univ := by
  refine P.prop1 hb ?_
  rw [Metric.isOpen_thickening.interior_eq]
  exact hK.mono (Metric.self_subset_thickening hδ K)

/-- **Move 3's criterion has no instances.**  There is no `B` with non-empty interior whose
tube has measure `< 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem no_tube_criterion (hb : P.b ≠ 0) [MeasurableSpace ((ℝ × ℝ) ⧸ P.lattice)]
    (ν : Measure ((ℝ × ℝ) ⧸ P.lattice)) [IsProbabilityMeasure ν] :
    ¬ ∃ B : Set ℝ, (interior B).Nonempty ∧
        ν (QuotientAddGroup.mk '' tube ℝ B) < 1 := by
  rintro ⟨B, hB, hlt⟩
  rw [P.measure_prop1 hb hB ν] at hlt
  exact lt_irrefl _ hlt

/-! ## The covolume, and why no bound on the window can help -/

/-- The covolume of `Λ = ι(ℤ[α])` in `ℝ²`: `|det [[1, α], [1, β]]| = |α - β|`. -/
def covol : ℝ := |P.α - P.β|

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem covol_pos : 0 < P.covol := by
  have h1 : P.β ≤ |P.β| := le_abs_self _
  have h2 : |P.β| < 1 := P.abs_beta_lt_one
  have h3 : (1 : ℝ) < P.α := P.one_lt
  have hpos : 0 < P.α - P.β := by linarith
  rw [covol, abs_of_pos hpos]
  exact hpos

/-- `covol² = a² + 4b`, the discriminant of `X² - aX - b`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem covol_sq : P.covol ^ 2 = (P.a : ℝ) ^ 2 + 4 * P.b := by
  rw [covol, sq_abs]
  have h1 := P.alpha_add_beta
  have h2 := P.alpha_mul_beta
  linear_combination (P.α + P.β + (P.a : ℝ)) * h1 - 4 * h2

/-- **The B-criterion cannot be met, quantitatively.**  For every `ε > 0` there is a tube
whose base has Lebesgue measure below `ε · covol` — the plan's "morally `Leb₁(K)` small
relative to the covolume of `Σ`", as small as one likes — and whose image is still all of the
torus.  No inequality between the size of the window and the covolume can produce a margin. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_tube_small_shadow (hb : P.b ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set ℝ, volume B < ENNReal.ofReal (ε * P.covol) ∧
      (QuotientAddGroup.mk '' tube ℝ B : Set ((ℝ × ℝ) ⧸ P.lattice)) = Set.univ := by
  have hc := P.covol_pos
  set r : ℝ := ε * P.covol / 4 with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  refine ⟨Set.Ioo (-r) r, ?_, P.prop1 hb ?_⟩
  · rw [Real.volume_Ioo, show r - -r = 2 * r by ring]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_
    rw [hr]; linarith
  · rw [isOpen_Ioo.interior_eq]
    exact ⟨0, by constructor <;> linarith⟩

/-! ## The `δ = 0` end: a null base never covers -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem countable_shadow : ((shadow P.lattice : AddSubgroup ℝ) : Set ℝ).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range fun z : ℤ × ℤ => (z.1 : ℝ) + z.2 * P.β)
  rintro x hx
  obtain ⟨u, v, rfl⟩ := P.mem_shadow_lattice.mp hx
  exact ⟨(u, v), rfl⟩

/-- A Lebesgue-null base stays null after adding the countable shadow. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem volume_add_shadow {B : Set ℝ} (hB : volume B = 0) :
    volume (B + ((shadow P.lattice : AddSubgroup ℝ) : Set ℝ)) = 0 := by
  rw [← Set.iUnion_add_right_image]
  refine (measure_biUnion_null_iff P.countable_shadow).mpr fun y _ => ?_
  rw [Set.image_add_right, measure_preimage_add_right]
  exact hB

/-- **Non-empty interior cannot be dropped.**  A tube over a Lebesgue-null base misses a
positive-measure set of the torus; its one-dimensional trace `B + (ℤ + βℤ)` is null. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem image_mk_tube_ne_univ_of_volume_zero {B : Set ℝ} (hB : volume B = 0) :
    (QuotientAddGroup.mk '' tube ℝ B : Set ((ℝ × ℝ) ⧸ P.lattice)) ≠ Set.univ := by
  intro h
  have hcov := (image_mk_tube_eq_univ_iff P.lattice B).mp h
  have h0 := P.volume_add_shadow hB
  rw [hcov] at h0
  simp at h0

/-- **The window is null on Route B's target family.**  `|β| < 1/2` makes M1 Lemma 3's ceiling
`dim_B K ≤ log 2 / log|β|⁻¹` smaller than `1`, and a subset of `ℝ` of upper box dimension
below `1` is Lebesgue-null. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem volume_windowSet_eq_zero (hβ : P.β ≠ 0) (h : |P.β| < 1 / 2) :
    volume P.windowSet = 0 := by
  refine Real.volume_eq_zero_of_upperBoxDim_lt_one
    (lt_of_le_of_lt (P.upperBoxDim_windowSet_le hβ) ?_)
  have hpos : 0 < |P.β| := abs_pos.mpr hβ
  have hlb : Real.log |P.β| < Real.log (1 / 2) := Real.log_lt_log hpos h
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : Real.log |P.β|⁻¹ = -Real.log |P.β| := Real.log_inv _
  have hden : Real.log 2 < Real.log |P.β|⁻¹ := by rw [hinv]; rw [hhalf] at hlb; linarith
  have hfrac : Real.log 2 / Real.log |P.β|⁻¹ < 1 :=
    (div_lt_one (by linarith)).mpr hden
  exact_mod_cast hfrac

/-- **The dichotomy at `δ = 0`.**  On the plan's expected-coverage family `|β| < 1/2`: every
fattened window gives a tube that is all of the torus, and the exact window gives one that is
not.  `δ ↦ Haar(T_{K_δ})` is `1` for every `δ > 0` and `0` at `δ = 0`, with nothing in
between, so there is no `δ` at which Route B's move 3 has a margin. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tube_window_dichotomy (hb : P.b ≠ 0) (h : |P.β| < 1 / 2) :
    (∀ δ : ℝ, 0 < δ →
        (QuotientAddGroup.mk '' tube ℝ (Metric.thickening δ P.windowSet)
          : Set ((ℝ × ℝ) ⧸ P.lattice)) = Set.univ)
      ∧ (QuotientAddGroup.mk '' tube ℝ P.windowSet
          : Set ((ℝ × ℝ) ⧸ P.lattice)) ≠ Set.univ := by
  have hK : P.windowSet.Nonempty := ⟨_, ⟨fun _ => false, rfl⟩⟩
  refine ⟨fun δ hδ => P.prop1_thickening hb hK hδ, ?_⟩
  exact P.image_mk_tube_ne_univ_of_volume_zero
    (P.volume_windowSet_eq_zero (P.beta_ne_zero_of_b hb) h)

/-! ## The note's own mechanism: the image of the line is dense -/

/-- **The image of `ℝ × {0}` in `𝕋²_Λ` is dense** — the note's `L`, and the step it proves by
Pontryagin duality.  The main proof above does not route through it: the tube already contains
a whole line through each of its points, so the covering question collapses to the shadow
directly. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dense_image_mk_line (hb : P.b ≠ 0) :
    Dense (QuotientAddGroup.mk '' tube ℝ ({0} : Set ℝ) : Set ((ℝ × ℝ) ⧸ P.lattice)) := by
  have hsub :
      (QuotientAddGroup.mk ''
          (Set.univ ×ˢ ((shadow P.lattice : AddSubgroup ℝ) : Set ℝ))
            : Set ((ℝ × ℝ) ⧸ P.lattice))
        ⊆ QuotientAddGroup.mk '' tube ℝ ({0} : Set ℝ) := by
    rintro _ ⟨p, ⟨-, hp2⟩, rfl⟩
    obtain ⟨g, hg, hg2⟩ := mem_shadow.mp hp2
    refine ⟨p - g, ?_, ?_⟩
    · show (p - g).2 ∈ ({0} : Set ℝ)
      show p.2 - g.2 ∈ ({0} : Set ℝ)
      rw [hg2]
      simp
    · exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using neg_mem hg)
  refine Dense.mono hsub ?_
  exact (Function.Surjective.denseRange Quot.mk_surjective).dense_image continuous_quot_mk
    (dense_univ.prod (P.dense_shadow hb))

end QuadSetup

/-! ## The two `α` where M4 is blind -/

private theorem sqrt2_lt_three_halves : Real.sqrt 2 < 3 / 2 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private theorem two_lt_sqrt5 : (2 : ℝ) < Real.sqrt 5 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- At `α = 1 + √2`: `|β| = √2 - 1 < 1/2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_abs_beta_lt_half : |silver.β| < 1 / 2 := by
  rw [silver_beta, abs_neg, abs_of_pos (by have := silver_rho_pos; linarith)]
  have := sqrt2_lt_three_halves
  linarith

/-- **Route B is vacuous at `α = 1 + √2`**, the plan's "first genuinely hard case": every
fattened window covers the torus, the exact window does not. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_tube_window_dichotomy :
    (∀ δ : ℝ, 0 < δ →
        (QuotientAddGroup.mk '' tube ℝ (Metric.thickening δ silver.windowSet)
          : Set ((ℝ × ℝ) ⧸ silver.lattice)) = Set.univ)
      ∧ (QuotientAddGroup.mk '' tube ℝ silver.windowSet
          : Set ((ℝ × ℝ) ⧸ silver.lattice)) ≠ Set.univ :=
  silver.tube_window_dichotomy (by norm_num [silver]) silver_abs_beta_lt_half

/-- At `α = (3 + √5)/2`: `|β| = (3 - √5)/2 < 1/2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_abs_beta_lt_half : |goldenSq.β| < 1 / 2 := by
  rw [abs_of_pos goldenSq_beta_pos, goldenSq_beta]
  have := two_lt_sqrt5
  linarith

/-- **Route B is vacuous at `α = (3 + √5)/2`** as well. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_tube_window_dichotomy :
    (∀ δ : ℝ, 0 < δ →
        (QuotientAddGroup.mk '' tube ℝ (Metric.thickening δ goldenSq.windowSet)
          : Set ((ℝ × ℝ) ⧸ goldenSq.lattice)) = Set.univ)
      ∧ (QuotientAddGroup.mk '' tube ℝ goldenSq.windowSet
          : Set ((ℝ × ℝ) ⧸ goldenSq.lattice)) ≠ Set.univ :=
  goldenSq.tube_window_dichotomy (by norm_num [goldenSq]) goldenSq_abs_beta_lt_half

end BB61
