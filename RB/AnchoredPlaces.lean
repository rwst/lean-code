/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.AnchoredHeight
import ForMathlib.NumberTheory.FinitePlaceProduct
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Place values of the anchored `S`-unit data over `ℚ(δ)` (report B1E2a-v2, WP-G bill item 1)

`RB/Anchored.lean` instantiates the Subspace Theorem at `K = ℚ⟮δ⟯` with the place set
`RB.anchoredPlaces δ` (all infinite places, plus the finite places dividing `6`), and
`RB/AnchoredHeight.lean` computes the height of the data.  What is still missing before the
`n = 3` machine can be run on the anchored family is the **left-hand side**: the value of
`Subspace.approxProduct` at the triple `x = (m, (3/2)^d, 1)`, i.e. the values of the places of
`ℚ(δ)` on the `S`-units `2^x3^y` — the first item of the WP-G gate bill.  This file supplies
them, and assembles them into a closed formula for `approxProduct`.

## The `S`-unit place values

The finite places are handled *without ramification theory*.  A finite place `w` of `K` outside
`S` satisfies `w 6 = 1`, hence `w 2 = w 3 = 1` (both are `≤ 1` and multiply to `1`), hence
`w (2^a3^b) = 1`: the `S`-units are invisible outside `S`.  The product formula then evaluates
the whole finite contribution in one stroke
(`ForMathlib/NumberTheory/FinitePlaceProduct.lean`):

  `∏_{w ∈ S_fin} w (q) = (|q|^{[K:ℚ]})⁻¹`   for every rational `S`-unit `q`,

and over the *full* place set `S` the two halves combine to

  `∏_{w ∈ S} w (q) = |q|^{#InfinitePlace K} · |q|^{-[K:ℚ]} = (|q|^{r₂})⁻¹`

(`RB.prod_anchoredPlaces_sUnit`, `RB.prod_anchoredPlaces_sUnit_eq`) — the excess of the degree
over the number of infinite places is exactly the number `r₂` of complex places, so for a totally
real `ℚ(δ)` the `S`-unit product over `S` is `1`.

## The approximation product of the anchored triple

`Subspace.approxProduct` is invariant under scaling (`RB.approxProduct_smul`, proved here), so the
computation may be done on the *primitive* representative `X = (m·2^d, 3^d, 2^d)` of
`RB.anchoredTriple`, where the local norms are as simple as possible: `1` at every finite place
(coprimality) and `M = max(|m|·2^d, 3^d)` at every infinite place.  Writing

  `Λ = δ(3/2)^b((3/2)^d − 1) − m`   (`RB.anchoredDefect`, the quantity `RB.InhomOnePower` bounds)

the three groups of places contribute
`|Λ|·12^d / M³` at the distinguished real place, `|m|·12^d / M³` at each of the other
`n_∞ − 1` infinite places, and `∏_{w ∈ S_fin} w(m) · 12^{-dD}` at the finite ones, giving

  **`approxProduct = (|Λ|·12^d/M³) · (|m|·12^d/M³)^{n_∞−1} · (∏_{S_fin} w(m)) / 12^{dD}`**

(`RB.approxProduct_anchoredTriple_eq`), and, since a finite place contracts integers,

  **`approxProduct ≤ (|Λ|·12^d/M³) · (|m|·12^d/M³)^{n_∞−1} / 12^{dD}`**

(`RB.approxProduct_anchoredTriple_le`).  Over `ℚ` (`n_∞ = D = 1`) this collapses to the familiar
`|Λ|/M³`.  Combined with `RB.anchored_rehearsal_triple` this yields
`RB.anchored_rehearsal_defect`: the Subspace hypothesis is now an *elementary inequality* between
`|Λ|`, `|m|`, `d` and the field constants `n_∞`, `D` — no places left in it.  What remains of the
bill is item 3: choosing `ε` from the geometric scale `θ` and running the subspace-escape endgame.

## A normalization caveat

`Subspace.approxProduct` counts each place of `S` once, whereas the Evertse–Schlickewei theorem is
normally stated with the local degrees as exponents (which Mathlib's height carries as
`InfinitePlace.mult`).  For the forms used here every factor is `≤ 1` at the places where the two
conventions differ, so the cited axiom as encoded is the *weaker* statement; no conclusion drawn
here or in `RB/Anchored.lean` depends on the stronger one.  The discrepancy is a factor
`|q|^{r₂}`, and it is visible above: it is the only reason `∏_{w ∈ S} w(q) ≠ 1`.

## Contents

* `RB.localNorm_smul`, `RB.approxProduct_smul` — scaling invariance (candidates to move next to
  the definitions in `CITED/SubspaceTheorem.lean`).
* `RB.anchoredFinitePlaces`, `RB.prod_anchoredPlaces`, `RB.infinitePlace_mem_anchoredPlaces`,
  `RB.realPlace_isInfinitePlace`, `RB.realPlace_mem_anchoredPlaces`.
* `RB.finitePlace_apply_two_eq_one`, `RB.finitePlace_apply_three_eq_one`,
  `RB.finitePlace_apply_sUnit_eq_one`, **`RB.prod_anchoredFinitePlaces_sUnit`**,
  **`RB.prod_anchoredPlaces_sUnit`**, `RB.prod_anchoredPlaces_sUnit_eq`.
* `RB.localNorm_finitePlace_anchoredTripleInt`, `RB.localNorm_infinitePlace_anchoredTripleInt`,
  `RB.prod_infinitePlace_anchoredTripleInt`, `RB.prod_finitePlace_anchoredTripleInt`,
  `RB.anchoredDefect`, `RB.realPlace_form_anchoredTripleInt`.
* **`RB.approxProduct_anchoredTriple_eq`**, **`RB.approxProduct_anchoredTriple_le`**,
  **`RB.anchored_rehearsal_defect`**.

## References

* [B1E2a2] `plans/report-B1E2a-v2.html` (2026-08-06): §4 N4, §6 P3, §7 WP-G (gate bill item 1).
* [Schmidt91] W. M. Schmidt, LNM 1467, Thm 1D′ — `Subspace.evertseSchlickewei`.
* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, CUP 2006, §1.4–1.5.
-/

namespace RB

open NumberField IntermediateField

/-! ## Scaling invariance of the Subspace data -/

section Scaling

variable {K : Type*} [Field K]

/-- The local sup-norm is homogeneous: `‖c·x‖_v = |c|_v ‖x‖_v`. -/
@[category API, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_anchored"]
theorem localNorm_smul {n : ℕ} [Nonempty (Fin n)] (v : AbsoluteValue K ℝ) (c : K)
    (x : Fin n → K) : Subspace.localNorm v (c • x) = v c * Subspace.localNorm v x := by
  unfold Subspace.localNorm
  have hmono : Monotone (fun t : ℝ => v c * t) := fun a b h =>
    mul_le_mul_of_nonneg_left h (v.nonneg c)
  rw [Finite.map_iSup_of_monotone (fun i => v (x i)) hmono]
  exact iSup_congr fun i => by simp [Pi.smul_apply, smul_eq_mul]

/-- **The approximation product is scaling invariant**: each of its factors is a quotient of two
quantities homogeneous of the same degree.  This is what allows the anchored computation to be
carried out on the primitive integer representative of the rational triple. -/
@[category API, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_anchored"]
theorem approxProduct_smul {n : ℕ} [Nonempty (Fin n)] (S : Finset (AbsoluteValue K ℝ))
    (L : AbsoluteValue K ℝ → Fin n → ((Fin n → K) →ₗ[K] K)) {c : K} (hc : c ≠ 0)
    (x : Fin n → K) :
    Subspace.approxProduct S L (c • x) = Subspace.approxProduct S L x := by
  unfold Subspace.approxProduct
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun i _ => ?_
  rw [map_smul, localNorm_smul, smul_eq_mul, map_mul, mul_div_mul_left _ _ (v.pos hc).ne']

end Scaling

/-! ## The two halves of the anchored place set -/

section Places

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

/-- The finite half of `RB.anchoredPlaces`: the finite places of `ℚ(δ)` above `2` and `3`, as
places rather than as bare absolute values. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
noncomputable def anchoredFinitePlaces : Finset (FinitePlace ℚ⟮δ⟯) :=
  Set.Finite.toFinset
    (show (Function.mulSupport fun w : FinitePlace ℚ⟮δ⟯ => w ((6 : ℚ⟮δ⟯))).Finite from
      FinitePlace.hasFiniteMulSupport (show (6 : ℚ⟮δ⟯) ≠ 0 by norm_num))

/-- **The place set splits**: a product over `RB.anchoredPlaces` is the product over all infinite
places times the product over `RB.anchoredFinitePlaces`.  The two halves are disjoint because an
infinite place takes the value `2` at `2` while a finite place is contracting on integers. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem prod_anchoredPlaces (f : AbsoluteValue ℚ⟮δ⟯ ℝ → ℝ) :
    ∏ v ∈ anchoredPlaces δ, f v
      = (∏ v : InfinitePlace ℚ⟮δ⟯, f v.val) * ∏ w ∈ anchoredFinitePlaces δ, f w.val := by
  let := Classical.decEq (AbsoluteValue ℚ⟮δ⟯ ℝ)
  have hdisj : Disjoint (Finset.univ.image (fun v : InfinitePlace ℚ⟮δ⟯ => v.val))
      (((FinitePlace.hasFiniteMulSupport (show (6 : ℚ⟮δ⟯) ≠ 0 by norm_num)).image
        Subtype.val).toFinset) := by
    rw [Finset.disjoint_left]
    rintro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
    simp only [Set.Finite.mem_toFinset] at hb
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, _, hw⟩ := hb
    exact FinitePlace.val_ne_infinitePlace_val w v (hw.trans hv.symm)
  rw [anchoredPlaces, Finset.prod_union hdisj]
  congr 1
  · exact Finset.prod_image (fun v _ v' _ h => Subtype.ext h)
  · rw [Set.Finite.toFinset_image Subtype.val (FinitePlace.hasFiniteMulSupport
        (show (6 : ℚ⟮δ⟯) ≠ 0 by norm_num)),
      Finset.prod_image (fun v _ v' _ h => Subtype.ext h)]
    rfl

/-- Every infinite place belongs to the anchored place set. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem infinitePlace_mem_anchoredPlaces (v : InfinitePlace ℚ⟮δ⟯) :
    v.val ∈ anchoredPlaces δ := by
  let := Classical.decEq (AbsoluteValue ℚ⟮δ⟯ ℝ)
  rw [anchoredPlaces]
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))

/-- The finite places outside the anchored set are trivial at `6` — this is the defining property
of the set, and the reason the `S`-units are invisible there. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem finitePlace_apply_six_eq_one_of_notMem {w : FinitePlace ℚ⟮δ⟯}
    (hw : w ∉ anchoredFinitePlaces δ) : w ((6 : ℚ⟮δ⟯)) = 1 := by
  rw [anchoredFinitePlaces, Set.Finite.mem_toFinset] at hw
  simpa [Function.mem_mulSupport] using hw

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The distinguished place of the anchored application is an infinite place: it is induced by the
complex embedding `ℚ⟮δ⟯ ↪ ℝ ↪ ℂ`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem realPlace_isInfinitePlace : ∃ v : InfinitePlace ℚ⟮δ⟯, v.val = realPlace δ := by
  refine ⟨InfinitePlace.mk ((algebraMap ℝ ℂ).comp (algebraMap ℚ⟮δ⟯ ℝ)), ?_⟩
  ext x
  rw [realPlace_apply]
  simp [InfinitePlace.mk, NumberField.place_apply]

/-- The distinguished place belongs to the anchored place set. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem realPlace_mem_anchoredPlaces : realPlace δ ∈ anchoredPlaces δ := by
  obtain ⟨v, hv⟩ := realPlace_isInfinitePlace δ
  exact hv ▸ infinitePlace_mem_anchoredPlaces δ v

end Places

/-! ## The `S`-unit place values -/

section SUnits

variable {δ : ℝ} [NumberField ℚ⟮δ⟯]

/-- A finite place trivial at `6` is trivial at `2`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem finitePlace_apply_two_eq_one {w : FinitePlace ℚ⟮δ⟯} (hw : w ((6 : ℚ⟮δ⟯)) = 1) :
    w ((2 : ℚ⟮δ⟯)) = 1 := by
  refine FinitePlace.apply_natCast_eq_one_of_mul_eq_one w (m := 2) (n := 3) ?_
  push_cast
  exact hw

/-- A finite place trivial at `6` is trivial at `3`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem finitePlace_apply_three_eq_one {w : FinitePlace ℚ⟮δ⟯} (hw : w ((6 : ℚ⟮δ⟯)) = 1) :
    w ((3 : ℚ⟮δ⟯)) = 1 := by
  refine FinitePlace.apply_natCast_eq_one_of_mul_eq_one w (m := 3) (n := 2) ?_
  push_cast
  exact hw

/-- **The `S`-units are invisible outside `S`**: a finite place trivial at `6` is trivial at every
`2^a3^b`, `a, b ∈ ℤ`. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem finitePlace_apply_sUnit_eq_one {w : FinitePlace ℚ⟮δ⟯} (hw : w ((6 : ℚ⟮δ⟯)) = 1) (a b : ℤ) :
    w (((((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ)) : ℚ⟮δ⟯)) = 1 := by
  have h2 := finitePlace_apply_two_eq_one hw
  have h3 := finitePlace_apply_three_eq_one hw
  have hcast : ((((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ)) : ℚ⟮δ⟯) = (2 : ℚ⟮δ⟯) ^ a * (3 : ℚ⟮δ⟯) ^ b := by
    push_cast
    ring
  rw [hcast, map_mul, map_zpow₀, map_zpow₀, h2, h3, one_zpow, one_zpow, one_mul]

variable (δ)

/-- **The finite contribution of an `S`-unit**, computed by the product formula alone:
`∏_{w ∈ S_fin} w(2^a3^b) = (|2^a3^b|^{[K:ℚ]})⁻¹`.  No ramification data enters. -/
@[category research solved, AMS 11, ref "B1E2a2" "BG06", group "rb_anchored"]
theorem prod_anchoredFinitePlaces_sUnit (a b : ℤ) :
    (∏ w ∈ anchoredFinitePlaces δ, w (((((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ)) : ℚ⟮δ⟯)))
      = (|(((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ) : ℝ)| ^ Module.finrank ℚ ℚ⟮δ⟯)⁻¹ := by
  have hq : ((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ) ≠ 0 := by positivity
  exact NumberField.prod_finitePlace_ratCast hq _
    (fun w hw => finitePlace_apply_sUnit_eq_one (finitePlace_apply_six_eq_one_of_notMem δ hw) a b)

/-- **The `S`-unit product over the whole anchored place set**: the infinite places contribute
`|q|` each, the finite ones `|q|^{-[K:ℚ]}` jointly. -/
@[category research solved, AMS 11, ref "B1E2a2" "BG06", group "rb_anchored"]
theorem prod_anchoredPlaces_sUnit (a b : ℤ) :
    (∏ v ∈ anchoredPlaces δ, v (((((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ)) : ℚ⟮δ⟯)))
      = |(((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ) : ℝ)| ^ Fintype.card (InfinitePlace ℚ⟮δ⟯)
        * (|(((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ) : ℝ)| ^ Module.finrank ℚ ℚ⟮δ⟯)⁻¹ := by
  rw [prod_anchoredPlaces δ]
  simp only [InfinitePlace.val_apply, FinitePlace.val_apply]
  rw [prod_anchoredFinitePlaces_sUnit δ a b]
  congr 1
  rw [Finset.prod_congr rfl (fun v _ => InfinitePlace.apply_ratCast v _)]
  rw [Finset.prod_const, Finset.card_univ]

/-- The same product as a single power: the excess of the degree over the number of infinite
places is the number `r₂` of complex places, so `∏_{w ∈ S} w(q) = (|q|^{r₂})⁻¹`.  In particular the
product is `1` when `ℚ(δ)` is totally real. -/
@[category research solved, AMS 11, ref "B1E2a2" "BG06", group "rb_anchored"]
theorem prod_anchoredPlaces_sUnit_eq (a b : ℤ) :
    (∏ v ∈ anchoredPlaces δ, v (((((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ)) : ℚ⟮δ⟯)))
      = (|(((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ) : ℝ)| ^ InfinitePlace.nrComplexPlaces ℚ⟮δ⟯)⁻¹ := by
  have hq : (0 : ℝ) < |(((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ) : ℝ)| := by
    refine abs_pos.mpr ?_
    have : ((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ) ≠ 0 := by positivity
    exact_mod_cast this
  have hcard : Fintype.card (InfinitePlace ℚ⟮δ⟯) + InfinitePlace.nrComplexPlaces ℚ⟮δ⟯
      = Module.finrank ℚ ℚ⟮δ⟯ := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    have := InfinitePlace.card_add_two_mul_card_eq_rank (K := ℚ⟮δ⟯)
    omega
  rw [prod_anchoredPlaces_sUnit δ a b, ← hcard, pow_add]
  field_simp

end SUnits

/-! ## The local data of the anchored triple -/

section TripleData

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

/-- At a finite place the primitive triple has local norm `1` — it is a coprime integer triple. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem localNorm_finitePlace_anchoredTripleInt (w : FinitePlace ℚ⟮δ⟯) (m : ℤ) (d : ℕ) :
    Subspace.localNorm w.val (fun i ↦ ((anchoredTripleInt m d i : ℤ) : ℚ⟮δ⟯)) = 1 :=
  NumberField.iSup_finitePlace_intCast_eq_one_of_gcd_eq_one w (anchoredTripleInt_gcd m d)

omit [NumberField ↥ℚ⟮δ⟯] in
/-- At an infinite place the primitive triple has local norm `M = max(|m|·2^d, 3^d)`, the base of
its height (`RB.mulHeight_anchoredTriple`). -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem localNorm_infinitePlace_anchoredTripleInt (v : InfinitePlace ℚ⟮δ⟯) (m : ℤ) (d : ℕ) :
    Subspace.localNorm v.val (fun i ↦ ((anchoredTripleInt m d i : ℤ) : ℚ⟮δ⟯))
      = max (|(m : ℝ)| * 2 ^ d) (3 ^ d) := by
  unfold Subspace.localNorm
  rw [← iSup_abs_anchoredTripleInt m d]
  refine iSup_congr fun i ↦ ?_
  simp only [InfinitePlace.val_apply]
  rw [InfinitePlace.map_intCast, Int.norm_eq_abs]

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The coordinate product of the primitive triple at an infinite place is `|m|·12^d`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem prod_infinitePlace_anchoredTripleInt (v : InfinitePlace ℚ⟮δ⟯) (m : ℤ) (d : ℕ) :
    (∏ i, v.val (((anchoredTripleInt m d i : ℤ) : ℚ⟮δ⟯))) = |(m : ℝ)| * 12 ^ d := by
  rw [Fin.prod_univ_three]
  simp only [anchoredTripleInt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, InfinitePlace.val_apply]
  rw [InfinitePlace.map_intCast, InfinitePlace.map_intCast, InfinitePlace.map_intCast,
    Int.norm_eq_abs, Int.norm_eq_abs, Int.norm_eq_abs]
  push_cast
  simp only [abs_mul, abs_pow]
  rw [abs_two, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    show (12 : ℝ) = 2 * 3 * 2 by norm_num, mul_pow, mul_pow]
  ring

/-- The coordinate product of the primitive triple at a finite place splits into the integer part
`w(m)` — invisible to the product formula — and the `S`-unit part `w(12^d)`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem prod_finitePlace_anchoredTripleInt (w : FinitePlace ℚ⟮δ⟯) (m : ℤ) (d : ℕ) :
    (∏ i, w.val (((anchoredTripleInt m d i : ℤ) : ℚ⟮δ⟯)))
      = w ((m : ℚ⟮δ⟯)) * w ((((12 : ℚ) ^ d : ℚ) : ℚ⟮δ⟯)) := by
  rw [Fin.prod_univ_three]
  simp only [anchoredTripleInt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, FinitePlace.val_apply]
  push_cast
  have h12 : ((12 : ℚ⟮δ⟯)) ^ d = ((2 : ℚ⟮δ⟯) ^ d * (3 : ℚ⟮δ⟯) ^ d) * (2 : ℚ⟮δ⟯) ^ d := by
    rw [show (12 : ℚ⟮δ⟯) = 2 * 3 * 2 by norm_num, mul_pow, mul_pow]
  rw [h12, map_mul, map_mul, map_mul]
  ring

/-- **The anchored defect** `Λ = δ(3/2)^b((3/2)^d − 1) − m`: the distance from the inhomogeneous
one-power quantity to the integer `m`.  `RB.InhomOnePower` asserts that `|Λ| ≤ θ^d` has only
finitely many solutions `d` (with `m` the nearest integer). -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
noncomputable def anchoredDefect (δ : ℝ) (b : ℕ) (m : ℤ) (d : ℕ) : ℝ :=
  δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1) - m

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The distinguished form of `RB.nkForms`, evaluated at the primitive triple, is `2^d` times the
anchored defect: this is the single small quantity in the whole approximation product. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem realPlace_form_anchoredTripleInt (b : ℕ) (m : ℤ) (d : ℕ) :
    realPlace δ (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ) (realPlace δ) 0
        (fun i ↦ ((anchoredTripleInt m d i : ℤ) : ℚ⟮δ⟯)))
      = 2 ^ d * |anchoredDefect δ b m d| := by
  rw [nkForms_apply_self, realPlace_apply]
  simp only [anchoredTripleInt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have hcoe : (((genMultiplier δ b * (((3 : ℤ) ^ d : ℤ) : ℚ⟮δ⟯)
      + -genMultiplier δ b * (((2 : ℤ) ^ d : ℤ) : ℚ⟮δ⟯)
      - (((m * 2 ^ d : ℤ)) : ℚ⟮δ⟯)) : ℚ⟮δ⟯) : ℝ)
      = 2 ^ d * anchoredDefect δ b m d := by
    rw [anchoredDefect]
    push_cast
    rw [show ((3 : ℚ⟮δ⟯) : ℝ) = 3 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 3,
      show ((2 : ℚ⟮δ⟯) : ℝ) = 2 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 2, genMultiplier_coe]
    simp only [div_pow]
    have h2 : (2 : ℝ) ^ d ≠ 0 := by positivity
    field_simp
    ring
  rw [hcoe, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d)]

end TripleData

/-! ## The approximation product of the anchored triple -/

section Assembly

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

omit [NumberField ↥ℚ⟮δ⟯] in
/-- At a place other than the distinguished one, `RB.nkForms` is the coordinate system, so the
form product is the coordinate product. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem prod_nkForms_of_ne {v : AbsoluteValue ℚ⟮δ⟯ ℝ} (hv : v ≠ realPlace δ) (γ₁ γ₂ : ℚ⟮δ⟯)
    (x : Fin 3 → ℚ⟮δ⟯) :
    (∏ i, v (nkForms γ₁ γ₂ (realPlace δ) v i x)) = ∏ i, v (x i) := by
  unfold nkForms coordForms
  rw [ite_eq_right hv]
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  simp

omit [NumberField ↥ℚ⟮δ⟯] in
/-- At the distinguished place the form product is the defect times the two `S`-unit
coordinates. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem prod_nkForms_realPlace (b : ℕ) (m : ℤ) (d : ℕ) :
    (∏ i, realPlace δ (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ)
        (realPlace δ) i (fun i ↦ ((anchoredTripleInt m d i : ℤ) : ℚ⟮δ⟯))))
      = |anchoredDefect δ b m d| * 12 ^ d := by
  rw [Fin.prod_univ_three]
  rw [realPlace_form_anchoredTripleInt δ b m d]
  have h1 : nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ) (realPlace δ) 1
      = LinearMap.proj 1 := by unfold nkForms approxForms; rw [ite_eq_left rfl]; simp
  have h2 : nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ) (realPlace δ) 2
      = LinearMap.proj 2 := by unfold nkForms approxForms; rw [ite_eq_left rfl]; simp
  rw [h1, h2]
  simp only [LinearMap.proj_apply, anchoredTripleInt, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  rw [realPlace_apply, realPlace_apply]
  push_cast
  rw [show ((3 : ℚ⟮δ⟯) : ℝ) = 3 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 3,
    show ((2 : ℚ⟮δ⟯) : ℝ) = 2 from map_ofNat (algebraMap ℚ⟮δ⟯ ℝ) 2]
  simp only [abs_pow]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    show (12 : ℝ) = 3 * 2 * 2 by norm_num, mul_pow, mul_pow]
  ring

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The local norm of the primitive triple at the distinguished place is again `M`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem localNorm_realPlace_anchoredTripleInt (m : ℤ) (d : ℕ) :
    Subspace.localNorm (realPlace δ) (fun i ↦ ((anchoredTripleInt m d i : ℤ) : ℚ⟮δ⟯))
      = max (|(m : ℝ)| * 2 ^ d) (3 ^ d) := by
  obtain ⟨v₀, hv₀⟩ := realPlace_isInfinitePlace δ
  rw [← hv₀]
  exact localNorm_infinitePlace_anchoredTripleInt δ v₀ m d

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The approximation-product factor at the distinguished place: `|Λ|·12^d / M³`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem factor_realPlace (b : ℕ) (m : ℤ) (d : ℕ) :
    (∏ i, realPlace δ (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ)
        (realPlace δ) i (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯))))
        / Subspace.localNorm (realPlace δ)
            (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)) ^ 3
      = |anchoredDefect δ b m d| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 := by
  rw [prod_nkForms_realPlace δ b m d, localNorm_realPlace_anchoredTripleInt δ m d]

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The factor at any other infinite place: the same expression with `|m|` in place of `|Λ|`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem factor_infinitePlace (v : InfinitePlace ℚ⟮δ⟯) (hv : v.val ≠ realPlace δ) (b : ℕ) (m : ℤ)
    (d : ℕ) :
    (∏ i, v.val (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ)
        v.val i (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯))))
        / Subspace.localNorm v.val (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)) ^ 3
      = |(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 := by
  rw [prod_nkForms_of_ne δ hv, prod_infinitePlace_anchoredTripleInt δ v m d,
    localNorm_infinitePlace_anchoredTripleInt δ v m d]

/-- The factor at a finite place: the local norm is `1`, so only the coordinate values survive. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem factor_finitePlace (w : FinitePlace ℚ⟮δ⟯) (b : ℕ) (m : ℤ) (d : ℕ) :
    (∏ i, w.val (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ)
        w.val i (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯))))
        / Subspace.localNorm w.val (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)) ^ 3
      = w ((m : ℚ⟮δ⟯)) * w ((((12 : ℚ) ^ d : ℚ) : ℚ⟮δ⟯)) := by
  have hne : w.val ≠ realPlace δ := by
    obtain ⟨v₁, hv₁⟩ := realPlace_isInfinitePlace δ
    rw [← hv₁]
    exact FinitePlace.val_ne_infinitePlace_val w v₁
  rw [prod_nkForms_of_ne δ hne, prod_finitePlace_anchoredTripleInt δ w m d,
    localNorm_finitePlace_anchoredTripleInt δ w m d, one_pow, div_one]

/-- **The approximation product of the anchored triple, computed** ([B1E2a2] §7 WP-G, bill item 1).
With `Λ` the anchored defect, `M = max(|m|·2^d, 3^d)` the base of the height, `n_∞` the number of
infinite places and `D = [ℚ(δ) : ℚ]`:

  `approxProduct = (|Λ|·12^d/M³) · (|m|·12^d/M³)^{n_∞−1} · (∏_{w ∈ S_fin} w(m)) / 12^{dD}`.

The distinguished place contributes the small factor, the remaining infinite places contribute the
same expression with `|Λ|` replaced by `|m|`, and the finite places contribute the `S`-unit
product `12^{-dD}` (product formula) times an integer factor `≤ 1`. -/
@[category research solved, AMS 11, ref "Schmidt91" "B1E2a2" "BG06", group "rb_anchored"]
theorem approxProduct_anchoredTriple_eq (b : ℕ) (m : ℤ) (d : ℕ) :
    Subspace.approxProduct (anchoredPlaces δ)
        (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ))
        (fun i ↦ ((anchoredTriple m d i : ℚ) : ℚ⟮δ⟯))
      = (|anchoredDefect δ b m d| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
        * (|(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
            ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) - 1)
        * ((∏ w ∈ anchoredFinitePlaces δ, w ((m : ℚ⟮δ⟯)))
            / (12 : ℝ) ^ (d * Module.finrank ℚ ℚ⟮δ⟯)) := by
  classical
  rw [anchoredTriple_eq_smul (K := ℚ⟮δ⟯) m d,
    approxProduct_smul _ _ (inv_ne_zero (pow_ne_zero d (two_ne_zero (α := ℚ⟮δ⟯)))),
    Subspace.approxProduct,
    prod_anchoredPlaces δ (fun v ↦ ∏ i, v (nkForms (genMultiplier δ b) (-(genMultiplier δ b))
        (realPlace δ) v i (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)))
      / Subspace.localNorm v (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)))]
  -- each factor is the form product divided by the cube of the local norm
  have hfac : ∀ v : AbsoluteValue ℚ⟮δ⟯ ℝ,
      (∏ i, v (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ) v i
            (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)))
          / Subspace.localNorm v (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)))
        = (∏ i, v (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ) v i
              (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯))))
            / Subspace.localNorm v (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)) ^ 3 := by
    intro v
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [hfac]
  obtain ⟨v₀, hv₀⟩ := realPlace_isInfinitePlace δ
  -- the infinite places: the distinguished one, then the remaining `n_∞ − 1` equal factors
  have hinf : (∏ v : InfinitePlace ℚ⟮δ⟯,
      (∏ i, v.val (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ) v.val i
          (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯))))
        / Subspace.localNorm v.val (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)) ^ 3)
      = (|anchoredDefect δ b m d| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
        * (|(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
            ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) - 1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀)]
    congr 1
    · rw [hv₀]
      exact factor_realPlace δ b m d
    · refine (Finset.prod_congr rfl (fun v hv ↦ factor_infinitePlace δ v ?_ b m d)).trans ?_
      · rw [← hv₀]
        exact fun h ↦ (Finset.ne_of_mem_erase hv) (Subtype.ext h)
      · rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ]
  -- the finite places: an integer factor times the `S`-unit product formula
  have h12 : (((12 : ℚ) ^ d : ℚ)) = ((2 : ℚ) ^ ((2 * d : ℕ) : ℤ) * (3 : ℚ) ^ ((d : ℕ) : ℤ)) := by
    rw [zpow_natCast, zpow_natCast, show (12 : ℚ) = 2 ^ 2 * 3 by norm_num, mul_pow, ← pow_mul]
  have habs : |(((12 : ℚ) ^ d : ℚ) : ℝ)| = (12 : ℝ) ^ d := by
    push_cast
    rw [abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]
  have hfin : (∏ w ∈ anchoredFinitePlaces δ,
      (∏ i, w.val (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ) w.val i
          (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯))))
        / Subspace.localNorm w.val (fun j ↦ ((anchoredTripleInt m d j : ℤ) : ℚ⟮δ⟯)) ^ 3)
      = (∏ w ∈ anchoredFinitePlaces δ, w ((m : ℚ⟮δ⟯)))
          / (12 : ℝ) ^ (d * Module.finrank ℚ ℚ⟮δ⟯) := by
    rw [Finset.prod_congr rfl (fun w _ ↦ factor_finitePlace δ w b m d), Finset.prod_mul_distrib,
      div_eq_mul_inv]
    congr 1
    rw [h12, prod_anchoredFinitePlaces_sUnit δ _ _, ← h12, habs, ← pow_mul]
  rw [hinf, hfin]

/-- **The approximation product bound** ([B1E2a2] §7 WP-G, bill item 1): dropping the integer
factor `∏_{w ∈ S_fin} w(m) ≤ 1` of `RB.approxProduct_anchoredTriple_eq` leaves an expression in
`|Λ|`, `|m|`, `d` and the two field constants only.  Over `ℚ` (`n_∞ = D = 1`) it reads
`approxProduct ≤ |Λ|/M³`. -/
@[category research solved, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_anchored"]
theorem approxProduct_anchoredTriple_le (b : ℕ) (m : ℤ) (d : ℕ) :
    Subspace.approxProduct (anchoredPlaces δ)
        (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ))
        (fun i ↦ ((anchoredTriple m d i : ℚ) : ℚ⟮δ⟯))
      ≤ (|anchoredDefect δ b m d| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
        * (|(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
            ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) - 1)
        / (12 : ℝ) ^ (d * Module.finrank ℚ ℚ⟮δ⟯) := by
  rw [approxProduct_anchoredTriple_eq δ b m d, ← mul_div_assoc]
  have hMnn : (0 : ℝ) ≤ max (|(m : ℝ)| * 2 ^ d) (3 ^ d) :=
    le_trans (by positivity) (le_max_right _ _)
  have h₁ : (0 : ℝ) ≤ |anchoredDefect δ b m d| * 12 ^ d
      / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 :=
    div_nonneg (by positivity) (pow_nonneg hMnn 3)
  have h₂ : (0 : ℝ) ≤ |(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3 :=
    div_nonneg (by positivity) (pow_nonneg hMnn 3)
  have hprod : (∏ w ∈ anchoredFinitePlaces δ, w ((m : ℚ⟮δ⟯))) ≤ 1 := by
    have := NumberField.prod_finitePlace_intCast_le_one (K := ℚ⟮δ⟯) m (anchoredFinitePlaces δ)
    simpa using this
  have h12 : (0 : ℝ) ≤ (12 : ℝ) ^ (d * Module.finrank ℚ ℚ⟮δ⟯) := by positivity
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (mul_nonneg h₁ (pow_nonneg h₂ _)) hprod) h12

/-- **The rehearsal with the place values eliminated**: combining
`RB.approxProduct_anchoredTriple_le` with `RB.anchored_rehearsal_triple`, the Subspace hypothesis
becomes an elementary inequality between the anchored defect `Λ`, the integer `m`, the exponent
`d`, and the two constants `n_∞`, `D` of the field `ℚ(δ)`.  Every place has been evaluated; what
is left of the WP-G bill is the endgame (item 3). -/
@[category research solved, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_anchored"]
theorem anchored_rehearsal_defect (ε : ℝ) (hε : 0 < ε) (b : ℕ) :
    ∃ T : Finset (Submodule ℚ⟮δ⟯ (Fin 3 → ℚ⟮δ⟯)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ (m : ℤ) (d : ℕ),
        (|anchoredDefect δ b m d| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
            * (|(m : ℝ)| * 12 ^ d / (max (|(m : ℝ)| * 2 ^ d) (3 ^ d)) ^ 3)
                ^ (Fintype.card (InfinitePlace ℚ⟮δ⟯) - 1)
            / (12 : ℝ) ^ (d * Module.finrank ℚ ℚ⟮δ⟯)
          ≤ (max (|(m : ℝ)| * 2 ^ d) (3 ^ d))
              ^ ((Module.finrank ℚ ℚ⟮δ⟯ : ℝ) * (-(3 : ℝ) - ε)) →
        ∃ W ∈ T, (fun i ↦ ((anchoredTriple m d i : ℚ) : ℚ⟮δ⟯)) ∈ W := by
  obtain ⟨T, hT, hsol⟩ := anchored_rehearsal_triple δ ε hε b
  exact ⟨T, hT, fun m d hle ↦ hsol m d ((approxProduct_anchoredTriple_le δ b m d).trans hle)⟩

end Assembly

end RB
