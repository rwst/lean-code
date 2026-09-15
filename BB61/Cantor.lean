/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Lemma 1: the coding IFS, the gap, separation, and the conjugacy

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Lemma 1.  This is the place where `α > 2` first enters the problem.

`C(α) = Set.range (piVal α)` is the attractor of the IFS `f₀ x = x/α`, `f₁ x = (x + α - 1)/α`
on `[0,1]` (`ifsMap`, and the self-similarity `piVal_eq_ifsMap`).  Part (ii) says that the
two branches do not meet:

* `image_ifsMap_false`, `image_ifsMap_true` — `f₀[0,1] = [0, α⁻¹]` and
  `f₁[0,1] = [(α-1)/α, 1]`;
* `sub_inv_eq_gap` — the two are separated by exactly `g := (α-2)/α` (`gap`), and
  `gap_pos_iff` says `g > 0` **iff** `α > 2`;
* `gap_le_sub_ifsMap`, `gap_le_piVal_sub` — the quantitative form, on points and on digits:
  a word beginning with `1` and a word beginning with `0` have `π`-values at least `g` apart;
* `disjoint_image_ifsMap` — the disjointness itself, for `α > 2`.

Part (iv) is that separation carried down the tree:

* `piVal_sub_eq_pow_mul` — words agreeing on their first `k` letters have
  `π(ε) - π(ε') = α^{-k} (π(σᵏ ε) - π(σᵏ ε'))`, the first `k` terms cancelling exactly;
* `gap_mul_le_abs_piVal_sub` — **M1 Lemma 1(iv)**: if moreover they differ at letter `k`
  then `|π(ε) - π(ε')| ≥ g α^{-k}`.

Both are stated for every `α > 1`; the hypothesis `α > 2` enters only through `0 < gap α`,
which is where the bound acquires content.  Note that the hypotheses of `QuadSetup`
(`BB61/Defs.lean`) deliberately do *not* include `α > 2`, so `gap` is carried as a
quantity rather than as a standing assumption.

Part (i) is the attractor description and the extreme values:

* `consW`, `piVal_consW` — prefixing a letter is applying a branch, `π(b :: δ) = f_b(π(δ))`;
* `cantorSet_eq_union` — **M1 Lemma 1(i)**: `C(α) = f₀(C(α)) ∪ f₁(C(α))`;
* `piVal_const_false`, `piVal_const_true`, `isLeast_cantorSet`, `isGreatest_cantorSet` —
  `min C(α) = 0` and `max C(α) = 1`, attained at `0^∞` and `1^∞`.

Part (iii), everything but the dimension values:

* `continuous_piVal`, `isCompact_cantorSet` — `π` is continuous and `C(α)` compact;
* `injective_piVal` — injectivity, straight from (iv) at the first index where two words
  differ;
* `piHomeomorph` — **M1 Lemma 1(iii)**: `π : {0,1}^ℕ ≃ₜ C(α)`, a continuous bijection from
  a compact space to a Hausdorff one;
* `volume_cantorSet` — `Leb(C(α)) = 0`.  The note gets this from `dim_H = log2/log α < 1`;
  here it is elementary and needs no dimension theory: `C(α)` is the *disjoint* union of
  two copies of itself scaled by `α⁻¹`, so its measure `v` satisfies `v = 2α⁻¹v` with
  `2α⁻¹ < 1` and `v < ∞`.

Part (v) is the conjugacy:

* `tauMap` — `τ_α x = α x - (α-1) ε₁(x)`, the first digit read off `x` by the threshold
  `(α-1)/α`, which is legitimate exactly because the branches are separated;
* `tauMap_piVal` — **M1 Lemma 1(v)**: `π ∘ σ = τ_α ∘ π`, and `tauMap_mapsTo` says `τ_α`
  preserves `C(α)`.  With `piHomeomorph` this is the topological conjugacy of
  `(C(α), τ_α)` with the one-sided full `2`-shift.

The dimension values `dim_H C(α) = dim_B C(α) = log 2 / log α` of (iii) are **not** here,
because they needed a box dimension Mathlib does not have: they live in `BB61/BoxDim.lean`
(the ceiling, on `ForMathlib/Topology/MetricSpace/BoxDimension.lean`) and
`BB61/Hausdorff.lean` (the Hausdorff floor).  The reading of the same coding as a
restriction of the Rényi–Parry `α`-expansion — M1 Proposition 14, the licence for citing
the `θ`-shift literature — is `BB61/Admissible.lean`.
-/

namespace BB61

variable {α : ℝ}

/-! ## The two branches and the gap between them -/

/-- The gap `g = (α-2)/α` between the two branches of the IFS (M1 Lemma 1(ii)). -/
noncomputable def gap (α : ℝ) : ℝ := (α - 2) / α

/-- The IFS whose attractor is `C(α)` (M1 Lemma 1(i)): `f₀ x = x/α` and
`f₁ x = (x + α - 1)/α`, indexed by the digit `b`. -/
noncomputable def ifsMap (α : ℝ) (b : Bool) (x : ℝ) : ℝ :=
  (x + (α - 1) * (if b then 1 else 0)) / α

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ifsMap_false (α x : ℝ) : ifsMap α false x = x / α := by
  simp [ifsMap]

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ifsMap_true (α x : ℝ) : ifsMap α true x = (x + (α - 1)) / α := by
  simp [ifsMap]

/-- `g > 0` is exactly `α > 2`: this is the first of the three uses of the hypothesis
`α > 2` in M1 (§5, U1). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gap_pos_iff (hα0 : 0 < α) : 0 < gap α ↔ 2 < α := by
  constructor
  · intro h
    have h' : 0 < (α - 2) / α * α := mul_pos h hα0
    rw [div_mul_cancel₀ _ hα0.ne'] at h'
    linarith
  · intro h
    exact div_pos (by linarith) hα0

/-- The right endpoint of `f₀[0,1]` and the left endpoint of `f₁[0,1]` are exactly `g`
apart (M1 Lemma 1(ii)). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sub_inv_eq_gap (hα0 : α ≠ 0) : (α - 1) / α - α⁻¹ = gap α := by
  rw [gap]
  field_simp
  ring

/-- **M1 Lemma 1(ii)**, first half: `f₀([0,1]) = [0, 1/α]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem image_ifsMap_false (hα : 1 < α) :
    ifsMap α false '' Set.Icc (0 : ℝ) 1 = Set.Icc 0 α⁻¹ := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hfun : ifsMap α false = fun x : ℝ => x * α⁻¹ := by
    funext x; rw [ifsMap_false, div_eq_mul_inv]
  rw [hfun, Set.image_mul_right_Icc (by norm_num) (inv_nonneg.mpr hα0.le), zero_mul, one_mul]

/-- **M1 Lemma 1(ii)**, second half: `f₁([0,1]) = [(α-1)/α, 1]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem image_ifsMap_true (hα : 1 < α) :
    ifsMap α true '' Set.Icc (0 : ℝ) 1 = Set.Icc ((α - 1) / α) 1 := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hfun : ifsMap α true = (fun x : ℝ => x * α⁻¹) ∘ fun x : ℝ => x + (α - 1) := by
    funext x; rw [Function.comp_apply, ifsMap_true, div_eq_mul_inv]
  rw [hfun, Set.image_comp, Set.image_add_const_Icc,
    Set.image_mul_right_Icc (by linarith) (inv_nonneg.mpr hα0.le),
    show (0 : ℝ) + (α - 1) = α - 1 by ring, show (1 : ℝ) + (α - 1) = α by ring,
    mul_inv_cancel₀ hα0.ne', ← div_eq_mul_inv]

/-- **M1 Lemma 1(ii)**, quantitative form: a point of the right branch exceeds a point of
the left branch by at least the gap `g`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gap_le_sub_ifsMap (hα0 : 0 < α) {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1) :
    gap α ≤ ifsMap α true x - ifsMap α false y := by
  have hne : α ≠ 0 := hα0.ne'
  have key : ifsMap α true x - ifsMap α false y - gap α = (x + 1 - y) / α := by
    rw [ifsMap_true, ifsMap_false, gap]
    field_simp
    ring
  have h0 : (0 : ℝ) ≤ (x + 1 - y) / α := div_nonneg (by linarith) hα0.le
  linarith [key, h0]

/-- **M1 Lemma 1(ii)**: for `α > 2` the two branch images are disjoint. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem disjoint_image_ifsMap (h2 : 2 < α) :
    Disjoint (ifsMap α false '' Set.Icc (0 : ℝ) 1) (ifsMap α true '' Set.Icc (0 : ℝ) 1) := by
  have hα : (1 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have hgap : 0 < gap α := (gap_pos_iff hα0).mpr h2
  have hlt : α⁻¹ < (α - 1) / α := by
    have := sub_inv_eq_gap hα0.ne'
    linarith
  rw [image_ifsMap_false hα, image_ifsMap_true hα, Set.disjoint_left]
  rintro x ⟨-, hx1⟩ ⟨hy0, -⟩
  linarith

/-! ## Self-similarity of `piVal` -/

/-- The coding is the IFS read on words: `π(ε) = f_{ε₀}(π(σ ε))`.  This is M1 Lemma 1(i)
(and (v)) in the form the separation argument uses. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_eq_ifsMap (hα : 1 < α) (ε : ℕ → Bool) :
    piVal α ε = ifsMap α (ε 0) (piVal α (shift ε 1)) := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have h0 : shift ε 0 = ε := funext fun j => by simp [shift]
  have h := alpha_mul_tPart hα ε 0
  simp only [tPart, h0] at h
  by_cases hb : ε 0 = true
  · rw [hb, ifsMap_true, eq_div_iff hα0.ne']
    simp [dR, hb] at h
    linear_combination h
  · have hb' : ε 0 = false := by simpa using hb
    rw [hb', ifsMap_false, eq_div_iff hα0.ne']
    simp [dR, hb'] at h
    linear_combination h

/-- **M1 Lemma 1(ii)** on digits: a word beginning with `1` and a word beginning with `0`
have `π`-values at least the gap `g` apart. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gap_le_piVal_sub (hα : 1 < α) {ε ε' : ℕ → Bool} (h : ε 0 = true) (h' : ε' 0 = false) :
    gap α ≤ piVal α ε - piVal α ε' := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  rw [piVal_eq_ifsMap hα ε, piVal_eq_ifsMap hα ε', h, h']
  exact gap_le_sub_ifsMap hα0 (piVal_nonneg hα _) (piVal_le_one hα _)

/-! ## M1 Lemma 1(iv): strong separation -/

/-- The first `k` digits cancel exactly: if `ε` and `ε'` agree on `[0, k)` then
`π(ε) - π(ε') = α^{-k} (π(σᵏ ε) - π(σᵏ ε'))`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_sub_eq_pow_mul (hα : 1 < α) {ε ε' : ℕ → Bool} :
    ∀ k : ℕ, (∀ j < k, ε j = ε' j) →
      piVal α ε - piVal α ε' = (α⁻¹) ^ k * (piVal α (shift ε k) - piVal α (shift ε' k)) := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  intro k
  induction k with
  | zero =>
      intro _
      have h0 : ∀ δ : ℕ → Bool, shift δ 0 = δ := fun δ => funext fun j => by simp [shift]
      simp [h0]
  | succ k ih =>
      intro h
      have hk := ih fun j hj => h j (by omega)
      have he := alpha_mul_tPart hα ε k
      have he' := alpha_mul_tPart hα ε' k
      simp only [tPart] at he he'
      have hd : dR ε k = dR ε' k := by simp only [dR, h k (by omega)]
      rw [hd] at he
      have hsub : α * (piVal α (shift ε k) - piVal α (shift ε' k))
          = piVal α (shift ε (k + 1)) - piVal α (shift ε' (k + 1)) := by
        linear_combination he - he'
      have hstep : piVal α (shift ε k) - piVal α (shift ε' k)
          = α⁻¹ * (piVal α (shift ε (k + 1)) - piVal α (shift ε' (k + 1))) := by
        rw [← hsub, ← mul_assoc, inv_mul_cancel₀ hα0.ne', one_mul]
      rw [hk, hstep]
      ring

/-- **M1 Lemma 1(iv)**: two words that agree on their first `k` letters and differ at
letter `k` have `π`-values at least `g α^{-k}` apart.  For `α > 2` the right-hand side is
positive (`gap_pos_iff`), so `piVal` is injective and `C(α)` is a Cantor set with strong
separation; that is where `α > 2` is used. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gap_mul_le_abs_piVal_sub (hα : 1 < α) {ε ε' : ℕ → Bool} {k : ℕ}
    (hagree : ∀ j < k, ε j = ε' j) (hne : ε k ≠ ε' k) :
    gap α * (α⁻¹) ^ k ≤ |piVal α ε - piVal α ε'| := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hinv : (0 : ℝ) < (α⁻¹) ^ k := pow_pos (inv_pos.mpr hα0) k
  have hsplit := piVal_sub_eq_pow_mul hα k hagree
  have hs : ∀ δ : ℕ → Bool, shift δ k 0 = δ k := fun δ => by simp [shift]
  have key : gap α ≤ |piVal α (shift ε k) - piVal α (shift ε' k)| := by
    by_cases hb : ε k = true
    · have hb' : ε' k = false := by
        have : ε' k ≠ true := fun hh => hne (hb.trans hh.symm)
        simpa using this
      refine le_trans (gap_le_piVal_sub hα (ε := shift ε k) (ε' := shift ε' k)
        (by rw [hs]; exact hb) (by rw [hs]; exact hb')) (le_abs_self _)
    · have hb0 : ε k = false := by simpa using hb
      have hb' : ε' k = true := by
        have : ε' k ≠ false := fun hh => hne (hb0.trans hh.symm)
        simpa using this
      rw [abs_sub_comm]
      refine le_trans (gap_le_piVal_sub hα (ε := shift ε' k) (ε' := shift ε k)
        (by rw [hs]; exact hb') (by rw [hs]; exact hb0)) (le_abs_self _)
  calc gap α * (α⁻¹) ^ k = (α⁻¹) ^ k * gap α := by ring
  _ ≤ (α⁻¹) ^ k * |piVal α (shift ε k) - piVal α (shift ε' k)| :=
      mul_le_mul_of_nonneg_left key hinv.le
  _ = |piVal α ε - piVal α ε'| := by rw [hsplit, abs_mul, abs_of_pos hinv]

/-! ## M1 Lemma 1(i): the attractor, and the extreme values -/

/-- `b :: δ`: the word beginning with the letter `b` and continuing with `δ`. -/
def consW (b : Bool) (δ : ℕ → Bool) : ℕ → Bool := fun k => if k = 0 then b else δ (k - 1)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem consW_zero (b : Bool) (δ : ℕ → Bool) : consW b δ 0 = b := by simp [consW]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shift_consW (b : Bool) (δ : ℕ → Bool) : shift (consW b δ) 1 = δ := by
  funext k
  simp [shift, consW]

/-- **M1 Lemma 1(i)** on words: prefixing a letter is applying a branch,
`π(b :: δ) = f_b(π(δ))`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_consW (hα : 1 < α) (b : Bool) (δ : ℕ → Bool) :
    piVal α (consW b δ) = ifsMap α b (piVal α δ) := by
  rw [piVal_eq_ifsMap hα (consW b δ), consW_zero, shift_consW]

/-- **M1 Lemma 1(i)**: `C(α)` is the attractor of the IFS — it is exactly the union of its
two branch images. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cantorSet_eq_union (hα : 1 < α) :
    cantorSet α = ifsMap α false '' cantorSet α ∪ ifsMap α true '' cantorSet α := by
  ext x
  constructor
  · rintro ⟨ε, rfl⟩
    rw [piVal_eq_ifsMap hα ε]
    by_cases h : ε 0 = true
    · exact Or.inr ⟨piVal α (shift ε 1), ⟨_, rfl⟩, by rw [h]⟩
    · have h' : ε 0 = false := by simpa using h
      exact Or.inl ⟨piVal α (shift ε 1), ⟨_, rfl⟩, by rw [h']⟩
  · rintro (⟨_, ⟨δ, rfl⟩, rfl⟩ | ⟨_, ⟨δ, rfl⟩, rfl⟩)
    · exact ⟨consW false δ, by rw [piVal_consW hα]⟩
    · exact ⟨consW true δ, by rw [piVal_consW hα]⟩

/-- `π(0^∞) = 0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_const_false : piVal α (fun _ => false) = 0 := by
  simp [piVal, dR]

/-- `π(1^∞) = (α-1)·(α-1)⁻¹ = 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_const_true (hα : 1 < α) : piVal α (fun _ => true) = 1 := by
  have hne : α - 1 ≠ 0 := by linarith
  have h : ∀ k : ℕ, dR (fun _ => true) k * (α⁻¹) ^ (k + 1) = (α⁻¹) ^ (k + 1) := by
    intro k; simp [dR]
  rw [piVal, tsum_congr h, tsum_inv_pow_succ hα, mul_inv_cancel₀ hne]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cantorSet_subset_Icc (hα : 1 < α) : cantorSet α ⊆ Set.Icc 0 1 := by
  rintro _ ⟨ε, rfl⟩
  exact ⟨piVal_nonneg hα ε, piVal_le_one hα ε⟩

/-- **M1 Lemma 1(i)**: `min C(α) = 0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isLeast_cantorSet (hα : 1 < α) : IsLeast (cantorSet α) 0 :=
  ⟨⟨fun _ => false, piVal_const_false⟩, fun _ hx => (cantorSet_subset_Icc hα hx).1⟩

/-- **M1 Lemma 1(i)**: `max C(α) = 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isGreatest_cantorSet (hα : 1 < α) : IsGreatest (cantorSet α) 1 :=
  ⟨⟨fun _ => true, piVal_const_true hα⟩, fun _ hx => (cantorSet_subset_Icc hα hx).2⟩

/-! ## M1 Lemma 1(iii): `π` is a homeomorphism onto `C(α)` -/

/-- A single digit, as a real observable on `{0,1}^ℕ`: `Bool` is discrete, so any function
out of it is continuous. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_dR (m : ℕ) : Continuous fun δ : ℕ → Bool => dR δ m :=
  (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
    (continuous_apply m)

/-- The coding map is continuous: a uniformly convergent series of coordinate
observables. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_piVal (hα : 1 < α) : Continuous (piVal α) := by
  have hr0 : (0 : ℝ) ≤ α⁻¹ := (inv_pos_of_one_lt hα).le
  have hr1 : α⁻¹ < 1 := inv_lt_one_of_one_lt hα
  refine continuous_const.mul (continuous_tsum
    (fun k => (continuous_dR k).mul continuous_const)
    (summable_geom_succ hr0 hr1) fun k δ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dR_nonneg _ _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (α⁻¹) ^ (k + 1))]
  exact mul_le_of_le_one_left (by positivity) (dR_le_one _ _)

/-- **`C(α)` is compact** — a continuous image of `{0,1}^ℕ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isCompact_cantorSet (hα : 1 < α) : IsCompact (cantorSet α) :=
  isCompact_range (continuous_piVal hα)

/-- **M1 Lemma 1(iii)**, injectivity: two distinct words differ at a first index `k`, and
there Lemma 1(iv) separates their values by `g α^{-k} > 0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem injective_piVal (h2 : 2 < α) : Function.Injective (piVal α) := by
  have hα : (1 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have hgap : 0 < gap α := (gap_pos_iff hα0).mpr h2
  intro ε ε' heq
  by_contra hne
  have hex : ∃ k, ε k ≠ ε' k := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  have hspec : ε (Nat.find hex) ≠ ε' (Nat.find hex) := Nat.find_spec hex
  have hagree : ∀ j < Nat.find hex, ε j = ε' j := fun j hj => by
    simpa using Nat.find_min hex hj
  have hb := gap_mul_le_abs_piVal_sub hα hagree hspec
  rw [heq, sub_self, abs_zero] at hb
  nlinarith [pow_pos (inv_pos.mpr hα0) (Nat.find hex)]

/-- **M1 Lemma 1(iii)**: `π` is a homeomorphism of `{0,1}^ℕ` onto `C(α)` — a continuous
bijection from a compact space to a Hausdorff one.  Together with `tauMap_piVal` below
this is the topological conjugacy of `(C(α), τ_α)` with the one-sided full `2`-shift. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
noncomputable def piHomeomorph (h2 : 2 < α) : (ℕ → Bool) ≃ₜ cantorSet α :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective (piVal α) (injective_piVal h2))
    ((continuous_piVal (by linarith)).subtype_mk _)

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piHomeomorph_apply (h2 : 2 < α) (ε : ℕ → Bool) :
    (piHomeomorph h2 ε : ℝ) = piVal α ε := rfl

/-! ## M1 Lemma 1(iii): `C(α)` is Lebesgue-null -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_ifsMap (α : ℝ) (b : Bool) : Continuous (ifsMap α b) :=
  (continuous_id.add continuous_const).div_const α

open MeasureTheory in
/-- A branch of the IFS scales Lebesgue measure by `α⁻¹`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem volume_image_ifsMap (hα : 1 < α) (b : Bool) (s : Set ℝ) :
    volume (ifsMap α b '' s) = ENNReal.ofReal α⁻¹ * volume s := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hfun : ifsMap α b
      = (fun y : ℝ => y + α⁻¹ * ((α - 1) * (if b then 1 else 0)))
        ∘ (fun x : ℝ => α⁻¹ * x) := by
    funext x
    simp only [Function.comp_apply, ifsMap]
    field_simp
  have hmul : (fun x : ℝ => α⁻¹ * x) '' s = (fun x : ℝ => α * x) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxx : α * (α⁻¹ * x) = x := by field_simp
      simpa [hxx] using hx
    · intro hy
      exact ⟨α * y, hy, by field_simp⟩
  rw [hfun, Set.image_comp, hmul, Set.image_add_right, measure_preimage_add_right,
    Real.volume_preimage_mul_left hα0.ne', abs_of_pos (inv_pos.mpr hα0)]

open MeasureTheory in
/-- **M1 Lemma 1(iii)**, the measure statement: `Leb(C(α)) = 0` for `α > 2`.  The note
deduces it from `dim_H C(α) = log2/log α < 1`; no dimension theory is needed.  `C(α)` is
the *disjoint* union of two copies of itself scaled by `α⁻¹` (Lemma 1(i) and (ii)), so its
measure `v` obeys `v = 2α⁻¹ v` with `2α⁻¹ < 1` and `v < ∞`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem volume_cantorSet (h2 : 2 < α) : volume (cantorSet α) = 0 := by
  have hα : (1 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have hsub := cantorSet_subset_Icc hα
  have hfin : volume (cantorSet α) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hdisj : Disjoint (ifsMap α false '' cantorSet α) (ifsMap α true '' cantorSet α) :=
    Disjoint.mono (Set.image_mono hsub) (Set.image_mono hsub) (disjoint_image_ifsMap h2)
  have hmeas : MeasurableSet (ifsMap α true '' cantorSet α) :=
    ((isCompact_cantorSet hα).image (continuous_ifsMap α true)).isClosed.measurableSet
  have hsplit : volume (cantorSet α)
      = ENNReal.ofReal α⁻¹ * volume (cantorSet α)
        + ENNReal.ofReal α⁻¹ * volume (cantorSet α) := by
    nth_rewrite 1 [cantorSet_eq_union hα]
    rw [measure_union hdisj hmeas, volume_image_ifsMap hα, volume_image_ifsMap hα]
  have hterm : ENNReal.ofReal α⁻¹ * volume (cantorSet α) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hcast : (volume (cantorSet α)).toReal
      = α⁻¹ * (volume (cantorSet α)).toReal + α⁻¹ * (volume (cantorSet α)).toReal := by
    have h := congrArg ENNReal.toReal hsplit
    rwa [ENNReal.toReal_add hterm hterm, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_pos.mpr hα0).le] at h
  have hprod : α * α⁻¹ = 1 := mul_inv_cancel₀ hα0.ne'
  have hipos : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα0
  have hlt : 2 * α⁻¹ < 1 := by nlinarith
  have hz : (volume (cantorSet α)).toReal * (1 - 2 * α⁻¹) = 0 := by linear_combination hcast
  have hr0 : (volume (cantorSet α)).toReal = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · linarith
  exact ((ENNReal.toReal_eq_zero_iff _).mp hr0).resolve_right hfin

/-! ## M1 Lemma 1(v): the conjugacy with the one-sided full `2`-shift -/

/-- The expanding map `τ_α x = α x - (α-1) ε₁(x)` of M1 Lemma 1(v).  The first digit is
read off `x` by the threshold `(α-1)/α`, which is exactly the left endpoint of the right
branch; this is well defined on `C(α)` because the branches are separated (Lemma 1(ii)). -/
noncomputable def tauMap (α : ℝ) (x : ℝ) : ℝ :=
  α * x - (α - 1) * (if (α - 1) / α ≤ x then 1 else 0)

/-- **M1 Lemma 1(v)**: `π ∘ σ = τ_α ∘ π`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tauMap_piVal (h2 : 2 < α) (ε : ℕ → Bool) :
    tauMap α (piVal α ε) = piVal α (shift ε 1) := by
  have hα : (1 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have ht0 : 0 ≤ piVal α (shift ε 1) := piVal_nonneg hα _
  have ht1 : piVal α (shift ε 1) ≤ 1 := piVal_le_one hα _
  have hval := piVal_eq_ifsMap hα ε
  by_cases h : ε 0 = true
  · rw [h, ifsMap_true] at hval
    have hge : (α - 1) / α ≤ piVal α ε := by
      have hid : (piVal α (shift ε 1) + (α - 1)) / α - (α - 1) / α
          = piVal α (shift ε 1) / α := by ring
      have hnn := div_nonneg ht0 hα0.le
      rw [hval]
      linarith [hid]
    have hcond : (if (α - 1) / α ≤ piVal α ε then (1 : ℝ) else 0) = 1 := by
      simp only [hge, ite_true]
    rw [tauMap, hcond, hval]
    field_simp
    ring
  · have h' : ε 0 = false := by simpa using h
    rw [h', ifsMap_false] at hval
    have hgap : 0 < (α - 1) / α - piVal α ε := by
      have hid : (α - 1) / α - piVal α (shift ε 1) / α
          = (α - 1 - piVal α (shift ε 1)) / α := by ring
      rw [hval, hid]
      exact div_pos (by linarith) hα0
    have hno : ¬ (α - 1) / α ≤ piVal α ε := by linarith
    have hcond : (if (α - 1) / α ≤ piVal α ε then (1 : ℝ) else 0) = 0 := by
      simp only [hno, ite_false]
    rw [tauMap, hcond, hval]
    field_simp
    ring

/-- `τ_α` preserves `C(α)`: it is the shift read through the coding. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tauMap_mapsTo (h2 : 2 < α) : Set.MapsTo (tauMap α) (cantorSet α) (cantorSet α) := by
  rintro _ ⟨ε, rfl⟩
  rw [tauMap_piVal h2]
  exact ⟨shift ε 1, rfl⟩

end BB61
