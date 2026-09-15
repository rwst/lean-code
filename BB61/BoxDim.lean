/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Criterion
import ForMathlib.Topology.MetricSpace.BoxDimension
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Lemma 1(iii), Lemma 3 and Corollary 5: the box dimensions

`BB61/Criterion.lean` proves M1 Corollary 5's *conclusion* — Route A fires whenever
`A(α) = log2/log α + log2/log(1/ρ)` is below one — with the dimension theory removed, by
running the covering engine along a ray.  This file states the dimensions themselves, on
`ForMathlib/Topology/MetricSpace/BoxDimension.lean`:

* `upperBoxDim_cantorSet` / `lowerBoxDim_cantorSet` — **M1 Lemma 1(iii)**, the box-dimension
  half: `dim_B C(α) = log 2 / log α` for `α > 2`, both the upper and the lower value, so the
  box dimension of `C(α)` exists.  The upper bound is the depth-`M` truncation cover
  (`abs_piVal_sub_tCand`), the lower bound the `2^M` words supported in `[0, M)`, separated
  by `g·α^{1-M}` (`gap_mul_le_abs_piVal_sub`).
* `upperBoxDim_windowSet_le` — **M1 Lemma 3**, `dim_B K ≤ log 2 / log(1/ρ)`, from the
  depth-`M'` truncation of the window series.
* `upperBoxDim_confSet_le` — **M1 Corollary 5**, `dim_B X(α) ≤ A(α)`, by subadditivity of
  the upper box dimension on difference sets (`Metric.upperBoxDim_sub_le`) applied to
  `X(α) = C(α) - K` (`confSet_eq`).
* `dimH_cantorSet_le` and `dimH_confSet_le` — the same two ceilings for Mathlib's Hausdorff
  dimension, through `Metric.dimH_le_upperBoxDim`.  For Corollary 5 that route is not a
  convenience but a necessity: `dim_H` is not subadditive on difference sets.  The Cantor
  ceiling is matched by a floor in `BB61/Hausdorff.lean`.
* `volume_confSet_eq_zero_of_routeAExponent_lt_one` and
  `confCircle_ne_univ_of_volume_confSet_eq_zero` — Corollary 5's route to Problem 10.61:
  `A(α) < 1 ⇒ Leb(X(α)) = 0 ⇒ X(α) ≠ 𝕋`.  This is a second, measure-theoretic proof of
  `confCircle_ne_univ_of_routeAExponent_lt_one`, which `BB61/Criterion.lean` obtains from an
  explicit missed interval instead.

The matching Hausdorff *floor*, and with it the equality `dim_H C(α) = log 2 / log α`, is
`BB61/Hausdorff.lean`: Mathlib has no iterated function systems, so the measure that the mass
distribution principle needs is built there by hand.  None of this is needed for
`Leb(C(α)) = 0`, which `BB61/Cantor.lean` gets from the self-similarity directly
(`volume_cantorSet`).

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M1.html` Lemma 1(iii), Lemma 3, Corollary 5.
-/

namespace BB61

open Metric MeasureTheory

open QuadSetup (extendW tCand_extendW sCand_extendW)

open scoped NNReal ENNReal Pointwise

/-! ## Two `ℝ≥0`-valued bridges -/

/-- An upper bound on `|x - y|` is an upper bound on `edist x y`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem edist_le_of_abs_le {x y : ℝ} {r : ℝ≥0} (h : |x - y| ≤ (r : ℝ)) :
    edist x y ≤ (r : ℝ≥0∞) := by
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal h

/-- A strict lower bound on `|x - y|` is a strict lower bound on `edist x y`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_edist_of_lt_abs {x y : ℝ} {r : ℝ≥0} (h : (r : ℝ) < |x - y|) :
    (r : ℝ≥0∞) < edist x y := by
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mpr h

section Cantor

variable {α : ℝ}

/-- The contraction ratio `α⁻¹` of the Cantor IFS, as a nonnegative real. -/
noncomputable def invNN (α : ℝ) : ℝ≥0 := Real.toNNReal α⁻¹

/-- The gap `g = (α-2)/α`, as a nonnegative real. -/
noncomputable def gapNN (α : ℝ) : ℝ≥0 := Real.toNNReal (gap α)

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_invNN (hα : 0 < α) : ((invNN α : ℝ≥0) : ℝ) = α⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.mpr hα.le)

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_gapNN (h2 : 2 < α) : ((gapNN α : ℝ≥0) : ℝ) = gap α :=
  Real.coe_toNNReal _ ((gap_pos_iff (by linarith)).mpr h2).le

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem invNN_pos (hα : 0 < α) : 0 < invNN α := by
  rw [← NNReal.coe_pos, coe_invNN hα]; exact inv_pos.mpr hα

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem invNN_lt_one (hα : 1 < α) : invNN α < 1 := by
  have h0 : (0 : ℝ) < α := lt_trans one_pos hα
  rw [← NNReal.coe_lt_coe, coe_invNN h0, NNReal.coe_one]
  exact inv_lt_one_of_one_lt hα

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gapNN_pos (h2 : 2 < α) : 0 < gapNN α := by
  rw [← NNReal.coe_pos, coe_gapNN h2]; exact (gap_pos_iff (by linarith)).mpr h2

/-! ## M1 Lemma 1(iii), upper bound: the truncation cover -/

/-- The `2^M` depth-`M` truncation values: the centres of the cover of `C(α)`. -/
noncomputable def tCandSet (α : ℝ) (M : ℕ) : Set ℝ :=
  Set.range fun w : Fin M → Bool => tCand α (extendW M w) M

/-- **M1 Lemma 1(iii), the cover.**  Truncating the Cantor series at depth `M` puts every
point of `C(α)` within `α^{-M}` of one of `2^M` values. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isCover_tCandSet (hα : 1 < α) (M : ℕ) :
    IsCover (invNN α ^ M) (cantorSet α) (tCandSet α M) := by
  have h0 : (0 : ℝ) < α := lt_trans one_pos hα
  rintro _ ⟨ε, rfl⟩
  refine ⟨tCand α (extendW M fun i : Fin M => ε i) M, ⟨_, rfl⟩, ?_⟩
  rw [tCand_extendW]
  refine edist_le_of_abs_le ?_
  rw [NNReal.coe_pow, coe_invNN h0]
  exact abs_piVal_sub_tCand hα ε M

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem encard_tCandSet_le (α : ℝ) (M : ℕ) : (tCandSet α M).encard ≤ 2 ^ M := by
  rw [tCandSet, ← Set.image_univ]
  refine (Set.encard_image_le _ _).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  norm_cast

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem externalCoveringNumber_cantorSet_le (hα : 1 < α) (M : ℕ) :
    externalCoveringNumber (invNN α ^ M) (cantorSet α) ≤ 2 ^ M :=
  (isCover_tCandSet hα M).externalCoveringNumber_le_encard.trans (encard_tCandSet_le α M)

/-- **M1 Lemma 1(iii), upper bound**: `dim_B C(α) ≤ log 2 / log α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem upperBoxDim_cantorSet_le (hα : 1 < α) :
    upperBoxDim (cantorSet α) ≤ ((Real.log 2 / Real.log α : ℝ) : EReal) := by
  have h0 : (0 : ℝ) < α := lt_trans one_pos hα
  have h := upperBoxDim_le_of_covering_nat (A := cantorSet α) (r := invNN α) (C := 1) (k := 2)
    (invNN_pos h0) (invNN_lt_one hα) (by norm_num) fun n => by
      simpa using externalCoveringNumber_cantorSet_le hα n
  rw [coe_invNN h0, inv_inv] at h
  simpa using h

/-! ## M1 Lemma 1(iii), lower bound: the separated words -/

/-- The `2^M` points of `C(α)` whose digit word is supported in `[0, M)`. -/
noncomputable def cantorPoints (α : ℝ) (M : ℕ) : Set ℝ :=
  Set.range fun w : Fin M → Bool => piVal α (extendW M w)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cantorPoints_subset (α : ℝ) (M : ℕ) : cantorPoints α M ⊆ cantorSet α := by
  rintro _ ⟨w, rfl⟩
  exact ⟨_, rfl⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_pow_le_encard_cantorPoints (h2 : 2 < α) (M : ℕ) :
    (2 : ℕ∞) ^ M ≤ (cantorPoints α M).encard := by
  have hinj : Function.Injective fun w : Fin M → Bool => piVal α (extendW M w) := by
    intro w w' hww
    have he : extendW M w = extendW M w' := injective_piVal h2 hww
    funext i
    have := congrFun he (i : ℕ)
    simpa [extendW, i.2] using this
  have h := hinj.encard_range
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact le_trans (by norm_cast) h

/-- **M1 Lemma 1(iv), separation form.**  The `2^M` points of `cantorPoints α M` are pairwise
`g·α^{-M}` apart, in the strict sense the packing bound wants. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isSeparated_cantorPoints (h2 : 2 < α) (M : ℕ) :
    IsSeparated ((gapNN α * invNN α ^ M : ℝ≥0) : ℝ≥0∞) (cantorPoints α M) := by
  classical
  have h0 : (0 : ℝ) < α := by linarith
  have hα : (1 : ℝ) < α := by linarith
  have hg : 0 < gap α := (gap_pos_iff h0).mpr h2
  have hinv : (0 : ℝ) < α⁻¹ := inv_pos.mpr h0
  have hinv1 : α⁻¹ < 1 := inv_lt_one_of_one_lt hα
  rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ hxy
  set e := extendW M w with hedef
  set e' := extendW M w' with he'def
  have hne : ∃ j, e j ≠ e' j := by
    by_contra hcon
    push Not at hcon
    exact hxy (congrArg _ (funext hcon))
  have hkne : e (Nat.find hne) ≠ e' (Nat.find hne) := Nat.find_spec hne
  have hagree : ∀ j < Nat.find hne, e j = e' j := fun j hj => not_not.mp (Nat.find_min hne hj)
  have htail : ∀ j, ¬ j < M → e j = e' j := fun j hj => by
    simp [hedef, he'def, extendW, hj]
  have hkM : Nat.find hne < M := by
    by_contra hcon
    exact hkne (htail _ hcon)
  refine lt_edist_of_lt_abs ?_
  rw [NNReal.coe_mul, NNReal.coe_pow, coe_gapNN h2, coe_invNN h0]
  calc gap α * (α⁻¹) ^ M ≤ gap α * (α⁻¹) ^ (Nat.find hne + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hinv.le hinv1.le hkM) hg.le
    _ < gap α * (α⁻¹) ^ Nat.find hne := by
        refine mul_lt_mul_of_pos_left ?_ hg
        calc (α⁻¹) ^ (Nat.find hne + 1) = (α⁻¹) ^ Nat.find hne * α⁻¹ := pow_succ _ _
          _ < (α⁻¹) ^ Nat.find hne * 1 :=
              mul_lt_mul_of_pos_left hinv1 (pow_pos hinv _)
          _ = (α⁻¹) ^ Nat.find hne := mul_one _
    _ ≤ |piVal α e - piVal α e'| := gap_mul_le_abs_piVal_sub hα hagree hkne

/-- **M1 Lemma 1(iii), lower bound**: `log 2 / log α ≤ dim_B C(α)`, for the lower box
dimension already. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem le_lowerBoxDim_cantorSet (h2 : 2 < α) :
    ((Real.log 2 / Real.log α : ℝ) : EReal) ≤ lowerBoxDim (cantorSet α) := by
  have h0 : (0 : ℝ) < α := by linarith
  have hα : (1 : ℝ) < α := by linarith
  have h := le_lowerBoxDim_of_separated (A := cantorSet α) (r := invNN α) (c := gapNN α)
    (k := 2) (S := cantorPoints α) (invNN_pos h0) (invNN_lt_one hα) (gapNN_pos h2) (by norm_num)
    (cantorPoints_subset α) (isSeparated_cantorPoints h2) (two_pow_le_encard_cantorPoints h2)
  rw [coe_invNN h0, inv_inv] at h
  simpa using h

/-- **M1 Lemma 1(iii)**, the box-dimension half: the box dimension of `C(α)` exists and
equals `log 2 / log α`, which is `< 1` exactly because `α > 2`.  What stays out of reach is
the equality with the Hausdorff dimension, which `BB61/Hausdorff.lean` supplies. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem upperBoxDim_cantorSet (h2 : 2 < α) :
    upperBoxDim (cantorSet α) = ((Real.log 2 / Real.log α : ℝ) : EReal) :=
  le_antisymm (upperBoxDim_cantorSet_le (by linarith))
    ((le_lowerBoxDim_cantorSet h2).trans (lowerBoxDim_le_upperBoxDim _))

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lowerBoxDim_cantorSet (h2 : 2 < α) :
    lowerBoxDim (cantorSet α) = ((Real.log 2 / Real.log α : ℝ) : EReal) :=
  le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans (upperBoxDim_cantorSet h2).le)
    (le_lowerBoxDim_cantorSet h2)

/-- `dim_B C(α) < 1`: the numerical content of M1 Lemma 1(iii). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem upperBoxDim_cantorSet_lt_one (h2 : 2 < α) : upperBoxDim (cantorSet α) < 1 := by
  rw [upperBoxDim_cantorSet h2, ← EReal.coe_one, EReal.coe_lt_coe_iff,
    div_lt_one (Real.log_pos (by linarith))]
  exact Real.log_lt_log two_pos h2

/-- **M1 Lemma 1(iii)**, the Hausdorff *upper* bound: `dim_H C(α) ≤ log 2 / log α`, through
`Metric.dimH_le_upperBoxDim` and the truncation cover.  The matching lower bound is the half
that needs a measure carried by `C(α)`; it is `BB61/Hausdorff.lean`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dimH_cantorSet_le (hα : 1 < α) :
    (dimH (cantorSet α) : EReal) ≤ ((Real.log 2 / Real.log α : ℝ) : EReal) :=
  (dimH_le_upperBoxDim (A := cantorSet α) ⟨_, ⟨fun _ => false, rfl⟩⟩).trans
    (upperBoxDim_cantorSet_le hα)

end Cantor

namespace QuadSetup

variable (P : QuadSetup)

/-! ## M1 Lemma 3: the box dimension of the window -/

/-- The contraction ratio `ρ = |β|` of the window, as a nonnegative real. -/
noncomputable def rhoNN : ℝ≥0 := Real.toNNReal |P.β|

/-- The window's tail constant `(1+ρ)/(1-ρ)`, as a nonnegative real. -/
noncomputable def winConst : ℝ≥0 := Real.toNNReal ((1 + |P.β|) / (1 - |P.β|))

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_rhoNN : ((P.rhoNN : ℝ≥0) : ℝ) = |P.β| := Real.coe_toNNReal _ (abs_nonneg _)

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coe_winConst : ((P.winConst : ℝ≥0) : ℝ) = (1 + |P.β|) / (1 - |P.β|) := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  exact Real.coe_toNNReal _ (by positivity)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem rhoNN_lt_one : P.rhoNN < 1 := by
  rw [← NNReal.coe_lt_coe, coe_rhoNN, NNReal.coe_one]
  exact P.abs_beta_lt_one

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem rhoNN_pos (hβ : P.β ≠ 0) : 0 < P.rhoNN := by
  rw [← NNReal.coe_pos, coe_rhoNN]
  exact abs_pos.mpr hβ

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem winConst_pos : 0 < P.winConst := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  rw [← NNReal.coe_pos, coe_winConst]
  positivity

/-- **M1 Lemma 3, the tail estimate.**  Truncating the window series at depth `M'` costs at
most `(1+ρ)ρ^{M'}/(1-ρ)`.  This is `abs_sPart_sub_sCand` for the whole window `K` rather
than for the finite sums `S_n` that live in it. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_wVal_sub_sCand (δ : ℕ → Bool) (M' : ℕ) :
    |P.wVal δ - P.sCand δ M'| ≤ (1 + |P.β|) / (1 - |P.β|) * |P.β| ^ M' := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  have hf : Summable fun m : ℕ => P.cCoef m * dR δ m := P.summable_cCoef δ
  have hsplit := hf.sum_add_tsum_nat_add M'
  have hcand : P.sCand δ M' = ∑ m ∈ Finset.range M', P.cCoef m * dR δ m :=
    Finset.sum_congr rfl fun m _ => by rw [cCoef, mul_assoc]
  have hdiff : P.wVal δ - P.sCand δ M' = ∑' i : ℕ, P.cCoef (i + M') * dR δ (i + M') := by
    rw [wVal, hcand, ← hsplit]; ring
  have hbound : ∀ i : ℕ, |P.cCoef (i + M') * dR δ (i + M')|
      ≤ (1 + |P.β|) * |P.β| ^ M' * |P.β| ^ i := by
    intro i
    rw [abs_mul]
    have h2 : |dR δ (i + M')| ≤ 1 := by
      rw [abs_of_nonneg (dR_nonneg _ _)]; exact dR_le_one _ _
    calc |P.cCoef (i + M')| * |dR δ (i + M')|
        ≤ ((1 + |P.β|) * |P.β| ^ (i + M')) * 1 :=
          mul_le_mul (P.abs_cCoef_le _) h2 (abs_nonneg _) (by positivity)
      _ = (1 + |P.β|) * |P.β| ^ M' * |P.β| ^ i := by rw [mul_one, pow_add]; ring
  have hgeo : Summable fun i : ℕ => (1 + |P.β|) * |P.β| ^ M' * |P.β| ^ i :=
    (summable_geometric_of_lt_one hβ0 hβ).mul_left _
  have habs : Summable fun i : ℕ => |P.cCoef (i + M') * dR δ (i + M')| :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) hbound hgeo
  rw [hdiff]
  calc |∑' i : ℕ, P.cCoef (i + M') * dR δ (i + M')|
      ≤ ∑' i : ℕ, |P.cCoef (i + M') * dR δ (i + M')| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun i : ℕ => P.cCoef (i + M') * dR δ (i + M'))
          (by simpa [Real.norm_eq_abs] using habs)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' i : ℕ, (1 + |P.β|) * |P.β| ^ M' * |P.β| ^ i := habs.tsum_le_tsum hbound hgeo
    _ = (1 + |P.β|) * |P.β| ^ M' * (1 - |P.β|)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ]
    _ = (1 + |P.β|) / (1 - |P.β|) * |P.β| ^ M' := by field_simp

/-- The `2^{M'}` depth-`M'` truncation values of the window series. -/
noncomputable def sCandSet (M' : ℕ) : Set ℝ :=
  Set.range fun w : Fin M' → Bool => P.sCand (extendW M' w) M'

/-- **M1 Lemma 3, the cover**: `2^{M'}` intervals of radius `(1+ρ)ρ^{M'}/(1-ρ)` cover `K`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isCover_sCandSet (M' : ℕ) :
    IsCover (P.winConst * P.rhoNN ^ M') P.windowSet (P.sCandSet M') := by
  rintro _ ⟨δ, rfl⟩
  refine ⟨P.sCand (extendW M' fun i : Fin M' => δ i) M', ⟨_, rfl⟩, ?_⟩
  rw [sCand_extendW]
  refine edist_le_of_abs_le ?_
  rw [NNReal.coe_mul, NNReal.coe_pow, coe_winConst, coe_rhoNN]
  exact P.abs_wVal_sub_sCand δ M'

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem encard_sCandSet_le (M' : ℕ) : (P.sCandSet M').encard ≤ 2 ^ M' := by
  rw [sCandSet, ← Set.image_univ]
  refine (Set.encard_image_le _ _).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  norm_cast

/-- **M1 Lemma 3**: `dim_B K ≤ log 2 / log(1/ρ)`.  The hypothesis `β ≠ 0` excludes the
degenerate integer case, where `ρ = 0` and the right-hand side is Lean's junk value (which
here happens to be the true dimension `0`, `K` being finite). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem upperBoxDim_windowSet_le (hβ : P.β ≠ 0) :
    upperBoxDim P.windowSet ≤ ((Real.log 2 / Real.log |P.β|⁻¹ : ℝ) : EReal) := by
  have h := upperBoxDim_le_of_covering_mul_nat (A := P.windowSet) (r := P.rhoNN)
    (c := P.winConst) (C := 1) (k := 2) (P.rhoNN_pos hβ) P.rhoNN_lt_one P.winConst_pos
    (by norm_num) fun n => by
      simpa using (P.isCover_sCandSet n).externalCoveringNumber_le_encard.trans
        (P.encard_sCandSet_le n)
  rw [coe_rhoNN] at h
  simpa using h

/-! ## M1 Corollary 5: the Route A ceiling -/

/-- `X(α) = C(α) - K` as a pointwise difference of sets. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confSet_eq_sub : P.confSet = cantorSet P.α - P.windowSet := P.confSet_eq

/-- **M1 Corollary 5**: `dim_B X(α) ≤ A(α) = log2/log α + log2/log(1/ρ)`.  The upper box
dimension is subadditive on difference sets, so this is Lemma 1(iii) plus Lemma 3. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem upperBoxDim_confSet_le (h2 : 2 < P.α) (hβ : P.β ≠ 0) :
    upperBoxDim P.confSet ≤ ((P.routeAExponent : ℝ) : EReal) := by
  have hC : (cantorSet P.α).Nonempty := ⟨_, ⟨fun _ => false, rfl⟩⟩
  have hK : P.windowSet.Nonempty := ⟨_, ⟨fun _ => false, rfl⟩⟩
  rw [confSet_eq_sub, routeAExponent, EReal.coe_add]
  exact (upperBoxDim_sub_le hC hK).trans
    (add_le_add (upperBoxDim_cantorSet_le (by linarith)) (P.upperBoxDim_windowSet_le hβ))

/-- **M1 Corollary 5**, Hausdorff form: `dim_H X(α) ≤ A(α)`.  This *has* to go through the box
dimension: unlike `dim_B`, the Hausdorff dimension is not subadditive on difference sets, so
`dim_H X ≤ dim_H C(α) + dim_H K` is not available and would in any case be no help. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dimH_confSet_le (h2 : 2 < P.α) (hβ : P.β ≠ 0) :
    (dimH P.confSet : EReal) ≤ ((P.routeAExponent : ℝ) : EReal) :=
  (dimH_le_upperBoxDim (A := P.confSet) ⟨_, ⟨fun _ => false, rfl⟩⟩).trans
    (P.upperBoxDim_confSet_le h2 hβ)

/-- **M1 Corollary 5**, first consequence: `A(α) < 1` forces `Leb(X(α)) = 0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem volume_confSet_eq_zero_of_routeAExponent_lt_one (h2 : 2 < P.α) (hβ : P.β ≠ 0)
    (h : P.routeAExponent < 1) : volume P.confSet = 0 :=
  Real.volume_eq_zero_of_upperBoxDim_lt_one
    (lt_of_le_of_lt (P.upperBoxDim_confSet_le h2 hβ) (by exact_mod_cast h))

/-- **M1 Corollary 5**, second consequence: a null confinement set cannot cover the circle.
Compactness bounds `X(α)` inside `[-N, N]`, so its `2N+2` integer translates would have to
cover `[0,1)`, of measure one. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_ne_univ_of_volume_confSet_eq_zero (h : volume P.confSet = 0) :
    P.confCircle ≠ Set.univ := by
  intro hu
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ y ∈ P.confSet, |y| ≤ (N : ℝ) := by
    obtain ⟨R, hR⟩ := P.isCompact_confSet.isBounded.subset_closedBall 0
    refine ⟨⌈R⌉₊, fun y hy => ?_⟩
    have := mem_closedBall_zero_iff.mp (hR hy)
    rw [Real.norm_eq_abs] at this
    exact this.trans (Nat.le_ceil R)
  have hcov : Set.Ico (0 : ℝ) 1 ⊆
      ⋃ k ∈ Finset.Icc (-(N : ℤ)) (N + 1), (fun x : ℝ => x + (k : ℝ)) '' P.confSet := by
    intro x hx
    obtain ⟨ω, hω⟩ : ((x : ℝ) : AddCircle (1 : ℝ)) ∈ P.confCircle := by rw [hu]; trivial
    have hfr : Int.fract (P.fRaw ω) = x := by
      rw [fract_eq_of_coe_eq hω, Int.fract_eq_self.mpr ⟨hx.1, hx.2⟩]
    have hy : P.fRaw ω ∈ P.confSet := ⟨ω, rfl⟩
    have habs : |P.fRaw ω| ≤ (N : ℝ) := hN _ hy
    have hub : ⌊P.fRaw ω⌋ ≤ (N : ℤ) := by
      have h1 : P.fRaw ω ≤ ((N : ℤ) : ℝ) := by
        push_cast; exact (le_abs_self _).trans habs
      simpa using Int.floor_mono h1
    have hlb : -(N : ℤ) ≤ ⌊P.fRaw ω⌋ := by
      refine Int.le_floor.mpr ?_
      push_cast
      linarith [neg_abs_le (P.fRaw ω)]
    refine Set.mem_iUnion₂.mpr ⟨-⌊P.fRaw ω⌋, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      ⟨P.fRaw ω, hy, ?_⟩⟩
    show P.fRaw ω + ((-⌊P.fRaw ω⌋ : ℤ) : ℝ) = x
    push_cast
    rw [← hfr, Int.fract]
    ring
  have hle : volume (Set.Ico (0 : ℝ) 1)
      ≤ ∑ k ∈ Finset.Icc (-(N : ℤ)) (N + 1),
          volume ((fun x : ℝ => x + (k : ℝ)) '' P.confSet) :=
    (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
  have hzero : ∀ k : ℤ, volume ((fun x : ℝ => x + (k : ℝ)) '' P.confSet) = 0 := by
    intro k
    rw [Set.image_add_right, measure_preimage_add_right, h]
  rw [Real.volume_Ico] at hle
  simp only [hzero, Finset.sum_const, smul_zero] at hle
  norm_num at hle

/-- **M1 Corollary 5**, the note's route to Problem 10.61: `A(α) < 1` forces `Leb(X(α)) = 0`,
hence `X(α) ≠ 𝕋`.  This reproves `confCircle_ne_univ_of_routeAExponent_lt_one`, which
`BB61/Criterion.lean` obtains from an explicit missed interval instead. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_ne_univ_of_routeAExponent_lt_one' (h2 : 2 < P.α) (hβ : P.β ≠ 0)
    (h : P.routeAExponent < 1) : P.confCircle ≠ Set.univ :=
  P.confCircle_ne_univ_of_volume_confSet_eq_zero
    (P.volume_confSet_eq_zero_of_routeAExponent_lt_one h2 hβ h)

end QuadSetup

end BB61
