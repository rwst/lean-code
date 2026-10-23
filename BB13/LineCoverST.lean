/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.FrameSystem
import QuantitativeSubspace.SubspaceCountTwo
import QuantitativeSubspace.ResultantHeights
import DiophantineApproximation.SubspaceReduction

/-!
# The line cover of Problem 10.13 from the explicit Subspace count (WP A2 of plan-beyond-BB13)

`BB13.failures_line_cover` puts the frame points `(mₙ2ⁿ, 3ⁿ)` of the failures
`‖(3/2)ⁿ‖ < (3/4)ⁿ`, `n ≥ 10`, on at most `K(ε*) ≈ 1.86·10¹²` lines through the origin, on the
authority of the cited axiom `BugeaudEvertse.ridout_line_cover` ([BE08] Cor. 5.2). This file
proves the same kind of statement **without any cited axiom**, from Subspace-Theorems' explicit
count in two variables (`NumberField.exists_finset_submodule_of_isNormalizedSystem_two`), applied
to the normalized system of `BB13/FrameSystem.lean`:

* the generalized Roth lemma is Evertse's (`NumberField.SubspaceRoth.evertse`, Ev96 Lemma 24),
  with Rémond's heights realized by resultant forms (`MvPolynomial.resultantHeight`), so that
  `h(ℙ¹) ≤ 2 (log 4 / 2 + 2) < 5.4`;
* every subspace of the cover is a proper subspace of `ℚ²`, hence `⊥` or a line, and the frame
  points have second coordinate `3ⁿ ≠ 0`, so each subspace contributes at most one slope
  `linePoint n = mₙ2ⁿ/3ⁿ` (`BB13.subspaceSlope`).

The number of lines is `BB13.lineCountST δ`, the sum of the small, middle and large terms of the
count at the frame (`H = 1`, `R = 3` distinct forms, `[K : ℚ] = [E : K] = 1`). Gate G-1
(`BB13/g1_count.py`) evaluates it at `≈ 3.78·10⁹` for `δ` near `ε*` and `≈ 3.86·10⁹` at
`δ = 13/50`, against the computational record `2³⁶ + 2³⁴ ≈ 8.59·10¹⁰` and `K(ε*)`. Certifying a
numerical upper bound for `lineCountST (13/50)` is WP A3.

## Main results

* `BB13.frameRoth`: Evertse's Roth lemma over `ℚ`, with resultant heights.
* `BB13.lineCountST`: the count at the frame.
* `BB13.failures_line_cover_ST`: for `0 < δ ≤ ε* − 1/1000`, the slopes of the failures `n ≥ 20`
  lie in a set of at most `lineCountST δ` rationals.
* `BB13.towersAbove_card_le_ST`: the same in counting form.

## References

* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. **101**
  (1996), Lemma 24.
* J.-H. Evertse, *On the Quantitative Subspace Theorem*, J. Math. Sci. **171** (2010), Thms 2.1,
  2.2.
* `plans/plan-beyond-BB13.html`, §3.4, WP A2.
-/

namespace BB13

open NumberField IsDedekindDomain Height Module

/-! ### The Roth lemma and the count -/

/-- **Evertse's generalized Roth lemma over `ℚ`**, with the multiprojective heights on `(ℙ¹)ᵐ`
given by resultant forms. -/
noncomputable def frameRoth : SubspaceRoth.{0} ℚ :=
  SubspaceRoth.evertse fun _ ↦
    MvPolynomial.resultantHeight (MvPolynomial.archEmbedded_of_numberField ℚ) Prod.fst_surjective

open scoped Classical in
/-- **The number of lines of the failures**, from the explicit count in two variables at the frame:
the small term `δ⁻¹((2·10³)² + 8 log log 4)`, the middle term
`1 + log(systemMiddleRatio)/log(1 + δ/4)` and the large term `systemLargeCountTwo`. -/
noncomputable def lineCountST (δ : ℝ) : ℝ :=
  δ⁻¹ * ((10 ^ 3 * 2) ^ 2 + 4 * 2 * Real.log (Real.log 4)) +
    (1 + Real.log (systemMiddleRatio 1 2 1 δ
        (systemThresholdTwo ℚ frameS (fun v ↦ v) frameForms frameRoth.toRothParams 3 1 δ)) /
      Real.log (1 + δ / 4)) +
    systemLargeCountTwo frameRoth.toRothParams 1 3 δ

/-! ### Proper subspaces of `ℚ²` and their slopes -/

open scoped Classical in
/-- The slope `v₀/v₁` of a subspace of `ℚ²`, read off any of its vectors with `v₁ ≠ 0` (`0` if
there is none). For a proper subspace it does not depend on the vector (`BB13.subspaceSlope_eq`). -/
noncomputable def subspaceSlope (U : Submodule ℚ (Fin 2 → ℚ)) : ℚ :=
  if h : ∃ v ∈ U, v 1 ≠ 0 then h.choose 0 / h.choose 1 else 0

/-- A proper subspace of `ℚ²` containing `x` with `x₁ ≠ 0` has slope `x₀/x₁`. -/
theorem subspaceSlope_eq {U : Submodule ℚ (Fin 2 → ℚ)} (hU : U ≠ ⊤) {x : Fin 2 → ℚ} (hx : x ∈ U)
    (hx1 : x 1 ≠ 0) : subspaceSlope U = x 0 / x 1 := by
  have h : ∃ v ∈ U, v 1 ≠ 0 := ⟨x, hx, hx1⟩
  rw [subspaceSlope, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hv, hv1⟩ := h.choose_spec
  have hlt : finrank ℚ U < finrank ℚ (Fin 2 → ℚ) := Submodule.finrank_lt hU
  rw [Module.finrank_fin_fun] at hlt
  obtain ⟨w, hw⟩ := finrank_le_one_iff.1 (Nat.lt_succ_iff.1 hlt)
  obtain ⟨a, ha⟩ := hw ⟨x, hx⟩
  obtain ⟨b, hb⟩ := hw ⟨h.choose, hv⟩
  have hxa : x = a • (w : Fin 2 → ℚ) := (congrArg Subtype.val ha).symm
  have hvb : h.choose = b • (w : Fin 2 → ℚ) := (congrArg Subtype.val hb).symm
  rw [hvb] at hv1 ⊢
  rw [hxa] at hx1 ⊢
  simp only [Pi.smul_apply, smul_eq_mul] at hv1 hx1 ⊢
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hx1
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hv1
  have hw1 : (w : Fin 2 → ℚ) 1 ≠ 0 := right_ne_zero_of_mul hx1
  field_simp

/-! ### The line cover -/

/-- **The failures `n ≥ 20` lie on at most `lineCountST δ` lines**, for every
`0 < δ ≤ ε* − 1/1000`: the slopes `linePoint n = mₙ2ⁿ/3ⁿ` lie in a set of at most
`lineCountST δ` rationals. The explicit two-variable count of Subspace-Theorems at the frame of
`BB13/FrameSystem.lean`, with Evertse's Roth lemma; no cited axiom. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_ST {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ epsStar - 1 / 1000) :
    ∃ R : Finset ℚ, (R.card : ℝ) ≤ lineCountST δ ∧
      ∀ n : ℕ, 20 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨T, hT, hTtop, hcov⟩ := exists_finset_submodule_of_isNormalizedSystem_two frameRoth
    (Fintype.card_fin 2) frameS (fun v ↦ v) (fun v ↦ AbsoluteValue.liesOver_self _)
    (fun v _ ↦ AbsoluteValue.liesOver_self _) (frameSystem_isNormalized hδ0 hδ)
  refine ⟨T.image subspaceSlope, (Nat.cast_le.2 Finset.card_image_le).trans
    (hT.trans (le_of_eq ?_)), fun n hn hnf ↦ ?_⟩
  · simp only [lineCountST, Fintype.card_fin, Module.finrank_self]
    norm_num
  · obtain ⟨U, hU, hxU⟩ := hcov _ (frame_mem_systemSet hδ0 hδ hn hnf)
    have hy : framePt n 1 ≠ 0 := by
      simp [framePt, (frameY_pos n).ne']
    refine Finset.mem_image.2 ⟨U, hU, ?_⟩
    rw [subspaceSlope_eq (hTtop U hU) hxU hy]
    simp [linePoint, framePt]

/-- **The failures `n ≥ 20` span at most `lineCountST δ` scaling families** —
`failures_line_cover_ST` in counting form. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem towersAbove_card_le_ST {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ epsStar - 1 / 1000) :
    ({r : ℚ | ∃ n : ℕ, 20 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard : ℝ)
      ≤ lineCountST δ := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ST hδ0 hδ
  have hsub : {r : ℚ | ∃ n : ℕ, 20 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r} ⊆ ↑R := by
    rintro r ⟨n, hn, hnf, rfl⟩; exact hR n hn hnf
  calc ({r : ℚ | ∃ n : ℕ, 20 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard : ℝ)
      ≤ ((↑R : Set ℚ).ncard : ℝ) := Nat.cast_le.2 (Set.ncard_le_ncard hsub R.finite_toSet)
    _ = R.card := by rw [Set.ncard_coe_finset]
    _ ≤ lineCountST δ := hcard

end BB13
