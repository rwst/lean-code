/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.ConjugacyMap
import ForMathlib.MeasureTheory.UltrametricMeasurePreserving
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bernstein–Lagarias — the metric conjugacy: `Φ` preserves Haar measure (BL96, §1)

Daniel J. Bernstein and Jeffrey C. Lagarias, *The 3x+1 conjugacy map*, Canadian Journal of
Mathematics **48** (1996), no. 6, 1154–1169.

This file upgrades the topological conjugacy `(1.3)` to a **metric** one: the explicit 3x+1 conjugacy
map `Φ` (`BL.ConjugacyMap.Φ`) is **measure-preserving** for the 2-adic (additive Haar) measure, so
`(ℤ₂, μ, T₂)` and `(ℤ₂, μ, S)` are isomorphic measure-preserving systems. Formerly the cited `axiom`
`BL.exists_metric_conjugacy` (in `BL.Basic`), it is now **proved**.

## The argument

`Φ` is already known to be **solenoidal** and **bijective** (`Φ_solenoidal`, `qMap_bijective`), hence
a **2-adic isometry** by Appendix A (`corollary_A3`): `‖Φ x − Φ y‖ = ‖x − y‖` (`Φ_isometry`). The
measure-preservation is then an instance of a general fact about ultrametric groups
(`ForMathlib/MeasureTheory/UltrametricMeasurePreserving.lean`,
`MeasureTheory.measurePreserving_of_surjective_isometry`):

> A continuous surjective isometry of a second-countable ultrametric normed additive group preserves
> every finite left-invariant measure.

The proof of that general lemma uses that in an ultrametric space the closed balls of positive radius
are clopen, form a topological basis (so they generate the Borel `σ`-algebra) and a `π`-system; a
finite left-invariant measure gives equal mass to balls of equal radius (translation invariance), and
a surjective isometry maps each ball onto a ball of the same radius, so it preserves the mass of every
ball, hence the whole measure (`π`-system uniqueness). No coset-counting or explicit value `μ(ball) =
2^{-n}` is needed — only that same-radius balls have *equal* measure.

This replaces the **Haar-pushforward analysis** that would otherwise be required: rather than computing
the pushforward `Φ_* μ` on cylinders directly, we exploit that `Φ` is a metric isometry.

## `T₂` is Bernoulli

With the metric conjugacy in hand, **`T₂` is Bernoulli** (`T₂_bernoulli`, moved here from `BL.Basic`
since it now depends on the downstream `exists_metric_conjugacy`): transport the Bernoulli structure of
the shift `S` (`S_bernoulli`, the cited [Kin09] p-adic digit fact) across the measure-preserving
conjugacy `Φ`. The conjugating equivalence `e ∘ Φ⁻¹` is measure-preserving and intertwines `T₂` with
the coordinate shift `seqShift`, because `Φ⁻¹ ∘ T₂ = S ∘ Φ⁻¹`.

## Contents
* `Φ_isometry` — `Φ` is a 2-adic isometry (`‖Φ x − Φ y‖ = ‖x − y‖`), from `corollary_A3`.
* `Φ_measurePreserving` — `Φ` preserves the 2-adic Haar measure (via the general ultrametric lemma).
* `exists_metric_conjugacy` — **(1.3) metric form, PROVED.** The conjugacy `Φ` is measure-preserving.
* `T₂_bernoulli` — **PROVED** (moved from `BL.Basic`): `T₂` is a Bernoulli system.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian Journal
  of Mathematics 48 (1996), no. 6, 1154–1169.
* [Kin09] Kingsbery, James, et al. *Dynamics of the `p`-adic shift and applications.* arXiv:0903.4226
  (2009) (the 2-adic shift is the one-sided Bernoulli `(½,½)` shift).
* [Lag85] Lagarias, Jeffrey C. *The 3x+1 problem and its generalizations.* American Mathematical
  Monthly 92 (1985), no. 1, 3–23.
-/

namespace BL

open PadicInt MeasureTheory

/-- `Φ` is a **2-adic isometry**: `‖Φ x − Φ y‖ = ‖x − y‖` for all `x, y` (equivalently `Isometry ⇑Φ`).
This is Appendix A's `corollary_A3` applied to `Φ`, which is solenoidal (`Φ_solenoidal`) and bijective
(`Φ.bijective`). -/
@[category API, AMS 37 11, ref "BL96"]
theorem Φ_isometry : Isometry (⇑Φ) := by
  have hiff := (corollary_A3 (⇑Φ)).out 0 2
  have hnorm : ∀ x y, ‖Φ x - Φ y‖ = ‖x - y‖ := hiff.mp ⟨Φ_solenoidal, Φ.bijective⟩
  exact Isometry.of_dist_eq fun x y => by rw [dist_eq_norm, dist_eq_norm]; exact hnorm x y

/-- **`Φ` is measure-preserving** for the 2-adic (additive Haar) measure. It is a continuous surjective
isometry (`Φ_isometry`, `Φ.continuous`, `Φ.surjective`), and such a map on the second-countable
ultrametric group `ℤ₂` preserves every finite left-invariant measure
(`MeasureTheory.measurePreserving_of_surjective_isometry`). -/
@[category research solved, AMS 37 28, ref "BL96", group "bl_conjugacy"]
theorem Φ_measurePreserving [MeasurableSpace ℤ_[2]] [BorelSpace ℤ_[2]]
    (μ : Measure ℤ_[2]) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] :
    MeasurePreserving (⇑Φ) μ μ :=
  measurePreserving_of_surjective_isometry μ Φ.continuous Φ_isometry Φ.surjective

/-- **(1.3), metric form — PROVED.** `T` is **metrically conjugate** to the shift `S`: the conjugacy
`Φ` of `(1.3)` is **measure-preserving** for the 2-adic measure, so `(ℤ₂, μ, T₂)` and `(ℤ₂, μ, S)` are
isomorphic measure-preserving systems. The witness is the explicit `Φ` (`Φ_semiconj`,
`Φ_measurePreserving`). Formerly a cited `axiom` in `BL.Basic`. -/
@[category research solved, AMS 37 28, ref "BL96", group "bl_conjugacy"]
theorem exists_metric_conjugacy [MeasurableSpace ℤ_[2]] [BorelSpace ℤ_[2]]
    (μ : Measure ℤ_[2]) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] :
    ∃ Φ : ℤ_[2] ≃ₜ ℤ_[2], Function.Semiconj (⇑Φ) S T₂ ∧ MeasurePreserving (⇑Φ) μ μ :=
  ⟨Φ, Φ_semiconj, Φ_measurePreserving μ⟩

/-- **(Bernstein–Lagarias 1996; PROVED from `S_bernoulli` + `exists_metric_conjugacy`.)** **`T` is
Bernoulli.** Transport the Bernoulli structure of the shift `S` (`S_bernoulli`, with conjugating
equivalence `e`) across the measure-preserving conjugacy `Φ` (`exists_metric_conjugacy`): the map
`e ∘ Φ⁻¹` conjugates `(T₂, μ)` to the Bernoulli shift. It is measure-preserving (a composite of
measure-preserving maps, `Φ⁻¹` being measure-preserving as the inverse of the measure-preserving
homeomorphism `Φ`), and it intertwines `T₂` with `seqShift` because `Φ⁻¹ ∘ T₂ = S ∘ Φ⁻¹` (a
rearrangement of `Φ ∘ S = T₂ ∘ Φ`). Moved here from `BL.Basic` with `exists_metric_conjugacy`. -/
@[category research solved, AMS 37 28, ref "BL96" "Lag85" "Kin09", group "bl_conjugacy"]
theorem T₂_bernoulli [MeasurableSpace ℤ_[2]] [BorelSpace ℤ_[2]]
    (μ : Measure ℤ_[2]) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] :
    IsBernoulli T₂ μ := by
  obtain ⟨Φ, hsc, hmp⟩ := exists_metric_conjugacy μ
  obtain ⟨e, he_mp, he_sc⟩ := S_bernoulli μ
  -- `Φ⁻¹` is measure-preserving (inverse of the measure-preserving equivalence `Φ`).
  have hΦsymm_mp : MeasurePreserving (⇑Φ.symm) μ μ := by
    have hmp' : MeasurePreserving (⇑Φ.toMeasurableEquiv) μ μ := by
      rw [Homeomorph.toMeasurableEquiv_coe]; exact hmp
    have hsymm : MeasurePreserving (⇑(Φ.toMeasurableEquiv).symm) μ μ :=
      MeasurePreserving.symm (Φ.toMeasurableEquiv) hmp'
    rwa [Homeomorph.toMeasurableEquiv_symm_coe] at hsymm
  refine ⟨(Φ.symm.toMeasurableEquiv).trans e, ?_, ?_⟩
  · -- `e ∘ Φ⁻¹ : μ → bernoulliSeqMeasure` is measure-preserving.
    rw [MeasurableEquiv.coe_trans, Homeomorph.toMeasurableEquiv_coe]
    exact he_mp.comp hΦsymm_mp
  · -- `e ∘ Φ⁻¹` intertwines `T₂` with `seqShift`.
    intro x
    have hkey : Φ.symm (T₂ x) = S (Φ.symm x) := by
      have h := hsc (Φ.symm x)
      rw [Φ.apply_symm_apply] at h
      rw [← h, Φ.symm_apply_apply]
    simp only [MeasurableEquiv.coe_trans, Homeomorph.toMeasurableEquiv_coe, Function.comp_apply]
    rw [hkey]
    exact he_sc (Φ.symm x)

end BL
