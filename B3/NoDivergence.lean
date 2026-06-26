/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.AutomaticParityVectors
import B3.NonConfinement
import B3.InfinitePlaceFactor
import B3.PhiRate
import B3.StammeringApproximants
import BL.ConjugacyMap
import L90.DivergentAperiodic
import B3.DigitPeriodicity
import ForMathlib.NumberTheory.RatPadicFinitePlace
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The no-divergence capstone: no divergent trajectory has an automatic parity vector

## References
* [Lag90] Lagarias, Jeffrey C. *The set of rational cycles for the `3x+1` problem.* Acta Arithmetica 56
  (1990), 33–53 (**Corollary 2.1b**: a divergent trajectory has an aperiodic parity sequence — the
  connector axiom; **Theorem 2.1**: the explicit periodic point `x(v) = (2ⁿ − 3^{Σ vⱼ})⁻¹ Σ vⱼ 3^{…} 2ʲ`).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the parity-vector map, divergent trajectories, the Periodicity Conjecture).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6: the `p`-adic stammering transcendence criterion — the template).
* [Sch77] Schlickewei, Hans Peter. *The `p`-adic Thue–Siegel–Roth–Schmidt theorem.* Arch. Math. (Basel)
  29 (1977), 267–270 (the `p`-adic Subspace Theorem behind the criterion).
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311 (the quantitative Subspace form used in the reduction).
-/

namespace B3

open BL AB Function Filter Height Height.AdmissibleAbsValues
open scoped Classical

/-! ### The `Φ`-side Missing Lemma: transcendence of the `Φ`-image -/

open NumberField IsDedekindDomain in
/-- There is an archimedean absolute value `vinf` that is the
*unique* archimedean place of `ℚ` (Ostrowski), distinct from the `2`-adic place, with
`Rat.AbsoluteValue.padic 2` a finite place (`Rat.HeightOneSpectrum.isFinitePlace_padic`, from
`ForMathlib`), and which is the standard absolute value `vinf q = |q|` (`Rat.infinitePlace_apply`). This
supplies the place-set hypotheses `hS_inf`/`hS_place` of `AB.subspace_theorem_E` for `S = {vinf, padic 2}`,
and the `hvinf` characterization that `B3.sup_vinf_placePoint_eq_mulHeight` (Tier 2.1) needs to identify
`⨆ⱼ vinf(xⱼ)` with the height `H(x)`. -/
@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem rat_arch_padic_places : ∃ vinf : AbsoluteValue ℚ ℝ,
    (∀ w ∈ archAbsVal (K := ℚ), w = vinf) ∧ vinf ∈ archAbsVal (K := ℚ) ∧
      Rat.AbsoluteValue.padic 2 ∈ nonarchAbsVal (K := ℚ) ∧ vinf ≠ Rat.AbsoluteValue.padic 2 ∧
      (∀ q : ℚ, vinf q = ((|q| : ℚ) : ℝ)) := by
  refine ⟨(Rat.infinitePlace : InfinitePlace ℚ).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [show (archAbsVal (K := ℚ)) = multisetInfinitePlace ℚ from rfl,
      mem_multisetInfinitePlace] at hw
    obtain ⟨wp, rfl⟩ := (isInfinitePlace_iff w).mp hw
    ext x
    exact (Rat.infinitePlace_apply _ x).trans (Rat.infinitePlace_apply _ x).symm
  · rw [show (archAbsVal (K := ℚ)) = multisetInfinitePlace ℚ from rfl, mem_multisetInfinitePlace]
    exact (Rat.infinitePlace : InfinitePlace ℚ).isInfinitePlace
  · exact Rat.HeightOneSpectrum.isFinitePlace_padic 2
  · intro h
    have h2 : ((Rat.infinitePlace : InfinitePlace ℚ).1) (2 : ℚ)
        = Rat.AbsoluteValue.padic 2 (2 : ℚ) := by rw [h]
    rw [show ((Rat.infinitePlace : InfinitePlace ℚ).1) (2 : ℚ)
          = (Rat.infinitePlace : InfinitePlace ℚ) (2 : ℚ) from (InfinitePlace.coe_apply _ _).symm,
      Rat.infinitePlace_apply, Rat.AbsoluteValue.padic_eq_padicNorm] at h2
    rw [show padicNorm 2 (2 : ℚ) = 2⁻¹ by simp [padicNorm, padicValRat, padicValInt, padicValNat]] at h2
    norm_num at h2
  · intro q
    rw [show ((Rat.infinitePlace : InfinitePlace ℚ).1 q) = (Rat.infinitePlace : InfinitePlace ℚ) q from rfl,
      Rat.infinitePlace_apply]

/-- *If `v` is automatic and irrational, then `Φ v ≠ n` for every `n ∈ ℕ`*. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96" "Sch77", group "b3_missing_lemma"]
theorem phi_ne_natCast (v : ℤ_[2]) (hauto : IsAutomatic2Adic v) (hirr : v ∉ RatInt)
    (n : ℕ) : Φ v ≠ (n : ℤ_[2]) := by
  intro hv
  obtain ⟨w, hw, hCS⟩ := binaryDigit_isStammering v hauto hirr
  obtain ⟨α, N, hNtend, hRat, hbound, htend, hαrat⟩ := conditionStar_tooWellApproximated hv hw hCS
  choose q hq using hRat
  set D : ℕ → ℤ := fun m => ((q m).den : ℤ) with hD_def
  set P : ℕ → ℤ := fun m => -(q m).num with hP_def
  obtain ⟨vinf, hvuniq, hvarch, hpadic, hvne, hvabs⟩ := rat_arch_padic_places
  set S : Finset (AbsoluteValue ℚ ℝ) := {vinf, Rat.AbsoluteValue.padic 2} with hS_def
  have hodd : ∀ k, Odd (D k) := fun k => ratInt_odd_den (q k) (hq k)
  have hrel : ∀ k, (D k : ℚ) * q k = -(P k : ℚ) := by
    intro k; simp only [hD_def, hP_def]; push_cast; rw [mul_comm, Rat.mul_den_eq_num]; ring
  have heq : ∀ k, Rat.AbsoluteValue.padic 2 ((n : ℚ) - q k) = ‖((n : ℕ) : ℤ_[2]) - Φ (α k)‖ := by
    intro k
    rw [padicTwo_eq_norm]
    have hcast : (((n : ℚ) - q k : ℚ) : ℚ_[2]) = ((((n : ℕ) : ℤ_[2]) - Φ (α k) : ℤ_[2]) : ℚ_[2]) := by
      push_cast; rw [← hq k]
    rw [hcast, PadicInt.padic_norm_e_of_padicInt]
  have hconv : Tendsto (fun k => Rat.AbsoluteValue.padic 2 ((n : ℚ) - q k)) atTop (nhds 0) := by
    apply htend.congr; intro k; exact (heq k).symm
  have hdist : ∀ k, q k ≠ (n : ℚ) := by
    intro k hqn
    have hΦeq : Φ (α k) = Φ v := PadicInt.ext (by rw [hq k, hqn, hv]; norm_cast)
    exact hirr (Φ.injective hΦeq ▸ hαrat k)
  have hncf : ¬ Confinable (fun k => placePoint (D k : ℚ) (P k : ℚ)) :=
    phiPoints_nonConfined (n : ℤ) D P q hodd hrel hconv hdist
  refine subspace_contradiction_of_rate_sharp_frequently (m := 3) (by norm_num) S ?_ ?_
    (phiForms (n : ℤ)) ?_ (1 / 2 : ℝ) (by norm_num) (by norm_num)
    (fun k => placePoint (D k : ℚ) (P k : ℚ)) ?_ N ?_ ?_ ?_ hncf
  · intro u hu; rw [hvuniq u hu]; simp [hS_def]
  · intro u hu
    simp only [hS_def, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Or.inl hvarch
    · exact Or.inr hpadic
  · intro u hu
    simp only [hS_def, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · show LinearIndependent ℚ (phiForms (n : ℤ) u)
      rw [show phiForms (n : ℤ) u = coordForms from if_neg hvne]
      exact coordForms_linearIndependent
    · show LinearIndependent ℚ (phiForms (n : ℤ) (Rat.AbsoluteValue.padic 2))
      rw [show phiForms (n : ℤ) (Rat.AbsoluteValue.padic 2) = placeForms (n : ℤ) from if_pos rfl]
      exact placeForms_linearIndependent (n : ℤ)
  · intro k hk
    have := congrFun hk 1
    simp [placePoint] at this
  · intro k
    exact mulHeight_placePoint_pos (D k) (P k)
  · intro k
    have hDunit : Rat.AbsoluteValue.padic 2 ((D k : ℤ) : ℚ) = 1 := padicTwo_odd_eq_one (D k) (hodd k)
    have hPle : Rat.AbsoluteValue.padic 2 ((P k : ℤ) : ℚ) ≤ 1 := padicTwo_intCast_le_one (P k)
    have hbnd : ‖((n : ℤ) : ℤ_[2]) - Φ (α k)‖ ≤ (2 : ℝ) ^ (-(N k : ℤ)) := by
      rw [Int.cast_natCast]; exact hbound k
    have h2 : (∏ i, Rat.AbsoluteValue.padic 2 (placeForms (n : ℤ) i (placePoint (D k : ℚ) (P k : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint (D k : ℚ) (P k : ℚ) j))) ≤ (2 : ℝ) ^ (-(N k : ℤ)) :=
      placeFactor_le_of_ratInt (n : ℤ) (D k : ℚ) (P k : ℚ) (q k) (hrel k) hDunit hPle (hq k) _ hbnd
    have hx1 : (placePoint (D k : ℚ) (P k : ℚ)) 1 = -1 := by simp [placePoint]
    have hfull := phi_twoPlace_product_le_invSup vinf hvne (n : ℤ)
      (placePoint (D k : ℚ) (P k : ℚ)) hx1 _ h2
    rw [sup_vinf_placePoint_eq_mulHeight (D k) (P k) vinf hvabs] at hfull
    have heqr : (2 : ℝ) ^ (-(N k : ℤ)) = (2 : ℝ) ^ (-(N k : ℝ)) := by
      rw [← Real.rpow_intCast]; norm_num
    rw [hS_def, ← heqr]; exact hfull
  · exact (phiPoints_rate n D P N (1 / 2 : ℝ) (by norm_num)).mono
      (fun k h => by convert h using 2; norm_num)

/-- *An automatic parity vector is rational.* -/
@[category API, AMS 11 37]
theorem automatic_parityVector_ratInt
    (n : ℕ) (hauto : IsAutomatic2Adic (parityVector n)) :
    parityVector n ∈ RatInt := by
  by_contra hirr
  have hm : Φ (parityVector n) = ((n : ℕ) : ℤ_[2]) := by rw [Φ_parityVector]
  exact phi_ne_natCast (parityVector n) hauto hirr n hm

@[category API, AMS 11 37, ref "BL96" "Lag90"]
theorem l90Divergent_of_divergent {n : ℕ} (h : Divergent n) : L90.Divergent (n : ℚ) := by
  rw [L90.Divergent, L90.orbit]
  have hcast : (fun k => L90.T^[k] (n : ℚ))
      = (fun m : ℕ => (m : ℚ)) ∘ (fun k => CC.T_iter k n) := by
    funext k; simp only [Function.comp_apply, L90.T_iterate_natCast, T_iter_eq_iterate]
  rw [hcast, Set.range_comp]
  rw [Divergent] at h
  exact (Set.infinite_image_iff (Nat.cast_injective.injOn)).mpr h

/-- **The no-divergence capstone.** *No divergent `3x+1` trajectory has an automatic parity vector.*
If `n > 0` is divergent then its parity vector `parityVector n` is **not** automatic. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07" "Lag90", group "b3_missing_lemma"]
theorem divergent_imp_not_automatic
    (n : ℕ) (_hn : 0 < n) (hdiv : Divergent n) :
    ¬ IsAutomatic2Adic (parityVector n) := by
  intro hauto
  exact L90.corollary_2_1b_nat n (l90Divergent_of_divergent hdiv)
    (ratInt_imp_eventuallyPeriodicParity n (automatic_parityVector_ratInt n hauto))

end B3
