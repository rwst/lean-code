/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Floor
import CITED.WaltersVariationalPrinciple
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Theorem 3.4 in the paper's own form, and Corollary 3.5

`BB61/Price.lean` proved the duality

`⨅_{a ∈ ℂ^H} sup_{μ ∈ M(σ)} (h(μ) + ∫ψ_a dμ) = E_H(α)`

outright.  This file replaces the supremum by the **topological pressure** — that replacement is
the variational principle, `Walters.partitionPressure_eq_measurePressure` of
`CITED/WaltersVariationalPrinciple.lean`, whose hard half is the cited axiom — and draws the
consequence the paper calls Corollary 3.5.

## Main results

* `BB61.iInf_partitionPressure_eq_priceEntropy` — **Theorem 3.4 (`paper.tex` §3.3, Theorem B(iii)),
  the exact price**: `⨅_{a ∈ ℂ^H} P(ψ_a) = E_H(α)`.
* `BB61.problem_10_61_tfae` — **Corollary 3.5, completeness of the pressure criterion.**  For a
  quadratic Pisot **unit** `α > 2` the following are equivalent:
  (i) 10.61 holds at `α`; (ii) `K_H = ∅` for some `H`; (iii) `E_H(α) < h_min(α)` for some `H`;
  (iv) some `ψ_a` has `P(ψ_a) < h_min(α)`.
* `BB61.entDegree_le_flatDegree` — the paper's `H_ent ≤ H_flat`, the gap being what the entropy
  floor buys.

## The two cited axioms, and which implication needs which

| implication | needs |
| --- | --- |
| (i) ⇒ (ii) | nothing cited (`BB61/Certificate.lean`, M3 Theorem 9) |
| (ii) ⇒ (iii) | nothing (`E_H = -∞`) |
| (iii) ⇒ (iv) | `Walters.partitionPressure_le_measurePressure` |
| (iv) ⇒ (i) | `LY.entropyRate_floor` (through `BB61.floor_of_quadratic_unit`) |

The `α`-hypothesis `hunit` enters only through the entropy floor, i.e. only in (iv) ⇒ (i); the
other three implications hold for every `QuadSetup`.
-/

namespace BB61

open MeasureTheory Dynamics BoundedContinuousFunction

/-! ## Theorem 3.4, with the topological pressure -/

/-- The pressure of `ψ_a` over cylinders is the supremum of `h(μ) + ∫ψ_a dμ` over `M(σ)`: the
variational principle, at the potentials of Theorem 3.4. -/
@[category research solved, AMS 37 28 11, ref "Wal82", group "bugeaud_10_61"]
theorem partitionPressure_fourierPotential (P : QuadSetup) (Hs : Finset ℤ) (a : ℤ → ℂ) :
    partitionPressure shiftZ (fourierPotential P Hs a) coordPartition
      = measurePressure (fourierPotential P Hs a) :=
  Walters.partitionPressure_eq_measurePressure (fourierPotentialBC P Hs a)

/-- **Theorem 3.4 of `paper.tex` — the price of a certificate** (Theorem B(iii)).  For every finite
set `H` of frequencies,

`inf_{a ∈ ℂ^H} P(ψ_a) = E_H(α)`,  `ψ_a = Re ∑_{h ∈ H} a_h e(hF)`.

Every number a pressure minimisation of degree `H` reports is an upper approximation to the largest
entropy an invariant measure of the full `2`-shift can have while being Fourier-flat to degree `H`.

The duality is proved (`BB61.iInf_measurePressure_eq_priceEntropy`); the passage from the measure
side to the topological pressure is the cited variational principle. -/
@[category research solved, AMS 37 28 11, ref "Bug12" "Sio58" "Wal82", group "bugeaud_10_61"]
theorem iInf_partitionPressure_eq_priceEntropy (P : QuadSetup) (Hs : Finset ℤ) :
    ⨅ a : ℤ → ℂ, partitionPressure shiftZ (fourierPotential P Hs a) coordPartition
      = priceEntropy P Hs := by
  rw [← iInf_measurePressure_eq_priceEntropy P Hs]
  exact iInf_congr fun a => partitionPressure_fourierPotential P Hs a

/-- Theorem 3.4 at the paper's own frequency set `H = {1, …, H}`. -/
@[category research solved, AMS 37 28 11, ref "Bug12" "Sio58" "Wal82", group "bugeaud_10_61"]
theorem iInf_partitionPressure_eq_priceEntropy_Icc (P : QuadSetup) (H : ℕ) :
    ⨅ a : ℤ → ℂ,
        partitionPressure shiftZ (fourierPotential P (Finset.Icc 1 (H : ℤ)) a) coordPartition
      = priceEntropy P (Finset.Icc 1 (H : ℤ)) :=
  iInf_partitionPressure_eq_priceEntropy P _

/-! ## Nestedness of `K_H` -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem flatSet_subset_of_subset (P : QuadSetup) {Hs Hs' : Finset ℤ} (h : Hs ⊆ Hs') :
    flatSet P Hs' ⊆ flatSet P Hs :=
  fun _ hμ => ⟨hμ.1, fun k hk => hμ.2 k (h hk)⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem priceEntropy_mono (P : QuadSetup) {Hs Hs' : Finset ℤ} (h : Hs ⊆ Hs') :
    priceEntropy P Hs' ≤ priceEntropy P Hs :=
  sSup_le_sSup (Set.image_mono (flatSet_subset_of_subset P h))

/-! ## The four conditions of Corollary 3.5 -/

/-- A potential of nonzero frequencies is annihilated by every measure that `F` pushes forward to
Lebesgue: the `hann` hypothesis of the pressure criterion, discharged. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourierPotential_eq_zero_of_map (P : QuadSetup) {Hs : Finset ℤ}
    (h0 : (0 : ℤ) ∉ Hs) (a : ℤ → ℂ) (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hmap : Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ)))) :
    ∫ ω, fourierPotential P Hs a ω ∂μ = 0 := by
  have h : ∫ z, trigPoly Hs a z ∂(Measure.map P.fMap μ) = ∫ ω, trigPoly Hs a (P.fMap ω) ∂μ :=
    integral_map P.measurable_fMap.aemeasurable
      (trigPoly Hs a).continuous.aestronglyMeasurable
  show ∫ ω, trigPoly Hs a (P.fMap ω) ∂μ = 0
  rw [← h, hmap, integral_trigPoly_eq_zero h0]

/-- **(iv) ⇒ (i)**: a pressure certificate below the entropy floor settles 10.61 at `α`. -/
@[category research solved, AMS 37 28 11, ref "You82" "LY85" "BPS99", group "bugeaud_10_61"]
theorem forall_not_equidistributed_of_partitionPressure_lt_floor (P : QuadSetup) (hα : 2 < P.α)
    (hunit : P.b = 1 ∨ P.b = -1) {Hs : Finset ℤ} (h0 : (0 : ℤ) ∉ Hs) (a : ℤ → ℂ)
    (hpress : partitionPressure shiftZ (fourierPotential P Hs a) coordPartition
      < ((Real.log P.α / 2 : ℝ) : EReal)) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  forall_not_equidistributed_of_partitionPressure_lt P
    (continuous_fourierPotential P Hs a).measurable (abs_fourierPotential_le P Hs a)
    (fun μ hprob _ hmap => @integral_fourierPotential_eq_zero_of_map P Hs h0 a μ hprob hmap)
    (floor_of_quadratic_unit P hα hunit) hpress

/-- **(i) ⇒ (ii)**: if 10.61 holds at `α` then some `K_H` is empty.  The certificate of M3
Theorem 9 (`BB61/Certificate.lean`) is a potential that every invariant measure integrates to at
least `c > 0`, while a flat measure would integrate it to `0`. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_flatSet_eq_empty (P : QuadSetup)
    (hno : ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n) :
    ∃ Hs : Finset ℤ, (0 : ℤ) ∉ Hs ∧ flatSet P Hs = ∅ := by
  obtain ⟨Hs, a, c, h0, hc, -, hlb⟩ :=
    P.forall_not_equidistributed_iff_exists_trigCertificate.1 hno
  refine ⟨Hs, h0, Set.eq_empty_iff_forall_notMem.2 fun μ hμ => ?_⟩
  have hzero : ∫ ω, trigPoly Hs a (P.fMap ω) ∂(μ : Measure Shift) = 0 :=
    integral_fourierPotential_eq_zero P Hs a hμ
  have hge := hlb μ hμ.1
  rw [hzero] at hge
  linarith

/-- **(ii) ⇒ (iii)**: an empty `K_H` makes `E_H(α) = -∞`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem priceEntropy_eq_bot_of_flatSet_eq_empty (P : QuadSetup) {Hs : Finset ℤ}
    (h : flatSet P Hs = ∅) : priceEntropy P Hs = ⊥ := by
  rw [priceEntropy, h, Set.image_empty, sSup_empty]

/-- **(iii) ⇒ (iv)**: below any bound on `E_H(α)` there is a potential of that degree whose
pressure is below the bound.  This is Theorem 3.4, hence the cited variational principle. -/
@[category research solved, AMS 37 28 11, ref "Bug12" "Sio58" "Wal82", group "bugeaud_10_61"]
theorem exists_partitionPressure_lt (P : QuadSetup) (Hs : Finset ℤ) {r : ℝ}
    (h : priceEntropy P Hs < (r : EReal)) :
    ∃ a : ℤ → ℂ,
      partitionPressure shiftZ (fourierPotential P Hs a) coordPartition < (r : EReal) := by
  rw [← iInf_partitionPressure_eq_priceEntropy P Hs] at h
  exact iInf_lt_iff.1 h

/-- **Corollary 3.5 of `paper.tex` — completeness of the pressure criterion.**

Let `α > 2` be a quadratic Pisot **unit**.  The following are equivalent:

(i) Problem 10.61 holds at `α`;
(ii) `K_H = ∅` for some finite set `H` of nonzero frequencies;
(iii) `E_H(α) < h_min(α) = ½ log α` for some such `H`;
(iv) some `ψ_a` of such a degree has `P(ψ_a) < h_min(α)`.

So the certificate scheme is complete: no method can settle an `α` that a pressure certificate
cannot, and the search for one terminates at a *named* quantity. -/
@[category research solved, AMS 37 28 11, ref "Bug12" "Sio58" "Wal82" "You82" "LY85" "BPS99",
  group "bugeaud_10_61"]
theorem problem_10_61_tfae (P : QuadSetup) (hα : 2 < P.α) (hunit : P.b = 1 ∨ P.b = -1) :
    List.TFAE
      [ ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n,
        ∃ Hs : Finset ℤ, (0 : ℤ) ∉ Hs ∧ flatSet P Hs = ∅,
        ∃ Hs : Finset ℤ, (0 : ℤ) ∉ Hs ∧ priceEntropy P Hs < ((Real.log P.α / 2 : ℝ) : EReal),
        ∃ (Hs : Finset ℤ) (a : ℤ → ℂ), (0 : ℤ) ∉ Hs ∧
          partitionPressure shiftZ (fourierPotential P Hs a) coordPartition
            < ((Real.log P.α / 2 : ℝ) : EReal) ] := by
  tfae_have 1 → 2 := fun h => exists_flatSet_eq_empty P h
  tfae_have 2 → 3 := by
    rintro ⟨Hs, h0, hempty⟩
    exact ⟨Hs, h0, by
      rw [priceEntropy_eq_bot_of_flatSet_eq_empty P hempty]; exact EReal.bot_lt_coe _⟩
  tfae_have 3 → 4 := by
    rintro ⟨Hs, h0, hlt⟩
    obtain ⟨a, ha⟩ := exists_partitionPressure_lt P Hs hlt
    exact ⟨Hs, a, h0, ha⟩
  tfae_have 4 → 1 := by
    rintro ⟨Hs, a, h0, ha⟩
    exact forall_not_equidistributed_of_partitionPressure_lt_floor P hα hunit h0 a ha
  tfae_finish

/-! ## The two degrees -/

/-- `H_flat(α) = min {H : K_H = ∅}`, the least degree at which the flat set is empty. -/
noncomputable def flatDegree (P : QuadSetup) : ℕ :=
  sInf {H : ℕ | flatSet P (Finset.Icc 1 (H : ℤ)) = ∅}

/-- `H_ent(α) = min {H : E_H(α) < h_min(α)}`, the least degree at which the entropy budget of the
flat measures falls below the Ledrappier–Young floor. -/
noncomputable def entDegree (P : QuadSetup) : ℕ :=
  sInf {H : ℕ | priceEntropy P (Finset.Icc 1 (H : ℤ)) < ((Real.log P.α / 2 : ℝ) : EReal)}

/-- **`H_ent ≤ H_flat`.**  A degree that empties `K_H` a fortiori puts `E_H(α)` below the floor —
`E_H = -∞` there — so the entropy criterion fires no later than the flatness criterion.  The gap
between the two is exactly what the entropy floor of Theorem B(i) buys. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem entDegree_le_flatDegree (P : QuadSetup)
    (h : ∃ H : ℕ, flatSet P (Finset.Icc 1 (H : ℤ)) = ∅) : entDegree P ≤ flatDegree P := by
  have hmem : flatSet P (Finset.Icc 1 ((flatDegree P : ℕ) : ℤ)) = ∅ := Nat.sInf_mem h
  refine Nat.sInf_le ?_
  rw [Set.mem_ofPred_eq, priceEntropy_eq_bot_of_flatSet_eq_empty P hmem]
  exact EReal.bot_lt_coe _

end BB61
