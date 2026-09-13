/-
(C) 2026 Nikolay Metchev, in collaboration with GitHub Copilot.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Density.DescentFromResidue
import CC.Density.ParityBadCount
import CET.VaryingShellDensity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Shell exceptional ratio for Terras density-1

Step 4 of the roadmap in [CC/Density/TerrasDensity.lean](./TerrasDensity.lean):
fixing the shell → parameter choice and driving the shell exceptional fraction
to zero. The headline theorem itself is assembled in `TerrasDensity.lean` from
`shellExceptionalRatio_descendsWithin_tendsto_zero` below.

## Contents

* `descendsWithin` — the "positive-step descent" predicate, and its equivalence
  with `CC.stopping_time n ≠ ⊤` (via `CC.stopping_time_ne_top_iff`).
* `kOfShell`, `KOfShell` — the concrete shell → level/threshold choice
  `k(M) = M / 2`, `K(M) = ⌊(2/5) · k(M)⌋`, feeding
  `card_shellBadResidues_le_hoeffding` at Hoeffding slack `t = 1 / 10`.
* `pow_three_kOfShell_le_pow_two` — the shell condition `3 ^ k(M) ≤ 2 ^ M`,
  the `3 ^ k ≤ n` hypothesis of `descent_of_not_mem_badResidues`. Elementary
  (`(log 3) / 2 < log 2`, i.e. `3 < 4`), by induction with step `2`.
* `pow_three_sub_two_fifths_add_one_le_pow_two` — the numerical gap
  `3 ^ (k − ⌊2k/5⌋ − 1) + 1 ≤ 2 ^ k`, the other hypothesis of that lemma.
  Elementary (`(3/5) · log 3 < log 2`, i.e. `27 < 32`), by induction with
  step `5`.
* `shellBad_descendsWithin_subset` — the shell inclusion
  `shellBad {n | descendsWithin n} M ⊆ shellBadResidues (k M) M (K M)` for
  `M ≥ 2`, the contrapositive of `descent_of_not_mem_badResidues`.
* `shellExceptionalRatio_descendsWithin_le` — the resulting shell fraction
  bound `≤ exp (−k(M) / 50)` (so `≤ exp ((1 − M) / 100)`) for `M ≥ 2`.
* `shellExceptionalRatio_descendsWithin_tendsto_zero` — that fraction tends
  to `0`, by squeeze.
-/

namespace CC

namespace Density

open CET.QuantitativeDensity
open Filter Topology

/-! ### Positive-step descent -/

/-- **Positive-step descent.** `descendsWithin n` iff some strictly positive
number of Terras iterates lands `n` below itself. This is the finite-stopping
side of `CC.stopping_time_ne_top_iff` in predicate form. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
def descendsWithin (n : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ T_iter k n < n

@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem descendsWithin_iff_stopping_time_ne_top (n : ℕ) :
    descendsWithin n ↔ CC.stopping_time n ≠ ⊤ :=
  (CC.stopping_time_ne_top_iff n).symm

/-- The descent set as an equation between the two natural formulations. -/
@[category API, AMS 11 37, group "terras_density"]
theorem setOf_descendsWithin_eq :
    {n | descendsWithin n} = {n | CC.stopping_time n ≠ ⊤} := by
  ext n; exact descendsWithin_iff_stopping_time_ne_top n

/-! ### Concrete shell → parameter choice -/

/-- Level `k` used on shell `M` in the Terras density argument: `k = M / 2`.
Chosen small enough that `3 ^ k ≤ 2 ^ M` (the descent shell condition) and
large enough that Hoeffding decay gives `exp (-M / 100)` shell fraction. -/
@[category API, AMS 11 37, group "terras_density"]
def kOfShell (M : ℕ) : ℕ := M / 2

/-- Threshold `K` used on shell `M`: `K = ⌊(2 / 5) · k(M)⌋`. Chosen so that
the Hoeffding upper-tail hypothesis `K ≤ (1/2 − t) · k` is satisfied at
`t = 1 / 10`, and so that the arithmetic gap
`3 ^ (k − K − 1) + 1 ≤ 2 ^ k` follows from `(3/5) · log 3 < log 2`. -/
@[category API, AMS 11 37, group "terras_density"]
def KOfShell (M : ℕ) : ℕ := 2 * kOfShell M / 5

@[category API, AMS 11 37, group "terras_density"]
theorem kOfShell_le (M : ℕ) : kOfShell M ≤ M := by
  unfold kOfShell; omega

/-! ### The shell condition `3 ^ k(M) ≤ 2 ^ M` -/

/-- **Shell condition.** `3 ^ k(M) ≤ 2 ^ M`: strong induction on `M` with step
`2`, using `3 · 2 ^ M ≤ 4 · 2 ^ M = 2 ^ (M + 2)`. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem pow_three_kOfShell_le_pow_two (M : ℕ) :
    3 ^ kOfShell M ≤ 2 ^ M := by
  unfold kOfShell
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    match M with
    | 0 => decide
    | 1 => decide
    | M + 2 =>
      have hM_div : (M + 2) / 2 = M / 2 + 1 := by omega
      have hih : 3 ^ (M / 2) ≤ 2 ^ M := ih M (by omega)
      have hpow2 : (2 : ℕ) ^ (M + 2) = 4 * 2 ^ M := by
        rw [show M + 2 = 2 + M from by ring, pow_add]; ring
      calc 3 ^ ((M + 2) / 2)
          = 3 ^ (M / 2 + 1) := by rw [hM_div]
        _ = 3 * 3 ^ (M / 2) := by rw [pow_succ]; ring
        _ ≤ 3 * 2 ^ M := by omega
        _ ≤ 4 * 2 ^ M := by omega
        _ = 2 ^ (M + 2) := hpow2.symm

/-! ### The numerical gap `3 ^ (k − ⌊2k/5⌋ − 1) + 1 ≤ 2 ^ k` -/

/-- **Numerical gap.** `3 ^ (k − ⌊2k/5⌋ − 1) + 1 ≤ 2 ^ k` for `k ≥ 1`, i.e.
`3 ^ (k − ⌊2k/5⌋ − 1) < 2 ^ k` — the inequality `(3/5) · log 3 < log 2` at Nat
level, numerically `27 = 3 ^ 3 < 2 ^ 5 = 32`.

Strong induction with step `5`: the arms `k ∈ {1, …, 5}` are closed by
`decide`, and the arm `k' + 6` recurses to `k' + 1`, where the exponent
`k − ⌊2k/5⌋ − 1` grows by `3` while `k` grows by `5`, so the two sides pick up
factors `27` and `32` respectively. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem pow_three_sub_two_fifths_add_one_le_pow_two (k : ℕ) (hk : 1 ≤ k) :
    3 ^ (k - 2 * k / 5 - 1) + 1 ≤ 2 ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, hk with
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
    | k' + 6, _ =>
      have hih := ih (k' + 1) (by omega) (by omega)
      -- `2 (k'+6) = 2 (k'+1) + 2·5`, so `2 (k'+6) / 5 = 2 (k'+1) / 5 + 2`.
      have hdiv : 2 * (k' + 6) / 5 = 2 * (k' + 1) / 5 + 2 := by
        have h : 2 * (k' + 6) = 2 * (k' + 1) + 2 * 5 := by ring
        rw [h]; exact Nat.add_mul_div_right (2 * (k' + 1)) 2 (by norm_num)
      have h_shift :
          (k' + 6) - 2 * (k' + 6) / 5 - 1
            = ((k' + 1) - 2 * (k' + 1) / 5 - 1) + 3 := by
        rw [hdiv]; omega
      have h_pow3 : (3 : ℕ) ^ ((k' + 6) - 2 * (k' + 6) / 5 - 1)
            = 27 * 3 ^ ((k' + 1) - 2 * (k' + 1) / 5 - 1) := by
        rw [h_shift, show ((k' + 1) - 2 * (k' + 1) / 5 - 1) + 3
              = 3 + ((k' + 1) - 2 * (k' + 1) / 5 - 1) from by omega, pow_add]
        ring
      have h_pow2 : (2 : ℕ) ^ (k' + 6) = 32 * 2 ^ (k' + 1) := by
        rw [show k' + 6 = 5 + (k' + 1) from by omega, pow_add]; ring
      have h2pos : 1 ≤ 2 ^ (k' + 1) := Nat.two_pow_pos _
      calc 3 ^ ((k' + 6) - 2 * (k' + 6) / 5 - 1) + 1
          = 27 * 3 ^ ((k' + 1) - 2 * (k' + 1) / 5 - 1) + 1 := by rw [h_pow3]
        _ ≤ 27 * (2 ^ (k' + 1) - 1) + 1 := by
              have hbound : 3 ^ ((k' + 1) - 2 * (k' + 1) / 5 - 1)
                  ≤ 2 ^ (k' + 1) - 1 := by omega
              omega
        _ ≤ 32 * 2 ^ (k' + 1) := by omega
        _ = 2 ^ (k' + 6) := h_pow2.symm

/-! ### Shell inclusion: non-descending integers have bad residues -/

/-- The numerical gap `3 ^ (k(M) − K(M) − 1) + 1 ≤ 2 ^ k(M)` on shell `M ≥ 2`,
instantiated from `pow_three_sub_two_fifths_add_one_le_pow_two`. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem pow_three_gap_kOfShell_le_pow_two (M : ℕ) (hM : 2 ≤ M) :
    3 ^ (kOfShell M - KOfShell M - 1) + 1 ≤ 2 ^ kOfShell M := by
  have hk : 1 ≤ kOfShell M := by unfold kOfShell; omega
  simpa [KOfShell] using pow_three_sub_two_fifths_add_one_le_pow_two (kOfShell M) hk

/-- **Shell inclusion.** If `n` sits on the dyadic shell `[2 ^ M, 2 ^ (M+1))`
with `M ≥ 2` and does not descend within any positive number of Terras steps,
then its residue mod `2 ^ k(M)` lies in `badResidues (kOfShell M) (KOfShell M)`.

Direct contrapositive of `descent_of_not_mem_badResidues`, using the
numerical gap and shell condition proved above. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem mem_shellBadResidues_of_not_descendsWithin
    {M n : ℕ} (hM : 2 ≤ M)
    (hn : 2 ^ M ≤ n ∧ n < 2 ^ (M + 1))
    (h_no_descent : ¬ descendsWithin n) :
    n ∈ shellBadResidues (kOfShell M) M (KOfShell M) := by
  rw [mem_shellBadResidues]
  refine ⟨hn, ?_⟩
  by_contra h_not_bad
  apply h_no_descent
  refine ⟨kOfShell M, ?_, ?_⟩
  · unfold kOfShell; omega
  · exact descent_of_not_mem_badResidues
      h_not_bad
      (pow_three_gap_kOfShell_le_pow_two M hM)
      (le_trans (pow_three_kOfShell_le_pow_two M) hn.1)

/-- Set-level restatement: the shell-exceptional set for `descendsWithin` on
shell `M ≥ 2` is contained in `shellBadResidues`. This is the input the
final natural-density-one argument consumes. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem shellBad_descendsWithin_subset {M : ℕ} (hM : 2 ≤ M) :
    shellBad {n | descendsWithin n} M
      ⊆ shellBadResidues (kOfShell M) M (KOfShell M) := by
  intro n hn
  simp only [shellBad, dyadicShell, Finset.mem_filter, Finset.mem_Ico,
    Set.mem_ofPred_eq] at hn
  obtain ⟨⟨h1, h2⟩, hnot⟩ := hn
  exact mem_shellBadResidues_of_not_descendsWithin hM ⟨h1, h2⟩ hnot

/-! ### Shell-ratio decay -/

/-- **Shell-ratio decay.** On shell `M ≥ 2`, the exceptional fraction of the
descent set is at most `exp (−k(M) / 50)`; since `k(M) = ⌊M/2⌋ ≥ (M − 1) / 2`,
in particular at most `exp ((1 − M) / 100)`.

Uses the shell inclusion `shellBad_descendsWithin_subset` combined with
`card_shellBadResidues_le_hoeffding` at Hoeffding slack `t = 1 / 10`, and the
algebraic identity `−2 · (1/10)² = −1/50`. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "terras_density"]
theorem shellExceptionalRatio_descendsWithin_le
    {M : ℕ} (hM : 2 ≤ M) :
    shellExceptionalRatio {n | descendsWithin n} M ≤
      Real.exp (-(kOfShell M : ℝ) / 50) := by
  set k := kOfShell M with hk_def
  set K := KOfShell M with hK_def
  have hkM : k ≤ M := kOfShell_le M
  -- `5·K ≤ 2·k` (Nat) ⇒ `(K : ℝ) ≤ (2/5)·k = (1/2 − 1/10)·k`.
  have hK_le : 5 * K ≤ 2 * k := by
    show 5 * (2 * kOfShell M / 5) ≤ 2 * kOfShell M
    have := Nat.div_mul_le_self (2 * kOfShell M) 5
    omega
  have hK_le_real : (5 : ℝ) * (K : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hK_le
  have hcut : (K : ℝ) ≤ ((1 : ℝ) / 2 - 1 / 10) * (k : ℝ) := by linarith
  -- Hoeffding shell bound.
  have hoeff := card_shellBadResidues_le_hoeffding
    (k := k) (M := M) (K := K) (t := (1 / 10 : ℝ))
    hkM (by norm_num) hcut
  -- Shell inclusion transports the card.
  have hcard_le : (shellBad {n | descendsWithin n} M).card
      ≤ (shellBadResidues k M K).card :=
    Finset.card_le_card (shellBad_descendsWithin_subset hM)
  have hcard_le_real :
      ((shellBad {n | descendsWithin n} M).card : ℝ)
        ≤ ((shellBadResidues k M K).card : ℝ) := by exact_mod_cast hcard_le
  have hchain :
      ((shellBad {n | descendsWithin n} M).card : ℝ)
        ≤ (2 : ℝ) ^ M * Real.exp (-2 * (1 / 10 : ℝ) ^ 2 * (k : ℝ)) :=
    hcard_le_real.trans hoeff
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  unfold shellExceptionalRatio
  rw [div_le_iff₀ h2pow_pos]
  have hexp : (-2 : ℝ) * (1 / 10 : ℝ) ^ 2 * (k : ℝ) = -(k : ℝ) / 50 := by ring
  rw [← hexp, mul_comm]
  exact hchain

/-! ### Tendsto: shell ratio → 0 -/

private lemma kOfShell_cast_tendsto_atTop :
    Tendsto (fun M : ℕ => (kOfShell M : ℝ)) atTop atTop := by
  -- Use the coarser bound `k(M) ≥ M / 4` valid for `M ≥ 2`.
  have hlb : ∀ᶠ M : ℕ in atTop, (M : ℝ) / 4 ≤ (kOfShell M : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with M hM
    show (M : ℝ) / 4 ≤ ((M / 2 : ℕ) : ℝ)
    have hnat : 4 * (M / 2) ≥ M := by omega
    have hreal : (4 : ℝ) * ((M / 2 : ℕ) : ℝ) ≥ (M : ℝ) := by exact_mod_cast hnat
    linarith
  have hlim : Tendsto (fun M : ℕ => (M : ℝ) / 4) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 4)
  exact tendsto_atTop_mono' _ hlb hlim

private lemma exp_neg_kOfShell_tendsto_zero :
    Tendsto (fun M => Real.exp (-(kOfShell M : ℝ) / 50)) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have h1 : Tendsto (fun M : ℕ => (kOfShell M : ℝ) / 50) atTop atTop :=
    kOfShell_cast_tendsto_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 50)
  have h2 : Tendsto (fun M : ℕ => -((kOfShell M : ℝ) / 50)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  simpa [neg_div] using h2

/-- **Shell ratio → 0.** The shell exceptional fraction of the descent set
tends to `0` as `M → ∞`, by squeeze between `0` and `exp (− k(M) / 50)`. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem shellExceptionalRatio_descendsWithin_tendsto_zero :
    Tendsto (fun M => shellExceptionalRatio {n | descendsWithin n} M)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ => (0 : ℝ))
    (h := fun M => Real.exp (-(kOfShell M : ℝ) / 50))
    tendsto_const_nhds exp_neg_kOfShell_tendsto_zero ?_ ?_
  · exact Eventually.of_forall (fun M => shellExceptionalRatio_nonneg _ M)
  · filter_upwards [eventually_ge_atTop 2] with M hM
    exact shellExceptionalRatio_descendsWithin_le hM

end Density

end CC
