/-
(C) 2026 Nikolay Metchev, in collaboration with GitHub Copilot.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Density.DescentFromResidue
import CC.Density.ParityBadCount
import CC.DescentEquivalence
import CET.VaryingShellDensity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Shell → prefix density: framework for Terras density-1

Structural setup for the final step of the roadmap in
[CC/Density/TerrasDensity.lean](./TerrasDensity.lean). The pieces landed in this
file are

* `descendsWithin` — the "positive-step descent" predicate, and its equivalence
  with `CC.stopping_time n ≠ ⊤` (via `CC.stopping_time_ne_top_iff`).
* `kOfShell`, `KOfShell` — the concrete shell → level/threshold choice
  (`k = M / 2`, `K = ⌊(2/5) · k⌋`) that will feed
  `card_shellBadResidues_le_hoeffding` in the closing step.
* `kOfShell_le` — `k(M) ≤ M`, the size hypothesis of the shell fiber count.

Not yet in this file (they are the closing real-analysis grunt-work, whose
completion replaces the cited axiom in `TerrasDensity.lean`):

1. The numerical gap `3 ^ (kOfShell M − KOfShell M − 1) + 1 ≤ 2 ^ kOfShell M`
   for `M ≥ 2` (elementary but Nat-arithmetic-heavy induction).
2. The shell-condition `3 ^ kOfShell M ≤ 2 ^ M` (uses `(log 3) / 2 ≤ log 2`).
3. The shell inclusion `shellBad {n | descendsWithin n} M ⊆
     shellBadResidues (kOfShell M) M (KOfShell M)` for `M ≥ 2` — immediate
   contrapositive of `descent_of_not_mem_badResidues` once 1 and 2 are in.
4. The shell exceptional ratio decay `≤ Real.exp ((1 - M) / 100)` for
   `M ≥ 2` — direct from `card_shellBadResidues_le_hoeffding` with
   `t = 1 / 10`.
5. `Filter.Tendsto (shellExceptionalRatio {n | descendsWithin n}) atTop (𝓝 0)`,
   via `tendsto_of_tendsto_of_tendsto_of_le_of_le'` on 4.
6. `HasNaturalDensityOne {n | descendsWithin n}` via
   `CET.QuantitativeDensity.hasNaturalDensityOne_assembleDyadic` applied to
   the constant family `fun _ => {n | descendsWithin n}`.
-/

namespace CC

namespace Density

open CET.QuantitativeDensity

/-! ### Positive-step descent -/

/-- **Positive-step descent.** `descendsWithin n` iff some strictly positive
number of Terras iterates lands `n` below itself. This is the finite-stopping
side of `CC.stopping_time_ne_top_iff` in predicate form. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
def descendsWithin (n : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ T_iter k n < n

@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem descendsWithin_iff_stopping_time_ne_top (n : ℕ) :
    descendsWithin n ↔ CC.stopping_time n ≠ ⊤ := by
  unfold descendsWithin
  rw [CC.stopping_time_ne_top_iff]

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

@[category API, AMS 11 37, group "terras_density"]
theorem KOfShell_le (M : ℕ) : KOfShell M ≤ kOfShell M := by
  unfold KOfShell; omega

/-! ### The shell condition `3 ^ k(M) ≤ 2 ^ M`

Elementary: `(log 3) / 2 < log 2`, i.e., `3 < 4 = 2 ^ 2`. Nat-level proof by
strong induction on `M` with step `2`, using `3 · 2 ^ M ≤ 4 · 2 ^ M = 2 ^ (M+2)`. -/

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

/-! ### The numerical gap `3 ^ (k − 2k/5 − 1) + 1 ≤ 2 ^ k`

Elementary: `(3 / 5) · log 3 < log 2` (numerically `27 = 3^3 < 32 = 2^5`).
Nat-level proof by strong induction with step `5`: five base cases
`k ∈ {1, …, 5}` closed by `decide`; the step uses
`3 ^ (k+5 term) = 27 · 3 ^ (k term)` and `2 ^ (k+5) = 32 · 2 ^ k`. -/

@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem numerical_gap (k : ℕ) (hk : 1 ≤ k) :
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
              nlinarith
        _ ≤ 32 * 2 ^ (k' + 1) := by omega
        _ = 2 ^ (k' + 6) := h_pow2.symm

/-! ### Shell inclusion: non-descending integers have bad residues -/

/-- `k(M) − K(M) ≥ 1` on shell `M ≥ 2`. -/
@[category API, AMS 11 37, group "terras_density"]
theorem one_le_k_sub_K (M : ℕ) (hM : 2 ≤ M) :
    1 ≤ kOfShell M - KOfShell M := by
  show 1 ≤ M / 2 - 2 * (M / 2) / 5
  have h1 : 2 * (M / 2) / 5 * 5 ≤ 2 * (M / 2) := Nat.div_mul_le_self _ 5
  omega

/-- The numerical gap `3 ^ (k(M) − K(M) − 1) + 1 ≤ 2 ^ k(M)` on shell `M ≥ 2`,
instantiated from `numerical_gap`. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem numerical_gap_kOfShell (M : ℕ) (hM : 2 ≤ M) :
    3 ^ (kOfShell M - KOfShell M - 1) + 1 ≤ 2 ^ kOfShell M := by
  have hk : 1 ≤ kOfShell M := by unfold kOfShell; omega
  simpa [KOfShell] using numerical_gap (kOfShell M) hk

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
      (one_le_k_sub_K M hM)
      h_not_bad
      (numerical_gap_kOfShell M hM)
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

end Density

end CC
