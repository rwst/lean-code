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

end Density

end CC
