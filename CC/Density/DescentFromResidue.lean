/-
(C) 2026 Nikolay Metchev, in collaboration with GitHub Copilot.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Density.BadResidues
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The descent-from-residue bridge for Terras density-1

Step 3 of the roadmap in [CC/Density/TerrasDensity.lean](./TerrasDensity.lean):
the mathematical bridge that turns the residue-side "not too many odd steps"
condition into an integer-side descent `T ^ [k] n < n`.

## The three pieces

`linear_decomposition` (in `CC/Decomposition.lean`) states
  `2 ^ k · T ^ [k] n = 3 ^ (num_odd_steps k n) · n + decomposition_correction k n`,
so `T ^ [k] n < n` reduces to `Q(k,n) + 3 ^ J · n + 1 ≤ 2 ^ k · n` with
`J = num_odd_steps k n` and `Q = decomposition_correction k n`. Three
ingredients close that gap; the first two live next to the decomposition they
come from, in `CC/Decomposition.lean`:

1. **Correction bound.** `CC.decomposition_correction_add_pow_two_le_pow_three`:
   `Q(k,n) + 2 ^ k ≤ 3 ^ k`, i.e. `Q(k,n) ≤ 3 ^ k − 2 ^ k`.
2. **Descent criterion.** `CC.descent_of_num_odd_steps_le`: given
   `num_odd_steps k n ≤ J₀` with `3 ^ J₀ + 1 ≤ 2 ^ k`, and `3 ^ k ≤ n`,
   the orbit descends.
3. **Good residues.** What this file adds: `r ∉ badResidues k J₀` bounds
   `num_odd_steps k n` by `J₀` via `oddCount_natCast` — verbatim the
   hypothesis that 2 wants, with no truncated `Nat` subtraction in between.
   The result is `descent_of_not_mem_badResidues`.

The `3 ^ k ≤ n` hypothesis of 2 is what confines the argument to the dyadic
shell `[2 ^ M, 2 ^ (M+1))` with `M · log 2 ≥ k · log 3`; `ShellExceptional.lean`
supplies it.
-/

namespace CC

namespace Density

/-! ### The residue-side bridge -/

/-- The residue-side reformulation of "not too many odd steps": if the
residue class of `n` mod `2 ^ k` is not in the "bad" set `badResidues k J₀`,
then `n` spends at most `J₀` of its first `k` Terras steps on a tripling. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem num_odd_steps_le_of_not_mem_badResidues {k J₀ n : ℕ}
    (h : (n : ZMod (2 ^ k)) ∉ badResidues k J₀) :
    CC.num_odd_steps k n ≤ J₀ := by
  by_contra hgt
  exact h (natCast_mem_badResidues.mpr (by omega))

/-- **Descent from a good residue class.** If `n` lies on a shell large
enough (`3 ^ k ≤ n`), its residue class is not bad
(`(n : ZMod (2^k)) ∉ badResidues k J₀`), and the budget clears the gap
threshold (`3 ^ J₀ + 1 ≤ 2 ^ k`), then `T ^ [k] n < n`.

This is the residue-side descent lemma that the density transport consumes:
membership of a good residue class forces descent within `k` Terras steps. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem descent_of_not_mem_badResidues {k J₀ n : ℕ}
    (h_not_bad : (n : ZMod (2 ^ k)) ∉ badResidues k J₀)
    (hgap : 3 ^ J₀ + 1 ≤ 2 ^ k)
    (hn : 3 ^ k ≤ n) :
    T_iter k n < n :=
  descent_of_num_odd_steps_le
    (num_odd_steps_le_of_not_mem_badResidues h_not_bad) hgap hn

end Density

end CC
