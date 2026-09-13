/-
(C) 2026 Nikolay Metchev, in collaboration with GitHub Copilot.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Density.ShellExceptional
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Terras density-1: almost every `n` has a finite stopping time (Ter76)

The main statement of [Ter76]: for the compact Collatz map `T = CC.T`, the set
of positive integers whose stopping time `CC.stopping_time` is finite has
**natural density one**.

Equivalently (via `CC.stopping_time_ne_top_iff`, cf. `CC.exists_descent_iff`),
almost every `n` eventually drops strictly below itself under `T`.

The literature-cited statement is proved below as a `theorem` — the proof
factors through `CC/Density/ShellExceptional.lean` and the roadmap files
under `CC/Density/`.

## Reference
* [Ter76] Terras, R. *A stopping time problem on the positive integers.*
  Acta Arithmetica 30 (1976), no. 3, 241–252.

## Proof roadmap

The classical proof factors cleanly through infrastructure already in the
corpus:

1. **Descent as a shell + residue property.** For fixed `k ≥ 1`, whether the
   first `k` Terras steps produce a descent `T^[i] n < n` (some `1 ≤ i ≤ k`) is
   *not* a property of `n mod 2^k` alone: the comparison `< n` uses the full
   value of `n`. Restricting `n` to the dyadic shell `[2^M, 2^(M+1))` fixes the
   leading dyadic scale, and on the shell the descent question is controlled by
     * the parity word (which determines the multiplicative factor
       `CC.C k n = 3^{CC.num_odd_steps k n} / 2^k` of `CC/Decomposition.lean`),
       and
     * the additive Terras correction `CC.decomposition_correction k n`, which
       is `O(3^k)` and independent of the dyadic scale.

2. **Bad parity words.** Sufficient for descent within `k` steps is that the
   odd-step ratio `num_odd_steps k n / k` sits strictly below
   `CC.SRSBridge.criticalRatio = log 2 / log 3` by a margin that swallows the
   correction on shell `M` (`k ≤ c · M` suffices for a small `c > 0`).
   The "no descent within `k`" residues then lie in the filter
     `{r : ZMod (2^k) | (1/2 + t) · k ≤ CC.ParityTail.oddCount k r}`
   for a fixed `t > 0` depending only on `log 2 / log 3` and `c`.

3. **Hoeffding count.** By
   `CC.ParityTail.card_residues_with_oddCount_ge_sub_le_hoeffding`, that filter
   has size at most `2^k · exp(-2 t² k)`. Distributing residues over the shell
   (each residue mod `2^k` contributes `2^{M-k}` shell members when `k ≤ M`)
   gives an exceptional shell count `≤ 2^M · exp(-2 t² k)`.

4. **Shell → global.** With `k = ⌊c · M⌋`, the shell rate is
   `exp(-(2 t² c) · M) = exp(-c' · M)` with `c' = 2 t² c`. Choosing `c` small
   keeps `c' < log 2`, so
   `CET.QuantitativeDensity.isCDDense_of_shell_bound` yields `IsCDDense S C D`
   with explicit `C, D > 0`; the standard `IsCDDense → HasNaturalDensityOne`
   step (to be added) concludes.

## Companion files

* `CC/Density/ParityBadSet.lean` — residue-class characterisation of the
  "high odd count" filter and its Hoeffding cardinality bound.
* `CC/Density/ParityBadCount.lean` — shell-level counting bound
  `≤ 2 ^ M · exp (−c' · M)` via the fiber decomposition of the shell.
* `CC/Density/DescentFromResidue.lean` — the descent bridge: a "good"
  residue class forces `T ^ [k] n < n` on shell `M` for `k = ⌊M / 2⌋`.
* `CC/Density/ShellExceptional.lean` — shell inclusion, ratio decay to zero,
  and the assembled density-one conclusion.
-/

namespace CC

namespace Density

/-- **Terras density-1** [Ter76]. The set of positive integers with finite
Collatz stopping time has natural density one under the compact map `CC.T`.

Proved via the four-step roadmap above; the closing step is
`hasNaturalDensityOne_stopping_time_ne_top'` in `CC/Density/ShellExceptional.lean`. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem hasNaturalDensityOne_stopping_time_ne_top :
    CET.QuantitativeDensity.HasNaturalDensityOne
      {n | CC.stopping_time n ≠ ⊤} :=
  hasNaturalDensityOne_stopping_time_ne_top'

end Density

end CC
