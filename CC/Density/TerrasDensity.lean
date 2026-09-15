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

The proof is complete — no `sorry`, and no literature axiom. It factors
through the companion files under `CC/Density/` listed below.

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
   odd-step count `num_odd_steps k n` stay within a budget `J₀` with
   `3 ^ J₀ < 2 ^ k`, i.e. an odd-step *ratio* `J₀ / k` strictly below
   `CC.SRSBridge.criticalRatio = log 2 / log 3`, by a margin that swallows the
   correction on shell `M`. The "no descent within `k`" residues then lie in
     `CC.Density.badResidues k J₀ = {r : ZMod (2^k) | J₀ < CC.ParityTail.oddCount k r}`.

3. **Hoeffding count.** By
   `CC.ParityTail.card_residues_with_oddCount_gt_le_hoeffding`, that filter has
   size at most `2^k · exp(-2 t² k)` whenever the budget sits a slack `t` above
   the mean, `(1/2 + t) · k ≤ J₀ + 1`. Distributing residues over the shell
   (each residue mod `2^k` contributes `2^{M-k}` shell members when `k ≤ M`)
   gives an exceptional shell count `≤ 2^M · exp(-2 t² k)`.

4. **Shell → global.** With `k` proportional to `M` the shell rate is
   `exp(-c' · M)`, so the shell exceptional fraction tends to `0`.
   `CET.QuantitativeDensity.hasNaturalDensityOne_assembleDyadic`, applied to
   the constant family `fun _ => {n | Descends n}`, turns that vanishing shell
   fraction into `HasNaturalDensityOne`.

## The constants

All of them come from the single numerical fact `3 ^ 5 = 243 ≤ 256 = 2 ^ 8`,
i.e. `5/8 ≤ log 2 / log 3`, used at both scales:

  `shellLevel M = ⌊5M/8⌋`  (shell condition `3 ^ k ≤ 2 ^ M`)
  `shellBudget M = ⌊5k/8⌋`  (gap condition `3 ^ J₀ < 2 ^ k`)

The Hoeffding slack is then *forced*, not chosen: `hoeffdingSlack = 5/8 − 1/2
= 1/8`, the distance from the budget ratio down to the mean ones-ratio. The
decay rate `2 · hoeffdingSlack² = 1/32` follows, giving
`exp(−shellLevel M / 32) ≈ exp(−5M/256)` per shell. See the "One ratio, used
twice" section of `CC/Density/ShellExceptional.lean`.

## Companion files

* `CC/Density/BadResidues.lean` — residue-class characterisation of the
  "over budget" filter and its Hoeffding cardinality bound.
* `CC/Density/ShellCount.lean` — shell-level counting bound
  `≤ 2 ^ M · exp (−2 t² k)` via the fiber decomposition of the shell.
* `CC/Density/DescentFromResidue.lean` — the descent bridge, for a general
  level `k`: a "good" residue class mod `2 ^ k` forces `T ^ [k] n < n` on any
  `n ≥ 3 ^ k`.
* `CC/Density/ShellExceptional.lean` — the concrete choice `shellLevel`,
  `shellBudget`, the shell inclusion, and the ratio decay to zero.
-/

namespace CC

namespace Density

open CET.QuantitativeDensity in
/-- **Terras density-1** [Ter76]. The set of positive integers with finite
Collatz stopping time has natural density one under the compact map `CC.T`.

Proved via the four-step roadmap above. The set is the dyadic assembly of the
constant family `fun _ => {n | Descends n}`, whose shell exceptional
fraction vanishes by `shellExceptionalRatio_Descends_tendsto_zero`. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem hasNaturalDensityOne_stopping_time_ne_top :
    HasNaturalDensityOne {n | CC.stopping_time n ≠ ⊤} := by
  have hassemble : ({n | Descends n} : Set ℕ)
      = assembleDyadic (fun _ => {n | Descends n}) := by
    ext n; simp [assembleDyadic]
  rw [← setOf_Descends_eq, hassemble]
  exact hasNaturalDensityOne_assembleDyadic _
    shellExceptionalRatio_Descends_tendsto_zero

end Density

end CC
