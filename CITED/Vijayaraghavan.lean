/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Round
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Vijayaraghavan's theorem: `{θⁿ}` has infinitely many limit points for rational `θ > 1` (Vij40)

T. Vijayaraghavan's 1940 note settles the structure of `G(θ)`, the set of limit points of the
fractional parts `{θⁿ}` (`n = 1, 2, 3, …`), for a *rational* base:

> **Theorem** ([Vij40]). If `θ = p/q` with `(p, q) = 1` and `p > q > 1`, then `G(θ)` consists of an
> infinity of points.

The one-page proof is elementary: if `G(θ)` were finite (say `{ξ₁, …, ξ_k}`), the recentred residues
`εₙ = fₙ − ξ_{l(n)}` would eventually satisfy the *exact* dilation `εₙ₊₁ = (p/q)·εₙ` (its `(A)`–`(D)`),
forcing `|εₙ| → ∞` — impossible, since `εₙ` is a bounded fractional residue. (Weil supplied a second
proof, also in the note.)

## Role in the `(3/2)ⁿ` program

This is **milestone M2** of the `(ξ(3/2)ⁿ)` equidistribution ladder (report2-weyl §5): the base `θ = 3/2`
(`p = 3`, `q = 2`) is exactly the coprime, non-integer, `p > q > 1` case, so the fractional parts
`{(3/2)ⁿ}` have infinitely many limit points (`limitPoints_three_halves_infinite`). It sits one rung
above M1 (`TH.not_eventually_periodic`, the aperiodicity of the parity/steering word) and below the
open density (M5) and equidistribution (M7) rungs. Recorded as a cited `axiom` on the authority of the
refereed 1940 note; the `3/2` instance is derived from it.

## Contents
* `limitPoints θ` — the set of limit points (cluster points along `atTop`) of `n ↦ {θⁿ}`.
* `limitPoints_infinite` — **Vijayaraghavan's theorem** ([Vij40]), a cited `axiom`.
* `limitPoints_three_halves_infinite` — the `θ = 3/2` corollary (**M2**), proved from the axiom.

## References
* [Vij40] Vijayaraghavan, T. "On the fractional parts of the powers of a number (I)."
  *Journal of the London Mathematical Society* **1.2** (1940), 159–160.
-/

namespace Vijayaraghavan

/-- `limitPoints θ` is `G(θ)`: the set of limit points of the sequence of fractional parts
`n ↦ Int.fract (θⁿ)`, i.e. the cluster points of that sequence along `atTop`.  A real `x` lies in it
iff some subsequence of `{θⁿ}` converges to `x`. -/
@[category API, AMS 11 37, ref "Vij40", group "three_halves_limit_points"]
def limitPoints (θ : ℝ) : Set ℝ :=
  {x : ℝ | MapClusterPt x Filter.atTop (fun n : ℕ => Int.fract (θ ^ n))}

/-- **Vijayaraghavan's theorem** ([Vij40]): for a rational base `θ = p/q` in lowest terms with
`p > q > 1`, the set of limit points of `{θⁿ}` is infinite.  A cited transcendence-free but
unformalised classical result, recorded as an `axiom`. -/
@[category research solved, AMS 11 37, ref "Vij40", group "three_halves_limit_points"]
axiom limitPoints_infinite (p q : ℕ) (hcop : Nat.Coprime p q) (hq : 1 < q) (hpq : q < p) :
    (limitPoints ((p : ℝ) / q)).Infinite

/-- **Milestone M2** (report2-weyl §5): the fractional parts of `(3/2)ⁿ` have infinitely many limit
points.  The `θ = 3/2` case of `limitPoints_infinite` (`p = 3`, `q = 2`). -/
@[category research solved, AMS 11 37, ref "Vij40", group "three_halves_limit_points"]
theorem limitPoints_three_halves_infinite : (limitPoints (3 / 2)).Infinite := by
  have h := limitPoints_infinite 3 2 (by decide) (by norm_num) (by norm_num)
  rw [show ((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = (3 / 2 : ℝ) by norm_num] at h
  exact h

end Vijayaraghavan
