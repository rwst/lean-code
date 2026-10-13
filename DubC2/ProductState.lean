/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NearestStep
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The product state: parity, the residue mod `5`, and the residue graph

Milestone M3 of `plans/plan-dubC2.html`, second layer.  The divisor set under test is
`𝒫 = {2, 5}`, so *avoidance* at step `n` means `xₙ` is odd **and** not divisible by `5`
(`DubC2.Avoids`).  The parity half already paid for itself in `DubC2/NearestStep.lean`: it
collapses the alphabet to `{−1, +1}` and makes the letter a function of `yₙ`.  This file adds
the second arithmetic coordinate, `rₙ = xₙ mod 5`, and reads off its transition graph.

## The residue graph

From `2x_{n+1} = 3xₙ + sₙ` and `2⁻¹ ≡ 3 (mod 5)` the residue map is `r ↦ 4r + 3s`:

| `rₙ` | letter `A` (`s = −1`) | letter `B` (`s = +1`) |
|---|---|---|
| `1` | `1` | `2` |
| `2` | `0` — **forbidden** | `1` |
| `3` | `4` | `0` — **forbidden** |
| `4` | `3` | `4` |

Two facts do all the work downstream.

* The graph splits into the two invariant components `{1,2}` and `{3,4}`; there is no edge
  between them, so an avoiding orbit lives in one of them forever.
* Each component has exactly one forbidden letter, at exactly one residue: `A` is impossible at
  `r = 2`, and `B` is impossible at `r = 3`.  Since the letter is a function of `yₙ`
  (`DubC2.stepA`/`DubC2.stepB`), each of these is a *window* constraint on `yₙ` — which is how
  the arithmetic coordinate and the interval coordinate talk to each other.

## Main results

* `DubC2.Avoids` — the avoidance predicate for `𝒫 = {2,5}`.
* `DubC2.stepA'`, `DubC2.stepB'` — the branch table in avoiding form.
* `DubC2.res_A_one`, … — the six edges of the table above.
* `DubC2.half_le_yN_of_res_two` — `A` is impossible at `r = 2`, i.e. `r = 2 ⇒ yₙ ≥ ½`.
* `DubC2.yN_lt_half_of_res_three` — `B` is impossible at `r = 3`, i.e. `r = 3 ⇒ yₙ < ½`.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648.
* [FS67] R. Forman, H. N. Shapiro, *An arithmetic property of certain rational powers*, Comm.
  Pure Appl. Math. **20** (1967), 561–573.
-/

namespace DubC2

variable {ξ : ℝ} {n : ℕ}

/-- **Avoidance of `𝒫 = {2, 5}` at step `n`**: `xₙ` is divisible neither by `2` nor by `5`. -/
def Avoids (ξ : ℝ) (n : ℕ) : Prop := ¬ (2 : ℤ) ∣ xN ξ n ∧ ¬ (5 : ℤ) ∣ xN ξ n

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem Avoids.two (h : Avoids ξ n) : ¬ (2 : ℤ) ∣ xN ξ n := h.1

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem Avoids.five (h : Avoids ξ n) : xN ξ n % 5 ≠ 0 := by
  have := h.2; omega

/-- An avoiding term has residue `1`, `2`, `3` or `4` mod `5`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem Avoids.res_mem (h : Avoids ξ n) :
    xN ξ n % 5 = 1 ∨ xN ξ n % 5 = 2 ∨ xN ξ n % 5 = 3 ∨ xN ξ n % 5 = 4 := by
  have := h.five; omega

/-! ## The branch table in avoiding form -/

/-- Branch `A` under avoidance. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem stepA' (h : Avoids ξ n) (hy : yN ξ n < 1 / 2) :
    sN ξ n = -1 ∧ 4 * yN ξ (n + 1) = 6 * yN ξ n + 1 ∧
      2 * xN ξ (n + 1) = 3 * xN ξ n - 1 := stepA h.two hy

/-- Branch `B` under avoidance. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem stepB' (h : Avoids ξ n) (hy : 1 / 2 ≤ yN ξ n) :
    sN ξ n = 1 ∧ 4 * yN ξ (n + 1) = 6 * yN ξ n - 3 ∧
      2 * xN ξ (n + 1) = 3 * xN ξ n + 1 := stepB h.two hy

/-! ## The six edges of the residue graph -/

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem res_A_one (hst : 2 * xN ξ (n + 1) = 3 * xN ξ n - 1) (hr : xN ξ n % 5 = 1) :
    xN ξ (n + 1) % 5 = 1 := by omega

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem res_A_three (hst : 2 * xN ξ (n + 1) = 3 * xN ξ n - 1) (hr : xN ξ n % 5 = 3) :
    xN ξ (n + 1) % 5 = 4 := by omega

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem res_A_four (hst : 2 * xN ξ (n + 1) = 3 * xN ξ n - 1) (hr : xN ξ n % 5 = 4) :
    xN ξ (n + 1) % 5 = 3 := by omega

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem res_B_one (hst : 2 * xN ξ (n + 1) = 3 * xN ξ n + 1) (hr : xN ξ n % 5 = 1) :
    xN ξ (n + 1) % 5 = 2 := by omega

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem res_B_two (hst : 2 * xN ξ (n + 1) = 3 * xN ξ n + 1) (hr : xN ξ n % 5 = 2) :
    xN ξ (n + 1) % 5 = 1 := by omega

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem res_B_four (hst : 2 * xN ξ (n + 1) = 3 * xN ξ n + 1) (hr : xN ξ n % 5 = 4) :
    xN ξ (n + 1) % 5 = 4 := by omega

/-! ## The two forbidden letters, read as windows on `yₙ` -/

/-- **`A` is impossible at `r = 2`.**  Since the letter is a function of `yₙ`, residue `2`
forces `yₙ ≥ ½`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem half_le_yN_of_res_two (h : Avoids ξ n) (h' : Avoids ξ (n + 1)) (hr : xN ξ n % 5 = 2) :
    1 / 2 ≤ yN ξ n := by
  by_contra hy
  push Not at hy
  obtain ⟨-, -, hst⟩ := stepA' h hy
  have := h'.five
  omega

/-- **`B` is impossible at `r = 3`.**  Residue `3` forces `yₙ < ½`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem yN_lt_half_of_res_three (h : Avoids ξ n) (h' : Avoids ξ (n + 1)) (hr : xN ξ n % 5 = 3) :
    yN ξ n < 1 / 2 := by
  by_contra hy
  push Not at hy
  obtain ⟨-, -, hst⟩ := stepB' h hy
  have := h'.five
  omega

end DubC2
