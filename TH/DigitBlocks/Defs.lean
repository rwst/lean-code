/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Digit-block counting vocabulary for the binary expansion of an integer

The counting functions on which the digit-block theorems B1–B3 of [A4+] are
stated.  All are `Finset.card` filters over `Nat.testBit` indices (**LSB = index
0**), taken over the window `[0, M)` of adjacent-bit positions below the top bit
`M := ⌊log₂ n⌋` (so a filter over `Finset.range M` ranges over the pairs
`(0,1), …, (M−1, M)` and thus sees every one of the `M+1` binary digits of `n`).

* `transitionCount n` — the number of positions `i < M` with `bitᵢ ≠ bitᵢ₊₁`,
  i.e. the count of **digit changes** in the binary expansion of `n`.  The
  number of maximal equal-digit **blocks** is `transitionCount n + 1`.

## Orientation dictionary

Writing `n` MSB-first as a string, a "transition at `i`" is a boundary between
two adjacent digits.  For `n = 3^5 = 243 = 11110011₂` the blocks are
`[1111][00][11]` (3 blocks), so there are `2` digit changes — `transitionCount`
counts the **changes**, not the blocks.  (The count of blocks is the quantity of
Bugeaud–Kaneko [BK17] Rem. 4.4 / Blecksmith–Filaseta–Nicol [BFN93].)

## Contents

* `transitionCount` — digit-change count (`category API`).
* `transitionCount_three_pow_five` — sanity: `transitionCount (3^5) = 2`.

## References

* [A4+] `plan-A4+.html` (this repository, 2026-07): §3.1 (B1), §5.2 (this file).
* [BK17] Bugeaud, Kaneko, *On the digital representation of smooth numbers*,
  arXiv:1704.00432 (2017).  (Rem. 4.4: the block count of `3^m`.)
* [BFN93] Blecksmith, Filaseta, Nicol, *A result on the digits of `aⁿ`*, Acta
  Arith. **64** (1993).  (The integer-power block-count precedent.)
-/

namespace TH

/-- The number of binary **digit changes** of `n`: positions `i < ⌊log₂ n⌋` at
which `bitᵢ(n) ≠ bitᵢ₊₁(n)`.  The number of maximal equal-digit blocks is
`transitionCount n + 1`. -/
@[category API, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
def transitionCount (n : ℕ) : ℕ :=
  ((Finset.range (Nat.log 2 n)).filter (fun i => n.testBit i ≠ n.testBit (i + 1))).card

/-- Sanity: `3^5 = 243 = 11110011₂` has blocks `[1111][00][11]`, hence `2`
digit changes. -/
@[category test, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
lemma transitionCount_three_pow_five : transitionCount (3 ^ 5) = 2 := by decide

end TH
