/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

/-!
# The Waring number `g(n)`

Waring's problem asks for the least number `g(n)` of `n`-th powers needed to represent every
positive integer as their sum.  This file records the two basic objects — the "sum of `s`
`n`-th powers" relation and the Waring number itself — together with the one structural fact
that makes `g` a well-defined threshold: representability is monotone in the number of summands
(pad with `0ⁿ = 0`).

These are the general definitions underlying the ideal-formula analysis
`g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ - 2` (Dickson–Pillai–Rubugunday–Niven; see `BB13.Waring`).

## Main definitions

* `Nat.IsSumOfPowers n s N` — `N` is a sum of `s` nonnegative `n`-th powers.
* `Nat.waringNumber n` — the least `s` such that *every* natural number is a sum of `s`
  nonnegative `n`-th powers.

## Main results

* `Nat.IsSumOfPowers.mono` — for `n ≥ 1`, representability with `s` summands implies
  representability with any `t ≥ s` (pad with zeros).
* `Nat.waringNumber_two` — `g(2) = 4`: Lagrange's four-square theorem gives `≤ 4`, and `7`,
  which needs four squares, gives `≥ 4`.
-/

namespace Nat

/-- `IsSumOfPowers n s N`: the natural number `N` is a sum of `s` nonnegative `n`-th powers.
Zeros are allowed (`0ⁿ = 0` once `n ≥ 1`), so this expresses "a sum of *at most* `s` positive
`n`-th powers". -/
def IsSumOfPowers (n s N : ℕ) : Prop := ∃ f : Fin s → ℕ, N = ∑ i, f i ^ n

/-- The **Waring number** `g(n)`: the least `s` such that *every* natural number is a sum of `s`
nonnegative `n`-th powers.  (Waring's theorem guarantees the defining set is nonempty for
`n ≥ 1`; when it is empty `sInf` returns `0` by convention.) -/
noncomputable def waringNumber (n : ℕ) : ℕ := sInf {s | ∀ N, IsSumOfPowers n s N}

/-- **Representability is monotone in the number of summands** (for `n ≥ 1`): pad an
`s`-term representation with `t - s` copies of `0ⁿ = 0`. -/
theorem IsSumOfPowers.mono {n s t N : ℕ} (hn : 1 ≤ n) (hst : s ≤ t)
    (h : IsSumOfPowers n s N) : IsSumOfPowers n t N := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨Fin.snoc f 0, ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [zero_pow (by omega : n ≠ 0), add_zero]
    exact hf

/-- **Every natural number is a sum of four squares** (Lagrange), in `IsSumOfPowers` form. -/
theorem isSumOfPowers_two_four (N : ℕ) : IsSumOfPowers 2 4 N := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares N
  exact ⟨![a, b, c, d], by rw [Fin.sum_univ_four]; simpa using h.symm⟩

/-- **`7` is not a sum of three squares** — the obstruction that makes `g(2) = 4`. -/
theorem not_isSumOfPowers_two_three_seven : ¬ IsSumOfPowers 2 3 7 := by
  rintro ⟨f, hf⟩
  rw [Fin.sum_univ_three] at hf
  set a := f 0 with ha
  set b := f 1 with hb
  set c := f 2 with hc
  have hbound : ∀ x : ℕ, x ^ 2 ≤ 7 → x ≤ 2 := by
    intro x hx
    by_contra hcon
    have h3 : 3 ≤ x := by omega
    have : 9 ≤ x ^ 2 := by calc (9 : ℕ) = 3 ^ 2 := by norm_num
                                _ ≤ x ^ 2 := Nat.pow_le_pow_left h3 2
    omega
  have ha2 : a ≤ 2 := hbound a (by omega)
  have hb2 : b ≤ 2 := hbound b (by omega)
  have hc2 : c ≤ 2 := hbound c (by omega)
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega

/-- **`g(2) = 4`**: the Waring number of the squares.  `≤ 4` is Lagrange's four-square theorem;
`≥ 4` holds because `7 = 4 + 1 + 1 + 1` needs four of them. -/
theorem waringNumber_two : waringNumber 2 = 4 := by
  have hmem : (4 : ℕ) ∈ {s | ∀ N, IsSumOfPowers 2 s N} := fun N => isSumOfPowers_two_four N
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hmem' := Nat.sInf_mem ⟨4, hmem⟩
  exact not_isSumOfPowers_two_three_seven
    (IsSumOfPowers.mono (by norm_num) (by omega : waringNumber 2 ≤ 3) (hmem' 7))

end Nat
