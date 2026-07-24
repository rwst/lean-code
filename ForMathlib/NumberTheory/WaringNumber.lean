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

open Finset in
/-- **Pillai's lower bound, summand form.**  The number `2ⁿ⌊(3/2)ⁿ⌋ - 1` is smaller than `3ⁿ`, so
it can only be built from the powers `0ⁿ = 0`, `1ⁿ = 1` and `2ⁿ`; any representation therefore
uses at least `2ⁿ + ⌊(3/2)ⁿ⌋ - 2` of them.  (`⌊(3/2)ⁿ⌋ = 3ⁿ / 2ⁿ` in `ℕ`.)  This is the
elementary half of the ideal Waring formula. -/
theorem le_of_isSumOfPowers_pillai {n s : ℕ} (hn : 2 ≤ n)
    (h : IsSumOfPowers n s (2 ^ n * (3 ^ n / 2 ^ n) - 1)) :
    2 ^ n + 3 ^ n / 2 ^ n - 2 ≤ s := by
  obtain ⟨f, hf⟩ := h
  have hn0 : n ≠ 0 := by omega
  have h2pos : 0 < 2 ^ n := by positivity
  have hq_mul_le : 2 ^ n * (3 ^ n / 2 ^ n) ≤ 3 ^ n := Nat.mul_div_le (3 ^ n) (2 ^ n)
  set q := 3 ^ n / 2 ^ n with hq
  set N := 2 ^ n * q - 1 with hN
  have hqpos : 1 ≤ q := by
    rw [hq]; exact (Nat.one_le_div_iff h2pos).mpr (Nat.pow_le_pow_left (by norm_num) n)
  have hPQpos : 0 < 2 ^ n * q := by positivity
  have hNlt3 : N < 3 ^ n := lt_of_lt_of_le (Nat.sub_lt hPQpos one_pos) hq_mul_le
  -- Every summand base is at most `2`: a base `≥ 3` gives a term `≥ 3ⁿ > N`.
  have hfle : ∀ i, f i ≤ 2 := by
    intro i
    by_contra hc
    have h3 : 3 ≤ f i := by omega
    have hpow : 3 ^ n ≤ f i ^ n := Nat.pow_le_pow_left h3 n
    have hle : f i ^ n ≤ N := by
      rw [hf]
      exact Finset.single_le_sum (f := fun i => f i ^ n) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  set a := (univ.filter (fun i => f i = 2)).card with ha
  -- Per-summand bound `xⁿ ≤ 1 + (2ⁿ-1)·[x = 2]`, valid for `x ∈ {0, 1, 2}`.
  have hterm : ∀ i ∈ (univ : Finset (Fin s)),
      f i ^ n ≤ 1 + (2 ^ n - 1) * (if f i = 2 then 1 else 0) := by
    intro i _
    have hi := hfle i
    interval_cases (f i)
    · simp [zero_pow hn0]
    · simp
    · rw [if_pos rfl]; omega
  -- Summing gives `N ≤ s + (2ⁿ-1)·a`, with `a` the number of `2`-summands.
  have hsum : N ≤ s + (2 ^ n - 1) * a := by
    calc N = ∑ i, f i ^ n := hf
      _ ≤ ∑ i, (1 + (2 ^ n - 1) * (if f i = 2 then 1 else 0)) := Finset.sum_le_sum hterm
      _ = s + (2 ^ n - 1) * a := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          · simp
          · rw [ha, Finset.card_filter]
  -- The `2`-summands alone contribute `a·2ⁿ ≤ N`, so `a ≤ q - 1`.
  have hsub : a * 2 ^ n ≤ N := by
    rw [ha]
    calc (univ.filter (fun i => f i = 2)).card * 2 ^ n
        = ∑ _i ∈ univ.filter (fun i => f i = 2), 2 ^ n := by rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ i ∈ univ.filter (fun i => f i = 2), f i ^ n := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [(Finset.mem_filter.mp hi).2]
      _ ≤ ∑ i, f i ^ n := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = N := hf.symm
  -- Combine, in `ℤ`: `(2ⁿ-1)(q-1-a) ≥ 0` turns the two bounds into `2ⁿ + q - 2 ≤ s`.
  have hNval : (N : ℤ) = (2 : ℤ) ^ n * q - 1 := by rw [hN, Nat.cast_sub hPQpos]; push_cast; ring
  have hsumZ : (N : ℤ) ≤ s + ((2 : ℤ) ^ n - 1) * a := by
    have h1 : (1 : ℕ) ≤ 2 ^ n := h2pos
    zify [h1] at hsum; linarith [hsum]
  have hsubZ : (a : ℤ) * (2 : ℤ) ^ n ≤ N := by exact_mod_cast hsub
  have hP1 : (0 : ℤ) ≤ (2 : ℤ) ^ n - 1 := by
    have : (1 : ℤ) ≤ (2 : ℤ) ^ n := by exact_mod_cast h2pos
    linarith
  have hAQ : (a : ℤ) < q := by
    have h2Z : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
    refine lt_of_mul_lt_mul_right (a := (2 : ℤ) ^ n) ?_ h2Z.le
    nlinarith [hsubZ, hNval]
  have hgoalZ : (2 : ℤ) ^ n + q ≤ s + 2 := by
    nlinarith [hsumZ, hNval, mul_nonneg hP1 (by linarith [hAQ] : (0 : ℤ) ≤ q - 1 - a)]
  have hgoalN : 2 ^ n + q ≤ s + 2 := by exact_mod_cast hgoalZ
  omega

/-- **Pillai's lower bound for the Waring number** (Bugeaud, Distribution Modulo One, (3.22)):
for `n ≥ 2`, if the Waring number is well defined (Hilbert–Waring: the set of universal summand
counts is nonempty), then `g(n) ≥ 2ⁿ + ⌊(3/2)ⁿ⌋ - 2`. -/
theorem pillai_le_waringNumber {n : ℕ} (hn : 2 ≤ n)
    (hne : {s | ∀ N, IsSumOfPowers n s N}.Nonempty) :
    2 ^ n + 3 ^ n / 2 ^ n - 2 ≤ waringNumber n :=
  le_of_isSumOfPowers_pillai hn (Nat.sInf_mem hne _)

end Nat
