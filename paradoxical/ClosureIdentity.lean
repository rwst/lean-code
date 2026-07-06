/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Decomposition
import Mathlib.Tactic.LinearCombination

/-!
# The circuit-closure identity for paradoxical Collatz sequences

The **closure identity** underlying the bounded-circuit (Baker) construction of
`length-bound.html` §1.  For the accelerated map `T(n)=(3n+1)/2` (n odd), `n/2`
(n even), write `j` for the length, `q = num_odd_steps j n` for the number of odd
steps, `s(V) = decomposition_correction j n` for the integer remainder `2^j E_j`,
and `d = T^j(n) - n` for the return difference.  Then

    (2^j - 3^q) · n  =  s(V)  -  2^j · d .

This is *not* in Rozier–Terracol (arXiv:2502.00948); it is the acyclic analogue
of the Steiner / Simons–de Weger circuit calculus, and the algebraic backbone of
the per-`(R,d)` length search (`bounded_circuit_search.py` in this directory).

It is a one-line consequence of the fundamental decomposition
`CC.linear_decomposition`:  `2^j · T^j(n) = 3^q · n + s(V)`.  Rearranging with
`d = T^j(n) - n` gives the identity; the remainder `s(V)` depends only on the
parity vector (residue mod `2^j`) by `CC.decomposition_correction_eq_of_E_vec_eq`,
and its per-burst circuit-sum form is `CC.decomposition_correction_eq_sum`.

Two forms are given: an unconditional integer identity `closure_identity`, and
the paper's boxed natural-number form `closure_identity_nat` (valid in the
paradoxical regime `3^q ≤ 2^j`, `n ≤ T^j n`), together with the paradoxical
corollary `closure_identity_of_paradoxical` phrased in condition (i) `C_j < 1`.

All results are `sorry`-free and depend only on the standard axioms
`propext, Classical.choice, Quot.sound`.
-/

namespace Paradoxical

open CC

/-- Return difference `d = T^j(n) - n`, as an integer (it is `≥ 0` exactly in the
    paradoxical / non-descending case `T^j(n) ≥ n`). -/
def retDiff (j n : ℕ) : ℤ := (T_iter j n : ℤ) - (n : ℤ)

/-- **Closure identity (integer form).**  For every start `n` and length `j`,

    `(2^j - 3^q) · n = s(V) - 2^j · d`,

with `q = num_odd_steps j n`, integer remainder `s(V) = decomposition_correction j n`,
and return difference `d = retDiff j n = T^j(n) - n`.  Holds unconditionally over
`ℤ` (no paradoxicality assumption). -/
theorem closure_identity (j n : ℕ) :
    ((2 : ℤ) ^ j - 3 ^ num_odd_steps j n) * (n : ℤ)
      = (decomposition_correction j n : ℤ) - 2 ^ j * retDiff j n := by
  have h : (2 : ℤ) ^ j * (T_iter j n : ℤ)
      = 3 ^ num_odd_steps j n * (n : ℤ) + (decomposition_correction j n : ℤ) := by
    exact_mod_cast linear_decomposition j n
  simp only [retDiff]
  linear_combination h

/-- **Closure identity (natural / boxed form).**  In the paradoxical regime
    `3^q ≤ 2^j` (condition (i), `C_j ≤ 1`) and `n ≤ T^j n` (condition (ii),
    `d ≥ 0`), the closure identity holds over `ℕ` in the paper's boxed shape

    `(2^j - 3^q) · n + 2^j · d = s(V)`. -/
theorem closure_identity_nat (j n : ℕ)
    (hC : 3 ^ num_odd_steps j n ≤ 2 ^ j) (hd : n ≤ T_iter j n) :
    (2 ^ j - 3 ^ num_odd_steps j n) * n + 2 ^ j * (T_iter j n - n)
      = decomposition_correction j n := by
  have key := closure_identity j n
  simp only [retDiff] at key
  zify [hC, hd]
  linear_combination key

/-- Condition (i) `C_j < 1` gives `3^q < 2^j`, hence `3^q ≤ 2^j`. -/
theorem pow_three_le_of_C_lt_one {j n : ℕ} (hC : C j n < 1) :
    3 ^ num_odd_steps j n ≤ 2 ^ j := by
  have h2 : (0 : ℚ) < 2 ^ j := by positivity
  rw [C, div_lt_one h2] at hC
  have : (3 : ℕ) ^ num_odd_steps j n < 2 ^ j := by exact_mod_cast hC
  exact le_of_lt this

/-- **Closure identity under the paper's paradoxical hypotheses** (i) `C_j < 1`
    and (ii) `T^j n ≥ n`:  `(2^j - 3^q) · n + 2^j · d = s(V)`. -/
theorem closure_identity_of_paradoxical (j n : ℕ)
    (hC : C j n < 1) (hd : n ≤ T_iter j n) :
    (2 ^ j - 3 ^ num_odd_steps j n) * n + 2 ^ j * (T_iter j n - n)
      = decomposition_correction j n :=
  closure_identity_nat j n (pow_three_le_of_C_lt_one hC) hd

end Paradoxical
