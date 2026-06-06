/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Dyadic decomposition of sums over `ℕ`-intervals

Two `Finset.sum` identities splitting a sum over an `ℕ`-interval into its dyadic (doubling) blocks:

* `Finset.sum_Ico_two_pow_mul` — the **anchored** form: `[a, 2^{P+1}·a)` is tiled by the blocks
  `[2ᵗ·a, 2ᵗ⁺¹·a)`, `t = 0, …, P`.
* `Finset.sum_Ico_one_two_pow` — the `a = 1` special case: `[1, 2^{K+1})` is tiled by
  `[2ᵏ, 2ᵏ⁺¹)`, `k = 0, …, K`.

Both hold in any `AddCommMonoid`; the proof is a short induction gluing consecutive blocks with
`Finset.sum_Ico_consecutive`.
-/

namespace Finset

variable {M : Type*} [AddCommMonoid M]

/-- The doubling blocks `[2ᵗ·a, 2ᵗ⁺¹·a)`, `t = 0, …, P`, tile `[a, 2^{P+1}·a)`:
`∑_{i ∈ [a, 2^{P+1}·a)} f i = ∑_{t ≤ P} ∑_{i ∈ [2ᵗ·a, 2ᵗ⁺¹·a)} f i`. -/
theorem sum_Ico_two_pow_mul (f : ℕ → M) (a P : ℕ) :
    ∑ i ∈ Finset.Ico a (2 ^ (P + 1) * a), f i
      = ∑ t ∈ Finset.range (P + 1), ∑ i ∈ Finset.Ico (2 ^ t * a) (2 ^ (t + 1) * a), f i := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_range_succ, ← ih]
    refine (Finset.sum_Ico_consecutive f ?_ ?_).symm
    · exact Nat.le_mul_of_pos_left a (by positivity)
    · gcongr <;> omega

/-- Dyadic grouping: the sum over `[1, 2^{K+1})` splits into the doubling blocks `[2ᵏ, 2ᵏ⁺¹)`,
`k = 0, …, K`. The `a = 1` case of `Finset.sum_Ico_two_pow_mul`. -/
theorem sum_Ico_one_two_pow (f : ℕ → M) (K : ℕ) :
    ∑ i ∈ Finset.Ico 1 (2 ^ (K + 1)), f i
      = ∑ k ∈ Finset.range (K + 1), ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f i := by
  simpa only [mul_one] using sum_Ico_two_pow_mul f 1 K

end Finset
