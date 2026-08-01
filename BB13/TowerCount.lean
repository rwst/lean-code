/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.GapPrinciple
import ForMathlib.Combinatorics.GeometricGrowthCount

/-!
# The `O(log N)` tower count for Problem 10.13 (deliverable D1 / T4)

The elementary payoff of `plans/plan-1013.html`: the failures of `‖(p/q)ⁿ‖ < cⁿ` decompose
into **towers**, and the number of towers below `N` is `O(log N)`, unconditionally and with an
explicit constant — no Diophantine input.

By the linkage lemma (`BB13.GapPrinciple`), any two failures within distance `d < ε·n` are
linked, one a `pᵈ`-scaling of the other.  A **tower base** (`BB13.IsTowerBase`) is a failure not
linked to any smaller failure, so two distinct tower bases `a < b` are *not* linked; the gap
`gap_of_nonlink` then gives `ρ·a ≤ b` for a ratio `ρ` approaching `1 + ε`.  Feeding this to the
geometric-growth count `card_le_logb_of_geomGap_above` bounds the number of tower bases below `N`
by `t + 1 + logᵨ N`.

Since `ε = log(1/c)/log p` (`= log(4/3)/log 3 = 0.26186…` for `(3, 2, 3/4)`), the sharp tower
ratio is `1 + ε = 1.26186…` and the asymptotic count is `1/log(1.26186…) = 4.30 ln N` towers
(plan §3, D4 — the M1 sharpening of the cruder `6.72 ln N`).  The theorem below realises any
ratio `ρ < 1 + ε` at the cost of an explicit threshold `t`; `t → ∞` recovers the sharp `4.30`.

This bounds the number of *towers* (T4), not the number of failures (T1): bounding the height of
each tower — the count of `E(n, d)`-events — is the Diophantine/subspace layer (D2, milestones
M3–M4), out of scope for this elementary note.

## Contents

* `BB13.towerBases_card_le` — general `(p/q, c)`: any finite set of tower bases in `[1, N]` has
  at most `t + (1 + logᵨ N)` elements, under the transparent threshold relation on `ρ, t`.
* `BB13.towerBases_card_le_three_halves` — the headline case `(3, 2, 3/4)` with `ρ = 6/5`,
  `t = 11`, modulo the standard numeric bounds `log 2 ≥ 0.6931`, `log 3 ≤ 1.0987`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
-/

namespace BB13

open scoped Real

/-- **`O(log N)` tower count** (general `(p/q, c)`).  Let `S` be any finite set of tower bases
in `[1, N]`.  If `ρ > 1` and the threshold relation `log 2 ≤ t·(log(1/c) − (ρ−1)·log p)` holds,
then `#S ≤ t + (1 + logᵨ N)`.

The relation forces `ρ < 1 + ε` with `ε = log(1/c)/log p`; as `t → ∞` one may take `ρ ↑ 1 + ε`,
giving the sharp asymptotic constant `1/log(1 + ε)` (`= 4.30…` for `(3, 2, 3/4)`, plan D4). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem towerBases_card_le (p q : ℕ) (c ρ : ℝ) (t N : ℕ)
    (hp1 : 1 < p) (hc0 : 0 < c) (ht1 : 1 ≤ t) (hρ1 : 1 < ρ)
    (hthr : Real.log 2 ≤ (t : ℝ) * (Real.log (1 / c) - (ρ - 1) * Real.log p))
    (S : Finset ℕ) (hbase : ∀ n ∈ S, IsTowerBase p q c n)
    (h1 : ∀ n ∈ S, 1 ≤ n) (hN : ∀ n ∈ S, n ≤ N) :
    (S.card : ℝ) ≤ t + (1 + Real.logb ρ N) := by
  refine card_le_logb_of_geomGap_above ρ hρ1 t N S h1 hN ?_
  intro a ha b hb hta hab
  have hfa : IsFailure p q c a := (hbase a ha).1
  have hnl : ¬ Linkable p c a b := (hbase b hb).2 a hab hfa
  rw [Linkable, not_le] at hnl
  exact gap_of_nonlink p c ρ a b t hp1 hc0 hab hta ht1 hnl hthr

/-- **`O(log N)` tower count for `‖(3/2)ⁿ‖ < (3/4)ⁿ`** (Problem 10.13 proper).  Any finite set
`S` of tower bases in `[1, N]` has at most `11 + (1 + log_{6/5} N) ≈ 12 + 5.49 ln N` elements.

The two numeric inputs `log 2 ≥ 0.6931` (Mathlib's `Real.log_two_gt_d9`) and `log 3 ≤ 1.0987`
are standard.  The ratio `6/5` and threshold `11` are a clean witness; the sharp asymptotic
`1/log(1.26186…) = 4.30 ln N` towers (plan D4) is obtained by pushing `ρ ↑ 1 + ε` in
`towerBases_card_le`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem towerBases_card_le_three_halves (N : ℕ) (S : Finset ℕ)
    (hbase : ∀ n ∈ S, IsTowerBase 3 2 (3 / 4) n)
    (h1 : ∀ n ∈ S, 1 ≤ n) (hN : ∀ n ∈ S, n ≤ N)
    (hlog2 : (0.6931 : ℝ) ≤ Real.log 2) (hlog3 : Real.log 3 ≤ (1.0987 : ℝ)) :
    (S.card : ℝ) ≤ 11 + (1 + Real.logb (6 / 5) N) := by
  refine towerBases_card_le 3 2 (3 / 4) (6 / 5) 11 N (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ S hbase h1 hN
  have hlog43 : Real.log (1 / (3 / 4 : ℝ)) = 2 * Real.log 2 - Real.log 3 := by
    rw [show (1 / (3 / 4 : ℝ)) = 4 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hlog43, show ((3 : ℕ) : ℝ) = 3 by norm_num]
  nlinarith [hlog2, hlog3]

end BB13
