/-
(C) 2026 Nikolay Metchev, in collaboration with GitHub Copilot.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Density.ParityBadSet
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The descent-from-residue bridge for Terras density-1

Step 3 of the roadmap in [CC/Density/TerrasDensity.lean](./TerrasDensity.lean):
the mathematical bridge that turns the residue-side "not too many odd steps"
condition into an integer-side descent `T ^ [k] n < n`.

## The three pieces

The linear decomposition of `CC/Decomposition.lean` states
  `2 ^ k · T ^ [k] n = 3 ^ (num_odd_steps k n) · n + decomposition_correction k n`.
So `T ^ [k] n < n` reduces to
  `Q(k,n) + 3 ^ J · n + 1 ≤ 2 ^ k · n`
where `J = num_odd_steps k n` and `Q = decomposition_correction k n`. Two
ingredients bound the two summands away from `2 ^ k · n`:

1. **Correction bound.** `decomposition_correction_add_pow_two_le_pow_three`:
   `Q(k,n) + 2 ^ k ≤ 3 ^ k`, i.e., `Q(k,n) ≤ 3 ^ k − 2 ^ k`. Proof by
   induction on `k`, splitting on the parity bit `X (T ^ [k] n) ∈ {0, 1}`.
2. **Ones-gap.** `3 ^ J + 1 ≤ 2 ^ k` (i.e., `3 ^ J < 2 ^ k`, delivered by the
   `¬ (n : ZMod (2^k)) ∈ badResidues k K` hypothesis via
   `oddCount_natCast`).
3. **Shell size.** `n ≥ 3 ^ k` (delivered on the shell `[2 ^ M, 2 ^ (M+1))`
   whenever `M · log 2 ≥ k · log 3`).

Combining, the residue-side hypothesis `r ∉ badResidues k K` with the shell
condition and a Nat-safe rearrangement of ones-gap yields `T ^ [k] n < n`:
`descent_of_not_mem_badResidues`.
-/

namespace CC

namespace Density

/-! ### Bound on the additive correction -/

/-- **Correction bound.** The Terras additive correction after `k` steps
satisfies `Q(k,n) ≤ 3 ^ k − 2 ^ k`, written Nat-safely as
`Q(k,n) + 2 ^ k ≤ 3 ^ k`.

Proof by induction: at `k + 1`, the recursion
`Q(k+1) = 3 ^ x · Q(k) + 2 ^ k · x` with `x = X (T ^ [k] n) ∈ {0, 1}` splits
into two arithmetic cases, both closed via the inductive bound `Q(k) + 2^k ≤ 3^k`
and the elementary `3^k ≥ 2^k`. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem decomposition_correction_add_pow_two_le_pow_three (k n : ℕ) :
    CC.decomposition_correction k n + 2 ^ k ≤ 3 ^ k := by
  induction k with
  | zero => simp [CC.decomposition_correction]
  | succ k ih =>
    have hx : X (T_iter k n) ≤ 1 := by rw [X_eq_mod]; omega
    have h2le3 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
    -- Unfold Q(k+1) and split on the parity bit x = X (T^[k] n).
    simp only [CC.decomposition_correction]
    rcases (show X (T_iter k n) = 0 ∨ X (T_iter k n) = 1 by omega) with h | h
    · -- x = 0: Q(k+1) = Q(k). Goal reduces to Q(k) + 2^(k+1) ≤ 3^(k+1).
      rw [h]; simp only [pow_zero, one_mul, mul_zero, add_zero]
      -- Q(k) + 2·2^k ≤ (Q(k) + 2^k) + 2^k ≤ 3^k + 3^k ≤ 3·3^k = 3^(k+1).
      have h_pow_succ_2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      have h_pow_succ_3 : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
      omega
    · -- x = 1: Q(k+1) = 3·Q(k) + 2^k.
      rw [h]; simp only [pow_one, mul_one]
      -- 3·Q(k) + 2^k + 2·2^k = 3·(Q(k) + 2^k) ≤ 3·3^k = 3^(k+1).
      have h_pow_succ_2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      have h_pow_succ_3 : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
      omega

/-! ### Algebraic descent from a gap -/

/-- **Algebraic descent.** Given the additive gap
`Q(k,n) + 3 ^ J · n + 1 ≤ 2 ^ k · n` (with `J = num_odd_steps k n`),
the linear decomposition of `CC/Decomposition.lean` immediately delivers
`T ^ [k] n < n`. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem descent_of_gap {k n : ℕ}
    (h : CC.decomposition_correction k n
          + 3 ^ CC.num_odd_steps k n * n + 1 ≤ 2 ^ k * n) :
    T_iter k n < n := by
  have hlin := CC.linear_decomposition k n
  -- 2^k · T^[k] n = 3^J · n + Q, so h gives 2^k · T^[k] n < 2^k · n.
  have hprod : 2 ^ k * T_iter k n < 2 ^ k * n := by
    have : 2 ^ k * T_iter k n + 1 ≤ 2 ^ k * n := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left hprod

/-! ### Descent from few odd steps -/

/-- **Descent from few odd steps.** If the ones-count is strictly below the
gap threshold (`3 ^ J + 1 ≤ 2 ^ k`, equivalently `3 ^ J < 2 ^ k`) and the
starting value is large (`n ≥ 3 ^ k`), then `T ^ [k] n < n`.

The shell-side hypothesis `3 ^ k ≤ n` is what forces the argument to be
applied on shells `[2 ^ M, 2 ^ (M+1))` with `M` large in relation to `k`
(specifically, `M · log 2 ≥ k · log 3`, i.e., `k / M < log 2 / log 3`). -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem descent_of_low_num_odd_steps {k n : ℕ}
    (hcont : 3 ^ CC.num_odd_steps k n + 1 ≤ 2 ^ k)
    (hn : 3 ^ k ≤ n) :
    T_iter k n < n := by
  apply descent_of_gap
  have hcorr := decomposition_correction_add_pow_two_le_pow_three k n
  have h2k_pos : (1 : ℕ) ≤ 2 ^ k := Nat.two_pow_pos k
  -- `(3^J + 1) · n ≤ 2^k · n`, expanded: `3^J · n + n ≤ 2^k · n`.
  have hmul : (3 ^ CC.num_odd_steps k n + 1) * n ≤ 2 ^ k * n :=
    Nat.mul_le_mul_right n hcont
  have hmul_dist :
      3 ^ CC.num_odd_steps k n * n + n ≤ 2 ^ k * n := by
    have hexpand : (3 ^ CC.num_odd_steps k n + 1) * n
        = 3 ^ CC.num_odd_steps k n * n + n := by ring
    omega
  -- `n ≥ 3^k ≥ Q + 2^k ≥ Q + 1`, so `Q + 1 ≤ n`, then chain with hmul_dist.
  omega

/-! ### Monotonicity in the ones-count -/

/-- A monotone form of `descent_of_low_num_odd_steps`: it suffices to know
`num_odd_steps k n` is bounded above by some `J₀` with `3 ^ J₀ + 1 ≤ 2 ^ k`. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem descent_of_num_odd_steps_le {k J₀ n : ℕ}
    (hJ : CC.num_odd_steps k n ≤ J₀)
    (hgap : 3 ^ J₀ + 1 ≤ 2 ^ k)
    (hn : 3 ^ k ≤ n) :
    T_iter k n < n := by
  apply descent_of_low_num_odd_steps _ hn
  have h3pow : 3 ^ CC.num_odd_steps k n ≤ 3 ^ J₀ :=
    Nat.pow_le_pow_right (by norm_num) hJ
  omega

/-! ### The residue-side bridge -/

/-- The residue-side reformulation of "not too many odd steps": if the
residue class of `n` mod `2 ^ k` is not in the "bad" set `badResidues k K`,
then `n` has strictly fewer than `k - K` odd steps in its first `k` Terras
iterates. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem num_odd_steps_lt_of_not_mem_badResidues {k K n : ℕ}
    (h : (n : ZMod (2 ^ k)) ∉ badResidues k K) :
    CC.num_odd_steps k n < k - K := by
  by_contra hle
  simp only [not_lt] at hle
  apply h
  rw [natCast_mem_badResidues]
  exact hle

/-- **Descent from a good residue class.** If `n` lies on a shell large
enough (`3 ^ k ≤ n`), its residue class is not bad
(`(n : ZMod (2^k)) ∉ badResidues k K`), and the gap threshold is met
(`3 ^ (k - K - 1) + 1 ≤ 2 ^ k`), then `T ^ [k] n < n`.

This is the residue-side descent lemma that the density transport consumes:
membership of a good residue class forces descent within `k` Terras steps. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem descent_of_not_mem_badResidues {k K n : ℕ}
    (hK : 1 ≤ k - K)
    (h_not_bad : (n : ZMod (2 ^ k)) ∉ badResidues k K)
    (hgap : 3 ^ (k - K - 1) + 1 ≤ 2 ^ k)
    (hn : 3 ^ k ≤ n) :
    T_iter k n < n := by
  apply descent_of_num_odd_steps_le (J₀ := k - K - 1) _ hgap hn
  have := num_odd_steps_lt_of_not_mem_badResidues h_not_bad
  omega

end Density

end CC
