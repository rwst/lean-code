/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.Basic

/-!
# The gap principle and linkage lemma for Problem 10.13 (§3 of plan-1013)

The elementary, decisive core of deliverable **D1**: for two failures at `n` and `n' = n + d`,
writing `pⁿ = m·qⁿ + k` and `pⁿ⁺ᵈ = m'·qⁿ⁺ᵈ + k'`, a two-line computation gives the **exact
integer identity** (`gap_identity`)
```
    qⁿ · (pᵈ·m − qᵈ·m')  =  k' − pᵈ·k .
```
Since `|k| < (c·q)ⁿ` and `|k'| < (c·q)ⁿ⁺ᵈ`, the left factor is an integer of absolute value
`< cⁿ·((c·q)ᵈ + pᵈ) ≤ 2·cⁿ·pᵈ`, which is `< 1` — hence **`0`** — as soon as `2·cⁿ·pᵈ ≤ 1`,
i.e. asymptotically `d < ε·n` with `ε = log(1/c)/log p` (`= log(4/3)/log 3 = 0.26186…` for
`(3, 2, 3/4)`; the M1 sharp constant).  The **linkage lemma** then reads off all four
consequences (`linkage`, `link_resid`, `link_dvd`, `link_scaling`, `link_quality`):
```
    pᵈ·m = qᵈ·m',   qᵈ ∣ m,   m' = pᵈ·(m/qᵈ),   k' = pᵈ·k,   |k| < (c·q)ⁿ·pᵈ .
```
This is fully elementary — no Diophantine input — matching `TH.W_closed` of the steering-word
draft (`2ⁿ·W = k' − 3ᵈ·k`, plan §3 ancestry note).

`gap_of_nonlink` turns the *failure* of linkage into a multiplicative gap `ρ·a ≤ b` between two
non-linked failures, the input to the `O(log N)` tower count in `BB13.TowerCount`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957), 122–124 (Thm 1: the qualitative sparsity ancestor of the linkage lemma).
-/

namespace BB13

open scoped Real

/-- **§3 gap identity** (exact, pure ring): `qⁿ·(pᵈ·m − qᵈ·m') = k' − pᵈ·k` where `m = round`,
`k = resid`.  The whole gap principle rests on this one integer identity. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem gap_identity (p q n d : ℕ) :
    (q : ℤ) ^ n * ((p : ℤ) ^ d * Mnum p q n - (q : ℤ) ^ d * Mnum p q (n + d))
      = resid p q (n + d) - (p : ℤ) ^ d * resid p q n := by
  simp only [resid, pow_add]; ring

/-- **Sharp linkage.**  If `n` and `n + d` are both failures and the sharp gap bound
`cⁿ·((c·q)ᵈ + pᵈ) ≤ 1` holds, then `pᵈ·m = qᵈ·m'`: the integer `pᵈ·m − qᵈ·m'` has absolute value
`< 1`, hence vanishes. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linkage (p q : ℕ) (c : ℝ) (n d : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hn : IsFailure p q c n) (hnd : IsFailure p q c (n + d))
    (hthr : c ^ n * ((c * q) ^ d + (p : ℝ) ^ d) ≤ 1) :
    (p : ℤ) ^ d * Mnum p q n = (q : ℤ) ^ d * Mnum p q (n + d) := by
  simp only [IsFailure] at hn hnd
  set X : ℤ := (p : ℤ) ^ d * Mnum p q n - (q : ℤ) ^ d * Mnum p q (n + d) with hXdef
  have hid : (q : ℤ) ^ n * X = resid p q (n + d) - (p : ℤ) ^ d * resid p q n := gap_identity p q n d
  have hqRpos : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hpRpos : (0 : ℝ) < (p : ℝ) ^ d := by positivity
  have hidR : (q : ℝ) ^ n * |(X : ℝ)| = |(resid p q (n + d) : ℝ) - (p : ℝ) ^ d * (resid p q n : ℝ)| := by
    have hcast : ((q : ℝ)) ^ n * (X : ℝ) = (resid p q (n + d) : ℝ) - (p : ℝ) ^ d * (resid p q n : ℝ) := by
      exact_mod_cast hid
    rw [← hcast, abs_mul, abs_of_pos hqRpos]
  have hnR : |(resid p q n : ℝ)| < (c * q) ^ n := by rw [← Int.cast_abs]; exact_mod_cast hn
  have hkey : (q : ℝ) ^ n * |(X : ℝ)| < (c * q) ^ (n + d) + (p : ℝ) ^ d * (c * q) ^ n := by
    rw [hidR]
    calc |(resid p q (n + d) : ℝ) - (p : ℝ) ^ d * (resid p q n : ℝ)|
        ≤ |(resid p q (n + d) : ℝ)| + (p : ℝ) ^ d * |(resid p q n : ℝ)| := by
          calc |(resid p q (n + d) : ℝ) - (p : ℝ) ^ d * (resid p q n : ℝ)|
              ≤ |(resid p q (n + d) : ℝ)| + |(p : ℝ) ^ d * (resid p q n : ℝ)| := abs_sub _ _
            _ = |(resid p q (n + d) : ℝ)| + (p : ℝ) ^ d * |(resid p q n : ℝ)| := by
                rw [abs_mul, abs_of_nonneg (le_of_lt hpRpos)]
      _ < (c * q) ^ (n + d) + (p : ℝ) ^ d * (c * q) ^ n := by
          have hnR' : |(resid p q (n + d) : ℝ)| < (c * q) ^ (n + d) := by
            rw [← Int.cast_abs]; exact_mod_cast hnd
          have : (p : ℝ) ^ d * |(resid p q n : ℝ)| < (p : ℝ) ^ d * (c * q) ^ n :=
            mul_lt_mul_of_pos_left hnR hpRpos
          linarith
  have hrhs : (c * q) ^ (n + d) + (p : ℝ) ^ d * (c * q) ^ n
      = (q : ℝ) ^ n * (c ^ n * ((c * q) ^ d + (p : ℝ) ^ d)) := by
    rw [mul_pow, mul_pow, pow_add]; ring
  rw [hrhs] at hkey
  have hXlt1 : |(X : ℝ)| < 1 := by
    have h2 : (q : ℝ) ^ n * |(X : ℝ)| < (q : ℝ) ^ n * 1 := by
      calc (q : ℝ) ^ n * |(X : ℝ)| < (q : ℝ) ^ n * (c ^ n * ((c * q) ^ d + (p : ℝ) ^ d)) := hkey
        _ ≤ (q : ℝ) ^ n * 1 := mul_le_mul_of_nonneg_left hthr (le_of_lt hqRpos)
    exact lt_of_mul_lt_mul_left h2 (le_of_lt hqRpos)
  have hXint : |X| < 1 := by exact_mod_cast hXlt1
  have hX0 : X = 0 := Int.abs_lt_one_iff.mp hXint
  rw [hXdef] at hX0; linarith [hX0]

/-- **Crude ⟹ sharp threshold.**  `2·cⁿ·pᵈ ≤ 1` (the cleaner `2·pᵈ`-bound of the draft) implies
the sharp bound `cⁿ·((c·q)ᵈ + pᵈ) ≤ 1`, since `(c·q)ᵈ ≤ pᵈ` when `c·q ≤ p`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem crude_to_sharp (p q : ℕ) (c : ℝ) (n d : ℕ) (hc0 : 0 ≤ c) (hcq : c * q ≤ p)
    (hcrude : 2 * c ^ n * (p : ℝ) ^ d ≤ 1) :
    c ^ n * ((c * q) ^ d + (p : ℝ) ^ d) ≤ 1 := by
  have hcqd : (c * q) ^ d ≤ (p : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hcq d
  have hcn : (0 : ℝ) ≤ c ^ n := by positivity
  nlinarith [hcqd, hcn, hcrude]

/-- **Linkage from the `Linkable` predicate.**  If `n` and `n + d` are failures and are linkable
(`2·cⁿ·pᵈ ≤ 1`), then `pᵈ·m = qᵈ·m'`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linkage_of_linkable (p q : ℕ) (c : ℝ) (n d : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc0 : 0 ≤ c) (hcq : c * q ≤ p) (hn : IsFailure p q c n) (hnd : IsFailure p q c (n + d))
    (hlink : Linkable p c n (n + d)) :
    (p : ℤ) ^ d * Mnum p q n = (q : ℤ) ^ d * Mnum p q (n + d) := by
  have hcrude : 2 * c ^ n * (p : ℝ) ^ d ≤ 1 := by
    have : Linkable p c n (n + d) = (2 * c ^ n * (p : ℝ) ^ (n + d - n) ≤ 1) := rfl
    rw [Nat.add_sub_cancel_left] at this
    rwa [this] at hlink
  exact linkage p q c n d hp hq hn hnd (crude_to_sharp p q c n d hc0 hcq hcrude)

/-- **First consequence** `k' = pᵈ·k`: the residues themselves scale by `pᵈ` along a tower. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem link_resid (p q : ℕ) {n d : ℕ}
    (hlink : (p : ℤ) ^ d * Mnum p q n = (q : ℤ) ^ d * Mnum p q (n + d)) :
    resid p q (n + d) = (p : ℤ) ^ d * resid p q n := by
  have hid := gap_identity p q n d
  have hz : (p : ℤ) ^ d * Mnum p q n - (q : ℤ) ^ d * Mnum p q (n + d) = 0 := by rw [hlink]; ring
  rw [hz, mul_zero] at hid; linarith [hid]

/-- **Second consequence** `qᵈ ∣ m` (needs `gcd(p, q) = 1`): the base numerator is divisible by
`qᵈ`, i.e. `v_q(m) ≥ d`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem link_dvd (p q : ℕ) {n d : ℕ} (hcop : Nat.Coprime p q)
    (hlink : (p : ℤ) ^ d * Mnum p q n = (q : ℤ) ^ d * Mnum p q (n + d)) :
    (q : ℤ) ^ d ∣ Mnum p q n := by
  have hcopZ : IsCoprime (q : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact (Nat.coprime_comm.mpr hcop)
  have hcopP : IsCoprime ((q : ℤ) ^ d) ((p : ℤ) ^ d) := hcopZ.pow
  have hdvd : (q : ℤ) ^ d ∣ (p : ℤ) ^ d * Mnum p q n := ⟨Mnum p q (n + d), by rw [← hlink]⟩
  exact hcopP.dvd_of_dvd_mul_left hdvd

/-- **Third consequence** `m = qᵈ·μ`, `m' = pᵈ·μ`: the whole tower is the `pᵈ`-scaling of a
single reduced base `μ = m/qᵈ` (the `E(n, d)`-anatomy of plan §3). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem link_scaling (p q : ℕ) {n d : ℕ} (hq : 0 < q) (hcop : Nat.Coprime p q)
    (hlink : (p : ℤ) ^ d * Mnum p q n = (q : ℤ) ^ d * Mnum p q (n + d)) :
    ∃ μ : ℤ, Mnum p q n = (q : ℤ) ^ d * μ ∧ Mnum p q (n + d) = (p : ℤ) ^ d * μ := by
  obtain ⟨μ, hμ⟩ := link_dvd p q hcop hlink
  refine ⟨μ, hμ, ?_⟩
  have hqd : (0 : ℤ) < (q : ℤ) ^ d := by positivity
  have hcancel : (q : ℤ) ^ d * ((p : ℤ) ^ d * μ) = (q : ℤ) ^ d * Mnum p q (n + d) := by
    rw [← hlink, hμ]; ring
  exact (mul_left_cancel₀ (ne_of_gt hqd) hcancel).symm

/-- **Fourth consequence: quality surplus.**  The base residue is a factor `pᵈ` better than a
generic failure: `pᵈ·|k| < (c·q)ⁿ⁺ᵈ`, i.e. `|k| < (c·q)ⁿ·(c·q/p)ᵈ` (for `(3, 2, 3/4)`:
`|k| < (3/2)ⁿ·2⁻ᵈ`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem link_quality (p q : ℕ) (c : ℝ) {n d : ℕ} (hnd : IsFailure p q c (n + d))
    (hlink : (p : ℤ) ^ d * Mnum p q n = (q : ℤ) ^ d * Mnum p q (n + d)) :
    (p : ℝ) ^ d * |(resid p q n : ℝ)| < (c * q) ^ (n + d) := by
  have hk : resid p q (n + d) = (p : ℤ) ^ d * resid p q n := link_resid p q hlink
  have h2 : (|resid p q (n + d)| : ℝ) < (c * q) ^ (n + d) := hnd
  have hcast : |(resid p q (n + d) : ℝ)| = (p : ℝ) ^ d * |(resid p q n : ℝ)| := by
    rw [hk]; push_cast
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  rw [hcast] at h2; exact h2

/-- **Non-linkage gives a multiplicative gap.**  If two failures `a < b` are *not* linked
(`1 < 2·cᵃ·pᵇ⁻ᵃ`) and `a ≥ t ≥ 1`, then `ρ·a ≤ b`, provided the transparent threshold relation
`log 2 ≤ t·(log(1/c) − (ρ−1)·log p)` holds (which forces `ρ < 1 + ε`).  This is the gap fed to
the `O(log N)` count; taking `t → ∞` lets `ρ → 1 + ε`, the plan's `1.26186…` tower ratio. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem gap_of_nonlink (p : ℕ) (c ρ : ℝ) (a b t : ℕ) (hp1 : 1 < p) (hc0 : 0 < c) (hab : a < b)
    (ht : t ≤ a) (ht1 : 1 ≤ t) (hnl : 1 < 2 * c ^ a * (p : ℝ) ^ (b - a))
    (hthr : Real.log 2 ≤ (t : ℝ) * (Real.log (1 / c) - (ρ - 1) * Real.log p)) :
    ρ * a ≤ b := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp1)
  have hgap : ((b : ℝ) - a) * Real.log p > (a : ℝ) * Real.log (1 / c) - Real.log 2 := by
    have hstep := Real.log_lt_log (by norm_num) hnl
    rw [Real.log_one, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hstep
    have hba : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by rw [Nat.cast_sub (le_of_lt hab)]
    rw [hba] at hstep
    have hlogc : Real.log (1 / c) = -Real.log c := by
      rw [Real.log_div (by norm_num) (ne_of_gt hc0), Real.log_one]; ring
    rw [hlogc]; nlinarith [hstep]
  set br : ℝ := Real.log (1 / c) - (ρ - 1) * Real.log p with hbr
  have hbrpos : 0 ≤ br := by
    by_contra h; rw [not_le] at h
    have h1 : (t : ℝ) * br ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt h)
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have haR : (t : ℝ) ≤ a := by exact_mod_cast ht
  have habr : Real.log 2 ≤ (a : ℝ) * br := le_trans hthr (by nlinarith [hbrpos, haR])
  have hfinal : ρ * (a : ℝ) * Real.log p < (b : ℝ) * Real.log p := by
    have expand : (a : ℝ) * br = a * Real.log (1 / c) - (ρ - 1) * a * Real.log p := by rw [hbr]; ring
    nlinarith [hgap, habr, expand]
  exact le_of_lt (lt_of_mul_lt_mul_right hfinal (le_of_lt hlp))

end BB13
