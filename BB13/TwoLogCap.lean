/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.QualityLedger
import BB13.TwoAdicRigidity

/-!
# The rate ledger, and why the reduction step has no input (strategy B6(ii))

Tier (ii) of strategy **B6** of `plans/report3-BB13.html` asks for

> explicit two-log forms (Laurent–Mignotte–Nesterenko) plus a `2×2` LLL step that uses the extra
> smallness `|kₐ| < 2^{0.585a−H}` as a second approximation, aimed at a **finite cap on `a` for
> fibres `≥ 2`**,

which together with the census would kill all multiplicity.  This file executes the item.  The
outcome is negative and it is *priced*: the target is unreachable not by a constant but by the
direction of the inequality, and the reduction step has nothing to reduce.

## The rate ledger (§1)

Every archimedean lower bound for `|kₐ|` — Padé (Beukers, Habsieger, Zudilin), Baker/LMN, or the
trivial `|kₐ| ≥ 1` — has the same exponential shape `‖(3/2)ᵃ‖ ≥ cᵃ`, i.e. `|kₐ| ≥ (2c)ᵃ`.  Against
the tower arm `2ᵈ|kₐ|2ᵃ ≤ 3ᵃ` (`BB13.tower_arms`) it gives, with `c = P/Q`,

`rate_fibre_cap` :  `2ᵈ·(4P)ᵃ ≤ (3Q)ᵃ`,  i.e.  `d ≤ a·log₂(3/(4c))`,

the exact analogue of B6(i)'s `quality_ledger` for rate information instead of `abc` information.
The slope `log₂(3/(4c))` is `0.58496` at `c = 1/2` (the corridor), `0.37009` at [Zud07]'s
`c = 0.5803` (the report's `0.371a` row), and **`0` exactly at `c = 3/4`** — which is Problem 2
itself.  Integer instances: `corridor_slope` (`17d ≤ 10a`, unconditional) and `zudilin_slope`
(`35d ≤ 13a`).  Both route through `exponent_transfer`, which converts a rational slope into a
one-line numeral certificate (`3¹⁷ ≤ 2²⁷`; `7500³⁵ ≤ 2¹³·5803³⁵`).

## Why the target is unreachable (§2)

The ledger's slope is positive for every `c < 3/4`, so it bounds `d` *in terms of* `a`.  Read for
a fibre of size `≥ 2` (`d ≥ 1`) it becomes a **lower** bound on `a`
(`fibre_needs_large_a`, `zudilin_excludes_small_only`: `a ≥ 3`), and the ledger stays satisfiable
at every larger index (`zudilin_ledger_no_upper_cap`): for every `A` there is an `a ≥ A` at which
the best published rate permits a fibre of size `2`.  The excluded set is always an initial
segment, never a tail, so **no exponential rate input can produce a finite cap on `a`** — except
at `c ≥ 3/4`, where it already settles Problem 2 outright (`no_exception_of_rate`,
`no_fibre_of_rate`).  There is no intermediate regime.  This is the same shape as B6(i)'s
threshold `q* = 1.35476`, with `3/4` in place of `q*`.

## Baker's constant, priced (§3)

`lmnSlope = 24.34·21²·log3·log(3/2) = 4781.42…` is the constant [LMN95] Cor. 2 delivers for the
actual form `Λₐ = log mₐ − a·log(3/2)`: `D = 1`, `h'(3/2) = log 3`, `h'(mₐ) = log mₐ ~ a log(3/2)`,
and `b' → 3.3765` is **bounded**, so `max{log b' + 0.14, 21/D, 1/2} = 21` throughout and the bound
is `log|Λ| ≥ −4781.42·a`.  The thresholds are `log 3 = 1.0986` (below which a bound says less than
`|kₐ| ≥ 1`) and `log 2 = 0.6931` (below which it settles Problem 2).  Hence
`log_three_lt_lmnSlope` and `lmn_below_trivial`: **the published two-log bound contributes zero
bits here** — it is `4352×` weaker than the trivial one and `6898×` weaker than what Problem 2
needs.  No sharpening of the constant can help: the miss is a factor in the exponent, and it is
structural — one of the two algebraic numbers is `mₐ`, whose height grows *linearly with the
coefficient*, so the bound is linear in `a` rather than logarithmic.  `baker_fibre_cap` is the
general conversion, `baker_solves_problem_two` the threshold.

*Provenance note.*  Nothing here axiomatizes [LMN95]: `lmnSlope` is a real number and the theorems
about it are arithmetic.  The theorem being priced enters only as a hypothesis.

## The `2×2` lattice is degenerate (§2, `pair_candidate_unique`)

The reduction step of a Baker–Davenport/LLL argument needs an initial finite bound `a ≤ A` to
reduce.  A rate bound never supplies one (§2), and the lattice itself supplies nothing: for
`a ≥ 3` the affine line `{(m,k) : m2ᵃ + k = 3ᵃ}` meets the corridor `|k| < (3/2)ᵃ` in exactly one
point (`BB13.corridor_candidate_unique`), so the "lattice step" has a single candidate per index
and its verdict *is* the census bit.  Measured in `BB13/b6ii_twolog.py` [C]: the same reduction
clears `a ≤ 10¹⁵` in `0.02` ms for the genuine two-log problem `|3ᵃ − 2ᵇ| ≤ 1000` (both exponents
free, so `a·log₂3 mod 1` has convergents), and offers no shortcut whatsoever here, where the
unknown is a **coefficient** and `‖(3/2)ᵃ‖` is a geometric sequence mod `1`.

## What the pair problem actually is (§4)

`tower_iff_shifted`: for `a ≥ 3`, `d ≥ 1`,

`2ᵈ ∣ mₐ ∧ 2ᵈ|kₐ|2ᵃ ≤ 3ᵃ`  ⟺  `∃ν, 2^{2d}|3ᵃ − ν2^{a+d}|4ᵃ ≤ 3ᵃ2^{a+d}`,

i.e. **a fibre of size `≥ d+1` at `a` is exactly a failure of the shifted point `2^{−d}(3/2)ᵃ` at
the constant `2^{−2d}(3/4)ᵃ`**.  So Problem 2′ for `h = 2` is not a new problem: it is the same
Mahler problem for `δ = 1/2`, to which the root's general-`δ` package (`BB13/MahlerFrame.lean`,
`BB13/MahlerCount.lean`) applies verbatim — `num δ = 1`, so the degeneracy recorded there cannot
occur — and returns the *same* cover at the *same* `ε*`.  A3's "quantified circularity" is exact:
passing to pairs creates no independent input.

## B4's absorbed half

The report moved B4's `8%` measure branch here on the grounds that B6(ii) "is the one place where
a constraint on `k` beyond its height enters".  It does not: the LMN bound sees `kₐ` only through
`|Λ| ≈ |kₐ|/3ᵃ`.  Being height-only, it falls under `BB13.measure_iff_problem_two` and
`BB13.corridor_saturation` — free reach `0.585a`, and every bit above that is Problem 2.  The
absorbed half is therefore closed with the same verdict it arrived with.

## Trust ledger

Footprint `std3` throughout; **no cited axiom**, no `sorry`.  Every hypothesis that stands for a
literature theorem ([Zud07]'s rate, a Baker bound with constant `C`) is an explicit hypothesis of
the statement that uses it, never an axiom.

## Claim level

`corridor_slope`, `pair_candidate_unique`, `tower_iff_shifted`, `log_three_lt_lmnSlope`,
`lmn_below_trivial`, `zudilin_ledger_no_upper_cap` are unconditional.  `zudilin_slope`,
`no_exception_of_rate`, `no_fibre_of_rate`, `baker_fibre_cap`, `baker_solves_problem_two` are
conditional on their stated rate hypothesis.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  in Mathematics **193**, 2012 (Problem 10.13).
* [LMN95] M. Laurent, M. Mignotte, Y. Nesterenko, *Formes linéaires en deux logarithmes et
  déterminants d'interpolation*, J. Number Theory **55** (1995), 285–321 (Cor. 2).
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)ᵏ‖`*, J. Théor. Nombres Bordeaux **19**
  (2007), 311–323.
* [Bak75] A. Baker, *Transcendental Number Theory*, Cambridge, 1975 (the method being priced).
* [DD90] F. Delmer, J.-M. Deshouillers, Math. Comp. **54** (1990), 885–893.
-/

namespace BB13

open scoped Real

/-! ## 1. The rate ledger

Everything in this section is integer arithmetic: a rate `c = P/Q` enters as
`(2P)ᵃ ≤ Qᵃ|kₐ|` and leaves as `2ᵈ(4P)ᵃ ≤ (3Q)ᵃ`. -/

/-- `kₐ ≠ 0` for `a ≥ 1`: otherwise `2ᵃ ∣ 3ᵃ`.  This is the trivial rate `c = 1/2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem resid_natAbs_pos {a : ℕ} (ha : 1 ≤ a) : 0 < (resid 3 2 a).natAbs := by
  rw [Int.natAbs_pos, resid, Mnum_eq_mNat, sub_ne_zero]
  intro h
  push_cast at h
  have h2 : (2 : ℤ) ∣ (3 : ℤ) ^ a := by
    rw [h]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega : a ≠ 0)) _
  have h2' : (2 : ℕ) ∣ 3 ^ a := by exact_mod_cast h2
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2'
  omega

/-- **The rate ledger.**  A lower bound `|kₐ| ≥ (2P/Q)ᵃ` — i.e. `‖(3/2)ᵃ‖ ≥ (P/Q)ᵃ` — against the
tower arm `2ᵈ|kₐ|2ᵃ ≤ 3ᵃ` gives

`2ᵈ·(4P)ᵃ ≤ (3Q)ᵃ`,  i.e.  `d ≤ a·log₂(3/(4c))`  with  `c = P/Q`.

The slope vanishes exactly at `4P = 3Q`, i.e. `c = 3/4`.  Compare `BB13.quality_ledger`: the same
shape, with `abc` information in place of rate information. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem rate_fibre_cap {a d P Q : ℕ}
    (hrate : (2 * P) ^ a ≤ Q ^ a * (resid 3 2 a).natAbs)
    (htower : 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) :
    2 ^ d * (4 * P) ^ a ≤ (3 * Q) ^ a := by
  have h4 : (4 : ℕ) ^ a = 2 ^ a * 2 ^ a := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have h1 : (4 * P) ^ a = 2 ^ a * (2 * P) ^ a := by
    rw [mul_pow, h4, mul_pow, mul_assoc]
  calc 2 ^ d * (4 * P) ^ a = 2 ^ a * (2 ^ d * (2 * P) ^ a) := by rw [h1]; ring
    _ ≤ 2 ^ a * (2 ^ d * (Q ^ a * (resid 3 2 a).natAbs)) := by gcongr
    _ = Q ^ a * (2 ^ d * (resid 3 2 a).natAbs * 2 ^ a) := by ring
    _ ≤ Q ^ a * 3 ^ a := by gcongr
    _ = (3 * Q) ^ a := by rw [mul_pow]; ring

/-- Cancelling a common factor from both sides of a ledger inequality. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem cancel_pow_factor {a d P R c : ℕ} (hc : 0 < c)
    (h : 2 ^ d * (c * P) ^ a ≤ (c * R) ^ a) : 2 ^ d * P ^ a ≤ R ^ a := by
  rw [mul_pow, mul_pow] at h
  refine Nat.le_of_mul_le_mul_left ?_ (pow_pos hc a)
  calc c ^ a * (2 ^ d * P ^ a) = 2 ^ d * (c ^ a * P ^ a) := by ring
    _ ≤ c ^ a * R ^ a := h

/-- **Rational slope from a numeral certificate.**  From `2ᵈPᵃ ≤ Qᵃ` and one numeral inequality
`Qᵖ ≤ 2^q·Pᵖ` (which says `log₂(Q/P) ≤ q/p`) one gets the integer slope `p·d ≤ q·a`.  Raise the
first to the `p`-th power, substitute the certificate, cancel `P^{ap}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem exponent_transfer {P Q p q d a : ℕ} (hP : 0 < P)
    (hcert : Q ^ p ≤ 2 ^ q * P ^ p) (h : 2 ^ d * P ^ a ≤ Q ^ a) :
    p * d ≤ q * a := by
  have h1 : (2 ^ d * P ^ a) ^ p ≤ (Q ^ a) ^ p := Nat.pow_le_pow_left h p
  have h2 : (Q ^ p) ^ a ≤ (2 ^ q * P ^ p) ^ a := Nat.pow_le_pow_left hcert a
  have e1 : (2 ^ d * P ^ a) ^ p = 2 ^ (d * p) * P ^ (a * p) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  have e2 : (Q ^ a) ^ p = (Q ^ p) ^ a := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have e3 : (2 ^ q * P ^ p) ^ a = 2 ^ (q * a) * P ^ (a * p) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm q a, Nat.mul_comm p a]
  have h2' : (Q ^ a) ^ p ≤ (2 ^ q * P ^ p) ^ a := by rw [e2]; exact h2
  have key : 2 ^ (d * p) * P ^ (a * p) ≤ 2 ^ (q * a) * P ^ (a * p) := by
    rw [← e1, ← e3]
    exact le_trans h1 h2'
  have hle : (2 : ℕ) ^ (d * p) ≤ 2 ^ (q * a) :=
    Nat.le_of_mul_le_mul_right key (pow_pos hP _)
  have hdp := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  rw [Nat.mul_comm p d]
  exact hdp

/-- The unconditional rate: `|kₐ| ≥ 1`, i.e. `c = 1/2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem trivial_rate {a : ℕ} (ha : 1 ≤ a) :
    (2 * 1) ^ a ≤ 2 ^ a * (resid 3 2 a).natAbs := by
  have hK := resid_natAbs_pos ha
  calc (2 * 1 : ℕ) ^ a = 2 ^ a * 1 := by ring
    _ ≤ 2 ^ a * (resid 3 2 a).natAbs := by gcongr; omega

/-- **The corridor slope, unconditionally.**  `17d ≤ 10a`, i.e. `d ≤ 0.5882a`, from `|kₐ| ≥ 1`
alone; the exact value of the slope is `log₂(3/2) = 0.58496…`.  Certificate: `3¹⁷ ≤ 2²⁷`.  This
is `BB13.corridor_saturation` in fibre form, and it is the *best* an archimedean input can do
without a genuine rate theorem. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem corridor_slope {a d : ℕ} (ha : 1 ≤ a)
    (htower : 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) :
    17 * d ≤ 10 * a := by
  have h1 : 2 ^ d * (4 * 1) ^ a ≤ (3 * 2) ^ a := rate_fibre_cap (trivial_rate ha) htower
  have h2 : 2 ^ d * (2 * 2) ^ a ≤ (2 * 3) ^ a := by
    calc 2 ^ d * (2 * 2 : ℕ) ^ a = 2 ^ d * (4 * 1) ^ a := by norm_num
      _ ≤ (3 * 2) ^ a := h1
      _ = (2 * 3) ^ a := by norm_num
  exact exponent_transfer (by norm_num) (by norm_num : (3 : ℕ) ^ 17 ≤ 2 ^ 10 * 2 ^ 17)
    (cancel_pow_factor (by norm_num) h2)

/-- **[Zud07]'s row, in integer form.**  Under `‖(3/2)ᵃ‖ ≥ (5803/10000)ᵃ` a tower over `a` has
depth `35d ≤ 13a`, i.e. `d ≤ 0.37143a` — the report's `0.371a` row (exact slope `0.370092`).
Certificate: `7500³⁵ ≤ 2¹³·5803³⁵`. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem zudilin_slope {a d : ℕ}
    (hrate : (11606 : ℕ) ^ a ≤ 10000 ^ a * (resid 3 2 a).natAbs)
    (htower : 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) :
    35 * d ≤ 13 * a := by
  have h1 : 2 ^ d * (4 * 5803) ^ a ≤ (3 * 10000) ^ a := by
    refine rate_fibre_cap ?_ htower
    calc (2 * 5803 : ℕ) ^ a = 11606 ^ a := by norm_num
      _ ≤ 10000 ^ a * (resid 3 2 a).natAbs := hrate
  have h2 : 2 ^ d * (4 * 5803) ^ a ≤ (4 * 7500) ^ a := by
    calc 2 ^ d * (4 * 5803 : ℕ) ^ a ≤ (3 * 10000) ^ a := h1
      _ = (4 * 7500) ^ a := by norm_num
  exact exponent_transfer (by norm_num)
    (by norm_num : (7500 : ℕ) ^ 35 ≤ 2 ^ 13 * 5803 ^ 35)
    (cancel_pow_factor (by norm_num) h2)

/-! ## 2. Direction: the ledger bounds `a` from below, never from above

This is the section that closes tier (ii).  A rate `c < 3/4` gives a positive slope, so reading
the ledger at `d ≥ 1` produces a *lower* bound on `a`; and the ledger remains satisfiable at every
larger index, so no `A` with "no fibre `≥ 2` above `A`" ever follows.  A rate `c ≥ 3/4` gives a
non-positive slope — but that is Problem 2, which needs no cap. -/

/-- **The excluded set is an initial segment.**  A fibre of size `≥ 2` at `a` forces `p ≤ q·a`
under a rate with certified slope `q/p` — a lower bound on `a`, which is the wrong direction for
tier (ii)'s target. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem fibre_needs_large_a {a d P Q p q : ℕ} (hd : 1 ≤ d) (hP : 0 < P)
    (hcert : Q ^ p ≤ 2 ^ q * P ^ p) (h : 2 ^ d * P ^ a ≤ Q ^ a) :
    p ≤ q * a := by
  have := exponent_transfer hP hcert h
  calc p = p * 1 := by ring
    _ ≤ p * d := by gcongr
    _ ≤ q * a := this

/-- **What [Zud07] actually excludes: `a ≤ 2`.**  Under his rate a fibre of size `≥ 2` needs
`a ≥ 3` — and the one known pair sits at `a = 2`, below the effective threshold of every
published rate theorem. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem zudilin_excludes_small_only {a d : ℕ} (hd : 1 ≤ d)
    (hrate : (11606 : ℕ) ^ a ≤ 10000 ^ a * (resid 3 2 a).natAbs)
    (htower : 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) :
    3 ≤ a := by
  have h := zudilin_slope hrate htower
  have : 35 * 1 ≤ 35 * d := by gcongr
  omega

/-- Monotone continuation of a ledger inequality: if it holds at `a₀` and `X ≤ Y`, it holds at
every `a ≥ a₀`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem ledger_holds_of_base {X Y d a₀ : ℕ} (hXY : X ≤ Y) (hbase : 2 ^ d * X ^ a₀ ≤ Y ^ a₀) :
    ∀ a, a₀ ≤ a → 2 ^ d * X ^ a ≤ Y ^ a := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => exact hbase
  | succ n _ ih =>
    calc 2 ^ d * X ^ (n + 1) = 2 ^ d * X ^ n * X := by ring
      _ ≤ Y ^ n * X := by gcongr
      _ ≤ Y ^ n * Y := by gcongr
      _ = Y ^ (n + 1) := by ring

/-- **The target of tier (ii) is unreachable.**  Even at the best published rate the ledger
permits a fibre of size `2` at arbitrarily large `a`: for every `A` there is `a ≥ A` with
`2·23212ᵃ ≤ 30000ᵃ`.  So no finite cap on `a` follows from an exponential rate bound, whatever its
constant — the only way out is a slope `≤ 0`, i.e. `c ≥ 3/4`, which is Problem 2 itself. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem zudilin_ledger_no_upper_cap (A : ℕ) :
    ∃ a, A ≤ a ∧ 2 ^ 1 * 23212 ^ a ≤ 30000 ^ a :=
  ⟨max A 3, le_max_left _ _,
    ledger_holds_of_base (by norm_num) (by norm_num) _ (le_max_right _ _)⟩

/-- **A rate `c > 3/4` settles Problem 2 outright**: no exception at all above the range where the
rate is valid. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem no_exception_of_rate {a P Q : ℕ} (ha : 1 ≤ a) (h34 : 3 * Q < 4 * P)
    (hrate : (2 * P) ^ a ≤ Q ^ a * (resid 3 2 a).natAbs)
    (hf : IsFailure 3 2 (3 / 4) a) : False := by
  have h := rate_fibre_cap (d := 0) hrate (exception_arm hf)
  have h' : (4 * P : ℕ) ^ a ≤ (3 * Q) ^ a := by simpa using h
  have hlt : (3 * Q : ℕ) ^ a < (4 * P) ^ a := Nat.pow_lt_pow_left h34 (by omega)
  omega

/-- **A rate `c ≥ 3/4` leaves no fibre of size `≥ 2`.**  The ledger's slope is `≤ 0`, so `2ᵈ ≤ 1`
and `d = 0`. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem no_fibre_of_rate {a d P Q : ℕ} (hd : 1 ≤ d) (hP : 0 < P) (h34 : 3 * Q ≤ 4 * P)
    (hrate : (2 * P) ^ a ≤ Q ^ a * (resid 3 2 a).natAbs)
    (htower : 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) : False := by
  have h := rate_fibre_cap hrate htower
  have h2 : (3 * Q) ^ a ≤ (4 * P) ^ a := Nat.pow_le_pow_left h34 a
  have h3 : 2 ^ d * (4 * P) ^ a ≤ 1 * (4 * P) ^ a := by
    rw [one_mul]; exact le_trans h h2
  have hpos : 0 < (4 * P : ℕ) ^ a := pow_pos (by omega) a
  have hle : (2 : ℕ) ^ d ≤ 1 := Nat.le_of_mul_le_mul_right h3 hpos
  have : 1 < (2 : ℕ) ^ d := Nat.one_lt_two_pow_iff.mpr (by omega)
  omega

/-- **The `2×2` lattice is degenerate.**  For `a ≥ 3`, *any* representation `3ᵃ = ν2^{a+1} + t`
with `t` in the corridor already has `t = kₐ` and `2 ∣ mₐ`: the lattice step of a
Baker–Davenport/LLL argument has exactly one candidate per index, so its verdict is the census
bit and it cannot clear a range of `a` without evaluating each `a`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem pair_candidate_unique {a : ℕ} (ha : 3 ≤ a) {ν t : ℤ}
    (heq : (3 : ℤ) ^ a = ν * 2 ^ (a + 1) + t)
    (ht : |((t : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a) :
    t = resid 3 2 a ∧ (2 : ℤ) ^ 1 ∣ Mnum 3 2 a := by
  have hdvd : (2 : ℤ) ^ a ∣ 3 ^ a - t := by
    refine ⟨ν * 2, ?_⟩
    rw [heq, pow_succ]
    ring
  have hkey : t = resid 3 2 a := corridor_candidate_unique ha ht hdvd
  refine ⟨hkey, ?_⟩
  have h1 : (3 : ℤ) ^ a - resid 3 2 a = Mnum 3 2 a * 2 ^ a := three_pow_sub_resid a
  have h2 : Mnum 3 2 a * 2 ^ a = (ν * 2) * 2 ^ a := by
    rw [← h1, ← hkey, heq, pow_succ]
    ring
  have h3 : Mnum 3 2 a = ν * 2 :=
    mul_right_cancel₀ (by positivity : (0 : ℤ) < 2 ^ a).ne' h2
  exact ⟨ν, by rw [h3]; ring⟩

/-! ## 3. Baker's constant, priced

`lmnSlope` is the constant [LMN95] Cor. 2 delivers for this form.  Nothing about [LMN95] is
assumed: the theorems here are about the real number, and the bound being priced always appears
as a hypothesis. -/

/-- The [LMN95] Cor. 2 slope for `Λₐ = log mₐ − a log(3/2)`: `D = 1`, `h'₁ = log 3`,
`h'₂ = log mₐ ~ a log(3/2)`, and `b' → 3.3765` is bounded, so the inner maximum is `21/D = 21`
throughout.  Numerically `24.34·441·log3·log(3/2) = 4781.42…`. -/
noncomputable def lmnSlope : ℝ := 24.34 * 21 ^ 2 * Real.log 3 * Real.log (3 / 2)

/-- **The rate ledger for a Baker-type bound.**  From `|kₐ| ≥ 3ᵃe^{−Ca}` and the tower arm,
`d·log2 ≤ a·(C − log2)` — the same ledger as §1, with `c = 3e^{−C}/2`.  The slope
`C/log2 − 1` vanishes at `C = log 2`. -/
@[category research solved, AMS 11, ref "Bug12" "LMN95", group "bugeaud_10_13"]
theorem baker_fibre_cap {a d : ℕ} {C : ℝ}
    (hrate : (3 : ℝ) ^ a * Real.exp (-(C * a)) ≤ |((resid 3 2 a : ℤ) : ℝ)|)
    (htower : (2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| * 2 ^ a ≤ 3 ^ a) :
    (d : ℝ) * Real.log 2 ≤ a * (C - Real.log 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (a + d) := by positivity
  have hk : |((resid 3 2 a : ℤ) : ℝ)| * 2 ^ (a + d) ≤ 3 ^ a := by
    rw [pow_add]
    calc |((resid 3 2 a : ℤ) : ℝ)| * ((2 : ℝ) ^ a * 2 ^ d)
        = (2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| * 2 ^ a := by ring
      _ ≤ 3 ^ a := htower
  have hstep : (3 : ℝ) ^ a * Real.exp (-(C * a)) * 2 ^ (a + d) ≤ 3 ^ a := by
    refine le_trans ?_ hk
    gcongr
  have hexp : Real.exp (-(C * a)) * 2 ^ (a + d) ≤ 1 := by
    have h' : (3 : ℝ) ^ a * (Real.exp (-(C * a)) * 2 ^ (a + d)) ≤ 3 ^ a * 1 := by
      rw [mul_one, ← mul_assoc]; exact hstep
    exact le_of_mul_le_mul_left h' h3
  have hlog := Real.log_le_log (by positivity) hexp
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp, Real.log_pow,
    Real.log_one] at hlog
  push_cast at hlog
  nlinarith [hlog]

/-- **A Baker constant `C ≥ log 3` says less than `|kₐ| ≥ 1`.**  The bound `3ᵃe^{−Ca} ≤ |kₐ|` is
then implied by the trivial one, so it carries no information at all. -/
@[category research solved, AMS 11, ref "Bug12" "LMN95", group "bugeaud_10_13"]
theorem baker_below_trivial {C : ℝ} (hC : Real.log 3 ≤ C) (a : ℕ) :
    (3 : ℝ) ^ a * Real.exp (-(C * a)) ≤ 1 := by
  have h : Real.exp ((a : ℝ) * Real.log 3) = (3 : ℝ) ^ a := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [← h, ← Real.exp_add,
    show (a : ℝ) * Real.log 3 + -(C * a) = -((a : ℝ) * (C - Real.log 3)) by ring]
  exact Real.exp_le_one_iff.mpr (by
    have : (0 : ℝ) ≤ (a : ℝ) * (C - Real.log 3) :=
      mul_nonneg (Nat.cast_nonneg a) (by linarith)
    linarith)

/-- **`log 3 < lmnSlope`**: [LMN95]'s constant for this form is above the vacuity threshold, hence
(with `baker_below_trivial`) the published two-log bound is weaker than `|kₐ| ≥ 1`. -/
@[category research solved, AMS 11, ref "LMN95" "Bug12", group "bugeaud_10_13"]
theorem log_three_lt_lmnSlope : Real.log 3 < lmnSlope := by
  have hinv : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
    rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have h32 : (1 / 3 : ℝ) ≤ Real.log (3 / 2) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
    rw [hinv] at h
    linarith
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [lmnSlope]
  nlinarith

/-- **The published two-log bound contributes zero bits.**  `3ᵃ·e^{−lmnSlope·a} ≤ 1` for every
`a`: below the trivial `|kₐ| ≥ 1`, whose own ledger slope is already `0.58496`. -/
@[category research solved, AMS 11, ref "LMN95" "Bug12", group "bugeaud_10_13"]
theorem lmn_below_trivial (a : ℕ) : (3 : ℝ) ^ a * Real.exp (-(lmnSlope * a)) ≤ 1 :=
  baker_below_trivial log_three_lt_lmnSlope.le a

/-- **The miss is a factor `> 6800` in the exponent.**  Problem 2 needs a two-log constant below
`log 2`; [LMN95] delivers `4781.42`.  No sharpening of the constant closes a multiplicative gap of
this size, and the gap is structural: the second algebraic number is `mₐ`, whose height grows
linearly with the coefficient `a`. -/
@[category research solved, AMS 11, ref "LMN95" "Bug12", group "bugeaud_10_13"]
theorem lmn_miss_factor : 6800 * Real.log 2 < lmnSlope := by
  have h32 : (0.4054651077 : ℝ) ≤ Real.log (3 / 2) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [log_three_ge, Real.log_two_lt_d9]
  have h3 : (1.0986122885 : ℝ) ≤ Real.log 3 := log_three_ge
  have hp : (1.0986122885 : ℝ) * 0.4054651077 ≤ Real.log 3 * Real.log (3 / 2) :=
    mul_le_mul h3 h32 (by norm_num) (by linarith)
  rw [lmnSlope]
  nlinarith [hp, Real.log_two_lt_d9]

/-- **A two-log constant below `log 2` settles Problem 2.**  The threshold is sharp: the ledger's
slope is `C/log2 − 1`, zero exactly at `C = log 2`. -/
@[category research solved, AMS 11, ref "Bug12" "LMN95", group "bugeaud_10_13"]
theorem baker_solves_problem_two {C : ℝ} (hC : C < Real.log 2) {a : ℕ} (ha : 1 ≤ a)
    (hrate : (3 : ℝ) ^ a * Real.exp (-(C * a)) ≤ |((resid 3 2 a : ℤ) : ℝ)|) :
    ¬ IsFailure 3 2 (3 / 4) a := by
  intro hf
  have hlt : |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a := (isFailure_iff_abs_resid_lt a).mp hf
  have h2a : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have htower : (2 : ℝ) ^ 0 * |((resid 3 2 a : ℤ) : ℝ)| * 2 ^ a ≤ 3 ^ a := by
    have hmul := mul_lt_mul_of_pos_right hlt h2a
    rw [div_pow] at hmul
    have : (3 : ℝ) ^ a / 2 ^ a * 2 ^ a = 3 ^ a := by field_simp
    rw [this] at hmul
    simpa using hmul.le
  have h := baker_fibre_cap hrate htower
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  push_cast at h
  nlinarith [h]

/-! ## 4. The pair problem is the shifted Mahler problem

`tower_iff_shifted` identifies "fibre of size `≥ d+1` at `a`" with the failure of the *shifted*
point `2^{−d}(3/2)ᵃ` at the constant `2^{−2d}(3/4)ᵃ`.  Both smallness factors are genuine: one
comes from `|kₐ| ≤ 2^{−d}(3/2)ᵃ`, the other from dividing by `2ᵈ`. -/

/-- **The `h = d+1` problem is the `δ = 2^{−d}` Mahler problem.**  For `a ≥ 3` and `d ≥ 1`,

`2ᵈ ∣ mₐ ∧ 2ᵈ|kₐ|2ᵃ ≤ 3ᵃ`  ⟺  `∃ν, 2^{2d}·|3ᵃ − ν2^{a+d}|·4ᵃ ≤ 3ᵃ·2^{a+d}`,

the right side being `‖2^{−d}(3/2)ᵃ‖ ≤ 2^{−2d}(3/4)ᵃ` cleared of denominators.  So Problem 2′ for
`h = 2` is the same Mahler problem at `δ = 1/2`; passing to pairs creates no new input, which is
A3's "quantified circularity" made exact. -/
@[category research solved, AMS 11, ref "Bug12" "Mah57", group "bugeaud_10_13"]
theorem tower_iff_shifted {a d : ℕ} (ha : 3 ≤ a) (hd : 1 ≤ d) :
    (2 ^ d ∣ mNat a ∧ 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a)
      ↔ ∃ ν : ℕ, 2 ^ (2 * d) * ((3 : ℤ) ^ a - (ν : ℤ) * 2 ^ (a + d)).natAbs * 4 ^ a
            ≤ 3 ^ a * 2 ^ (a + d) := by
  have h4 : (4 : ℕ) ^ a = 2 ^ a * 2 ^ a := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have e2d : (2 : ℕ) ^ (2 * d) = 2 ^ d * 2 ^ d := by rw [two_mul, pow_add]
  have ead : (2 : ℕ) ^ (a + d) = 2 ^ a * 2 ^ d := by rw [pow_add]
  constructor
  · rintro ⟨⟨ν, hν⟩, htower⟩
    refine ⟨ν, ?_⟩
    have hres : (3 : ℤ) ^ a - (ν : ℤ) * 2 ^ (a + d) = resid 3 2 a := by
      have h1 : (3 : ℤ) ^ a - resid 3 2 a = Mnum 3 2 a * 2 ^ a := three_pow_sub_resid a
      have h2 : Mnum 3 2 a = (2 : ℤ) ^ d * (ν : ℤ) := by
        rw [Mnum_eq_mNat, hν]; push_cast; ring
      rw [pow_add]
      linear_combination h1 + (2 : ℤ) ^ a * h2
    rw [hres]
    calc 2 ^ (2 * d) * (resid 3 2 a).natAbs * 4 ^ a
        = (2 ^ d * (resid 3 2 a).natAbs * 2 ^ a) * (2 ^ d * 2 ^ a) := by
          rw [h4, e2d]; ring
      _ ≤ 3 ^ a * (2 ^ d * 2 ^ a) := by gcongr
      _ = 3 ^ a * 2 ^ (a + d) := by rw [ead]; ring
  · rintro ⟨ν, hν⟩
    set t : ℤ := (3 : ℤ) ^ a - (ν : ℤ) * 2 ^ (a + d) with ht
    -- the shifted inequality is the tower arm for `t`
    have harm : 2 ^ d * t.natAbs * 2 ^ a ≤ 3 ^ a := by
      have hpos : 0 < (2 : ℕ) ^ (a + d) := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      calc 2 ^ d * t.natAbs * 2 ^ a * 2 ^ (a + d)
          = 2 ^ (2 * d) * t.natAbs * 4 ^ a := by rw [h4, e2d, ead]; ring
        _ ≤ 3 ^ a * 2 ^ (a + d) := hν
    -- hence `t` lies in the corridor
    have hcor : |((t : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a := by
      have hstep : (2 : ℕ) ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
      have h2 : (2 : ℕ) * t.natAbs * 2 ^ a ≤ 3 ^ a := by
        calc 2 * t.natAbs * 2 ^ a = 2 ^ 1 * t.natAbs * 2 ^ a := by norm_num
          _ ≤ 2 ^ d * t.natAbs * 2 ^ a :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hstep)
          _ ≤ 3 ^ a := harm
      have h2' : (2 : ℝ) * (t.natAbs : ℝ) * 2 ^ a ≤ 3 ^ a := by exact_mod_cast h2
      have habs : |((t : ℤ) : ℝ)| = (t.natAbs : ℝ) := by
        rw [← Int.cast_abs]
        exact (Nat.cast_natAbs _).symm
      have h2a : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
      have h3a : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
      rw [habs, div_pow, lt_div_iff₀ h2a]
      linarith
    -- so `t = kₐ`, and the divisibility follows
    have hdvd : (2 : ℤ) ^ a ∣ 3 ^ a - t := ⟨(ν : ℤ) * 2 ^ d, by rw [ht, pow_add]; ring⟩
    have hkey : t = resid 3 2 a := corridor_candidate_unique ha hcor hdvd
    have h1 : (3 : ℤ) ^ a - resid 3 2 a = Mnum 3 2 a * 2 ^ a := three_pow_sub_resid a
    have h2 : Mnum 3 2 a * 2 ^ a = ((ν : ℤ) * 2 ^ d) * 2 ^ a := by
      rw [← h1, ← hkey, ht, pow_add]; ring
    have h3 : Mnum 3 2 a = (ν : ℤ) * 2 ^ d :=
      mul_right_cancel₀ (by positivity : (0 : ℤ) < 2 ^ a).ne' h2
    rw [hkey] at harm
    exact ⟨(two_pow_dvd_Mnum_iff a d).mp ⟨(ν : ℤ), by rw [h3]; ring⟩, harm⟩

/-! ## 5. The verdict

Collected: for every rate with slope certified by `(p, q)` and every bound `A`, the ledger admits
a fibre of size `≥ 2` at some `a ≥ A` unless the slope is zero — and a zero slope is `c ≥ 3/4`.
Tier (ii) therefore collapses to the census, exactly as its own risk line predicted. -/

/-- **Tier (ii), closed.**  For the strongest published rate, the two conclusions the item hoped
to combine are: a lower bound `a ≥ 3` on any pair (`zudilin_excludes_small_only`), and the
permanent satisfiability of the ledger above it (`zudilin_ledger_no_upper_cap`).  There is no `A`
beyond which pairs are excluded, so nothing is left for a census to finish. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07" "LMN95", group "bugeaud_10_13"]
theorem two_log_cap_fails (A : ℕ) :
    ∃ a, A ≤ a ∧ 3 ≤ a ∧ 2 ^ 1 * 23212 ^ a ≤ 30000 ^ a := by
  obtain ⟨a, hA, hle⟩ := zudilin_ledger_no_upper_cap (max A 3)
  exact ⟨a, le_trans (le_max_left _ _) hA, le_trans (le_max_right _ _) hA, hle⟩

end BB13
