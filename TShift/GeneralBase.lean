/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.FreeSojourn
import Z32.DubickasWord
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The `ξ = 1` orbit at a general rational base: `q`-adic floor, circuit sum, shadowing

Report `report-Tshift.html` S14 (idea N3) asks for the **free-zone theorem**: at a rational base
`p/q` with `p > q²` the free `q`-adic floor beats the sojourn threshold, so the carry word of
`(p/q)ⁿ` breaks every fixed periodicity in every dyadic block, unconditionally.  This file is the
arithmetic layer that statement needs — the specialization of `Z32/DubickasWord.lean` to `ξ = 1`,
`ν = 0`, together with the two independent inputs the cap can be built from.  The `κ` bookkeeping,
Proposition D and the capstone itself are assembled one file further up, in `TShift/FreeZone.lean`.

## The objects

`intPartB p q n = ⌊(p/q)ⁿ⌋`, `fracB p q n = {(p/q)ⁿ}` and the carry word
`carryB p q n = q·m_{n+1} − p·mₙ` ([Dub09AA] (2)) are `Z32.xInt`/`Z32.yFract`/`Z32.carry` at
`ξ = 1`, `ν = 0`; at `(p, q) = (3, 2)` they are the corpus's base-`3/2` objects on the nose
(`intPartB_three_two`, `fracB_three_two`, `carryB_three_two`), which is what makes this file a
generalization rather than a second convention.  At `ξ = 1` the orbit is *rational*:

  `yₙ = (pⁿ mod qⁿ)/qⁿ`  (`fracB_eq_mod_div`),  numerator coprime to `q` (`coprime_pow_mod`).

## Two routes to a sojourn cap, and why both are here

**(a) The `q`-adic floor** — `distToNearestInt_mul_ge_base`: `‖D·(p/q)ⁿ‖ ≥ q^{-n}` whenever
`gcd(D, q) = 1`, hence `‖(p/q)ⁿ − A/D‖ ≥ 1/(D·qⁿ)` (`distToNearestInt_ge_of_coprime_denom`).  This
is a genuine per-`n` **rate** `θ = 1/q`, and it exists only because `ξ = 1`: for a general real `ξ`
the rate is provably absent in this regime, since [Aki08] Thms 2.4/2.5 build `ξ` whose orbit stays
confined precisely when `p > q²`.  Against the shadowing bound of §8 it gives the slope
`κ_b = log q/log(p/q)`, which is `< 1` exactly when `p > q²` — the free zone.  That packaging is
`TShift/FreeZone.lean`'s.

**(b) The divisibility cascade** — `q_pow_dvd_of_carryRepetitionB`: equal factors of the carry word
accumulate equal circuit sums, so `p^k(m_c − m_a) = q^k(m_{c+k} − m_{a+k})` (`lemmaR_base`) and
therefore `q^k ∣ m_c − m_a`.  Against `q^c·m_c ≤ p^c` this is the growth ceiling
`q^{k+c} ≤ p^c` (`carryRepetitionB_pow_le`), i.e. the slope `κ_casc = log(p/q)/log q`.  No
Diophantine input whatever, and no `ξ = 1` needed for the mechanism.

The two slopes are **exact reciprocals** (`κ_b·κ_casc = 1`), so `min(κ_b, κ_casc) < 1` at every
coprime `p > q ≥ 2` — `p = q²` is excluded by coprimality — and the dichotomy `p ≷ q²` selects
which route delivers the rung rather than gating the conclusion.  That is finding **F7** of
`plans/note-Tshift-S1314-WP0.html` §3, and it is why route (b) is formalized here alongside (a):
the plan as written had only (a).  Route (b) at `(p, q) = (3, 2)` is exactly
`TShift.free_sojourn_cap` of `TShift/FreeSojourn.lean` (correction **C20**) — the `example` after
`periodic_block_pow_le` checks that the general statement reproduces it verbatim.

## Where the growth step lives

`carryRepetitionB_pow_le` needs `m_a < m_c`, and `⌊(p/q)ⁿ⌋` is strictly increasing only once it has
passed `q`: `q ≤ mₙ` forces `mₙ < m_{n+1}` (`intPartB_lt_succ`), because `p ≥ q+1` makes the step
`mₙ/q ≥ 1`.  The hypothesis is base-independent and reduces *exactly* to an integer inequality,
`q ≤ mₙ ↔ q^{n+1} ≤ pⁿ` (`intPartB_ge_iff`).  At `(3, 2)` the first date is therefore `n = 2`
(`2³ ≤ 3²`), reproducing `TShift.free_sojourn_cap`'s `2 ≤ n`.

At `n = 1` that criterion reads `q² ≤ p` (`intPartB_one_ge_iff`) — which is Proposition D's
dichotomy again.  So the free zone is exactly the zone in which route (b) pays **no burn-in**,
while inside the hard band, where route (b) is the winning one, it always costs at least one
date.  The same inequality `p ≷ q²` thus governs both routes, from opposite sides.

## Shadowing on a finite block

`TShift.abs_sub_fixed_le` (in `TShift/Basic.lean`) assumes the affine recursion at *every* index,
which a finite periodic block does not supply (plan risk **R6**).  §8 carries the finite-block
variants, both from the same identity `z_J − ρ = r^J(z_0 − ρ)` (`sub_fixed_pow_block`):
`abs_sub_fixed_le_block` (a bound on `|z_J − ρ|` pulls back) and `abs_sub_fixed_mul_le_block`
(a bound on `|z_J − z_0|` does too, and needs nothing about `ρ`).  The second is the one the
free-zone cap uses, because along a block both endpoints are fractional parts and
`|z_J − z_0| < 1` is free — no appeal to the position of the fixed point is needed.

The composition that feeds it is `fracB_block_step`: on an `m`-periodic block the window sums
`carrySumB` all agree (`carrySumB_shift_of_block`), so `z_j = y_{n+jm}` runs the *single* affine map
`z ↦ (p/q)^m z − A_w/q^m` with `A_w = carrySumB p q n m`, whose fixed point is `A_w/(p^m − q^m)`
(`affine_fixedPointB`, the general-base `TShift.affine_fixedPoint`).  `block_shadow` puts the two
together.

## κ-discipline

`κ_b = log q/log(p/q)` and `κ_casc = 1/κ_b`; no statement in this file mentions either, because no
statement in this file is a cap — the caps are `TShift/FreeZone.lean`'s, and they carry their `κ`
and its side of the `2/3` threshold there.  What is asserted here is arithmetic: a floor, a
divisibility, a growth ceiling and a shadowing identity.  In particular nothing here is a per-`n`
floor at base `3/2` (route (a) is vacuous there: `q/p = 2/3` is exactly the threshold and the
`q`-adic rate `1/q = 1/2 < 2/3`), and no instance of the T-shift problem is proven or approached.

## Scope

`ξ = 1` throughout, and `ν = 0`.  The qualitative companion for *every* real `ξ ≠ 0` and every base
is already in the corpus and is cited, not restated: `Z32.not_isEventuallyPeriodic_carry`
([Dub09AA] Lemma 2), specialized here as `carryB_not_isEventuallyPeriodic`.  Route (b) is
formalize-the-known — [GY26] Thm 1.2 proves it for every real `ξ ≠ 0` at every rational base, and
[Dub09] Thm 3 runs the same count in complexity clothing (in corpus: `RB/DubickasFloor.lean`,
whose constant is `κ_casc(3,2)`'s reciprocal).  Route (a)'s `q`-adic floor is the ingredient no
cited paper supplies above `q²`.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`, no kernel `decide` on `ℚ` or `ℝ`.

## References

* `plans/plan-Tshift-S1314.html` §1.4 (D3, D4), §2 (Theorem C, Proposition D), §3.1 (file map),
  WP4; `plans/note-Tshift-S1314-WP0.html` §3 (finding F7 and the reciprocal grid, machine-checked
  on every equal factor at periods `m ≤ 3`, `n ≤ 400`, at `(3,2), (5,2), (7,2), (10,3), (4,3)`).
* `report-Tshift.html` S14, N3, §1.5.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — §2, equations (2)–(4) and Lemma 2; the ambient layer is
  `Z32/DubickasWord.lean`.
* [Aki08] S. Akiyama, *Mahler's `Z`-number and `3/2` number systems*, Unif. Distrib. Theory **3**
  (2008), 3–17, Thms 2.4/2.5 — confined orbits for `p > q²`, the reason route (a) consumes `ξ = 1`.
* [GY26] X. Gao, C. H. Yip, *On the fractional parts of certain sequences of `ξαⁿ`*,
  arXiv:2408.02972v2 (23 May 2026), Thm 1.2 — route (b) in print, every real `ξ`, every base.
* [Dub09] A. Dubickas, *On integer sequences generated by linear maps*, Glasgow Math. J. **51**
  (2009), 243–252, Thm 3 — the same ceiling as a complexity floor; in corpus as
  `RB/DubickasFloor.lean`.
* [AFS08] S. Akiyama, C. Frougny, J. Sakarovitch, *Powers of rationals modulo 1 and rational base
  number systems*, Israel J. Math. **168** (2008), 53–91 — the carry word as a `p/q`-expansion.
-/

namespace TShift

/-! ## 1. The `ξ = 1` orbit at a general rational base

`Z32.orb p q 1 0 n = (p/q)ⁿ`, and the three derived objects get short names so that the statements
below read like their base-`3/2` originals in `TShift/Basic.lean`. -/

-- anonymous on purpose: a NAMED section would pop `TShift` off `TShift/AxTShift.lean`'s
-- `namespace`/`end` tracker and mis-name every declaration after it
section

variable (p q : ℕ)

/-- `mₙ = ⌊(p/q)ⁿ⌋`, the integer part of the `ξ = 1` orbit (`Z32.xInt` at `ξ = 1`, `ν = 0`). -/
noncomputable def intPartB (n : ℕ) : ℤ := Z32.xInt p q 1 0 n

/-- `yₙ = {(p/q)ⁿ}`, the fractional part of the `ξ = 1` orbit (`Z32.yFract` at `ξ = 1`, `ν = 0`). -/
noncomputable def fracB (n : ℕ) : ℝ := Z32.yFract p q 1 0 n

/-- The carry word `sₙ = q·m_{n+1} − p·mₙ` of the `ξ = 1` orbit ([Dub09AA] (2)). -/
noncomputable def carryB (n : ℕ) : ℤ := Z32.carry p q 1 0 n

end

variable {p q : ℕ}

@[category API, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem orbB (n : ℕ) : Z32.orb p q 1 0 n = ((p : ℝ) / q) ^ n := by
  simp [Z32.orb]

@[category API, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem intPartB_eq (n : ℕ) : intPartB p q n = ⌊((p : ℝ) / q) ^ n⌋ := by
  rw [intPartB, Z32.xInt, orbB]

@[category API, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem fracB_eq (n : ℕ) : fracB p q n = Int.fract (((p : ℝ) / q) ^ n) := by
  rw [fracB, Z32.yFract, orbB]

/-- The carry word in terms of the integer parts — the definition, unfolded. -/
@[category API, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem carryB_eq (n : ℕ) :
    carryB p q n = q * intPartB p q (n + 1) - p * intPartB p q n := rfl

/-- The orbit recursion `q·m_{n+1} = p·mₙ + sₙ` — the general-base
`TShift.two_mul_intPart_succ`. -/
@[category API, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem q_mul_intPartB_succ (n : ℕ) :
    (q : ℤ) * intPartB p q (n + 1) = p * intPartB p q n + carryB p q n := by
  rw [carryB_eq]; ring

@[category API, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem intPartB_add_fracB (n : ℕ) :
    (intPartB p q n : ℝ) + fracB p q n = ((p : ℝ) / q) ^ n := by
  have h := Z32.xInt_add_yFract (p := p) (q := q) (ξ := 1) (ν := 0) n
  simp only [intPartB, fracB]
  rw [h]; ring

@[category API, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem fracB_nonneg (n : ℕ) : 0 ≤ fracB p q n := Int.fract_nonneg _

@[category API, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem fracB_lt_one (n : ℕ) : fracB p q n < 1 := Int.fract_lt_one _

/-- **The carry alphabet at `ξ = 1`.**  `−q < sₙ < p`: the carry is trapped between the two
fractional parts it is made of.  At `(3, 2)` this is `TShift.carry_mem`'s `{−1, 0, 1, 2}`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem carryB_mem (hq : 0 < q) (hpq : q < p) (n : ℕ) :
    -(q : ℤ) < carryB p q n ∧ carryB p q n < p := by
  have h := Z32.carry_eq (p := p) (q := q) (ξ := 1) (ν := 0) hq n
  simp only [mul_zero, sub_zero] at h
  have hy0 := fracB_nonneg (p := p) (q := q) n
  have hy1 := fracB_lt_one (p := p) (q := q) n
  have hz0 := fracB_nonneg (p := p) (q := q) (n + 1)
  have hz1 := fracB_lt_one (p := p) (q := q) (n + 1)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hcast : (carryB p q n : ℝ)
      = p * fracB p q n - q * fracB p q (n + 1) := by
    simp only [carryB, fracB] at h ⊢
    linarith [h]
  constructor
  · have : (-(q : ℤ) : ℝ) < (carryB p q n : ℝ) := by
      rw [hcast]
      push_cast
      nlinarith [mul_nonneg hp0.le hy0, mul_lt_mul_of_pos_left hz1 hq0]
    exact_mod_cast this
  · have : (carryB p q n : ℝ) < ((p : ℤ) : ℝ) := by
      rw [hcast]
      push_cast
      nlinarith [mul_nonneg hq0.le hz0, mul_lt_mul_of_pos_left hy1 hp0]
    exact_mod_cast this

/-- **[Dub09AA] Lemma 2 at `ξ = 1`**, cited from `Z32/DubickasWord.lean`, not restated: the carry
word of `(p/q)ⁿ` is aperiodic at every coprime base.  This is the qualitative statement the
free-zone theorem upgrades to a *rate*. -/
@[category research solved, AMS 11 68, ref "Dub09AA" "DN05", group "tshift_s14"]
theorem carryB_not_isEventuallyPeriodic (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) :
    ¬ ForMathlib.SubwordComplexity.IsEventuallyPeriodic (carryB p q) :=
  Z32.not_isEventuallyPeriodic_carry hq hpq hcop one_ne_zero

/-! ### The base-`3/2` objects are the `(p, q) = (3, 2)` instance -/

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_three_two (n : ℕ) : intPartB 3 2 n = intPart n := by
  rw [intPartB_eq, intPart]; norm_num

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem fracB_three_two (n : ℕ) : fracB 3 2 n = Z32.x n := by
  rw [fracB_eq, Z32.x]; norm_num

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem carryB_three_two (n : ℕ) : carryB 3 2 n = carry n := by
  rw [carryB_eq, carry, intPartB_three_two, intPartB_three_two]
  norm_num

/-! ## 2. The rational structure of the `ξ = 1` orbit

The whole difference between `ξ = 1` and a general real `ξ` is here: the orbit is a ratio of
integers with a `q`-power denominator and a numerator coprime to `q`. -/

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem pow_ratio_eq (n : ℕ) : ((p : ℝ) / q) ^ n = ((p ^ n : ℕ) : ℝ) / ((q ^ n : ℕ) : ℝ) := by
  push_cast
  rw [div_pow]

/-- **The `ξ = 1` orbit is rational**: `yₙ = (pⁿ mod qⁿ)/qⁿ`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem fracB_eq_mod_div (n : ℕ) :
    fracB p q n = ((p ^ n % q ^ n : ℕ) : ℝ) / ((q ^ n : ℕ) : ℝ) := by
  rw [fracB_eq, pow_ratio_eq, Int.fract_div_natCast_eq_div_natCast_mod]

/-- **The numerator is coprime to `q`.**  This is what makes the `q`-adic floor of §3 available,
and it is exactly what a general real `ξ` does not supply. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem coprime_pow_mod (hcop : Nat.Coprime p q) {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (p ^ n % q ^ n) q := by
  have hdvd : q ∣ q ^ n := dvd_pow_self q (by omega)
  have hmod : p ^ n % q ^ n % q = p ^ n % q := Nat.mod_mod_of_dvd _ hdvd
  have hpn : Nat.Coprime (p ^ n) q := hcop.pow_left n
  -- `gcd q x = gcd (x % q) q` twice, through the common value `gcd (pⁿ % q) q`.
  have h1 : Nat.gcd q (p ^ n) = Nat.gcd (p ^ n % q) q := Nat.gcd_rec q (p ^ n)
  have h2 : Nat.gcd q (p ^ n % q ^ n) = Nat.gcd (p ^ n % q ^ n % q) q :=
    Nat.gcd_rec q (p ^ n % q ^ n)
  rw [hmod, ← h1] at h2
  have : Nat.gcd q (p ^ n) = 1 := hpn.symm
  exact (Nat.coprime_comm.mp (h2.trans this))

/-! ## 3. Route (a): the free `q`-adic floor

The general-base mirror of `TShift.distToNearestInt_mul_ge` — `Odd D` becomes `gcd(D, q) = 1` and
the `2`-power becomes a `q`-power.  The reduction to an integer multiplier
(`TShift.distToNearestInt_mul_le`) is base-independent and is reused verbatim. -/

/-- **The `q`-adic floor, multiplier form.**  `‖D·(p/q)ⁿ‖ ≥ q^{-n}` for `gcd(D, q) = 1`: the
numerator `D·pⁿ` is coprime to `q`, so its residue mod `qⁿ` and that residue's complement are both
at least `1`.  A genuine per-`n` rate `θ = 1/q`, available only because `ξ = 1`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem distToNearestInt_mul_ge_base (hq : 2 ≤ q) (hcop : Nat.Coprime p q)
    {D : ℕ} (hD : Nat.Coprime D q) {n : ℕ} (hn : 1 ≤ n) :
    1 / (q : ℝ) ^ n ≤ distToNearestInt ((D : ℝ) * ((p : ℝ) / q) ^ n) := by
  have hqpos : 0 < q ^ n := pow_pos (by omega) n
  have hrw : (D : ℝ) * ((p : ℝ) / q) ^ n = ((D * p ^ n : ℕ) : ℝ) / ((q ^ n : ℕ) : ℝ) := by
    rw [pow_ratio_eq]
    push_cast
    ring
  set r := (D * p ^ n) % q ^ n with hr
  have hlt : r < q ^ n := Nat.mod_lt _ hqpos
  have hcopn : Nat.Coprime (D * p ^ n) q := Nat.Coprime.mul_left hD (hcop.pow_left n)
  have hrne : r ≠ 0 := by
    intro h0
    have hdvd : q ^ n ∣ D * p ^ n := Nat.dvd_iff_mod_eq_zero.mpr h0
    have hq1 : q ∣ D * p ^ n := (dvd_pow_self q (by omega : n ≠ 0)).trans hdvd
    have : q = 1 := Nat.Coprime.eq_one_of_dvd hcopn.symm hq1
    omega
  have hmin : 1 ≤ min r (q ^ n - r) :=
    le_min (Nat.one_le_iff_ne_zero.mpr hrne) (by omega)
  have hminR : (1 : ℝ) ≤ ((min r (q ^ n - r) : ℕ) : ℝ) := by exact_mod_cast hmin
  have hdR : (0 : ℝ) < ((q ^ n : ℕ) : ℝ) := by exact_mod_cast hqpos
  rw [hrw, distToNearestInt_natCast_div _ _ hqpos]
  calc (1 : ℝ) / (q : ℝ) ^ n = 1 / ((q ^ n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((min r (q ^ n - r) : ℕ) : ℝ) / ((q ^ n : ℕ) : ℝ) := by gcongr

/-- **The `q`-adic floor at a shifted target.**  For `gcd(D, q) = 1` the orbit stays `1/(D·qⁿ)`
away from every rational `A/D`, modulo `1` — the general-base
`TShift.distToNearestInt_ge_of_odd_denom`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem distToNearestInt_ge_of_coprime_denom (hq : 2 ≤ q) (hcop : Nat.Coprime p q)
    {D : ℕ} (hD : Nat.Coprime D q) (hDpos : 0 < D) {n : ℕ} (hn : 1 ≤ n) (A : ℤ) :
    1 / ((D : ℝ) * (q : ℝ) ^ n) ≤ distToNearestInt (((p : ℝ) / q) ^ n - (A : ℝ) / D) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hqR : (0 : ℝ) < (q : ℝ) ^ n := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  have h3 : 1 / (q : ℝ) ^ n
      ≤ (D : ℝ) * distToNearestInt (((p : ℝ) / q) ^ n - (A : ℝ) / D) :=
    le_trans (distToNearestInt_mul_ge_base hq hcop hD hn) (distToNearestInt_mul_le hDpos _ A)
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hqR] at h3
  linarith [h3]

/-- Only the fractional part matters: `‖yₙ − ρ‖ = ‖(p/q)ⁿ − ρ‖`, the general-base
`TShift.distToNearestInt_pow_sub`. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem distToNearestInt_fracB_sub (n : ℕ) (ρ : ℝ) :
    distToNearestInt (fracB p q n - ρ) = distToNearestInt (((p : ℝ) / q) ^ n - ρ) := by
  have hx : fracB p q n = ((p : ℝ) / q) ^ n - ((intPartB p q n : ℤ) : ℝ) := by
    have := intPartB_add_fracB (p := p) (q := q) n
    linarith
  rw [hx, show ((p : ℝ) / q) ^ n - ((intPartB p q n : ℤ) : ℝ) - ρ
      = (((p : ℝ) / q) ^ n - ρ) + ((-intPartB p q n : ℤ) : ℝ) by push_cast; ring,
    distToNearestInt_add_intCast]

/-! ## 4. The cycle denominator at a general base

`D_m = p^m − q^m` is the general-base `Z32.cycleDenom` (which is its `(3, 2)` instance, `3^m −
2^m`).  Coprimality with `q` is what lets §3's floor be applied at the cycle targets `A/D_m`. -/

/-- `D_m = p^m − q^m`, the denominator of a period-`m` cycle point of the carry relation. -/
def cycleDenomB (p q m : ℕ) : ℕ := p ^ m - q ^ m

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem cycleDenomB_three_two (m : ℕ) : cycleDenomB 3 2 m = Z32.cycleDenom m := rfl

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem cycleDenomB_cast (hpq : q ≤ p) (m : ℕ) :
    ((cycleDenomB p q m : ℕ) : ℝ) = (p : ℝ) ^ m - (q : ℝ) ^ m := by
  have hle : q ^ m ≤ p ^ m := Nat.pow_le_pow_left hpq m
  rw [cycleDenomB]
  push_cast [Nat.cast_sub hle]
  ring

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem cycleDenomB_pos (hpq : q < p) {m : ℕ} (hm : 1 ≤ m) : 0 < cycleDenomB p q m := by
  have hlt : q ^ m < p ^ m := Nat.pow_lt_pow_left hpq (by omega)
  rw [cycleDenomB]
  exact Nat.sub_pos_of_lt hlt

/-- **`D_m` is coprime to `q`** — because `p^m − q^m ≡ p^m` mod `q`.  This is the hypothesis §3's
floor needs at the cycle targets, and it holds at every coprime base. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem cycleDenomB_coprime (hcop : Nat.Coprime p q) (hpq : q ≤ p) {m : ℕ} (hm : 1 ≤ m) :
    Nat.Coprime (cycleDenomB p q m) q := by
  have hle : q ^ m ≤ p ^ m := Nat.pow_le_pow_left hpq m
  set d := Nat.gcd (cycleDenomB p q m) q with hd
  have hd1 : d ∣ cycleDenomB p q m := Nat.gcd_dvd_left _ _
  have hd2 : d ∣ q := Nat.gcd_dvd_right _ _
  have hdq : d ∣ q ^ m := hd2.trans (dvd_pow_self q (by omega))
  have hsum : cycleDenomB p q m + q ^ m = p ^ m := Nat.sub_add_cancel hle
  have hdp : d ∣ p ^ m := hsum ▸ Nat.dvd_add hd1 hdq
  have hdvd1 : d ∣ Nat.gcd (p ^ m) q := Nat.dvd_gcd hdp hd2
  rw [hcop.pow_left m] at hdvd1
  exact Nat.eq_one_of_dvd_one hdvd1

/-- **The general-base cycle point.**  `A/D_m` is the fixed point of the period-`m` affine map
`y ↦ (p/q)^m·y − A/q^m`; at `(3, 2)` this is `TShift.affine_fixedPoint`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem affine_fixedPointB (hq : 1 ≤ q) (hpq : q < p) {m : ℕ} (hm : 1 ≤ m) (A : ℤ) :
    ((p : ℝ) / q) ^ m * ((A : ℝ) / (cycleDenomB p q m : ℕ)) - (A : ℝ) / (q : ℝ) ^ m
      = (A : ℝ) / (cycleDenomB p q m : ℕ) := by
  have hpos : (0 : ℝ) < ((cycleDenomB p q m : ℕ) : ℝ) := by
    exact_mod_cast cycleDenomB_pos hpq hm
  have hcast : ((cycleDenomB p q m : ℕ) : ℝ) = (p : ℝ) ^ m - (q : ℝ) ^ m :=
    cycleDenomB_cast (le_of_lt hpq) m
  have hq0 : (0 : ℝ) < (q : ℝ) ^ m := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  rw [hcast] at hpos ⊢
  rw [div_pow]
  field_simp
  ring

/-! ## 5. Route (b): the circuit sum and the divisibility cascade

The general-base port of `TShift/FreeSojourn.lean` §2, i.e. of the floor-convention Lemma R.  The
mechanism is `[Dub09AA]` (4) read as an *integer* identity: `q^k·m_{a+k} = p^k·m_a + W(a,k)`.  (The
real-valued form with `Z32.geomAcc` is `Z32.xInt_add`; the integer form below is what divisibility
needs, and it is one induction either way.) -/

/-- The circuit sum `W(a,k) = Σ_{i<k} p^{k−1−i}·q^i·s_{a+i}` — `TShift.carrySum` at a general
base. -/
noncomputable def carrySumB (p q a k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, (p : ℤ) ^ (k - 1 - i) * (q : ℤ) ^ i * carryB p q (a + i)

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14", simp]
theorem carrySumB_zero (a : ℕ) : carrySumB p q a 0 = 0 := by simp [carrySumB]

/-- Circuit-sum recurrence: `W(a,k+1) = p·W(a,k) + q^k·s_{a+k}`. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem carrySumB_succ (a k : ℕ) :
    carrySumB p q a (k + 1) = p * carrySumB p q a k + (q : ℤ) ^ k * carryB p q (a + k) := by
  unfold carrySumB
  rw [Finset.sum_range_succ]
  have h1 : k + 1 - 1 - k = 0 := by omega
  rw [h1, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i < k := Finset.mem_range.mp hi
  have h2 : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
  rw [h2, pow_succ]
  ring

/-- **[Dub09AA] (4), integer form.**  `q^k·m_{a+k} = p^k·m_a + W(a,k)`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem carryB_circuit_sum (a k : ℕ) :
    (q : ℤ) ^ k * intPartB p q (a + k) = (p : ℤ) ^ k * intPartB p q a + carrySumB p q a k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsucc : a + (k + 1) = (a + k) + 1 := rfl
    rw [hsucc, carrySumB_succ]
    calc (q : ℤ) ^ (k + 1) * intPartB p q ((a + k) + 1)
        = (q : ℤ) ^ k * ((q : ℤ) * intPartB p q ((a + k) + 1)) := by ring
      _ = (q : ℤ) ^ k * ((p : ℤ) * intPartB p q (a + k) + carryB p q (a + k)) := by
          rw [q_mul_intPartB_succ]
      _ = (p : ℤ) * ((q : ℤ) ^ k * intPartB p q (a + k)) + (q : ℤ) ^ k * carryB p q (a + k) := by
          ring
      _ = (p : ℤ) * ((p : ℤ) ^ k * intPartB p q a + carrySumB p q a k)
            + (q : ℤ) ^ k * carryB p q (a + k) := by rw [ih]
      _ = (p : ℤ) ^ (k + 1) * intPartB p q a
            + ((p : ℤ) * carrySumB p q a k + (q : ℤ) ^ k * carryB p q (a + k)) := by ring

/-- A length-`k` factor of the carry word occurring at both positions `a` and `c` — the general-base
`TShift.IsCarryRepetition`. -/
def IsCarryRepetitionB (p q a c k : ℕ) : Prop := ∀ i < k, carryB p q (a + i) = carryB p q (c + i)

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem carrySumB_eq_of_repetition {a c k : ℕ} (h : IsCarryRepetitionB p q a c k) :
    carrySumB p q a k = carrySumB p q c k :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-- **Lemma R at a general base.**  Equal factors accumulate equal circuit sums, so the main terms
cancel exactly: `p^k(m_c − m_a) = q^k(m_{c+k} − m_{a+k})`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem lemmaR_base {a c k : ℕ} (h : IsCarryRepetitionB p q a c k) :
    (p : ℤ) ^ k * (intPartB p q c - intPartB p q a)
      = (q : ℤ) ^ k * (intPartB p q (c + k) - intPartB p q (a + k)) := by
  have ha := carryB_circuit_sum (p := p) (q := q) a k
  have hc := carryB_circuit_sum (p := p) (q := q) c k
  have hw := carrySumB_eq_of_repetition h
  linear_combination ha - hc + hw

/-- **The divisibility cascade, general base.**  A length-`k` repetition of the carry word forces
`q^k ∣ m_c − m_a`.  No Diophantine input and no `ξ = 1`: this is read off the *word*. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem q_pow_dvd_of_carryRepetitionB (hcop : Nat.Coprime p q) {a c k : ℕ}
    (h : IsCarryRepetitionB p q a c k) :
    (q : ℤ) ^ k ∣ intPartB p q c - intPartB p q a := by
  have hcopz : IsCoprime ((q : ℤ) ^ k) ((p : ℤ) ^ k) :=
    (Nat.isCoprime_iff_coprime.mpr hcop.symm).pow
  have hdvd : (q : ℤ) ^ k ∣ (p : ℤ) ^ k * (intPartB p q c - intPartB p q a) := by
    rw [lemmaR_base h]
    exact Dvd.intro _ rfl
  exact hcopz.dvd_of_dvd_mul_left hdvd

/-! ## 6. Growth of the integer parts

`⌊(p/q)ⁿ⌋` increases strictly once it has passed `q`, which is what turns the divisibility of §5
into a size bound.  The threshold is base-independent and reduces to an integer inequality. -/

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem one_le_ratio (hq : 1 ≤ q) (hpq : q ≤ p) : (1 : ℝ) ≤ (p : ℝ) / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hle : (q : ℝ) ≤ p := by exact_mod_cast hpq
  rw [le_div_iff₀ hq0]
  linarith

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_pos (hq : 1 ≤ q) (hpq : q ≤ p) (n : ℕ) : 0 < intPartB p q n := by
  have h1 : (1 : ℝ) ≤ ((p : ℝ) / q) ^ n := one_le_pow₀ (one_le_ratio hq hpq)
  rw [intPartB_eq]
  have := Int.le_floor.mpr (by exact_mod_cast h1 : ((1 : ℤ) : ℝ) ≤ ((p : ℝ) / q) ^ n)
  omega

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_mono (hq : 1 ≤ q) (hpq : q ≤ p) : Monotone (intPartB p q) := by
  intro a b hab
  have h := pow_le_pow_right₀ (one_le_ratio (p := p) (q := q) hq hpq) hab
  rw [intPartB_eq, intPartB_eq]
  exact Int.floor_mono h

/-- **The growth threshold is an integer inequality**, and an exact one: `q ≤ mₙ` *iff*
`q^{n+1} ≤ pⁿ`.  Sharp, not merely sufficient, because `q` is an integer and `q ≤ ⌊x⌋ ↔ q ≤ x`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_ge_iff (hq : 1 ≤ q) {n : ℕ} :
    (q : ℤ) ≤ intPartB p q n ↔ q ^ (n + 1) ≤ p ^ n := by
  have hpos : (0 : ℝ) < ((q ^ n : ℕ) : ℝ) := by
    have : 0 < q ^ n := pow_pos (by omega) n
    exact_mod_cast this
  rw [intPartB_eq, Int.le_floor, pow_ratio_eq, le_div_iff₀ hpos]
  have hrw : ((q : ℤ) : ℝ) * ((q ^ n : ℕ) : ℝ) = ((q ^ (n + 1) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hrw]
  exact Nat.cast_le

/-- A cheap integer criterion for the growth threshold.  At `(3, 2)` the first date is `n = 2`
(`2³ ≤ 3²`); in the free zone `p > q²` it is `n = 1`. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_ge_of_pow_le (hq : 1 ≤ q) {n : ℕ} (h : q ^ (n + 1) ≤ p ^ n) :
    (q : ℤ) ≤ intPartB p q n := (intPartB_ge_iff hq).mpr h

/-- **The free zone is exactly the zero-burn-in zone for route (b).**  Route (a)'s dichotomy
`κ_b < 1 ⟺ q² < p` and route (b)'s growth threshold at the *first* date are the same integer
inequality: `q ≤ m₁ ↔ q² ≤ p`.  So above `q²` the cascade needs no burn-in at all, and inside the
hard band — where the cascade is the winning route — it costs at least one date. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_one_ge_iff (hq : 1 ≤ q) : (q : ℤ) ≤ intPartB p q 1 ↔ q * q ≤ p := by
  rw [intPartB_ge_iff hq]
  norm_num [pow_succ]

/-- **The growth step.**  Once `q ≤ mₙ`, the next integer part is strictly larger: the multiplier
`p/q ≥ (q+1)/q` adds at least `mₙ/q ≥ 1`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_lt_succ (hq : 1 ≤ q) (hpq : q < p) {n : ℕ} (h : (q : ℤ) ≤ intPartB p q n) :
    intPartB p q n < intPartB p q (n + 1) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqp : (q : ℝ) + 1 ≤ p := by exact_mod_cast hpq
  have hp0 : (0 : ℝ) < p := by linarith
  have hr : (0 : ℝ) < (p : ℝ) / q := by positivity
  have hMq : (q : ℝ) ≤ ((intPartB p q n : ℤ) : ℝ) := by exact_mod_cast h
  have hfl : ((intPartB p q n : ℤ) : ℝ) ≤ ((p : ℝ) / q) ^ n := by
    rw [intPartB_eq]
    exact Int.floor_le _
  have hgain : ((intPartB p q n : ℤ) : ℝ) + 1
      ≤ ((intPartB p q n : ℤ) : ℝ) * ((p : ℝ) / q) := by
    rw [← mul_div_assoc, le_div_iff₀ hq0]
    have hM0 : (0 : ℝ) ≤ ((intPartB p q n : ℤ) : ℝ) := by linarith
    have h1 : ((intPartB p q n : ℤ) : ℝ) * 1
        ≤ ((intPartB p q n : ℤ) : ℝ) * ((p : ℝ) - q) :=
      mul_le_mul_of_nonneg_left (by linarith) hM0
    linarith [h1]
  have hstep : ((intPartB p q n : ℤ) : ℝ) + 1 ≤ ((p : ℝ) / q) ^ (n + 1) := by
    calc ((intPartB p q n : ℤ) : ℝ) + 1
        ≤ ((intPartB p q n : ℤ) : ℝ) * ((p : ℝ) / q) := hgain
      _ ≤ ((p : ℝ) / q) ^ n * ((p : ℝ) / q) := mul_le_mul_of_nonneg_right hfl hr.le
      _ = ((p : ℝ) / q) ^ (n + 1) := (pow_succ _ _).symm
  have hle : intPartB p q n + 1 ≤ intPartB p q (n + 1) := by
    rw [intPartB_eq (p := p) (q := q) (n + 1)]
    refine Int.le_floor.mpr ?_
    push_cast
    linarith [hstep]
  omega

/-- Strict monotonicity of `⌊(p/q)ⁿ⌋` from the first date at which it reaches `q`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_strictMono (hq : 1 ≤ q) (hpq : q < p) {a c : ℕ} (ha : (q : ℤ) ≤ intPartB p q a)
    (hac : a < c) : intPartB p q a < intPartB p q c := by
  induction c with
  | zero => omega
  | succ d ih =>
    have hmono := intPartB_mono (p := p) (q := q) hq (le_of_lt hpq)
    rcases Nat.lt_or_ge a d with hlt | hge
    · have h1 := ih (by omega)
      have had : (q : ℤ) ≤ intPartB p q d := le_trans ha (hmono (by omega : a ≤ d))
      have h2 := intPartB_lt_succ (p := p) (q := q) hq hpq had
      omega
    · have had : a = d := by omega
      subst had
      exact intPartB_lt_succ hq hpq ha

/-- `qⁿ·mₙ ≤ pⁿ`: the floor convention needs no slack term. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem q_pow_mul_intPartB_le (hq : 1 ≤ q) (n : ℕ) :
    (q : ℤ) ^ n * intPartB p q n ≤ (p : ℤ) ^ n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hfl : ((intPartB p q n : ℤ) : ℝ) ≤ ((p : ℝ) / q) ^ n := by
    rw [intPartB_eq]; exact Int.floor_le _
  have hR : ((q : ℝ)) ^ n * ((intPartB p q n : ℤ) : ℝ) ≤ (p : ℝ) ^ n := by
    have := mul_le_mul_of_nonneg_left hfl hqn.le
    rw [div_pow] at this
    field_simp at this
    linarith
  exact_mod_cast hR

/-! ## 7. The growth ceiling and the general-base sojourn cap

Divisibility (§5) against growth (§6) is the whole of route (b): `q^k ≤ m_c − m_a ≤ m_c` and
`q^c·m_c ≤ p^c` give `q^{k+c} ≤ p^c`. -/

/-- **The growth ceiling, general base.**  A length-`k` repetition of the carry word at `a < c`,
with `mₐ` past the growth threshold, forces `q^{k+c} ≤ p^c` — pure integer arithmetic.  In log form
this is `k ≤ κ_casc·c` with `κ_casc = log(p/q)/log q`; the `(3, 2)` instance is
`TShift.carry_repetition_pow_le`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem carryRepetitionB_pow_le (hq : 1 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {a c k : ℕ} (ha : (q : ℤ) ≤ intPartB p q a) (hac : a < c)
    (h : IsCarryRepetitionB p q a c k) : (q : ℤ) ^ (k + c) ≤ (p : ℤ) ^ c := by
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hlt : intPartB p q a < intPartB p q c := intPartB_strictMono hq hpq ha hac
  have h1 : (q : ℤ) ^ k ≤ intPartB p q c - intPartB p q a :=
    Int.le_of_dvd (by omega) (q_pow_dvd_of_carryRepetitionB hcop h)
  have h2 : 0 < intPartB p q a := intPartB_pos hq (le_of_lt hpq) a
  have h4 : (q : ℤ) ^ k ≤ intPartB p q c := by omega
  calc (q : ℤ) ^ (k + c) = (q : ℤ) ^ k * (q : ℤ) ^ c := pow_add _ k c
    _ ≤ intPartB p q c * (q : ℤ) ^ c := by
        exact mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (q : ℤ) ^ c * intPartB p q c := by ring
    _ ≤ (p : ℤ) ^ c := q_pow_mul_intPartB_le hq c

/-- The carry word is `m`-periodic on the block of dates `[n, n+L)` — the general-base
`TShift.IsPeriodicBlock`. -/
def IsPeriodicBlockB (p q n L m : ℕ) : Prop :=
  ∀ i, i + m < L → carryB p q (n + i) = carryB p q (n + m + i)

/-- **The general-base free sojourn cap, integer form (route (b)).**  An `m`-periodic block of the
carry word of length `L` at a date `n` past the growth threshold obeys `q^{L+n} ≤ p^{n+m}`.
Unconditional: no repulsion hypothesis, no shadowing, no band, no multiplier.  In log form,
`L ≤ κ_casc·n + m·log p/log q` with `κ_casc = log(p/q)/log q`; `TShift/FreeZone.lean` packages it. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "GY26", group "tshift_s14"]
theorem periodic_block_pow_le (hq : 1 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {n L m : ℕ} (hn : (q : ℤ) ≤ intPartB p q n) (hm : 1 ≤ m) (hmL : m ≤ L)
    (h : IsPeriodicBlockB p q n L m) : (q : ℤ) ^ (L + n) ≤ (p : ℤ) ^ (n + m) := by
  have hrep : IsCarryRepetitionB p q n (n + m) (L - m) := fun i hi => h i (by omega)
  have hceil := carryRepetitionB_pow_le hq hpq hcop hn (by omega : n < n + m) hrep
  have hexp : (L - m) + (n + m) = L + n := by omega
  rwa [hexp] at hceil

/-- The `(3, 2)` instance is `TShift.free_sojourn_cap` (`TShift/FreeSojourn.lean`, correction C20)
on the nose, growth threshold and all: `2 ≤ n` is `intPartB_ge_of_pow_le` at `2³ ≤ 3²`.  Checked
here as an `example`, so that the generalization is machine-verified rather than asserted. -/
example {n L m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hmL : m ≤ L) (h : IsPeriodicBlock n L m) :
    (2 : ℤ) ^ (L + n) ≤ 3 ^ (n + m) := by
  have hthr : (2 : ℤ) ≤ intPartB 3 2 n := by
    have hmono := intPartB_mono (p := 3) (q := 2) (by norm_num) (by norm_num)
    have h2 : (2 : ℤ) ≤ intPartB 3 2 2 := intPartB_ge_of_pow_le (by norm_num) (by norm_num)
    exact le_trans h2 (hmono hn)
  have hgen : IsPeriodicBlockB 3 2 n L m := by
    intro i hi
    rw [carryB_three_two, carryB_three_two]
    exact h i hi
  have := periodic_block_pow_le (p := 3) (q := 2) (by norm_num) (by norm_num) (by norm_num)
    hthr hm hmL hgen
  exact_mod_cast this

/-! ## 8. Periodic-block affine composition, and shadowing on a finite block

Route (a)'s half.  `TShift.abs_sub_fixed_le` assumes the affine recursion at *every* index; a
finite block supplies it only inside the block (plan risk R6).  Both finite variants below come
from one identity, and the second needs nothing about where the fixed point sits. -/

/-- The exact deviation identity on a finite block: `z_J − ρ = r^J(z_0 − ρ)`. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem sub_fixed_pow_block {r c ρ : ℝ} (hfix : r * ρ - c = ρ) {z : ℕ → ℝ} {J : ℕ}
    (hz : ∀ i, i < J → z (i + 1) = r * z i - c) : z J - ρ = r ^ J * (z 0 - ρ) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hstep : z (J + 1) - ρ = r * (z J - ρ) := by
      rw [hz J (by omega)]
      nlinarith [hfix]
    rw [hstep, ih fun i hi => hz i (by omega), pow_succ]
    ring

/-- **Finite-block shadowing.**  A trajectory of an expanding affine map that is still within `B`
of the fixed point after `J` steps of the block started within `B/r^J` of it — the finite-block
variant of `TShift.abs_sub_fixed_le`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem abs_sub_fixed_le_block {r c ρ B : ℝ} (hr : 1 < r) (hfix : r * ρ - c = ρ) {z : ℕ → ℝ}
    {J : ℕ} (hz : ∀ i, i < J → z (i + 1) = r * z i - c) (hb : |z J - ρ| ≤ B) :
    |z 0 - ρ| ≤ B / r ^ J := by
  have hrj : (0 : ℝ) < r ^ J := by positivity
  have key := sub_fixed_pow_block hfix hz
  rw [le_div_iff₀ hrj, mul_comm]
  calc r ^ J * |z 0 - ρ| = |r ^ J * (z 0 - ρ)| := by
        rw [abs_mul, abs_of_pos hrj]
    _ = |z J - ρ| := by rw [key]
    _ ≤ B := hb

/-- **Finite-block shadowing without the fixed point.**  A bound on the *endpoint spread*
`|z_J − z_0|` pulls back the same way, and mentions `ρ` only through the recursion.  This is the
form the free-zone cap uses: along a block of the carry word both endpoints are fractional parts,
so `B = 1` is free. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem abs_sub_fixed_mul_le_block {r c ρ B : ℝ} (hfix : r * ρ - c = ρ) {z : ℕ → ℝ}
    {J : ℕ} (hz : ∀ i, i < J → z (i + 1) = r * z i - c) (hb : |z J - z 0| ≤ B) :
    |r ^ J - 1| * |z 0 - ρ| ≤ B := by
  have key := sub_fixed_pow_block hfix hz
  have hdiff : z J - z 0 = (r ^ J - 1) * (z 0 - ρ) := by
    have : z J - z 0 = (z J - ρ) - (z 0 - ρ) := by ring
    rw [this, key]; ring
  calc |r ^ J - 1| * |z 0 - ρ| = |(r ^ J - 1) * (z 0 - ρ)| := (abs_mul _ _).symm
    _ = |z J - z 0| := by rw [hdiff]
    _ ≤ B := hb

/-! ### The block composition -/

/-- The `m`-step composition, in fractional-part form: `y_{n+m} = (p/q)^m·yₙ − W(n,m)/q^m`.  The
integer circuit sum of §5 *is* the numerator `A_w` of the period-`m` cycle point. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem fracB_add (hq : 1 ≤ q) (n m : ℕ) :
    fracB p q (n + m)
      = ((p : ℝ) / q) ^ m * fracB p q n - (carrySumB p q n m : ℝ) / (q : ℝ) ^ m := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqm : (0 : ℝ) < (q : ℝ) ^ m := by positivity
  have hcs : ((q : ℤ) ^ m * intPartB p q (n + m) : ℤ)
      = ((p : ℤ) ^ m * intPartB p q n + carrySumB p q n m : ℤ) := carryB_circuit_sum n m
  have hcsR : (q : ℝ) ^ m * (intPartB p q (n + m) : ℝ)
      = (p : ℝ) ^ m * (intPartB p q n : ℝ) + (carrySumB p q n m : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hcs
  have hn := intPartB_add_fracB (p := p) (q := q) n
  have hnm := intPartB_add_fracB (p := p) (q := q) (n + m)
  have hpow : ((p : ℝ) / q) ^ (n + m) = ((p : ℝ) / q) ^ m * ((p : ℝ) / q) ^ n := by
    rw [pow_add]; ring
  rw [hpow] at hnm
  have e1 : (q : ℝ) ^ m * ((p : ℝ) / q) ^ m = (p : ℝ) ^ m := by
    rw [div_pow]
    field_simp
  -- clear the denominator once, then it is a linear identity in the four facts
  have key : (q : ℝ) ^ m * fracB p q (n + m)
      = (p : ℝ) ^ m * fracB p q n - (carrySumB p q n m : ℝ) := by
    linear_combination (q : ℝ) ^ m * hnm - (p : ℝ) ^ m * hn - hcsR
      + ((p : ℝ) / q) ^ n * e1
  rw [div_pow]
  field_simp
  linear_combination key

/-- On an `m`-periodic block the word repeats window by window: `s_{n+jm+i} = s_{n+i}`. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem carryB_block_shift {n L m : ℕ} (h : IsPeriodicBlockB p q n L m) :
    ∀ j i : ℕ, j * m + i < L → carryB p q (n + (j * m + i)) = carryB p q (n + i) := by
  intro j
  induction j with
  | zero => intro i _; simp
  | succ j ih =>
    intro i hi
    have hexp : (j + 1) * m + i = j * m + i + m := by ring
    rw [hexp] at hi
    have hstep : carryB p q (n + (j * m + i)) = carryB p q (n + m + (j * m + i)) :=
      h (j * m + i) (by omega)
    have hidx : n + m + (j * m + i) = n + (j * m + i + m) := by ring
    rw [hexp, ← hidx, ← hstep]
    exact ih i (by omega)

/-- Hence every window sum on the block is the same integer `A_w = W(n, m)`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem carrySumB_shift_of_block {n L m j : ℕ} (h : IsPeriodicBlockB p q n L m)
    (hj : j * m + m ≤ L) : carrySumB p q (n + j * m) m = carrySumB p q n m := by
  unfold carrySumB
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i < m := Finset.mem_range.mp hi
  have hidx : n + j * m + i = n + (j * m + i) := by omega
  rw [hidx, carryB_block_shift h j i (by omega)]

/-- **The periodic-block affine recursion.**  On an `m`-periodic block, `z_j = y_{n+jm}` runs the
*single* affine map `z ↦ (p/q)^m·z − A_w/q^m`, `A_w = W(n,m)`, whose fixed point is `A_w/D_m`
(`affine_fixedPointB`). -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem fracB_block_step (hq : 1 ≤ q) {n L m j : ℕ} (h : IsPeriodicBlockB p q n L m)
    (hj : j * m + m ≤ L) :
    fracB p q (n + (j + 1) * m)
      = ((p : ℝ) / q) ^ m * fracB p q (n + j * m) - (carrySumB p q n m : ℝ) / (q : ℝ) ^ m := by
  have hidx : n + (j + 1) * m = (n + j * m) + m := by ring
  rw [hidx, fracB_add hq (n + j * m) m, carrySumB_shift_of_block h hj]

/-- **The block shadow.**  An `m`-periodic block of length `L ≥ J·m` at date `n` pins the orbit to
the period-`m` cycle point `A_w/D_m` at the rate `(p/q)^{Jm}`:

  `((p/q)^{Jm} − 1)·|yₙ − A_w/D_m| ≤ 1`.

Free of any assumption on the target, because the endpoints of the block are fractional parts.
Against the `q`-adic floor of §3 (at `D = D_m`, which `cycleDenomB_coprime` licenses) this is the
free-zone cap; `TShift/FreeZone.lean` assembles it. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem block_shadow (hq : 1 ≤ q) (hpq : q < p) {n L m J : ℕ} (hm : 1 ≤ m) (hJ : J * m ≤ L)
    (h : IsPeriodicBlockB p q n L m) :
    |((p : ℝ) / q) ^ (J * m) - 1| *
        |fracB p q n - (carrySumB p q n m : ℝ) / ((cycleDenomB p q m : ℕ) : ℝ)| ≤ 1 := by
  set r : ℝ := ((p : ℝ) / q) ^ m with hrdef
  set A : ℝ := (carrySumB p q n m : ℝ) with hAdef
  set ρ : ℝ := A / ((cycleDenomB p q m : ℕ) : ℝ) with hρdef
  set z : ℕ → ℝ := fun j => fracB p q (n + j * m) with hzdef
  have hfix : r * ρ - A / (q : ℝ) ^ m = ρ := by
    rw [hrdef, hρdef, hAdef]
    exact affine_fixedPointB (p := p) (q := q) hq hpq hm (carrySumB p q n m)
  have hz : ∀ i, i < J → z (i + 1) = r * z i - A / (q : ℝ) ^ m := by
    intro i hi
    have hji : i * m + m ≤ L := by
      have : (i + 1) * m ≤ J * m := Nat.mul_le_mul_right m (by omega)
      calc i * m + m = (i + 1) * m := by ring
        _ ≤ J * m := this
        _ ≤ L := hJ
    simpa [hzdef, hrdef, hAdef] using fracB_block_step (p := p) (q := q) hq h hji
  have hb : |z J - z 0| ≤ 1 := by
    have h0 := fracB_nonneg (p := p) (q := q) (n + J * m)
    have h1 := fracB_lt_one (p := p) (q := q) (n + J * m)
    have h2 := fracB_nonneg (p := p) (q := q) (n + 0 * m)
    have h3 := fracB_lt_one (p := p) (q := q) (n + 0 * m)
    simp only [hzdef]
    rw [abs_le]
    constructor <;> linarith
  have hkey := abs_sub_fixed_mul_le_block (r := r) (c := A / (q : ℝ) ^ m) (ρ := ρ) (B := 1)
    hfix hz hb
  have hrJ : r ^ J = ((p : ℝ) / q) ^ (J * m) := by
    rw [hrdef, ← pow_mul, Nat.mul_comm]
  rw [hrJ] at hkey
  simpa [hzdef, hρdef, hAdef] using hkey

/-! ## 9. Sanity

The base `5/2`, the smallest free-zone base and Theorem C's instance: `mₙ = 1, 2, 6, 15, 39`,
carry word `−1, 2, 0, 3`, cycle denominators `D₁ = 3`, `D₂ = 21`, and the growth threshold already
at `n = 1` (against `n = 2` at base `3/2`). -/

@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_five_two :
    intPartB 5 2 0 = 1 ∧ intPartB 5 2 1 = 2 ∧ intPartB 5 2 2 = 6 ∧ intPartB 5 2 3 = 15 ∧
      intPartB 5 2 4 = 39 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [intPartB_eq]
      norm_num [Int.floor_eq_iff]

@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem carryB_five_two :
    carryB 5 2 0 = -1 ∧ carryB 5 2 1 = 2 ∧ carryB 5 2 2 = 0 ∧ carryB 5 2 3 = 3 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := intPartB_five_two
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [carryB_eq] <;> norm_num [h0, h1, h2, h3, h4]

@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem cycleDenomB_five_two : cycleDenomB 5 2 1 = 3 ∧ cycleDenomB 5 2 2 = 21 := by
  constructor <;> norm_num [cycleDenomB]

/-- The growth threshold `q ≤ mₙ` is reached at `n = 1` at base `5/2` and only at `n = 2` at base
`3/2` — the free zone pays no burn-in, the hard band pays one date.  The third clause is where
`intPartB_ge_iff`'s sharpness is used: `2 ≤ ⌊3/2⌋` is *false*. -/
@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem growth_threshold_five_two_three_two :
    (2 : ℤ) ≤ intPartB 5 2 1 ∧ (2 : ℤ) ≤ intPartB 3 2 2 ∧ ¬ ((2 : ℤ) ≤ intPartB 3 2 1) := by
  refine ⟨(intPartB_one_ge_iff (by norm_num)).mpr (by norm_num),
    intPartB_ge_of_pow_le (by norm_num) (by norm_num), ?_⟩
  have h := intPartB_ge_iff (p := 3) (q := 2) (n := 1) (by norm_num)
  norm_num at h
  omega

end TShift
