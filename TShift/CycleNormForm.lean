/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.Basic
import TShift.MultiplierTransfer
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The norm form over a cycle, and what the structure of `D_p` is worth

Strategy **S9** of `plans/report-Tshift.html` — "make the structure of `D_p` pay" — priced.  The
row proposes two mechanisms for beating the free `2`-adic floor by using something about the
cycle `A ↦ 3·2⁻¹A (mod D_p)` that the multiplier transfer does not use:

* **(i)** impose `D_p ∣ aᵢ` on the coefficients of the two eliminating forms (a pigeonhole over
  `D` parameter shifts), and align the numerator dynamics with the construction's residue
  classes, "turning the `O(log D)` transfer loss into a gain";
* **(ii)** multiply the floors over one `p`-cycle: `M_n = ∏_{i<p}(D rₙ − A⁽ⁱ⁾2ⁿ)` is an odd
  integer, so `|M_n| ≥ 1` — which alone *loses*, and pays only if forced divisibility is
  injected.

Both are closed here, negatively, and the closures are theorems rather than measurements.

## The verdict, in one line each

**(ii) is a restatement of the problem with a worse constant, and its arithmetic input is
capped at the free floor.**  Write `xₙ = rₙ/2ⁿ` and `ρᵢ = A⁽ⁱ⁾/D`.  The product is the exact
quantity `|M_n| = (D2ⁿ)^k ∏ᵢ|xₙ − ρᵢ|` (`abs_cycleProd_eq`), and since the far factors of a
`1/D`-separated cycle are pinned between `(2D)^{-(k-1)}` and `1`, a lower bound for `|M_n|` and
a lower bound for the single distance determine each other up to the explicit factor `(2D)^{k-1}`
(`le_abs_sub_of_le_abs_cycleProd`, `abs_cycleProd_le_of_near`).  So the route asks for the same
theorem.  What it *can* prove is bounded: the only property of `rₙ` it uses is that `rₙ` is odd,
and among the odd `r` there are always some for which the product is as small as the free floor
allows (`exists_odd_abs_cycleProd_le`).  Hence **no rate above `1/2` is derivable from the product
at all** — `route_rate_le_half`, unconditional, at every period and every cycle.

**(i) is a rescaling of the multiplier transfer, and rescaling is exactly what the ledger cannot
see.**  Imposing `t ∣ aᵢ, bᵢ` multiplies the content `P`, the size `Λ` and the height `B` of the
eliminating pair by `t` at once, and the transfer bound `(P·X − |c|·Λ)/B` is homogeneous of
degree `0` in that scaling (`TwoForms.scale`, `transfer_bound_scale`): the "content refund" `P = D`
is exactly the multiplier loss `|c|·Λ = D·Λ`, to the last digit — `scale_sanity_five` runs the
corpus's own worked instance at `t = 5` and returns the same `11/16`.  This is the general form of
what plan-S7's WP-D measured at the flagship (form quality is projective; a finite-index sublattice
spans the same projective space with fewer integer points).  And a device that survives the
rescaling is still `m`-uniform, i.e. it is the *multiplier* form — from which `‖(3/2)ⁿ‖ ≥ ‖D(3/2)ⁿ‖/D`
transports the same `θ` to `ρ = 0` (`isRepelled_zero_of_isRepelledMul`).  So the rung S9 is
listed under — **T1 without T4** — is unreachable down prong (i) by report N1, whatever the
construction.

## What is actually forced

Not nothing, and the file says exactly what.  A prime `q ∣ D` with `q ∤ A⁽ⁱ⁾` never divides the
product (`not_dvd_cycleProd`, the reason `5 ∤ M_n` at `D = 5`); a common divisor of `D` and the
whole cycle divides the product `k` times (`pow_dvd_cycleProd`); a prime dividing two factors at
once divides the difference of their numerators (`dvd_sub_of_dvd_tgtNum_two`, which is the
*correct* form of the row's resultant claim — the resultant governs coincidences between factors,
not the primes of `M_n`); and an odd prime `q ∤ D` that divides the product for **every** odd `r`
satisfies `q ≤ k` (`forced_prime_le_card`).  Every one of these is a constant: bounded in terms of
`D`, `k` and the cycle, never growing with `n`.  The route needs `2^{n(k-1)}`.

## What is *not* claimed

* Nothing here says the product `M_n` is small — it is not; on the real orbit
  `log|M_n|/n → k·log 2`, and the whole gap between that truth and the `2^{n(k-1)}` ceiling above
  is the T-shift problem itself.  What is proved is that the *guarantee* stops at the free floor.
* Nothing here is about a specific Padé construction.  Prong (i) is priced at the level of the
  elimination ledger (`TShift/MultiplierTransfer.lean`), which is where every effective `D = 1`
  proof ends; a construction that gains by some other route is not excluded by scale invariance,
  it is only excluded from gaining *by imposing a congruence on the coefficients*.
* `forced_prime_le_card` is about divisors forced for every odd `r`.  The real orbit's `rₙ` is one
  specific odd number per date, and its factorisations are measured, not proved: harness block
  `s9` [C] reports them (small primes carry 3.06% of `log|M_n|` at `D = 5`, against a null model
  of `k` independent factors).

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: **zero cited axioms**, no `sorry`,
no `native_decide`.  The file imports `TShift.Basic` and `TShift.MultiplierTransfer` only, so it
stays `#print axioms`-disjoint from all four engine lanes.

## Claim level

Formalization of a negative pricing.  The mathematics is elementary; the content is that the two
mechanisms are placed exactly, and that the ceilings are theorems.

## References

* `plans/report-Tshift.html` — S9 (the row), §4 (Proposition 1), N1 (T2 ⇒ T4), N2 (the cycles are
  the inequivalent targets), C11, and the dead-end entry "`q`-adic amplification at `q ∣ D`".
* `plans/note-Tshift-S9.html` — this item's record.
* `plans/note-Tshift-S7-WPD.html` — the flagship measurement of prong (i)'s congruence
  mechanism (Q2, and O-3's falsification), 2026-08-11; the projectivity argument this file
  generalises.
-/

namespace TShift

open Finset

/-! ## 1. The single-target numerator

`‖xₙ − A/D‖` is `|D·r − A·2ⁿ|/(D·2ⁿ)`, and the numerator is the only arithmetic in the problem.
Its two elementary properties — it is odd, and it is pinned to the class `−A·2ⁿ (mod D)` — are the
whole of what the "structure of `D_p`" contributes; §3 measures what that is worth. -/

/-- The single-target numerator `D·r − A·2ⁿ`: for `x = r/2ⁿ` and `ρ = A/D`,
`|x − ρ| = |tgtNum|/(D·2ⁿ)`. -/
@[category API, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
def tgtNum (D : ℕ) (A : ℤ) (n : ℕ) (r : ℤ) : ℤ := (D : ℤ) * r - A * 2 ^ n

/-- Odd denominator, odd numerator: the free `2`-adic floor, at the level of one factor. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem tgtNum_odd {D : ℕ} (hD : Odd D) {A r : ℤ} (hr : Odd r) {n : ℕ} (hn : 1 ≤ n) :
    Odd (tgtNum D A n r) := by
  obtain ⟨s, hs⟩ := hD
  obtain ⟨t, ht⟩ := hr
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hDz : (D : ℤ) = 2 * s + 1 := by exact_mod_cast hs
  refine ⟨(2 * s + 1) * t + s - A * 2 ^ j, ?_⟩
  rw [tgtNum, hDz, ht, pow_succ]
  ring

/-- The class the target pins: `tgtNum ≡ −A·2ⁿ (mod D)`.  This is the *only* thing a single-target
statement knows that the multiplier form does not — the free integer's residue mod `D`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem tgtNum_modEq (D : ℕ) (A : ℤ) (n : ℕ) (r : ℤ) :
    tgtNum D A n r ≡ -(A * 2 ^ n) [ZMOD (D : ℤ)] := by
  refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨r, ?_⟩)
  rw [tgtNum]; ring

/-- **The class is worth at most `D`.**  For every `A` and every `n` there is an *odd* `r` whose
numerator lies in the pinned class and has absolute value at most `D`.  So the two elementary
constraints — oddness and the residue class — are simultaneously satisfiable at the free floor,
and no argument using only them can prove more than `‖x − A/D‖ ≥ 1/(D·2ⁿ)`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem exists_odd_tgtNum_abs_le {D : ℕ} (hD : 0 < D) (A : ℤ) (n : ℕ) :
    ∃ r : ℤ, Odd r ∧ |tgtNum D A n r| ≤ (D : ℤ) := by
  have hDz : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  set t : ℤ := A * 2 ^ n with ht
  set q : ℤ := t / (D : ℤ) with hq
  have hmod : (D : ℤ) * q + t % (D : ℤ) = t := Int.mul_ediv_add_emod t (D : ℤ)
  have h0 : 0 ≤ t % (D : ℤ) := Int.emod_nonneg t (by omega)
  have h1 : t % (D : ℤ) < (D : ℤ) := Int.emod_lt_of_pos t hDz
  rcases Int.even_or_odd q with he | ho
  · refine ⟨q + 1, ?_, ?_⟩
    · exact Even.add_one he
    · rw [tgtNum, ← ht]
      have : (D : ℤ) * (q + 1) - t = (D : ℤ) - t % (D : ℤ) := by linarith [hmod]
      rw [this, abs_of_nonneg (by omega)]
      omega
  · refine ⟨q, ho, ?_⟩
    rw [tgtNum, ← ht]
    have : (D : ℤ) * q - t = -(t % (D : ℤ)) := by linarith [hmod]
    rw [this, abs_neg, abs_of_nonneg h0]
    omega

/-- **The mock orbit.**  The same statement in the real currency: an odd numerator at distance at
most `2⁻ⁿ` from the target.  Every hypothesis prong (i) or (ii) can impose on `rₙ` beyond
`rₙ ≡ 3ⁿ (mod 2ⁿ)` — oddness, the residue class of the target, the cycle it belongs to — is
satisfied by this `r`, so those hypotheses cap the provable rate at `θ = 1/2`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem exists_odd_near_target {D : ℕ} (hD : 0 < D) (A : ℤ) (n : ℕ) :
    ∃ r : ℤ, Odd r ∧ |(r : ℝ) / 2 ^ n - (A : ℝ) / (D : ℝ)| ≤ 1 / 2 ^ n := by
  obtain ⟨r, hr, hle⟩ := exists_odd_tgtNum_abs_le hD A n
  refine ⟨r, hr, ?_⟩
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcast : |((D : ℝ) * r - (A : ℝ) * 2 ^ n)| ≤ (D : ℝ) := by
    have h := hle
    rw [tgtNum] at h
    exact_mod_cast h
  have hrw : (r : ℝ) / 2 ^ n - (A : ℝ) / (D : ℝ)
      = ((D : ℝ) * r - (A : ℝ) * 2 ^ n) / ((D : ℝ) * 2 ^ n) := by
    field_simp
  have hstep : |((D : ℝ) * r - (A : ℝ) * 2 ^ n)| / ((D : ℝ) * 2 ^ n)
      ≤ (D : ℝ) / ((D : ℝ) * 2 ^ n) := by gcongr
  have hval : (D : ℝ) / ((D : ℝ) * 2 ^ n) = 1 / 2 ^ n := by field_simp
  rw [hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (D : ℝ) * 2 ^ n)]
  linarith [hstep, hval.le, hval.ge]

/-! ## 2. The norm form over a cycle

`M_n = ∏_{i<k}(D·rₙ − A⁽ⁱ⁾2ⁿ)`, the object S9(ii) proposes.  The index type is `Fin k` with `k`
the length of the cycle (a divisor of the period `p`; at `D₄ = 65` two of the seventeen cycles
have length `2`). -/

/-- The cycle norm form `∏ᵢ (D·r − A⁽ⁱ⁾2ⁿ)`. -/
@[category API, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
def cycleProd (D : ℕ) {k : ℕ} (A : Fin k → ℤ) (n : ℕ) (r : ℤ) : ℤ :=
  ∏ i, tgtNum D (A i) n r

/-- The product of odd numbers is odd — the row's "`M_n` is an odd integer". -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem cycleProd_odd {D : ℕ} (hD : Odd D) {k : ℕ} (A : Fin k → ℤ) {n : ℕ} (hn : 1 ≤ n) {r : ℤ}
    (hr : Odd r) : Odd (cycleProd D A n r) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one
    (fun _ _ => tgtNum_odd hD hr hn)

/-- …hence `|M_n| ≥ 1`: the whole arithmetic input the route offers. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem one_le_abs_cycleProd {D : ℕ} (hD : Odd D) {k : ℕ} (A : Fin k → ℤ) {n : ℕ} (hn : 1 ≤ n)
    {r : ℤ} (hr : Odd r) : 1 ≤ |cycleProd D A n r| := by
  have hodd := cycleProd_odd hD A hn hr
  refine Int.one_le_abs ?_
  intro h
  rw [h] at hodd
  simp [Int.odd_iff] at hodd

/-- **The identity.**  `|M_n| = (D·2ⁿ)^k · ∏ᵢ|xₙ − ρᵢ|` — the product carries no information the
distances do not, and vice versa. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem abs_cycleProd_eq {D : ℕ} (hD : 0 < D) {k : ℕ} (A : Fin k → ℤ) (n : ℕ) (r : ℤ) :
    ((|cycleProd D A n r| : ℤ) : ℝ)
      = ((D : ℝ) * 2 ^ n) ^ k * ∏ i, |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hpos : (0 : ℝ) < (D : ℝ) * 2 ^ n := by positivity
  have key : ∀ i : Fin k, |((tgtNum D (A i) n r : ℤ) : ℝ)|
      = ((D : ℝ) * 2 ^ n) * |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| := by
    intro i
    rw [← abs_of_pos hpos, ← abs_mul]
    congr 1
    rw [tgtNum]
    push_cast
    field_simp
  calc ((|cycleProd D A n r| : ℤ) : ℝ) = ∏ i, |((tgtNum D (A i) n r : ℤ) : ℝ)| := by
        rw [Int.cast_abs, cycleProd, Int.cast_prod, Finset.abs_prod]
    _ = ∏ i, ((D : ℝ) * 2 ^ n) * |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| :=
        Finset.prod_congr rfl fun i _ => key i
    _ = ((D : ℝ) * 2 ^ n) ^ k * ∏ i, |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Both the orbit point and the targets live in `[0,1)`, so every factor of the identity's
right-hand side is at most `1`: the hypothesis the next theorem needs, discharged from the ranges
`0 ≤ r < 2ⁿ` and `0 ≤ A < D`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem abs_sub_le_one {D : ℕ} (hD : 0 < D) {n : ℕ} {r A : ℤ} (hr0 : 0 ≤ r) (hr : r < 2 ^ n)
    (hA0 : 0 ≤ A) (hA : A < (D : ℤ)) : |(r : ℝ) / 2 ^ n - (A : ℝ) / (D : ℝ)| ≤ 1 := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hr0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have hrR : (r : ℝ) < 2 ^ n := by exact_mod_cast hr
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA0
  have hAR : (A : ℝ) < (D : ℝ) := by exact_mod_cast hA
  have h1 : (r : ℝ) / 2 ^ n < 1 := (div_lt_one h2).mpr hrR
  have h2' : (0 : ℝ) ≤ (r : ℝ) / 2 ^ n := div_nonneg hr0R h2.le
  have h3 : (A : ℝ) / (D : ℝ) < 1 := (div_lt_one hDR).mpr hAR
  have h4 : (0 : ℝ) ≤ (A : ℝ) / (D : ℝ) := div_nonneg hA0R hDR.le
  rw [abs_le]
  constructor <;> linarith

/-- **The route's conclusion.**  A lower bound for the product is a lower bound for every one of
the `k` distances, because the other factors are at most `1`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem le_abs_sub_of_le_abs_cycleProd {D : ℕ} (hD : 0 < D) {k : ℕ} {A : Fin k → ℤ} {n : ℕ}
    {r : ℤ} (hfar : ∀ i, |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| ≤ 1) (j : Fin k) :
    ((|cycleProd D A n r| : ℤ) : ℝ) / (((D : ℝ) * 2 ^ n) ^ k)
      ≤ |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| := by
  have hpos : (0 : ℝ) < ((D : ℝ) * 2 ^ n) ^ k := by
    have : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    positivity
  rw [abs_cycleProd_eq hD, mul_comm, mul_div_assoc, div_self (ne_of_gt hpos), mul_one,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j, |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| ≤ 1 :=
    Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => hfar i)
  have hnn : (0 : ℝ) ≤ |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| := abs_nonneg _
  nlinarith [hrest, hnn]

/-- **…and the converse, up to `(2D)^{k-1}`.**  If the cycle's numerators are distinct and the
orbit is within `1/(2D)` of one of them, the product is *also* bounded above by that one distance
times `(D2ⁿ)^k`, and below by `(2D)^{-(k-1)}` times the same.  So "prove `|M_n| ≥ c·λⁿ`" and
"prove `‖xₙ − ρⱼ‖ ≥ c'·θⁿ`" are the same demand in different units: the route is a restatement,
not a reduction. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem abs_cycleProd_le_of_near {D : ℕ} (hD : 0 < D) {k : ℕ} {A : Fin k → ℤ} {n : ℕ} {r : ℤ}
    {j : Fin k} (hdist : ∀ i, i ≠ j → A i ≠ A j)
    (hnear : |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| ≤ 1 / (2 * (D : ℝ))) :
    (1 / (2 * (D : ℝ))) ^ (k - 1) * (((D : ℝ) * 2 ^ n) ^ k)
        * |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)|
      ≤ ((|cycleProd D A n r| : ℤ) : ℝ) := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  -- every other target is at least `1/(2D)` away
  have hfar : ∀ i ∈ Finset.univ.erase j,
      1 / (2 * (D : ℝ)) ≤ |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| := by
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hne : A i ≠ A j := hdist i hij
    have hsep : 1 / (D : ℝ) ≤ |(A i : ℝ) / (D : ℝ) - (A j : ℝ) / (D : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |A i - A j| := Int.one_le_abs (sub_ne_zero.mpr hne)
      have h2 : (1 : ℝ) ≤ |(A i : ℝ) - (A j : ℝ)| := by exact_mod_cast h1
      rw [div_sub_div_same, abs_div, abs_of_pos hDR]
      gcongr
    have htri : |(A i : ℝ) / (D : ℝ) - (A j : ℝ) / (D : ℝ)|
        ≤ |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| + |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| := by
      calc |(A i : ℝ) / (D : ℝ) - (A j : ℝ) / (D : ℝ)|
          ≤ |(A i : ℝ) / (D : ℝ) - (r : ℝ) / 2 ^ n| + |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| :=
            abs_sub_le _ _ _
        _ = |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| + |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| := by
            rw [abs_sub_comm ((A i : ℝ) / (D : ℝ))]
        _ = |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| + |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| := by
            ring
    have hhalf : 1 / (D : ℝ) = 1 / (2 * (D : ℝ)) + 1 / (2 * (D : ℝ)) := by field_simp; ring
    linarith [hsep, htri, hnear]
  have hcard : (Finset.univ.erase j).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hprod : (1 / (2 * (D : ℝ))) ^ (k - 1)
      ≤ ∏ i ∈ Finset.univ.erase j, |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)| := by
    calc (1 / (2 * (D : ℝ))) ^ (k - 1)
        = ∏ _i ∈ Finset.univ.erase j, (1 / (2 * (D : ℝ))) := by
          rw [Finset.prod_const, hcard]
      _ ≤ _ := Finset.prod_le_prod (fun i _ => by positivity) hfar
  have hpos : (0 : ℝ) < ((D : ℝ) * 2 ^ n) ^ k := by positivity
  rw [abs_cycleProd_eq hD, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hnn : (0 : ℝ) ≤ |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| := abs_nonneg _
  calc (1 / (2 * (D : ℝ))) ^ (k - 1) * (((D : ℝ) * 2 ^ n) ^ k)
        * |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)|
      = ((D : ℝ) * 2 ^ n) ^ k
          * (|(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| * (1 / (2 * (D : ℝ))) ^ (k - 1)) := by ring
    _ ≤ ((D : ℝ) * 2 ^ n) ^ k * (|(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)|
          * ∏ i ∈ Finset.univ.erase j, |(r : ℝ) / 2 ^ n - (A i : ℝ) / (D : ℝ)|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hnn) hpos.le

/-- **Restatement, not reduction — the two-sided statement.**  Under the hypotheses of the two
previous lemmas the product and the near distance are within the explicit factor `(2D)^{k-1}` of
each other:
`|M_n|/(D2ⁿ)^k ≤ ‖xₙ − ρⱼ‖ ≤ (2D)^{k-1}·|M_n|/(D2ⁿ)^k`.
Proving the product bound S9(ii) wants *is* proving the T-shift bound, in different units. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem abs_sub_le_of_abs_cycleProd {D : ℕ} (hD : 0 < D) {k : ℕ} {A : Fin k → ℤ} {n : ℕ} {r : ℤ}
    {j : Fin k} (hdist : ∀ i, i ≠ j → A i ≠ A j)
    (hnear : |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| ≤ 1 / (2 * (D : ℝ))) :
    |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)|
      ≤ (2 * (D : ℝ)) ^ (k - 1) * (((|cycleProd D A n r| : ℤ) : ℝ) / (((D : ℝ) * 2 ^ n) ^ k)) := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hpos : (0 : ℝ) < ((D : ℝ) * 2 ^ n) ^ k := by positivity
  have hcpos : (0 : ℝ) < (2 * (D : ℝ)) ^ (k - 1) := by positivity
  have h := abs_cycleProd_le_of_near hD hdist hnear
  have hinv : (1 / (2 * (D : ℝ))) ^ (k - 1) = 1 / (2 * (D : ℝ)) ^ (k - 1) := by
    rw [div_pow, one_pow]
  rw [hinv] at h
  rw [mul_div_assoc']
  rw [le_div_iff₀ hpos]
  have hc0 : (2 * (D : ℝ)) ^ (k - 1) ≠ 0 := ne_of_gt hcpos
  have h2 : |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| * (((D : ℝ) * 2 ^ n) ^ k)
      ≤ (2 * (D : ℝ)) ^ (k - 1) * ((|cycleProd D A n r| : ℤ) : ℝ) := by
    calc |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)| * (((D : ℝ) * 2 ^ n) ^ k)
        = (2 * (D : ℝ)) ^ (k - 1) * (1 / (2 * (D : ℝ)) ^ (k - 1) * (((D : ℝ) * 2 ^ n) ^ k)
            * |(r : ℝ) / 2 ^ n - (A j : ℝ) / (D : ℝ)|) := by
          field_simp
      _ ≤ (2 * (D : ℝ)) ^ (k - 1) * ((|cycleProd D A n r| : ℤ) : ℝ) :=
          mul_le_mul_of_nonneg_left h hcpos.le
  linarith [h2]

/-! ## 3. The ceiling: the route cannot exceed the free floor

The only property of `rₙ` the product route uses is that it is odd.  Section 1's witness makes one
factor as small as `D`, and the remaining factors are then at most `2D·2ⁿ` each, so the guaranteed
size of `M_n` is at most a constant times `2^{n(k-1)}` — which is exactly `θ = 1/2`, the free
floor, and never more. -/

/-- Each factor at the witness: the near one is at most `D`, the far ones at most `2D·2ⁿ`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem abs_tgtNum_le_of_abs_tgtNum_le {D : ℕ} {A A' : ℤ} {n : ℕ} {r : ℤ}
    (hA : 0 ≤ A ∧ A < (D : ℤ)) (hA' : 0 ≤ A' ∧ A' < (D : ℤ)) (hn : 1 ≤ n)
    (h : |tgtNum D A n r| ≤ (D : ℤ)) : |tgtNum D A' n r| ≤ 2 * (D : ℤ) * 2 ^ n := by
  have h2 : (2 : ℤ) ≤ 2 ^ n := by
    calc (2 : ℤ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hsplit : tgtNum D A' n r = tgtNum D A n r + (A - A') * 2 ^ n := by
    rw [tgtNum, tgtNum]; ring
  have hAA : |A - A'| ≤ (D : ℤ) := by
    rcases hA with ⟨h1, h2'⟩
    rcases hA' with ⟨h3, h4⟩
    rw [abs_le]
    omega
  have hpow : (0 : ℤ) < 2 ^ n := by positivity
  calc |tgtNum D A' n r| ≤ |tgtNum D A n r| + |(A - A') * 2 ^ n| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ (D : ℤ) + (D : ℤ) * 2 ^ n := by
        rw [abs_mul, abs_of_pos hpow]
        have := mul_le_mul_of_nonneg_right hAA (le_of_lt hpow)
        linarith
    _ ≤ 2 * (D : ℤ) * 2 ^ n := by nlinarith [Int.natCast_nonneg D]

/-- **The witness.**  There is always an odd `r` at which the cycle product is at most
`D·(2D)^{k-1}·2^{n(k-1)}` — one full factor of `2ⁿ` below its typical size `2^{nk}`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem exists_odd_abs_cycleProd_le {D : ℕ} (hD : 0 < D) {k : ℕ} (hk : 0 < k) {A : Fin k → ℤ}
    (hA : ∀ i, 0 ≤ A i ∧ A i < (D : ℤ)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r : ℤ, Odd r ∧
      |cycleProd D A n r| ≤ (D : ℤ) * (2 * (D : ℤ)) ^ (k - 1) * (2 ^ n) ^ (k - 1) := by
  set j : Fin k := ⟨0, hk⟩ with hj
  obtain ⟨r, hr, hle⟩ := exists_odd_tgtNum_abs_le hD (A j) n
  refine ⟨r, hr, ?_⟩
  have hcard : (Finset.univ.erase j).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hstep : ∀ i ∈ Finset.univ.erase j, |tgtNum D (A i) n r| ≤ 2 * (D : ℤ) * 2 ^ n :=
    fun i _ => abs_tgtNum_le_of_abs_tgtNum_le (hA j) (hA i) hn hle
  have hrest : ∏ i ∈ Finset.univ.erase j, |tgtNum D (A i) n r|
      ≤ (2 * (D : ℤ) * 2 ^ n) ^ (k - 1) := by
    calc ∏ i ∈ Finset.univ.erase j, |tgtNum D (A i) n r|
        ≤ ∏ _i ∈ Finset.univ.erase j, (2 * (D : ℤ) * 2 ^ n) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) hstep
      _ = (2 * (D : ℤ) * 2 ^ n) ^ (k - 1) := by rw [Finset.prod_const, hcard]
  have hnn : (0 : ℤ) ≤ ∏ i ∈ Finset.univ.erase j, |tgtNum D (A i) n r| :=
    Finset.prod_nonneg fun i _ => abs_nonneg _
  have hexp : (D : ℤ) * (2 * (D : ℤ)) ^ (k - 1) * (2 ^ n) ^ (k - 1)
      = (D : ℤ) * (2 * (D : ℤ) * 2 ^ n) ^ (k - 1) := by
    rw [mul_assoc, ← mul_pow]
  rw [cycleProd, Finset.abs_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), hexp]
  have hDz : (0 : ℤ) ≤ (D : ℤ) := Int.natCast_nonneg D
  have hbig : (0 : ℤ) ≤ (2 * (D : ℤ) * 2 ^ n) ^ (k - 1) := by positivity
  nlinarith [abs_nonneg (tgtNum D (A j) n r)]

/-- **The rate ceiling.**  In the currency the route delivers — the product divided by `(D2ⁿ)^k` —
the witness of the previous theorem returns at most `2^{k-1}/2ⁿ`.  The free floor is `1/(D2ⁿ)`, so
the product route buys, at best, the free rate `θ = 1/2` times a constant. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem exists_odd_cycleProd_rate_le {D : ℕ} (hD : 0 < D) {k : ℕ} (hk : 0 < k) {A : Fin k → ℤ}
    (hA : ∀ i, 0 ≤ A i ∧ A i < (D : ℤ)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r : ℤ, Odd r ∧
      ((|cycleProd D A n r| : ℤ) : ℝ) / (((D : ℝ) * 2 ^ n) ^ k) ≤ 2 ^ (k - 1) / 2 ^ n := by
  obtain ⟨r, hr, hle⟩ := exists_odd_abs_cycleProd_le hD hk hA hn
  refine ⟨r, hr, ?_⟩
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcastle : ((|cycleProd D A n r| : ℤ) : ℝ)
      ≤ (D : ℝ) * (2 * (D : ℝ)) ^ (k - 1) * ((2 : ℝ) ^ n) ^ (k - 1) := by
    exact_mod_cast hle
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hid : (D : ℝ) * (2 * (D : ℝ)) ^ m * ((2 : ℝ) ^ n) ^ m / (((D : ℝ) * 2 ^ n) ^ (m + 1))
      = 2 ^ m / 2 ^ n := by
    rw [mul_pow, mul_pow]
    field_simp
    ring
  calc ((|cycleProd D A n r| : ℤ) : ℝ) / (((D : ℝ) * 2 ^ n) ^ (m + 1))
      ≤ ((D : ℝ) * (2 * (D : ℝ)) ^ m * ((2 : ℝ) ^ n) ^ m) / (((D : ℝ) * 2 ^ n) ^ (m + 1)) :=
        (div_le_div_iff_of_pos_right (by positivity)).mpr (by simpa using hcastle)
    _ = 2 ^ m / 2 ^ n := by simpa using hid

/-- **The verdict on prong (ii).**  If a bound `c·θⁿ ≤ |M_n|/(D2ⁿ)^k` holds for *every* odd
numerator — which is all the route's hypotheses ("`M_n` is an odd integer", plus any forced
divisibility, which by §4 is a constant) can see — then `θ ≤ 1/2`.  **The cycle product cannot
prove any rate above the free floor**, at any period, at any cycle, for any constant `c`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem route_rate_le_half {D : ℕ} (hD : 0 < D) {k : ℕ} (hk : 0 < k) {A : Fin k → ℤ}
    (hA : ∀ i, 0 ≤ A i ∧ A i < (D : ℤ)) {θ c : ℝ} (hc : 0 < c) {n₀ : ℕ}
    (hbound : ∀ n, n₀ ≤ n → 1 ≤ n → ∀ r : ℤ, Odd r →
      c * θ ^ n ≤ ((|cycleProd D A n r| : ℤ) : ℝ) / (((D : ℝ) * 2 ^ n) ^ k)) :
    θ ≤ 1 / 2 := by
  by_contra hcon
  push Not at hcon
  have hθpos : (0 : ℝ) < θ := lt_trans (by norm_num) hcon
  have h2θ : (1 : ℝ) < 2 * θ := by linarith
  -- at every admissible date, `c·(2θ)ⁿ ≤ 2^{k-1}`
  have hstep : ∀ n, n₀ ≤ n → 1 ≤ n → c * (2 * θ) ^ n ≤ 2 ^ (k - 1) := by
    intro n hn₀ hn
    obtain ⟨r, hr, hle⟩ := exists_odd_cycleProd_rate_le hD hk hA hn
    have h1 := hbound n hn₀ hn r hr
    have h2 : c * θ ^ n ≤ 2 ^ (k - 1) / 2 ^ n := le_trans h1 hle
    have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [le_div_iff₀ h2n] at h2
    calc c * (2 * θ) ^ n = c * θ ^ n * 2 ^ n := by rw [mul_pow]; ring
      _ ≤ 2 ^ (k - 1) := h2
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((2 : ℝ) ^ (k - 1) / c) h2θ
  set n := max N (max n₀ 1) with hn
  have hmono : (2 * θ) ^ N ≤ (2 * θ) ^ n :=
    pow_le_pow_right₀ (le_of_lt h2θ) (le_max_left _ _)
  have hfin := hstep n (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _))
  rw [div_lt_iff₀ hc] at hN
  nlinarith [hN, hmono, hfin]

/-- The trivial input is not merely weak, it is **below the free floor**: `|M_n| ≥ 1` returns
`(D2ⁿ)^{-k}`, and for `k ≥ 2` that is smaller than `1/(D2ⁿ)` — the near factor is capped by the
far ones, exactly as the row says. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem trivial_input_lt_free {D : ℕ} (hD : 0 < D) {k : ℕ} (hk : 2 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    1 / (((D : ℝ) * 2 ^ n) ^ k) < 1 / ((D : ℝ) * 2 ^ n) := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hbase : (1 : ℝ) < (D : ℝ) * 2 ^ n := by nlinarith
  have hlt : (D : ℝ) * 2 ^ n < ((D : ℝ) * 2 ^ n) ^ k := by
    calc (D : ℝ) * 2 ^ n = ((D : ℝ) * 2 ^ n) ^ 1 := (pow_one _).symm
      _ < ((D : ℝ) * 2 ^ n) ^ k := by
          exact pow_lt_pow_right₀ hbase (by omega)
  exact one_div_lt_one_div_of_lt (by linarith) hlt

/-- The same verdict against the threshold: a rate the product route can prove never clears `2/3`,
so no instance of `TShift.TShiftProblemAt` comes out of prong (ii). -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem route_not_two_thirds {D : ℕ} (hD : 0 < D) {k : ℕ} (hk : 0 < k) {A : Fin k → ℤ}
    (hA : ∀ i, 0 ≤ A i ∧ A i < (D : ℤ)) {θ c : ℝ} (hc : 0 < c) {n₀ : ℕ}
    (hbound : ∀ n, n₀ ≤ n → 1 ≤ n → ∀ r : ℤ, Odd r →
      c * θ ^ n ≤ ((|cycleProd D A n r| : ℤ) : ℝ) / (((D : ℝ) * 2 ^ n) ^ k)) :
    ¬ (2 / 3 < θ) := by
  have h := route_rate_le_half hD hk hA hc hbound
  intro hlt
  linarith

/-- **The verdict at the flagship**, at the corpus's own targets: the cycle denominators
`D_p = 3^p − 2^p` of `Z32.cycleDenom`.  Nothing about the shape `3^p − 2^p` changes the ceiling —
oddness and positivity are all that enter. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem route_rate_le_half_cycleDenom {p : ℕ} (hp : 1 ≤ p) {k : ℕ} (hk : 0 < k)
    {A : Fin k → ℤ} (hA : ∀ i, 0 ≤ A i ∧ A i < (Z32.cycleDenom p : ℤ)) {θ c : ℝ} (hc : 0 < c)
    {n₀ : ℕ}
    (hbound : ∀ n, n₀ ≤ n → 1 ≤ n → ∀ r : ℤ, Odd r →
      c * θ ^ n ≤ ((|cycleProd (Z32.cycleDenom p) A n r| : ℤ) : ℝ)
        / ((((Z32.cycleDenom p : ℕ) : ℝ) * 2 ^ n) ^ k)) :
    θ ≤ 1 / 2 :=
  route_rate_le_half (Z32.cycleDenom_pos hp) hk hA hc hbound

/-- **Orientation check.**  The `2`-cycle `{1/5, 4/5}` at `D₂ = 5`, date `n = 3`, numerator
`r = 5`: `M = (5·5 − 1·8)(5·5 − 4·8) = 17·(−7) = −119`, odd as promised, `|M| = 119` — and
`119 = 7·17` carries none of the cycle's own primes, which is the shape §4 predicts. -/
@[category test, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem cycleProd_sanity : cycleProd 5 ![(1 : ℤ), 4] 3 5 = -119 := by
  simp [cycleProd, tgtNum, Fin.prod_univ_two]

/-! ## 4. What divisibility is forced

The row's condition for the route to pay: "primes dividing `M_n` must divide explicit resultants of
the cycle polynomial".  As stated that is false — the primes dividing `M_n` are the primes for
which the free numerator lands in one of `k` residue classes, and nothing pins them.  What the
resultant governs is *coincidences* between two factors.  The forced divisibility that does exist
is bounded by the cycle's own data and does not grow with `n`. -/

/-- The correct form of the resultant claim: a prime dividing two factors at once divides the
difference of the two numerators, times `2ⁿ`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem dvd_sub_of_dvd_tgtNum_two {D : ℕ} {A A' : ℤ} {n : ℕ} {r q : ℤ}
    (h : q ∣ tgtNum D A n r) (h' : q ∣ tgtNum D A' n r) : q ∣ (A - A') * 2 ^ n := by
  have : (A - A') * 2 ^ n = tgtNum D A' n r - tgtNum D A n r := by rw [tgtNum, tgtNum]; ring
  rw [this]
  exact dvd_sub h' h

/-- A common divisor of `D` and of the whole cycle divides the product `k` times — and that is a
constant, the only *forced* growth available. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem pow_dvd_cycleProd {D : ℕ} {k : ℕ} {A : Fin k → ℤ} {n : ℕ} {r g : ℤ} (hgD : g ∣ (D : ℤ))
    (hgA : ∀ i, g ∣ A i) : g ^ k ∣ cycleProd D A n r := by
  have : ∀ i : Fin k, g ∣ tgtNum D (A i) n r := by
    intro i
    exact dvd_sub (Dvd.dvd.mul_right hgD r) (Dvd.dvd.mul_right (hgA i) _)
  calc g ^ k = ∏ _i : Fin k, g := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ∣ cycleProd D A n r := Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => this i)

/-- **Forced non-divisibility.**  A prime dividing `D` but no member of the cycle never divides the
product — at `D = 5` this is why `5 ∤ M_n` at every date, measured in harness block `s9` [C]. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem not_dvd_cycleProd {D : ℕ} {k : ℕ} {A : Fin k → ℤ} {n : ℕ} {r : ℤ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqD : (q : ℤ) ∣ (D : ℤ)) (hqA : ∀ i, ¬ (q : ℤ) ∣ A i) :
    ¬ (q : ℤ) ∣ cycleProd D A n r := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rw [cycleProd, hqZ.dvd_finsetProd_iff]
  rintro ⟨i, -, hi⟩
  have hfac : (q : ℤ) ∣ A i * 2 ^ n := by
    have : A i * 2 ^ n = (D : ℤ) * r - tgtNum D (A i) n r := by rw [tgtNum]; ring
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_right hqD r) hi
  rcases hqZ.dvd_mul.mp hfac with h | h
  · exact hqA i h
  · have h2 : (q : ℤ) ∣ 2 := hqZ.dvd_of_dvd_pow h
    have : q ∣ 2 := by exact_mod_cast h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this)

/-- **The fixed-divisor theorem.**  An odd prime `q ∤ D` that divides the cycle product for
*every* odd numerator satisfies `q ≤ k`.  So the "forced divisibility" the row needs is confined
to primes at most the cycle length (plus the divisors of `D` handled above): a constant, against
the `2^{n(k-1)}` the route would have to supply. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem forced_prime_le_card {D : ℕ} {k : ℕ} {A : Fin k → ℤ} {n : ℕ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqD : ¬ (q ∣ D))
    (hforced : ∀ r : ℤ, Odd r → (q : ℤ) ∣ cycleProd D A n r) : q ≤ k := by
  have : Fact q.Prime := ⟨hq⟩
  by_contra hcon
  push Not at hcon
  -- the `k` residues that a bad numerator has to hit
  set f : Fin k → ZMod q := fun i => ((A i : ZMod q) * (2 : ZMod q) ^ n) * ((D : ZMod q))⁻¹ with hf
  have hDne : (D : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hqD
  -- a residue class no factor can vanish on
  have hlt : (Finset.univ.image f).card < Fintype.card (ZMod q) := by
    have h1 : (Finset.univ.image f).card ≤ k :=
      le_trans Finset.card_image_le (by simp)
    have h2 : Fintype.card (ZMod q) = q := ZMod.card q
    omega
  obtain ⟨c, hc⟩ : ∃ c : ZMod q, c ∉ Finset.univ.image f := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (ZMod q)) ⊆ Finset.univ.image f := fun c _ => h c
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    omega
  -- an odd integer in that class
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  set r₀ : ℤ := (c.val : ℤ) with hr₀
  set r : ℤ := if Odd r₀ then r₀ else r₀ + (q : ℤ) with hrdef
  have hrodd : Odd r := by
    rw [hrdef]
    split_ifs with h
    · exact h
    · rcases Int.even_or_odd r₀ with he | ho
      · obtain ⟨a, ha⟩ := he
        obtain ⟨b, hb⟩ := hqodd
        exact ⟨a + b, by push_cast [ha, hb]; ring⟩
      · exact absurd ho h
  have hrc : ((r : ℤ) : ZMod q) = c := by
    have hbase : ((r₀ : ℤ) : ZMod q) = c := by
      rw [hr₀]
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id]
    rw [hrdef]
    split_ifs
    · exact hbase
    · push_cast
      rw [hbase]
      simp
  -- but the product is divisible, so some factor vanishes at `c`
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  obtain ⟨i, -, hi⟩ := (hqZ.dvd_finsetProd_iff _).mp (hforced r hrodd)
  have hzero : ((tgtNum D (A i) n r : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hi
  rw [tgtNum] at hzero
  push_cast at hzero
  rw [hrc] at hzero
  have hcf : c = f i := by
    rw [hf]
    field_simp
    linear_combination hzero
  exact hc (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hcf.symm⟩)

/-! ## 5. Prong (i): the elimination ledger is blind to the congruence

`TShift/MultiplierTransfer.lean` charges the multiplier once, in `|c|·Λ`, and pays the content back
once, in `P·X`.  Imposing `D ∣ aᵢ, bᵢ` scales `P`, `Λ` and `B` together — and the bound
`(P·X − |c|·Λ)/B` is homogeneous of degree zero under that scaling. -/

/-- Scaling a pair of eliminating forms by `t ≠ 0` scales its content, its size and its height by
`|t|`.  This is exactly the operation "impose `t ∣ aᵢ, bᵢ`": the `t`-divisible pairs are the
scalings of the arbitrary ones. -/
@[category API, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
def TwoForms.scale {X Y : ℤ} {P Λ B : ℝ} (F : TwoForms X Y P Λ B) {t : ℤ} (ht : t ≠ 0) :
    TwoForms X Y (|(t : ℝ)| * P) (|(t : ℝ)| * Λ) (|(t : ℝ)| * B) where
  a₁ := t * F.a₁
  b₁ := t * F.b₁
  Γ₁ := t * F.Γ₁
  a₂ := t * F.a₂
  b₂ := t * F.b₂
  Γ₂ := t * F.Γ₂
  det := fun h => F.det (mul_left_cancel₀ (mul_ne_zero ht ht) (by linear_combination h))
  dvd_a₁ := mul_dvd_mul_left t F.dvd_a₁
  dvd_b₁ := mul_dvd_mul_left t F.dvd_b₁
  dvd_a₂ := mul_dvd_mul_left t F.dvd_a₂
  dvd_b₂ := mul_dvd_mul_left t F.dvd_b₂
  le_content₁ := by
    push_cast
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left F.le_content₁ (abs_nonneg _)
  le_content₂ := by
    push_cast
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left F.le_content₂ (abs_nonneg _)
  size₁ := by
    have hrw : ((t * F.a₁ : ℤ) : ℝ) * (X : ℝ) + ((t * F.b₁ : ℤ) : ℝ) * (Y : ℝ)
        = (t : ℝ) * ((F.a₁ : ℝ) * (X : ℝ) + (F.b₁ : ℝ) * (Y : ℝ)) := by push_cast; ring
    rw [hrw, abs_mul]
    exact mul_le_mul_of_nonneg_left F.size₁ (abs_nonneg _)
  size₂ := by
    have hrw : ((t * F.a₂ : ℤ) : ℝ) * (X : ℝ) + ((t * F.b₂ : ℤ) : ℝ) * (Y : ℝ)
        = (t : ℝ) * ((F.a₂ : ℝ) * (X : ℝ) + (F.b₂ : ℝ) * (Y : ℝ)) := by push_cast; ring
    rw [hrw, abs_mul]
    exact mul_le_mul_of_nonneg_left F.size₂ (abs_nonneg _)
  coeff₁ := by
    push_cast
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left F.coeff₁ (abs_nonneg _)
  coeff₂ := by
    push_cast
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left F.coeff₂ (abs_nonneg _)

/-- **The ledger is scale-invariant.**  `(t·P·X − |c|·t·Λ)/(t·B) = (P·X − |c|·Λ)/B`: the content
refund `P ↦ tP` and the size cost `Λ ↦ tΛ` cancel to the last digit.  Prong (i)'s "turn the
`O(log D)` loss into a gain" asks for a gain from an operation the bound cannot see. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem transfer_bound_scale {P Λ B X cc t : ℝ} (ht : t ≠ 0) (hB : B ≠ 0) :
    (t * P * X - cc * (t * Λ)) / (t * B) = (P * X - cc * Λ) / B := by
  field_simp

/-- The content slot is capped by the size slot: a nonzero form of size `Λ` whose coefficients are
divisible by `Γ` has `|Γ| ≤ Λ`.  So `P ≤ Λ` always, and the "gain" `P/B` of the content-refined
transfer is at most `Λ/B` — the classical currency, with no room for a `D`-shaped bonus. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem content_le_size {X Y a b Γ : ℤ} {Λ : ℝ} (hΓa : Γ ∣ a) (hΓb : Γ ∣ b)
    (hne : a * X + b * Y ≠ 0) (hΛ : |((a * X + b * Y : ℤ) : ℝ)| ≤ Λ) : |(Γ : ℝ)| ≤ Λ := by
  have hdvd : Γ ∣ a * X + b * Y := dvd_add (hΓa.mul_right X) (hΓb.mul_right Y)
  have hZ : |Γ| ≤ |a * X + b * Y| :=
    Int.le_of_dvd (abs_pos.mpr hne) ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr hdvd))
  have : |((Γ : ℤ) : ℝ)| ≤ |((a * X + b * Y : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs]
    exact_mod_cast hZ
  linarith

/-- **Prong (i) at the flagship, worked.**  The corpus's own orientation instance
(`TShift.transfer_prop_one_sanity`: the forms `−5·2⁴ + 3⁴ = 1` and `−81·2⁴ + 16·3⁴ = 0`) run at
multiplier `c = 5` through the `5`-divisible scaling — content `P = 5`, size `Λ = 5`, height
`B = 80` — returns `11/16`, which is exactly what the *unscaled* pair returns at the same
multiplier.  The congruence is free and worth nothing, in one worked number. -/
@[category test, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem scale_sanity_five (m : ℤ) : (11 : ℝ) / 16 ≤ |5 * 81 - (m : ℝ) * 16| := by
  have F : TwoForms (2 ^ 4) (3 ^ 4) 1 1 16 :=
    { a₁ := -5, b₁ := 1, Γ₁ := 1, a₂ := -81, b₂ := 16, Γ₂ := 1
      det := by norm_num
      dvd_a₁ := one_dvd _, dvd_b₁ := one_dvd _, dvd_a₂ := one_dvd _, dvd_b₂ := one_dvd _
      le_content₁ := by norm_num
      le_content₂ := by norm_num
      size₁ := by norm_num
      size₂ := by norm_num
      coeff₁ := by norm_num
      coeff₂ := by norm_num }
  have hscaled := (F.scale (t := 5) (by norm_num)).transfer_div (c := 5) (by norm_num)
    (by norm_num) (by norm_num) m
  norm_num at hscaled
  convert hscaled using 2
  norm_num

/-- **The pincer.**  Any device that bounds `‖D·(3/2)ⁿ‖` — i.e. any device uniform in the free
integer, which is every instance of the transfer — yields the same rate at `ρ = 0`.  This is report
N1: prong (i) cannot deliver the rung S9 is listed under, "T1 without T4", because its conclusion
is the multiplier form.  Only a genuinely single-target argument could, and by §1 the extra
information a single target carries — the residue class mod `D` — is worth at most the factor
`D`. -/
@[category research solved, AMS 11 37, ref "TshiftS9", group "tshift_s9"]
theorem isRepelled_zero_of_isRepelledMul {θ : ℝ} {D : ℕ} (hD : 0 < D) (h : IsRepelledMul θ D) :
    IsRepelled θ 0 := by
  have h0 := h.isRepelled hD 0
  simpa using h0

end TShift
