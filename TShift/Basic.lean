/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.BalanceVectors
import ForMathlib.Data.Real.NearestInt
import ForMathlib.Data.Real.NearestIntNatDiv
import ForMathlib.Data.Rat.NearestInt
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The T-shift problem

Exponential repulsion of `(3/2)ⁿ` from the rational **cycle targets** `A/(3^p - 2^p)`.

This file states the problem (`TShift.TShiftProblem`) and proves everything around it that is
elementary — the free bound, the reduction to an integer multiplier, the shadowing lemma, the
sojourn cap and its threshold constant `2/3`, the visit-count recursion, and the identification of
the carry word of the `ξ = 1` orbit with the diagonal binary digit of `3ⁿ`.  Nothing *here* proves
any instance of the problem.

## Caveat on `TShiftProblem` (2026‑08‑13)

`TShiftProblem` quantifies `θ`, `c` and `n₀` existentially, and **that existential is a theorem**:
`TShift/MahlerCountMul.lean` proves `TShift.tShiftProblem_holds` at every period and numerator,
from finiteness of the multiplier failure set (Mahler 1957, along the quantitative Ridout route).
So is the sharper `∀ n ≥ 1` reading with no burn-in at all (`TShift.tShift_forall_ge_one`).
Effectivity is a property of the *witnesses*, not of the proposition, so no phrasing inside `∃`
states the open problem.

What is open is `TShift.TShiftProblemAt p A θ c n₀` — the same bound with the numerals **exhibited**
and `θ > 2/3`.  The corpus's best effective rate is `0.57434` at every period
(`TShift/HabsiegerTransfer.lean`), i.e. `TShift.RepelledAt` with all numerals and `θ < 2/3`.  The
definitions below are kept unchanged: they are consumed throughout `TShift/`, and the theorems
about them are true; only the word "open" was wrong about them.

## The statement

For `p ≥ 1` put `D_p = 3^p - 2^p` (`= 1, 5, 19, 65, 211, …`, always odd).  The rationals
`A/D_p` are exactly the `p`-periodic points of the two-branch carry relation
`2y_{n+1} = 3yₙ - sₙ` (`TShift.numerator_periodic` is the arithmetic half of that statement).
The problem is to prove, for one such target with `p ≥ 2`,

  `‖(3/2)ⁿ - A/D_p‖ ≥ c·θⁿ`  for all large `n`, with **`θ > 2/3`**,

where `‖·‖` is the distance to the nearest integer (`distToNearestInt`, from
`ForMathlib/Data/Real/NearestInt.lean`).

* `θ = 1/2` is free (`TShift.isRepelled_half`): the 2-adic floor, since `xₙ = rₙ/2ⁿ` with
  `rₙ` odd.
* At `p = 1` the target is `ρ = 0` and this is the classical problem on `‖(3/2)ⁿ‖`, where the
  record is `θ = 0.5803` [Zud07] — still short of `2/3`.
* At `p ≥ 2` the free `θ = 1/2` was, until this corpus, all that was recorded in either
  direction.  `TShift/HabsiegerTransfer.lean` now proves `θ = 0.57434` at **every** period
  (`TShift.isRepelled_cycle`), and at a single date `k` simultaneously for all `p ≤ k/1341`
  (`TShift.le_dist_cycle_uniform`), by transporting [Hab03]'s `D = 1` rate through the multiplier —
  still short of `2/3`, so the *effective* problem is untouched.

## Why `2/3`

`TShift.abs_sub_fixed_le` (shadowing): an orbit following the period-`p` affine map for `j` periods
is within `(2/3)^{jp}` of its fixed point.  Against a repulsion bound this caps the length `L` of
such a sojourn linearly in the date `n` (`TShift.sojourn_cap`, `TShift.sojourn_cap_kappa`):

  `L ≤ κ(θ)·n + C`,  `κ(θ) = log(1/θ)/log(3/2)`,

and `TShift.kappa_lt_one_iff` says `κ(θ) < 1 ⟺ θ > 2/3`.  Below that threshold the escape dates
may grow by a factor `> 2`; above it they do not (`TShift.lt_two_mul_of_lt_two`), so every dyadic
block of dates carries a visit.  The free `θ = 1/2` gives `κ = log 2/log(3/2) = 1.70951…`.

## What is *not* claimed

The sojourn cap needs, besides the repulsion bound, that the carry word actually is periodic on the
block; that is a separate combinatorial input and is not proved here (`sojourn_cap` takes the
shadowing conclusion as a hypothesis).  Nothing here bears on density of `{(3/2)ⁿ}`: repulsion says
the orbit does not *stick* to a target, not that it *reaches* one.

## Reuse

Nothing about `‖·‖` is rebuilt here.  `distToNearestInt x = |x - round x|` and its API
(`distToNearestInt_nonneg`, `distToNearestInt_le_abs_sub_intCast`, `distToNearestInt_add_intCast`,
`distToNearestInt_ratCast`) are `ForMathlib/Data/Real/NearestInt.lean`; the free bound below is the
ratio-of-naturals evaluation `distToNearestInt_natCast_div` of
`ForMathlib/Data/Real/NearestIntNatDiv.lean` applied to `D·3ⁿ/2ⁿ`; and the computable `ℚ`-valued
mirror `Rat.distToNearestInt` (with the same floor in certificate form,
`Rat.one_le_two_pow_mul_distToNearestInt`) is `ForMathlib/Data/Rat/NearestInt.lean`, reachable from
the `ℝ` side through `distToNearestInt_ratCast`.

From `Z32/`: the orbit `Z32.x`, the cycle denominator `Z32.cycleDenom` and the carry step
`Z32.exists_carry`.  This file adds only the multiplier reduction, the `κ` bookkeeping and the
diagonal-digit identity.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`.

## Claim level

Formalization only.  The shadowing bound and the `2/3` threshold are elementary bookkeeping; the
constant `log 2/log(3/2)` is the same one as in [Dub09G]-style aperiodicity arguments.  The problem
statement is a research problem, recorded, not attacked.

## References

* `plans/plan-A6+.html` C7 (the sojourn dichotomy and the σ-ledger).
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)^k‖`*, J. Théor. Nombres Bordeaux **19**
  (2007), 311–323.
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003).
* [Beu81] F. Beukers, *Fractional parts of powers of rationals*, Math. Proc. Cambridge Philos.
  Soc. **90** (1981), 13–20 — the shifted Padé estimate, targets `M/3^δ` only.
-/

namespace TShift

open Real

/-! ## 1. Distance to the nearest integer

`distToNearestInt` and its API live in `ForMathlib/Data/Real/NearestInt.lean`; only the following
orbit-specific lemma is added. -/

/-- Only the fractional part matters: `‖(3/2)ⁿ - ρ‖ = ‖xₙ - ρ‖`. -/
@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem distToNearestInt_pow_sub (n : ℕ) (ρ : ℝ) :
    distToNearestInt (((3 : ℝ) / 2) ^ n - ρ) = distToNearestInt (Z32.x n - ρ) := by
  have hx : Z32.x n = ((3 : ℝ) / 2) ^ n - (⌊((3 : ℝ) / 2) ^ n⌋ : ℝ) := rfl
  have h : ((3 : ℝ) / 2) ^ n - ρ = (Z32.x n - ρ) + (⌊((3 : ℝ) / 2) ^ n⌋ : ℝ) := by
    rw [hx]; ring
  rw [h, distToNearestInt_add_intCast]

/-! ## 2. The targets: cycle points and their denominators

`Z32.cycleDenom p = 3^p - 2^p` is already in the corpus, together with `Z32.cycleDenom_odd` and
`Z32.cycle_point_eq` (a `p`-periodic point of the carry relation has that denominator).  Added
here: the arithmetic converse — the numerator dynamics closes up after `p` steps. -/

@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem cycleDenom_values :
    Z32.cycleDenom 1 = 1 ∧ Z32.cycleDenom 2 = 5 ∧ Z32.cycleDenom 3 = 19 ∧
      Z32.cycleDenom 4 = 65 ∧ Z32.cycleDenom 5 = 211 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Z32.cycleDenom]

/-- `3^p ≡ 2^p` modulo `D_p = 3^p - 2^p` — the reason the numerator map has order dividing `p`. -/
@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem three_pow_modEq_two_pow (p : ℕ) :
    (3 : ℤ) ^ p ≡ 2 ^ p [ZMOD ((Z32.cycleDenom p : ℕ) : ℤ)] := by
  have hle : (2 : ℕ) ^ p ≤ 3 ^ p := Nat.pow_le_pow_left (by norm_num) p
  have hcast : ((Z32.cycleDenom p : ℕ) : ℤ) = 3 ^ p - 2 ^ p := by
    rw [Z32.cycleDenom]
    push_cast [Nat.cast_sub hle]
    ring
  refine Int.modEq_iff_dvd.mpr ⟨-1, ?_⟩
  rw [hcast]
  ring

/-- **Lemma 1, arithmetic half.**  On the numerators the carry relation reads
`2·A_{i+1} ≡ 3·A_i (mod D_p)`; after `p` steps it closes up. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem numerator_periodic {p : ℕ} (hp : 1 ≤ p) {A : ℕ → ℤ}
    (hstep : ∀ i, 2 * A (i + 1) ≡ 3 * A i [ZMOD ((Z32.cycleDenom p : ℕ) : ℤ)]) :
    A p ≡ A 0 [ZMOD ((Z32.cycleDenom p : ℕ) : ℤ)] := by
  set D : ℤ := ((Z32.cycleDenom p : ℕ) : ℤ) with hD
  -- iterate the step: `2^k · A k ≡ 3^k · A 0`
  have key : ∀ k : ℕ, (2 : ℤ) ^ k * A k ≡ 3 ^ k * A 0 [ZMOD D] := by
    intro k
    induction k with
    | zero => simp [Int.ModEq.refl]
    | succ k ih =>
        have h1 : (2 : ℤ) ^ (k + 1) * A (k + 1) = 2 ^ k * (2 * A (k + 1)) := by ring
        have h2 : (2 : ℤ) ^ k * (2 * A (k + 1)) ≡ 2 ^ k * (3 * A k) [ZMOD D] :=
          (hstep k).mul_left _
        have h3 : (2 : ℤ) ^ k * (3 * A k) = 3 * (2 ^ k * A k) := by ring
        have h4 : (3 : ℤ) * (2 ^ k * A k) ≡ 3 * (3 ^ k * A 0) [ZMOD D] := ih.mul_left _
        have h5 : (3 : ℤ) * (3 ^ k * A 0) = 3 ^ (k + 1) * A 0 := by ring
        calc (2 : ℤ) ^ (k + 1) * A (k + 1) = 2 ^ k * (2 * A (k + 1)) := h1
          _ ≡ 2 ^ k * (3 * A k) [ZMOD D] := h2
          _ = 3 * (2 ^ k * A k) := h3
          _ ≡ 3 * (3 ^ k * A 0) [ZMOD D] := h4
          _ = 3 ^ (k + 1) * A 0 := h5
  -- and `3^p ≡ 2^p`, so `2^p · A p ≡ 2^p · A 0`; cancel the unit `2^p`
  have hmul : (2 : ℤ) ^ p * A p ≡ 2 ^ p * A 0 [ZMOD D] :=
    (key p).trans ((three_pow_modEq_two_pow p).mul_right (A 0))
  have hodd : Odd (Z32.cycleDenom p) := Z32.cycleDenom_odd hp
  have hcopNat : Nat.Coprime (Z32.cycleDenom p) 2 := by
    refine Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr ?_)
    obtain ⟨s, hs⟩ := hodd
    rintro ⟨u, hu⟩
    omega
  have hcop2 : IsCoprime D (2 : ℤ) := by
    rw [hD]
    have h := Nat.isCoprime_iff_coprime.mpr hcopNat
    simpa using h
  have hcop : IsCoprime D ((2 : ℤ) ^ p) := hcop2.pow_right
  have hdvd : D ∣ (A 0 - A p) * 2 ^ p := by
    have h := Int.modEq_iff_dvd.mp hmul
    have hrw : (2 : ℤ) ^ p * A 0 - 2 ^ p * A p = (A 0 - A p) * 2 ^ p := by ring
    rwa [hrw] at h
  exact Int.modEq_iff_dvd.mpr (hcop.dvd_of_dvd_mul_right hdvd)

/-- The cycle point `A/(3^p - 2^p)` is the fixed point of the period-`p` affine map
`y ↦ (3/2)^p · y - A/2^p`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem affine_fixedPoint {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    ((3 : ℝ) / 2) ^ p * ((A : ℝ) / Z32.cycleDenom p) - (A : ℝ) / 2 ^ p
      = (A : ℝ) / Z32.cycleDenom p := by
  have hpos : (0 : ℝ) < (Z32.cycleDenom p : ℕ) := by
    exact_mod_cast Z32.cycleDenom_pos hp
  have hcast : ((Z32.cycleDenom p : ℕ) : ℝ) = 3 ^ p - 2 ^ p := Z32.cycleDenom_cast p
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  rw [hcast] at hpos ⊢
  rw [div_pow]
  field_simp
  ring

/-! ## 3. The free bound, and the reduction to an integer multiplier -/

/-- **The multiplier form of the free bound.**  `‖D·(3/2)ⁿ‖ ≥ 2^{-n}` for odd `D`.  Via
`distToNearestInt_natCast_div` at `D·3ⁿ / 2ⁿ`: the numerator is odd, so its residue mod `2ⁿ` and
that residue's complement are both at least `1`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem distToNearestInt_mul_ge {n : ℕ} (hn : 1 ≤ n) {D : ℕ} (hD : Odd D) :
    1 / (2 : ℝ) ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := by
  have hd : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hrw : (D : ℝ) * ((3 : ℝ) / 2) ^ n = ((D * 3 ^ n : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) := by
    push_cast
    rw [div_pow]
    ring
  have hmod2 : (D * 3 ^ n) % 2 = 1 := by
    have h1 : D % 2 = 1 := Nat.odd_iff.mp hD
    have h2 : (3 ^ n) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    rw [Nat.mul_mod, h1, h2]
  have hlink : (D * 3 ^ n) % 2 ^ n % 2 = (D * 3 ^ n) % 2 :=
    Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))
  have hlt : (D * 3 ^ n) % 2 ^ n < 2 ^ n := Nat.mod_lt _ hd
  have hmin : 1 ≤ min ((D * 3 ^ n) % 2 ^ n) (2 ^ n - (D * 3 ^ n) % 2 ^ n) := by omega
  have hminR : (1 : ℝ) ≤ ((min ((D * 3 ^ n) % 2 ^ n) (2 ^ n - (D * 3 ^ n) % 2 ^ n) : ℕ) : ℝ) := by
    exact_mod_cast hmin
  have hdR : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hd
  rw [hrw, distToNearestInt_natCast_div _ _ hd]
  calc (1 : ℝ) / (2 : ℝ) ^ n = 1 / ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((min ((D * 3 ^ n) % 2 ^ n) (2 ^ n - (D * 3 ^ n) % 2 ^ n) : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) :=
        by gcongr

/-- **The reduction (4).**  One bound for `‖D·t‖` controls *all* targets `A/D` at once:
`‖t - A/D‖ ≥ ‖D·t‖/D`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem distToNearestInt_mul_le {D : ℕ} (hD : 0 < D) (t : ℝ) (A : ℤ) :
    distToNearestInt ((D : ℝ) * t) ≤ D * distToNearestInt (t - (A : ℝ) / D) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  set m : ℤ := round (t - (A : ℝ) / D) with hm
  have hsplit : (D : ℝ) * t - ((A + (D : ℤ) * m : ℤ) : ℝ)
      = (D : ℝ) * (t - (A : ℝ) / D - (m : ℝ)) := by
    push_cast
    field_simp
    ring
  calc distToNearestInt ((D : ℝ) * t)
      ≤ |(D : ℝ) * t - ((A + (D : ℤ) * m : ℤ) : ℝ)| := distToNearestInt_le_abs_sub_intCast _ _
    _ = D * |t - (A : ℝ) / D - (m : ℝ)| := by rw [hsplit, abs_mul, abs_of_pos hDR]
    _ = D * distToNearestInt (t - (A : ℝ) / D) := by rw [distToNearestInt]

/-- **The free bound at a shifted target**, now a corollary of the previous two: for odd `D` the
orbit stays `1/(D·2ⁿ)` away from every rational `A/D`, modulo 1. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem distToNearestInt_ge_of_odd_denom {n : ℕ} (hn : 1 ≤ n) {D : ℕ} (hD : Odd D) (A : ℤ) :
    1 / ((D : ℝ) * 2 ^ n) ≤ distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / D) := by
  have hDpos : 0 < D := hD.pos
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h3 : 1 / (2 : ℝ) ^ n
      ≤ (D : ℝ) * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / D) :=
    le_trans (distToNearestInt_mul_ge hn hD) (distToNearestInt_mul_le hDpos _ A)
  rw [div_le_iff₀ h2] at h3
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (D : ℝ) * 2 ^ n)]
  nlinarith [h3]

/-! ## 4. The problem -/

/-- `IsRepelled θ ρ`: the orbit `(3/2)ⁿ` is exponentially repelled from `ρ` at rate `θ`, with an
effective constant and threshold. -/
def IsRepelled (θ ρ : ℝ) : Prop :=
  ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, c * θ ^ n ≤ distToNearestInt (((3 : ℝ) / 2) ^ n - ρ)

/-- `IsRepelledMul θ D`: the multiplier form, `‖D·(3/2)ⁿ‖ ≥ c·θⁿ`. -/
def IsRepelledMul (θ : ℝ) (D : ℕ) : Prop :=
  ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, c * θ ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n)

/-- **The T-shift problem** at period `p` and numerator `A`, in its existential form: exponential
repulsion of `(3/2)ⁿ` from the cycle target `A/(3^p - 2^p)` at some rate `θ > 2/3`.

**This proposition is a theorem** — `TShift.tShiftProblem_holds`, in `TShift/MahlerCountMul.lean`,
proves it for every `p ≥ 1` and every `A` — because the rate, the constant and the threshold are all
existentially quantified and Mahler's theorem supplies them ineffectively.  The *effective* problem
is `TShift.TShiftProblemAt`, which fixes the numerals; **that** is open for every `p`, and this
file's own rates do not reach it: `TShift.isRepelled_half` gives the free `1/2`, which does not
qualify (`TShift.half_not_gt_two_thirds`), and neither does the transported `0.57434` of
`TShift/HabsiegerTransfer.lean` (`TShift.thetaHab_lt_two_thirds`).  For `p = 1` the target is `0`
and the effective problem is the classical one, where the record rate is `0.5803` [Zud07].

Kept under this name and unchanged: it is the hypothesis every reduction in `TShift/` discharges,
and each such reduction remains exactly as informative as before. -/
def TShiftProblem (p : ℕ) (A : ℤ) : Prop :=
  ∃ θ > (2 : ℝ) / 3, IsRepelled θ ((A : ℝ) / Z32.cycleDenom p)

@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem half_not_gt_two_thirds : ¬ ((2 : ℝ) / 3 < 1 / 2) := by norm_num

/-- **The free rate.**  `θ = 1/2` always works, with `c = 1/D`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem isRepelled_half {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    IsRepelled (1 / 2) ((A : ℝ) / Z32.cycleDenom p) := by
  have hDpos : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have hDR : (0 : ℝ) < (Z32.cycleDenom p : ℕ) := by exact_mod_cast hDpos
  refine ⟨1 / (Z32.cycleDenom p : ℕ), by positivity, 1, fun n hn => ?_⟩
  have h := distToNearestInt_ge_of_odd_denom hn (Z32.cycleDenom_odd hp) A
  have hrw : 1 / ((Z32.cycleDenom p : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n
      = 1 / (((Z32.cycleDenom p : ℕ) : ℝ) * 2 ^ n) := by
    rw [div_pow, one_pow]
    field_simp
  rwa [hrw]

/-- The multiplier form of the free rate. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem isRepelledMul_half {D : ℕ} (hD : Odd D) : IsRepelledMul (1 / 2) D := by
  refine ⟨1, one_pos, 1, fun n hn => ?_⟩
  have h := distToNearestInt_mul_ge hn hD
  have hrw : (1 : ℝ) * (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
    rw [div_pow, one_pow, one_mul]
  rwa [hrw]

/-- **The reduction, in problem form.**  A multiplier bound at `D` gives the shifted bound at
*every* target `A/D`, uniformly in `A`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem IsRepelledMul.isRepelled {θ : ℝ} {D : ℕ} (hD : 0 < D) (h : IsRepelledMul θ D) (A : ℤ) :
    IsRepelled θ ((A : ℝ) / D) := by
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨c / D, by positivity, n₀, fun n hn => ?_⟩
  have h1 := hn₀ n hn
  have h2 := distToNearestInt_mul_le hD (((3 : ℝ) / 2) ^ n) A
  rw [distToNearestInt_pow_sub]
  rw [distToNearestInt_pow_sub] at h2
  rw [div_mul_eq_mul_div, div_le_iff₀ hDR]
  calc c * θ ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := h1
    _ ≤ (D : ℝ) * distToNearestInt (Z32.x n - (A : ℝ) / D) := h2
    _ = distToNearestInt (Z32.x n - (A : ℝ) / D) * D := by ring

/-- **It is enough to solve the multiplier form.**  A rate `θ > 2/3` for `‖D_p·(3/2)ⁿ‖` settles
the T-shift problem at *every* target of period `p` simultaneously. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem tShiftProblem_of_isRepelledMul {p : ℕ} (hp : 1 ≤ p) (A : ℤ)
    (h : ∃ θ > (2 : ℝ) / 3, IsRepelledMul θ (Z32.cycleDenom p)) : TShiftProblem p A := by
  obtain ⟨θ, hθ, hrep⟩ := h
  exact ⟨θ, hθ, hrep.isRepelled (Z32.cycleDenom_pos hp) A⟩

/-! ### The problem at fixed numerals

`TShiftProblem` and every existential variant of it is a theorem (`TShift.tShiftProblem_holds`,
`TShift.tShift_forall_ge_one`, both in `TShift/MahlerCountMul.lean`).  The open problem is about
*witnesses*, so the numerals have to be parameters.  These two definitions live here, with the
statement they repair and with `0` cited axioms, so that every rate theorem in `TShift/` can
instantiate them regardless of its own footprint. -/

/-- **Effective repulsion at fixed numerals**: `c·θⁿ ≤ ‖(3/2)ⁿ − A/D_p‖` for all `n ≥ n₀`, with
`θ`, `c` and `n₀` given rationals/naturals rather than existentially quantified.  This is the
predicate the corpus's rate theorems actually instantiate — see `TShift.repelledAt_half` (the free
`1/2`) and `TShift.repelledAt_habsieger` (the transported `0.57434`). -/
def RepelledAt (p : ℕ) (A : ℤ) (θ c : ℚ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, (c : ℝ) * (θ : ℝ) ^ n ≤ distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / Z32.cycleDenom p)

/-- **The T-shift problem at fixed data.**  Solving it means *exhibiting* numerals `θ, c, n₀` with
`2/3 < θ`.  Its existential closure is `TShiftProblem`, which is a theorem — which is exactly why
the numerals belong in the statement.

Status of the family in this corpus:

* `TShift.repelledAt_half` gives `RepelledAt p A (1/2) (1/D_p) 1` — every numeral explicit, but
  `1/2 < 2/3`, so it is not a `TShiftProblemAt` (`TShift.not_tShiftProblemAt_half`).
* `TShift.repelledAt_habsieger` gives `RepelledAt p A (57434/100000) (1/D_p) (max 64440001 (1341·D_p))`,
  again with every numeral explicit; still `< 2/3`.
* `TShift.exists_tShiftProblemAt` gives `TShiftProblemAt p A (3/4) (1/D_p) n₀` for *some* `n₀` — the
  rate clears `2/3`, but no numeral `n₀` is produced, `Set.Finite.bddAbove` supplying none.

**Open**: a single `(p, A, θ, c, n₀)` with `2/3 < θ` and all numerals exhibited. -/
def TShiftProblemAt (p : ℕ) (A : ℤ) (θ c : ℚ) (n₀ : ℕ) : Prop :=
  2 / 3 < θ ∧ RepelledAt p A θ c n₀

/-- Any solved instance of the family solves the problem. -/
@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem TShiftProblemAt.tShiftProblem {p : ℕ} {A : ℤ} {θ c : ℚ} {n₀ : ℕ} (hc : 0 < c)
    (h : TShiftProblemAt p A θ c n₀) : TShiftProblem p A := by
  obtain ⟨hθ, hrep⟩ := h
  have hθR : (2 : ℝ) / 3 < (θ : ℝ) := by
    have h' : ((2 / 3 : ℚ) : ℝ) < ((θ : ℚ) : ℝ) := by exact_mod_cast hθ
    push_cast at h'
    linarith
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  exact ⟨(θ : ℝ), hθR, (c : ℝ), hcR, n₀, hrep⟩

/-- **The free rate, with every numeral exhibited** — and below the threshold, so not a solution:
`‖(3/2)ⁿ − A/D_p‖ ≥ (1/D_p)·(1/2)ⁿ` for all `n ≥ 1`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem repelledAt_half {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    RepelledAt p A (1 / 2) (1 / (Z32.cycleDenom p : ℚ)) 1 := by
  intro n hn
  have hD : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have h := distToNearestInt_ge_of_odd_denom hn (Z32.cycleDenom_odd hp) A
  have hrw : ((1 / (Z32.cycleDenom p : ℚ) : ℚ) : ℝ) * ((1 / 2 : ℚ) : ℝ) ^ n
      = 1 / (((Z32.cycleDenom p : ℕ) : ℝ) * 2 ^ n) := by
    push_cast
    rw [div_pow, one_pow]
    field_simp
  rw [hrw]
  exact h

/-- `1/2` does not clear the threshold — the free rate is not a solution of the family. -/
@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem not_tShiftProblemAt_half {p : ℕ} {A : ℤ} {c : ℚ} {n₀ : ℕ} :
    ¬ TShiftProblemAt p A (1 / 2) c n₀ := by
  rintro ⟨h, -⟩
  norm_num at h

/-! ## 5. Shadowing, the sojourn cap, and the threshold `2/3` -/

/-- **The shadowing lemma.**  A trajectory of an expanding affine map that is still within `1`
of the fixed point after `j` steps started within `r^{-j}` of it. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem abs_sub_fixed_le {r c ρ : ℝ} (hr : 1 < r) (hfix : r * ρ - c = ρ) {z : ℕ → ℝ}
    (hz : ∀ i, z (i + 1) = r * z i - c) {j : ℕ} (hb : |z j - ρ| ≤ 1) :
    |z 0 - ρ| ≤ (1 / r) ^ j := by
  have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
  have key : ∀ i : ℕ, z i - ρ = r ^ i * (z 0 - ρ) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        have : z (i + 1) - ρ = r * (z i - ρ) := by
          rw [hz i]
          nlinarith [hfix]
        rw [this, ih]
        ring
  have hj : r ^ j * |z 0 - ρ| ≤ 1 := by
    have : |z j - ρ| = r ^ j * |z 0 - ρ| := by
      rw [key j, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < r ^ j)]
    linarith [hb, this.symm.le, this.le]
  have hrj : (0 : ℝ) < r ^ j := by positivity
  rw [div_pow, one_pow]
  rw [le_div_iff₀ hrj, mul_comm]
  exact hj

/-- **The sojourn cap.**  Repulsion at rate `θ` plus a shadowing bound `(2/3)^L` cap the sojourn
length `L` linearly in the date `n`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem sojourn_cap {c θ d : ℝ} {n L : ℕ} (hc : 0 < c) (hθ : 0 < θ)
    (hrep : c * θ ^ n ≤ d) (hshadow : d ≤ (2 / 3 : ℝ) ^ L) :
    (L : ℝ) * Real.log (3 / 2) ≤ (n : ℝ) * (-Real.log θ) + (-Real.log c) := by
  have hpos : 0 < c * θ ^ n := by positivity
  have hle : c * θ ^ n ≤ (2 / 3 : ℝ) ^ L := le_trans hrep hshadow
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_mul (ne_of_gt hc) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have h23 : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
    rw [show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
  rw [h23] at hlog
  linarith

/-- `κ(θ) = log(1/θ)/log(3/2)`, the sojourn-cap slope. -/
noncomputable def kappa (θ : ℝ) : ℝ := -Real.log θ / Real.log (3 / 2)

@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem log_three_halves_pos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)

/-- The sojourn cap in `κ` form: `L ≤ κ(θ)·n + C`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem sojourn_cap_kappa {c θ d : ℝ} {n L : ℕ} (hc : 0 < c) (hθ : 0 < θ)
    (hrep : c * θ ^ n ≤ d) (hshadow : d ≤ (2 / 3 : ℝ) ^ L) :
    (L : ℝ) ≤ kappa θ * n + (-Real.log c) / Real.log (3 / 2) := by
  have hlog := sojourn_cap hc hθ hrep hshadow
  have hpos := log_three_halves_pos
  rw [kappa, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hpos]
  linarith

/-- **The threshold.**  `κ(θ) < 1` exactly when `θ > 2/3`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem kappa_lt_one_iff {θ : ℝ} (hθ : 0 < θ) : kappa θ < 1 ↔ (2 : ℝ) / 3 < θ := by
  have hpos := log_three_halves_pos
  rw [kappa, div_lt_one hpos]
  constructor
  · intro h
    have h1 : Real.log ((2 : ℝ) / 3) < Real.log θ := by
      rw [show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
      linarith
    exact (Real.log_lt_log_iff (by norm_num) hθ).mp h1
  · intro h
    have h1 : Real.log ((2 : ℝ) / 3) < Real.log θ :=
      Real.log_lt_log (by norm_num) h
    rw [show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv] at h1
    linarith

@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem kappa_two_thirds : kappa (2 / 3 : ℝ) = 1 := by
  have hpos := log_three_halves_pos
  rw [kappa, show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv, neg_neg]
  exact div_self (ne_of_gt hpos)

/-- The free rate `θ = 1/2` gives `κ = log 2/log(3/2) > 1`: the 2-adic floor alone permits sojourns
*longer* than the date. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem one_lt_kappa_half : 1 < kappa (1 / 2 : ℝ) := by
  have hpos := log_three_halves_pos
  rw [kappa, show (1 : ℝ) / 2 = ((2 : ℝ))⁻¹ by norm_num, Real.log_inv, neg_neg, lt_div_iff₀ hpos]
  have : Real.log (3 / 2 : ℝ) < Real.log 2 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## 6. What a linear sojourn cap buys: the visit recursion -/

/-- **The geometric bound.**  `a_{k+1} ≤ q·a_k + C` with `q > 1` forces `a_k` below a geometric
sequence of ratio `q` — so the number of `k` with `a_k ≤ N` is at least `log N/log q - O(1)`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem geometric_bound {q C : ℝ} (hq : 1 < q) {a : ℕ → ℝ}
    (ha : ∀ k, a (k + 1) ≤ q * a k + C) (k : ℕ) :
    a k + C / (q - 1) ≤ q ^ k * (a 0 + C / (q - 1)) := by
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : a (k + 1) + C / (q - 1) ≤ q * (a k + C / (q - 1)) := by
        have : q * (a k + C / (q - 1)) = q * a k + C + C / (q - 1) := by
          field_simp
          ring
        linarith [ha k]
      calc a (k + 1) + C / (q - 1) ≤ q * (a k + C / (q - 1)) := hstep
        _ ≤ q * (q ^ k * (a 0 + C / (q - 1))) := by
            exact mul_le_mul_of_nonneg_left ih (by linarith)
        _ = q ^ (k + 1) * (a 0 + C / (q - 1)) := by ring

/-- **The dyadic payoff.**  Once `κ < 1`, i.e. `q = 1 + κ < 2`, consecutive escape dates satisfy
`n_{k+1} < 2·n_k` from the point where the date exceeds `C/(2-q)`: every dyadic block of dates
carries a visit. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem lt_two_mul_of_lt_two {q C a b : ℝ} (hq2 : q < 2) (hab : b ≤ q * a + C)
    (ha : C / (2 - q) < a) : b < 2 * a := by
  have h2q : (0 : ℝ) < 2 - q := by linarith
  have : C < (2 - q) * a := by
    rw [div_lt_iff₀ h2q] at ha
    linarith
  linarith

/-! ## 7. The carry word of `ξ = 1` is the diagonal binary digit of `3ⁿ`

The successor of `xₙ` is not determined by `xₙ` — there are two candidates, `1/2` apart — and the
bit that decides is the parity of `⌊(3/2)ⁿ⌋`, i.e. **bit `n` of `3ⁿ`**.  This is the second
ingredient of a sojourn, alongside the closeness that T-shift denies: a sojourn needs *both*. -/

/-- `mₙ = ⌊(3/2)ⁿ⌋`. -/
noncomputable def intPart (n : ℕ) : ℤ := ⌊((3 : ℝ) / 2) ^ n⌋

/-- The carry digit of the `ξ = 1` orbit, as an explicit integer. -/
noncomputable def carry (n : ℕ) : ℤ := 2 * intPart (n + 1) - 3 * intPart n

@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem carry_cast (n : ℕ) : (carry n : ℝ) = 3 * Z32.x n - 2 * Z32.x (n + 1) := by
  have hpow : ((3 : ℝ) / 2) ^ (n + 1) = (3 / 2) * (3 / 2) ^ n := by ring
  simp only [carry, intPart, Z32.x, Int.fract]
  push_cast
  rw [hpow]
  ring

/-- The carry alphabet: `sₙ ∈ {-1,0,1,2}`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem carry_mem (n : ℕ) : -1 ≤ carry n ∧ carry n ≤ 2 := by
  obtain ⟨s, hs, h1, h2⟩ := Z32.exists_carry n
  have : (carry n : ℝ) = (s : ℝ) := by
    rw [carry_cast]
    linarith
  have hcs : carry n = s := by exact_mod_cast this
  exact ⟨hcs ▸ h1, hcs ▸ h2⟩

/-- **The lost bit.**  The carry digit has the parity of `⌊(3/2)ⁿ⌋`. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem carry_emod_two (n : ℕ) : carry n % 2 = intPart n % 2 := by
  rw [carry]
  omega

/-- `⌊(3/2)ⁿ⌋ = 3ⁿ / 2ⁿ` (natural division). -/
@[category API, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem intPart_eq (n : ℕ) : intPart n = ((3 ^ n / 2 ^ n : ℕ) : ℤ) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hdm : (2 : ℕ) ^ n * (3 ^ n / 2 ^ n) + 3 ^ n % 2 ^ n = 3 ^ n := Nat.div_add_mod _ _
  have hlt : (3 : ℕ) ^ n % 2 ^ n < 2 ^ n := Nat.mod_lt _ (pow_pos (by norm_num) n)
  have hcast : ((3 : ℝ) / 2) ^ n
      = ((3 ^ n / 2 ^ n : ℕ) : ℝ) + ((3 ^ n % 2 ^ n : ℕ) : ℝ) / 2 ^ n := by
    have h := congrArg (fun m : ℕ => (m : ℝ)) hdm
    push_cast at h
    rw [div_pow]
    field_simp
    linarith
  have hfrac0 : (0 : ℝ) ≤ ((3 ^ n % 2 ^ n : ℕ) : ℝ) / 2 ^ n := by positivity
  have hfrac1 : ((3 ^ n % 2 ^ n : ℕ) : ℝ) / 2 ^ n < 1 := by
    rw [div_lt_one h2]
    exact_mod_cast hlt
  rw [intPart, Int.floor_eq_iff]
  simp only [Int.cast_natCast]
  rw [hcast]
  exact ⟨by linarith, by linarith⟩

/-- **The diagonal-digit identity.**  The carry digit is odd exactly when bit `n` of `3ⁿ` is set.
So the carry word of the `ξ = 1` orbit *is* the diagonal binary digit sequence of the powers of
`3` — the object a "parity decoupling" route would have to control. -/
@[category research solved, AMS 11 37, ref "A6plus", group "tshift_basic"]
theorem testBit_iff_carry_odd (n : ℕ) :
    Nat.testBit (3 ^ n) n = true ↔ carry n % 2 = 1 := by
  rw [carry_emod_two, intPart_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  omega

end TShift
