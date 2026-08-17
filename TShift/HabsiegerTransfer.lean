/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.Basic
import TShift.MultiplierTransfer
import CITED.HabsiegerPade

/-!
# A machine-checked effective bound at a shifted target

`‖D·(3/2)^k‖ ≥ (0.57434)^k` for every `k ≥ 64 440 001`, simultaneously for every multiplier
`1 ≤ D ≤ (1 + 8.227·10⁻⁴)^k` — hence, by the multiplier reduction of `TShift.Basic`, exponential
repulsion of the orbit `(3/2)ⁿ` from **every** cycle target `A/(3^p − 2^p)`, of every period, at
rate `0.57434`, uniformly in the numerator; and at a single date `k`, simultaneously for all
periods `p ≤ k/1341` (at the first date covered: all `p ≤ 48 053` at once).

The three ingredients are separately auditable and meet here for the first time:

* `TShift/MultiplierTransfer.lean` — the elimination step, engine-agnostic, `std3`;
* `CITED/HabsiegerPade.lean` — one cited axiom, [Hab03]'s construction, multiplier-free;
* this file — the descent, the endgame numerics, and the assembly.

## What is new here, and what is not

The rate `0.57434` at `D = 1` is [Hab03] Theorem 2.  What is not in the literature is that it
**transports to every multiplier at no cost**: `D` never enters the Padé construction, only the
error column of the elimination step, where it is charged once as `2^δ·D·Λ`.  The whole content of
the transport is `TShift.multiplier_transfer`, and the whole cost is the correction lemma
`TShift.habsieger_correction_le` below, whose hypothesis is literally `D ≤ sHab^m` — the multiplier
is admissible up to the per-`m` gain of the correction term, and nothing else about it is used.

That is why there is no cut on `D`.  Per date `k` the admissible range is `D ≤ bHab^k` with
`bHab = 1 + 8.2270664·10⁻⁴` (`TShift.le_distToNearestInt_uniform`, Theorem B); per fixed `D` the
bound then holds from `max(64 440 001, 1341·D)` on, so *every* multiplier and *every* period is
covered asymptotically.  A factor `53.17` of admissible multiplier is left unspent — Theorem B's
additive constant, recorded in `habsieger_correction_le` and not claimed in any statement.

## The chain

Write `k = 6m − δ` with `m = ⌈k/6⌉` and `δ ∈ {0,…,5}`.

1. **Descent** (`TShift.distToNearestInt_descent`).  `2^δ·D·(3/2)^{6m} = 3^δ·(D·(3/2)^k)`, so
   `‖2^δ·D·(3/2)^{6m}‖ ≤ 3^δ·‖D·(3/2)^k‖` by `TShift.distToNearestInt_mul_le`.  One line — the
   `H`/`W` bookkeeping the plan expected here is not needed at all; see the WP2 docstring.
2. **Transfer** (`TShift.le_distToNearestInt_pow` at `N = 6m`, `v = δ`, fed by
   `Habsieger.padeData m`).
3. **Endgame** (`TShift.habsieger_endgame`).  The resulting bound beats `3^δ·(0.57434)^k`.

## The numeric discipline

Every comparison is between rational bases raised to `ℕ`-powers: no `Real.exp`, no `Real.rpow`, no
`native_decide`, no `decide` on `ℚ`.  Two devices carry it:

* **32nd-power brackets.**  The index `n` of the Padé data enters only through `8^{n+1}`, and the
  axiom bounds `n` by `30m − 45 < 32n ≤ 30m − 13`.  Clearing that to `96(n+1) ≤ 90m + 57` and
  `90m ≤ 96(n+1) + 39` and comparing 32nd powers gives rational brackets
  `(21/50)·(281/40)^m ≤ 8^{n+1} ≤ (86/25)·(60956/8677)^m`, where `60956/8677` is a convergent of
  `2^{45/16} = 7.02500864…` accurate to `2·10⁻⁹` and `281/40 = 7.025` undershoots it by
  `1.23·10⁻⁶`.  Neither accuracy is decoration: the upper bracket has only `1.06·10⁻⁴` of margin
  per `m`, so a four-digit surrogate there makes the goal **false**; and the lower bracket's base
  *is* Theorem B's `ε`, so every digit of it is a digit of the uniformity range.
* **Bernoulli, not evaluation.**  The main term needs `q^m ≥ 2` for `q = 1.000106…`, which
  `one_add_mul_le_pow` supplies from its *linear* bound since `m > 10⁷`; the period range needs
  `3 ≤ bHab^{1341}`, which is the same lemma applied to 149 chunks of 9
  (`TShift.three_le_bHab_pow`).  Nothing of size `r^m` is ever evaluated, and no literal above
  500 digits occurs (`norm_num` refuses to evaluate `1215^1336` — the direct route is not
  available even if one wanted it).
  It matters that the brackets are introduced *before* the 32nd power is taken rather than after:
  raising the whole master inequality to the 32nd power multiplies its constant by 32 in the
  exponent (`e^{0.52} ↦ e^{16.7}`), and Bernoulli's linear bound no longer reaches it.

## The margins, for anyone re-deriving

At the threshold `m = 10 740 001`, `δ = 5`: the correction lemma needs `32 ≤ 1701.63` (and that
ratio is the unspent `53.17`) and the main lemma needs `6838 ≤ 8103`.  In nats against the
exact-constant computation of `plans/note-Tshift-S1-constants.html` §3 this is the same `109` nats
of margin the constants note reports, spent as `0.7` on halving the numerator and the rest left on
the table.  The three surrogates that are *not* comfortable, with their true margins:
`60956/8677` above `2^{45/16}` (`2.05·10⁻⁹`), `281/40` below it (`1.23·10⁻⁶`), and `bHab⁶ ≤ sHab`
(`2.03·10⁻⁶` in the logarithm).

## Trust ledger

`std3 + Habsieger.padeData` — one cited axiom, and it is the only one.  `#print axioms` on every
declaration below returns exactly that.

## Claim level

Formalization.  The `D = 1` rate is [Hab03] Theorem 2 and is cited, not reproved; the transport to
`D > 1` and every constant of the endgame are proved here.  **No instance of the effective problem
`TShift.TShiftProblemAt` is settled here**: `0.57434 < 2/3` (`TShift.thetaHab_lt_two_thirds`), so
the sojourn cap stays above `1`
(`TShift.kappa_lt_one_iff`).  What the bound does clear is the free 2-adic floor
(`TShift.half_lt_thetaHab`), which is the first time anything in this corpus does so at a shifted
target.

## References

* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003),
  299–308.  In repo: `papers/Habsieger.pdf`.
* `plans/plan-Tshift-S1.html` §2.1 (the chain), §3.3 (the numeric discipline), §4 WP3 (Theorem A)
  and WP4 (Theorem B, the uniformity).
* `plans/note-Tshift-S1-constants.html` §3–§5 (the endgame constants), §7 (the surrogates).
-/

namespace TShift

open Habsieger

/-! ## 1. The constants of the statement -/

/-- The rate: `0.57434`, just below Habsieger's `2^{-0.8} = 0.5743491774…`. -/
noncomputable def thetaHab : ℝ := 57434 / 100000

/-- The first date the transported bound covers, `6·(10 740 000 + 1) − 5`.  One more than the
`64 440 000` of the printed statement, because `CITED/HabsiegerPade.lean` reads (3.11)'s threshold
strictly. -/
def kHab : ℕ := 64440001

/-- A round multiplier, kept only so that Theorem A has a concrete reading.  It is *not* a cut:
`TShift.le_bHab_pow_of_le_dHab` derives `10⁶ ≤ bHab^k` from `k ≥ kHab` with `e^{53000}` to spare,
so the `D ≤ 10⁶` form is a corollary of the uniform one, not a restriction of it. -/
def dHab : ℕ := 1000000

@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem thetaHab_pos : 0 < thetaHab := by rw [thetaHab]; norm_num

/-- **Honesty lemma.**  The transported rate does not reach the `2/3` threshold: this file exhibits
numerals (`TShift.RepelledAt p A (57434/100000) c kHab`) but at a rate below the demand, so no
instance of `TShift.TShiftProblemAt` follows from anything in it. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem thetaHab_lt_two_thirds : thetaHab < 2 / 3 := by rw [thetaHab]; norm_num

/-- …but it does clear the free 2-adic floor of `TShift.isRepelledMul_half`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem half_lt_thetaHab : 1 / 2 < thetaHab := by rw [thetaHab]; norm_num

/-! ## 2. The 32nd-power brackets for `8^{n+1}`

The Padé index enters the endgame only as `8^{n+1}`, and only through the two-sided range the
axiom carries.  Cleared of denominators that range reads `96(n+1) ≤ 90m + 57` and
`90m ≤ 96(n+1) + 39`, and comparing 32nd powers converts it into rational brackets. -/

/-- Upper bracket: `8^{n+1} ≤ (86/25)·(60956/8677)^m`, from `32n + 13 ≤ 30m`.
`60956/8677 = 7.0250086435…` exceeds `2^{45/16} = 7.0250086415…` by `2·10⁻⁹`; `86/25` exceeds
`2^{57/32} = 3.4372386…`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem eightPow_le {m n : ℕ} (h : 32 * n + 13 ≤ 30 * m) :
    (8 : ℝ) ^ (n + 1) ≤ (86 / 25) * (60956 / 8677) ^ m := by
  have hexp : 96 * (n + 1) ≤ 90 * m + 57 := by omega
  refine le_of_pow_le_pow_left₀ (n := 32) (by norm_num) (by positivity) ?_
  calc ((8 : ℝ) ^ (n + 1)) ^ 32
      = 2 ^ (96 * (n + 1)) := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
    _ ≤ 2 ^ (90 * m + 57) := pow_le_pow_right₀ (by norm_num) hexp
    _ = 2 ^ 57 * ((2 : ℝ) ^ 90) ^ m := by rw [pow_add, ← pow_mul, Nat.mul_comm]; ring
    _ ≤ ((86 : ℝ) / 25) ^ 32 * (((60956 : ℝ) / 8677) ^ 32) ^ m := by
        apply mul_le_mul (by norm_num) (pow_le_pow_left₀ (by positivity) (by norm_num) m)
          (by positivity) (by positivity)
    _ = ((86 / 25 : ℝ) * (60956 / 8677) ^ m) ^ 32 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Lower bracket: `(21/50)·(281/40)^m ≤ 8^{n+1}`, from `30m < 32n + 45`.  `281/40 = 7.025` sits
`1.23·10⁻⁶` below `2^{45/16}`, and that precision *is* used: this base is the whole per-`m` budget
of the multiplier, so the coarser `7.02` of a first draft would cost 15% of Theorem B's `ε`.  The
prefactor `21/50 = 0.42 ≤ 2^{-39/32} = 0.42876` may stay coarse — it is a one-off constant. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem le_eightPow {m n : ℕ} (h : 30 * m < 32 * n + 45) :
    (21 / 50 : ℝ) * (281 / 40) ^ m ≤ (8 : ℝ) ^ (n + 1) := by
  have hexp : 90 * m ≤ 96 * (n + 1) + 39 := by omega
  refine le_of_pow_le_pow_left₀ (n := 32) (by norm_num) (by positivity) ?_
  calc ((21 / 50 : ℝ) * (281 / 40) ^ m) ^ 32
      = ((21 : ℝ) / 50) ^ 32 * (((281 : ℝ) / 40) ^ 32) ^ m := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ ((21 : ℝ) / 50) ^ 32 * (((2 : ℝ) ^ 90) ^ m) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by positivity)
    _ = ((21 : ℝ) / 50) ^ 32 * 2 ^ (90 * m) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ ((21 : ℝ) / 50) ^ 32 * 2 ^ (96 * (n + 1) + 39) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hexp) (by positivity)
    _ = (((21 : ℝ) / 50) ^ 32 * 2 ^ 39) * 2 ^ (96 * (n + 1)) := by rw [pow_add]; ring
    _ ≤ 1 * 2 ^ (96 * (n + 1)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = ((8 : ℝ) ^ (n + 1)) ^ 32 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; ring_nf

/-! ## 3. The two per-`m` gains

`qHab` is the per-`m` gain of the main term and `sHab` that of the correction term.  Both exceed
`1`.  The main term needs only `qHab^m ≥ 2`, which `m > 10⁷` gets from Bernoulli's *linear* bound
with a factor `180` to spare; the correction term needs no lower bound on `sHab^m` at all — it
needs the multiplier to stay below it, which is exactly what `bHab` measures. -/

/-- The per-`m` gain of the main term:
`contentBase / (upper bracket base · denomBase · thetaHab⁶) = 1.000106036…`. -/
noncomputable def qHab : ℝ := contentBase / ((60956 / 8677) * denomBase * thetaHab ^ 6)

/-- The per-`m` gain of the correction term, hence **the rate at which the admissible multiplier
may grow**: `(lower bracket base) · contentBase / errorBase = 1.0049504823…`, against the
exact-constant `e^{0.0049396} = 1.0049518…` of the constants note (§3, `R_m`) — the loss is the
`1.23·10⁻⁶` by which `281/40` undershoots `2^{45/16}`. -/
noncomputable def sHab : ℝ := (281 / 40) * contentBase / errorBase

/-- The per-`k` gain, `sHab^{1/6}` rounded down to a rational with a small denominator:
`1216/1215 = 1 + 8.2270664·10⁻⁴`.  This is **Theorem B's `ε`**, and it is `0.07%` below the
exact-constant `ε = 8.23273737·10⁻⁴` of `plans/plan-Tshift-S1.html` §2. -/
noncomputable def bHab : ℝ := 1216 / 1215

@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem sHab_pos : 0 < sHab := by rw [sHab, contentBase, errorBase]; norm_num

@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem one_le_bHab : (1 : ℝ) ≤ bHab := by rw [bHab]; norm_num

@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem one_add_le_qHab : (1 : ℝ) + 1 / 60000 ≤ qHab := by
  rw [qHab, contentBase, denomBase, thetaHab]
  norm_num

/-- `qHab^m ≥ 2` once `m ≥ 60000` — a factor `180` less than Bernoulli actually gives at the
threshold, and all the endgame asks for. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem two_le_qHab_pow {m : ℕ} (hm : 60000 ≤ m) : (2 : ℝ) ≤ qHab ^ m := by
  have hb : (1 : ℝ) + (m : ℝ) * (1 / 60000) ≤ (1 + 1 / 60000) ^ m :=
    one_add_mul_le_pow (by norm_num) m
  have hmR : (60000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : ((1 : ℝ) + 1 / 60000) ^ m ≤ qHab ^ m :=
    pow_le_pow_left₀ (by norm_num) one_add_le_qHab m
  nlinarith

/-- **The `k ↦ m` conversion, and the only place `bHab` is tied to `sHab`**: `bHab⁶ ≤ sHab`, with
`2.03·10⁻⁶` of margin in the logarithm.  Exact rational arithmetic decides it; a five-digit
surrogate for either base would not survive. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem bHab_pow_six_le_sHab : bHab ^ 6 ≤ sHab := by
  rw [bHab, sHab, contentBase, errorBase]
  norm_num

/-- Hence `bHab^k ≤ sHab^m` whenever `k ≤ 6m`, which is what the date `k = 6m − δ` gives. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem bHab_pow_le_sHab_pow {k m : ℕ} (h : k ≤ 6 * m) : bHab ^ k ≤ sHab ^ m := by
  calc bHab ^ k ≤ bHab ^ (6 * m) := pow_le_pow_right₀ one_le_bHab h
    _ = (bHab ^ 6) ^ m := by rw [← pow_mul]
    _ ≤ sHab ^ m := pow_le_pow_left₀ (by positivity) bHab_pow_six_le_sHab m

/-! ## 4. The endgame -/

/-- **The correction term is at most half the main term.**  This is the *only* place the
multiplier is charged, and the charge is exactly the hypothesis `D ≤ sHab^m`: the requirement is
`2^δ·D ≤ (8103/2)·(21/50)·sHab^m`, and `2^δ ≤ 32 ≤ 1701.63` leaves a factor `53.17` of the
admissible multiplier unspent (that factor is Theorem B's additive constant, not claimed below). -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem habsieger_correction_le {m n δ D : ℕ} (hδ : δ ≤ 5) (hDs : (D : ℝ) ≤ sHab ^ m)
    (hn : 30 * m < 32 * n + 45) :
    (2 : ℝ) ^ δ * (D : ℝ) * formBound m n ≤ (1 / 2) * contentBound m * 2 ^ (6 * m) := by
  have hEne : errorBase ≠ 0 := ne_of_gt errorBase_pos
  have hE : (0 : ℝ) < errorBase ^ m := pow_pos errorBase_pos m
  have h8 : (0 : ℝ) < (8 : ℝ) ^ (n + 1) := by positivity
  have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ (6 * m) := by positivity
  have hsE : sHab * errorBase = (281 / 40) * contentBase := by rw [sHab]; field_simp
  -- (a) the scalar requirement: `2^δ·D ≤ (8103/2)·(21/50)·sHab^m`
  have hscal : (2 : ℝ) ^ δ * (D : ℝ) ≤ (8103 / 2) * (21 / 50) * sHab ^ m := by
    have h1 : (2 : ℝ) ^ δ ≤ 32 := by
      calc (2 : ℝ) ^ δ ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) hδ
        _ = 32 := by norm_num
    have hs : (0 : ℝ) < sHab ^ m := pow_pos sHab_pos m
    calc (2 : ℝ) ^ δ * (D : ℝ)
        ≤ 32 * sHab ^ m := mul_le_mul h1 hDs (Nat.cast_nonneg D) (by norm_num)
      _ ≤ (8103 / 2) * (21 / 50) * sHab ^ m :=
          mul_le_mul_of_nonneg_right (by norm_num) hs.le
  -- (b) transport it through the two `^m` factors
  have hkey : (2 : ℝ) ^ δ * (D : ℝ) * errorBase ^ m
      ≤ (8103 / 2) * ((21 / 50) * (281 / 40) ^ m) * contentBase ^ m := by
    have hpow : sHab ^ m * errorBase ^ m = ((281 : ℝ) / 40) ^ m * contentBase ^ m := by
      rw [← mul_pow, hsE, mul_pow]
    calc (2 : ℝ) ^ δ * (D : ℝ) * errorBase ^ m
        ≤ ((8103 / 2) * (21 / 50) * sHab ^ m) * errorBase ^ m :=
          mul_le_mul_of_nonneg_right hscal hE.le
      _ = (8103 / 2) * (21 / 50) * (sHab ^ m * errorBase ^ m) := by ring
      _ = (8103 / 2) * ((21 / 50) * (281 / 40) ^ m) * contentBase ^ m := by rw [hpow]; ring
  -- (c) and through the lower bracket
  have hform : (2 : ℝ) ^ δ * (D : ℝ) * formBound m n
      = ((2 : ℝ) ^ δ * (D : ℝ) * errorBase ^ m * 2 ^ (6 * m)) / (8 : ℝ) ^ (n + 1) := by
    rw [formBound]; ring
  have hcB : (0 : ℝ) ≤ (1 / 2) * contentBound m * 2 ^ (6 * m) := by
    have := contentBound_pos m
    positivity
  rw [hform, div_le_iff₀ h8]
  calc (2 : ℝ) ^ δ * (D : ℝ) * errorBase ^ m * 2 ^ (6 * m)
      ≤ ((8103 / 2) * ((21 / 50) * (281 / 40) ^ m) * contentBase ^ m) * 2 ^ (6 * m) :=
        mul_le_mul_of_nonneg_right hkey h2m
    _ = ((1 / 2) * contentBound m * 2 ^ (6 * m)) * ((21 / 50) * (281 / 40) ^ m) := by
        rw [contentBound, contentConst]; ring
    _ ≤ ((1 / 2) * contentBound m * 2 ^ (6 * m)) * (8 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (le_eightPow hn) hcB

/-- **Half the main term already beats the target.**  The requirement is
`(3/θ)⁵·(86/25)·(639/1250) ≤ (8103/2)·qHab^m`, i.e. `6838 ≤ 8103` once `qHab^m ≥ 2`.  Everything
`δ` costs is the factor `(3/θ)^δ ≤ (3/θ)⁵`, which is the `δ`-budget of the constants note. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem habsieger_main_le {m n δ : ℕ} (hm : 60000 ≤ m) (hδ : δ ≤ 5) (hδm : δ ≤ 6 * m)
    (hn : 32 * n + 13 ≤ 30 * m) :
    3 ^ δ * thetaHab ^ (6 * m - δ) * (coeffBound m n * 2 ^ (6 * m))
      ≤ (1 / 2) * contentBound m * 2 ^ (6 * m) := by
  have hθ := thetaHab_pos
  have hden := denomBase_pos
  have hr1 : (1 : ℝ) ≤ 3 / thetaHab := by rw [thetaHab]; norm_num
  have hX : ((60956 : ℝ) / 8677) * denomBase * thetaHab ^ 6 ≠ 0 := by
    rw [denomBase, thetaHab]; norm_num
  -- `3^δ ≤ (3/θ)⁵·θ^δ`: the whole cost of `δ`
  have h3 : (3 : ℝ) ^ δ ≤ (3 / thetaHab) ^ 5 * thetaHab ^ δ := by
    have hid : (3 / thetaHab) ^ δ * thetaHab ^ δ = 3 ^ δ := by
      rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt hθ)]
    calc (3 : ℝ) ^ δ = (3 / thetaHab) ^ δ * thetaHab ^ δ := hid.symm
      _ ≤ (3 / thetaHab) ^ 5 * thetaHab ^ δ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr1 hδ) (by positivity)
  have hsplit : thetaHab ^ (6 * m) = thetaHab ^ (6 * m - δ) * thetaHab ^ δ := by
    rw [← pow_add]; congr 1; omega
  have hq : qHab * (((60956 : ℝ) / 8677) * denomBase * thetaHab ^ 6) = contentBase := by
    rw [qHab, div_mul_cancel₀ _ hX]
  have hqm : contentBase ^ m
      = qHab ^ m * (((60956 : ℝ) / 8677) * denomBase * thetaHab ^ 6) ^ m := by
    rw [← mul_pow, hq]
  have hscal : ((3 : ℝ) / thetaHab) ^ 5 * ((86 / 25) * (639 / 1250))
      ≤ (8103 / 2) * qHab ^ m := by
    have hconst : ((3 : ℝ) / thetaHab) ^ 5 * ((86 / 25) * (639 / 1250)) ≤ 8103 := by
      rw [thetaHab]; norm_num
    have h2q : (2 : ℝ) ≤ qHab ^ m := two_le_qHab_pow hm
    nlinarith
  have hYpos : (0 : ℝ) ≤ (((60956 : ℝ) / 8677) * denomBase * thetaHab ^ 6) ^ m * 2 ^ (6 * m) := by
    positivity
  calc 3 ^ δ * thetaHab ^ (6 * m - δ) * (coeffBound m n * 2 ^ (6 * m))
      ≤ ((3 / thetaHab) ^ 5 * thetaHab ^ δ) * thetaHab ^ (6 * m - δ)
          * (coeffBound m n * 2 ^ (6 * m)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (by positivity))
          (by have := coeffBound_pos m n; positivity)
    _ = (3 / thetaHab) ^ 5 * thetaHab ^ (6 * m) * (coeffBound m n * 2 ^ (6 * m)) := by
        rw [hsplit]; ring
    _ ≤ (3 / thetaHab) ^ 5 * thetaHab ^ (6 * m)
          * (((86 / 25) * (60956 / 8677) ^ m * denomConst * denomBase ^ m) * 2 ^ (6 * m)) := by
        rw [coeffBound]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (eightPow_le hn) ?_) ?_
        · rw [denomConst]; norm_num
        · positivity
    _ = (((3 : ℝ) / thetaHab) ^ 5 * ((86 / 25) * (639 / 1250)))
          * ((((60956 : ℝ) / 8677) * denomBase * thetaHab ^ 6) ^ m * 2 ^ (6 * m)) := by
        rw [denomConst, mul_pow, mul_pow, ← pow_mul, Nat.mul_comm 6 m]
        ring
    _ ≤ ((8103 / 2) * qHab ^ m)
          * ((((60956 : ℝ) / 8677) * denomBase * thetaHab ^ 6) ^ m * 2 ^ (6 * m)) :=
        mul_le_mul_of_nonneg_right hscal hYpos
    _ = (1 / 2) * (8103 * contentBase ^ m) * 2 ^ (6 * m) := by rw [hqm]; ring
    _ = (1 / 2) * contentBound m * 2 ^ (6 * m) := by rw [contentBound, contentConst]

/-- **The endgame.**  Both halves together. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem habsieger_endgame {m n δ D : ℕ} (hm : 60000 ≤ m) (hδ : δ ≤ 5) (hδm : δ ≤ 6 * m)
    (hDs : (D : ℝ) ≤ sHab ^ m) (hn1 : 32 * n + 13 ≤ 30 * m) (hn2 : 30 * m < 32 * n + 45) :
    3 ^ δ * thetaHab ^ (6 * m - δ)
      ≤ (contentBound m * 2 ^ (6 * m) - 2 ^ δ * (D : ℝ) * formBound m n)
          / (coeffBound m n * 2 ^ (6 * m)) := by
  have hB : (0 : ℝ) < coeffBound m n * 2 ^ (6 * m) := by
    have := coeffBound_pos m n
    positivity
  rw [le_div_iff₀ hB]
  have hcorr := habsieger_correction_le hδ hDs hn2
  have hmain := habsieger_main_le (m := m) (n := n) (δ := δ) hm hδ hδm hn1
  linarith

/-! ## 5. The descent from `6m` to the date `k = 6m − δ` -/

/-- `2^δ·D·(3/2)^{6m} = 3^δ·(D·(3/2)^k)`, so the `6m`-bound descends to the date `k` at the cost
of `3^δ`.  This is where the `3^δ` of the printed (4.2) comes from; no `H`, no `W`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem distToNearestInt_descent {D δ k m : ℕ} (hk : 6 * m = k + δ) :
    distToNearestInt ((2 : ℝ) ^ δ * (D : ℝ) * ((3 : ℝ) / 2) ^ (6 * m))
      ≤ 3 ^ δ * distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) := by
  have h32 : (2 : ℝ) ^ δ * ((3 : ℝ) / 2) ^ δ = 3 ^ δ := by rw [← mul_pow]; norm_num
  have hrw : (2 : ℝ) ^ δ * (D : ℝ) * ((3 : ℝ) / 2) ^ (6 * m)
      = ((3 ^ δ : ℕ) : ℝ) * ((D : ℝ) * ((3 : ℝ) / 2) ^ k) := by
    have hc : ((3 ^ δ : ℕ) : ℝ) = (3 : ℝ) ^ δ := by push_cast; ring
    rw [hc, hk, pow_add, ← h32]
    ring
  rw [hrw]
  have h := distToNearestInt_mul_le (D := 3 ^ δ) (by positivity)
    ((D : ℝ) * ((3 : ℝ) / 2) ^ k) 0
  simpa using h

/-! ## 6. The transported bound, uniformly in the multiplier -/

/-- **Theorem B, machine-checked.**  `‖D·(3/2)^k‖ ≥ (0.57434)^k` for every `k ≥ 64 440 001`,
*simultaneously* for every `1 ≤ D ≤ bHab^k = (1 + 8.227·10⁻⁴)^k`.  The quantifier order is the
point: `D` is not fixed before `k`.  Footprint: `std3 + Habsieger.padeData`. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem le_distToNearestInt_uniform {D k : ℕ} (hD : 0 < D) (hk : kHab ≤ k)
    (hDk : (D : ℝ) ≤ bHab ^ k) :
    thetaHab ^ k ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) := by
  have hk' : 64440001 ≤ k := by rw [kHab] at hk; exact hk
  set m : ℕ := (k + 5) / 6 with hmdef
  set δ : ℕ := 6 * m - k with hδdef
  have hkm : 6 * m = k + δ := by omega
  have hm : 10740001 ≤ m := by omega
  have hδ : δ ≤ 5 := by omega
  have hδm : δ ≤ 6 * m := by omega
  have hkeq : 6 * m - δ = k := by omega
  have hDs : (D : ℝ) ≤ sHab ^ m :=
    le_trans hDk (bHab_pow_le_sHab_pow (by omega))
  obtain F := Habsieger.padeData m (by rw [Habsieger.mLow]; omega)
  have htrans := le_distToNearestInt_pow (N := 6 * m) (v := δ) (D := D) hD
    (coeffBound_pos m F.n) F.det_ne_zero F.dvd_a₁ F.dvd_b₁ F.dvd_a₂ F.dvd_b₂
    F.content₁_abs F.content₂_abs F.size₁ F.size₂ F.coeff₁ F.coeff₂
  have hend := habsieger_endgame (m := m) (n := F.n) (δ := δ) (D := D) (by omega) hδ hδm hDs
    F.n_upper F.n_lower
  have hdesc := distToNearestInt_descent (D := D) (δ := δ) (k := k) (m := m) hkm
  have h3 : (0 : ℝ) < 3 ^ δ := by positivity
  rw [hkeq] at hend
  have hchain : 3 ^ δ * thetaHab ^ k ≤ 3 ^ δ * distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) :=
    le_trans (le_trans hend htrans) hdesc
  exact le_of_mul_le_mul_left hchain h3

/-- `3 ≤ bHab^1341`, by Bernoulli in 149 chunks of 9.  The exact exponent is
`log 3 / log bHab = 1335.2`, so the chunking costs `0.4%`; 149 is the optimal chunk count.  This is
the only lemma standing between Theorem B and its two usable forms below, and `1341` is the
constant `1/c'` of the plan (`c' = 7.4571·10⁻⁴` here against the exact `7.49376·10⁻⁴`). -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem three_le_bHab_pow : (3 : ℝ) ≤ bHab ^ 1341 := by
  have h9 : (1 : ℝ) + 9 / 1215 ≤ bHab ^ 9 := by
    have h := one_add_mul_le_pow (a := (1 : ℝ) / 1215) (by norm_num) 9
    rw [bHab]
    calc (1 : ℝ) + 9 / 1215 = 1 + (9 : ℕ) * (1 / 1215) := by norm_num
      _ ≤ (1 + 1 / 1215) ^ 9 := h
      _ = ((1216 : ℝ) / 1215) ^ 9 := by norm_num
  calc (3 : ℝ) ≤ ((1 : ℝ) + 9 / 1215) ^ 149 := by norm_num
    _ ≤ (bHab ^ 9) ^ 149 := pow_le_pow_left₀ (by norm_num) h9 149
    _ = bHab ^ 1341 := by rw [← pow_mul]

/-- Every multiplier is admissible from date `1341·D` on: `D ≤ 3^D ≤ (bHab^{1341})^D`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem le_bHab_pow_self (D : ℕ) : (D : ℝ) ≤ bHab ^ (1341 * D) := by
  have h3 : (D : ℝ) ≤ 3 ^ D := by
    have : D < 3 ^ D := Nat.lt_pow_self (by norm_num)
    exact_mod_cast this.le
  calc (D : ℝ) ≤ 3 ^ D := h3
    _ ≤ (bHab ^ 1341) ^ D := pow_le_pow_left₀ (by norm_num) three_le_bHab_pow D
    _ = bHab ^ (1341 * D) := by rw [← pow_mul]

/-- The `10⁶` cut of the first draft, now a consequence: `10⁶ ≤ 3¹³ ≤ bHab^{17433} ≤ bHab^k`. -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem le_bHab_pow_of_le_dHab {D k : ℕ} (hDle : D ≤ dHab) (hk : kHab ≤ k) :
    (D : ℝ) ≤ bHab ^ k := by
  have hk' : 17433 ≤ k := by rw [kHab] at hk; omega
  have hD : (D : ℝ) ≤ 1000000 := by
    have : D ≤ 1000000 := by rw [dHab] at hDle; exact hDle
    exact_mod_cast this
  calc (D : ℝ) ≤ 1000000 := hD
    _ ≤ (3 : ℝ) ^ 13 := by norm_num
    _ ≤ (bHab ^ 1341) ^ 13 := pow_le_pow_left₀ (by norm_num) three_le_bHab_pow 13
    _ = bHab ^ 17433 := by rw [← pow_mul]
    _ ≤ bHab ^ k := pow_le_pow_right₀ one_le_bHab hk'

/-- **Theorem A, machine-checked** — the concrete reading of Theorem B: `‖D·(3/2)^k‖ ≥ (0.57434)^k`
for every `k ≥ 64 440 001` and every `1 ≤ D ≤ 10⁶`. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem le_distToNearestInt_habsieger {D : ℕ} (hD : 0 < D) (hDle : D ≤ dHab)
    {k : ℕ} (hk : kHab ≤ k) :
    thetaHab ^ k ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) :=
  le_distToNearestInt_uniform hD hk (le_bHab_pow_of_le_dHab hDle hk)

/-- The multiplier form, in the corpus' vocabulary: `TShift.IsRepelledMul` at rate `0.57434` for
**every** positive multiplier, with `c = 1` and `n₀ = max(64 440 001, 1341·D)`. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem isRepelledMul_habsieger {D : ℕ} (hD : 0 < D) : IsRepelledMul thetaHab D := by
  refine ⟨1, one_pos, max kHab (1341 * D), fun k hk => ?_⟩
  have hDk : (D : ℝ) ≤ bHab ^ k :=
    le_trans (le_bHab_pow_self D)
      (pow_le_pow_right₀ one_le_bHab (le_trans (le_max_right _ _) hk))
  simpa using le_distToNearestInt_uniform hD (le_trans (le_max_left _ _) hk) hDk

/-- The `D = 5` instance: the period-2 cycle denominator. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem isRepelledMul_five : IsRepelledMul thetaHab 5 :=
  isRepelledMul_habsieger (by norm_num)

/-! ## 7. Corollary A′: the cycle targets -/

/-- **Corollary A′.**  For **every** period `p ≥ 1` and every numerator `A`, the orbit `(3/2)ⁿ` is
repelled from the cycle target `A/(3^p − 2^p)` at rate `0.57434` — uniformly in `A`, with constant
`1/(3^p − 2^p)`.  At `p = 2` this covers each of `1/5, 2/5, 3/5, 4/5`.  The period is no longer
bounded: WP4's uniformity turned the first draft's `p ≤ 12` into an `n₀` that grows with `p`. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem isRepelled_cycle {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    IsRepelled thetaHab ((A : ℝ) / Z32.cycleDenom p) :=
  (isRepelledMul_habsieger (Z32.cycleDenom_pos hp)).isRepelled (Z32.cycleDenom_pos hp) A

/-- **Corollary A′ as a member of the `TShiftProblemAt` family** — every numeral exhibited:
`θ = 0.57434`, `c = 1/D_p`, `n₀ = max(64 440 001, 1341·D_p)`.  This is the *shape* the T-shift
problem asks for; only the rate falls short of `2/3` (`thetaHab_lt_two_thirds`), which is why it is
a `TShift.RepelledAt` and not a `TShift.TShiftProblemAt` (`TShift.not_tShiftProblemAt_half` is the
same remark for the free rate).  Contrast `TShift.exists_tShiftProblemAt`, which clears `2/3` but
exhibits no `n₀`. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem repelledAt_habsieger {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    RepelledAt p A (57434 / 100000) (1 / (Z32.cycleDenom p : ℚ))
      (max kHab (1341 * Z32.cycleDenom p)) := by
  intro n hn
  have hD : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have hDR : (0 : ℝ) < ((Z32.cycleDenom p : ℕ) : ℝ) := by exact_mod_cast hD
  have hDk : ((Z32.cycleDenom p : ℕ) : ℝ) ≤ bHab ^ n :=
    le_trans (le_bHab_pow_self _)
      (pow_le_pow_right₀ one_le_bHab (le_trans (le_max_right _ _) hn))
  have h1 : thetaHab ^ n ≤ distToNearestInt (((Z32.cycleDenom p : ℕ) : ℝ) * ((3 : ℝ) / 2) ^ n) :=
    le_distToNearestInt_uniform hD (le_trans (le_max_left _ _) hn) hDk
  have h2 := distToNearestInt_mul_le hD (((3 : ℝ) / 2) ^ n) A
  have hcast : ((1 / (Z32.cycleDenom p : ℚ) : ℚ) : ℝ) * ((57434 / 100000 : ℚ) : ℝ) ^ n
      = thetaHab ^ n / ((Z32.cycleDenom p : ℕ) : ℝ) := by
    rw [thetaHab]; push_cast; ring
  rw [hcast, div_le_iff₀ hDR]
  calc thetaHab ^ n
      ≤ distToNearestInt (((Z32.cycleDenom p : ℕ) : ℝ) * ((3 : ℝ) / 2) ^ n) := h1
    _ ≤ ((Z32.cycleDenom p : ℕ) : ℝ)
        * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ)) := h2
    _ = distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ))
        * ((Z32.cycleDenom p : ℕ) : ℝ) := by ring

/-- **Corollary B′, the pointwise form**: at a single date `k`, *all* periods `p ≤ k/1341` are
covered at once, uniformly in the numerator.  This is the statement the plan calls "uniformity in
the period"; the asymptotic `isRepelled_cycle` is its per-`p` shadow. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem le_dist_cycle_uniform {p k : ℕ} (hp : 1 ≤ p) (hk : kHab ≤ k) (hpk : 1341 * p ≤ k)
    (A : ℤ) :
    thetaHab ^ k / (Z32.cycleDenom p : ℕ)
      ≤ distToNearestInt (((3 : ℝ) / 2) ^ k - (A : ℝ) / (Z32.cycleDenom p : ℕ)) := by
  have hDpos : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have hDR : (0 : ℝ) < ((Z32.cycleDenom p : ℕ) : ℝ) := by exact_mod_cast hDpos
  have hD3 : ((Z32.cycleDenom p : ℕ) : ℝ) ≤ 3 ^ p := by
    rw [Z32.cycleDenom_cast]
    have : (0 : ℝ) ≤ 2 ^ p := by positivity
    linarith
  have hDk : ((Z32.cycleDenom p : ℕ) : ℝ) ≤ bHab ^ k := by
    refine le_trans hD3 (le_trans ?_ (pow_le_pow_right₀ one_le_bHab hpk))
    calc (3 : ℝ) ^ p ≤ (bHab ^ 1341) ^ p := pow_le_pow_left₀ (by norm_num) three_le_bHab_pow p
      _ = bHab ^ (1341 * p) := by rw [← pow_mul]
  have h1 := le_distToNearestInt_uniform hDpos hk hDk
  have h2 := distToNearestInt_mul_le hDpos (((3 : ℝ) / 2) ^ k) A
  rw [div_le_iff₀ hDR]
  calc thetaHab ^ k ≤ distToNearestInt (((Z32.cycleDenom p : ℕ) : ℝ) * ((3 : ℝ) / 2) ^ k) := h1
    _ ≤ ((Z32.cycleDenom p : ℕ) : ℝ)
          * distToNearestInt (((3 : ℝ) / 2) ^ k - (A : ℝ) / (Z32.cycleDenom p : ℕ)) := h2
    _ = distToNearestInt (((3 : ℝ) / 2) ^ k - (A : ℝ) / (Z32.cycleDenom p : ℕ))
          * ((Z32.cycleDenom p : ℕ) : ℝ) := by ring

/-- What Corollary B′ says at the first date it covers: every period up to `48 053`, simultaneously
(the plan's exact-constant count is `48 292`). -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem period_range_at_kHab : 1341 * 48053 ≤ kHab := by rw [kHab]; norm_num

/-- **Honesty lemma, in problem form.**  Corollary A′ is not an instance of
`TShift.TShiftProblemAt`: the rate it delivers is below the `2/3` threshold, so the sojourn cap
`TShift.kappa_lt_one_iff` stays `≥ 1`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem one_le_kappa_thetaHab : 1 ≤ kappa thetaHab := by
  by_contra hcon
  push Not at hcon
  exact absurd ((kappa_lt_one_iff thetaHab_pos).mp hcon)
    (not_lt.mpr (le_of_lt thetaHab_lt_two_thirds))

end TShift
