/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.Basic
import TH.RepetitionIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The free sojourn cap for the `(3/2)ⁿ` carry word

The T-shift problem asks for repulsion of `(3/2)ⁿ` from a cycle target at a rate `θ > 2/3`, with
the rate, the constant and the threshold **exhibited** (`TShift.TShiftProblemAt`).  That is open;
the bare existential `TShift.TShiftProblem` is a theorem (`TShift.tShiftProblem_holds`), which is
why the numerals belong in the statement.  This file proves what is **free**: a periodic block of
the carry word of length `L` starting at date `n` obeys

  `2^(L+n) ≤ 3^(n+p)`,   i.e.   `L ≤ log₂(3/2)·n + p·log₂3`   (`free_sojourn_cap`)

unconditionally, with no Diophantine input at all.  The slope is
`κ_free = log₂(3/2) = 0.5849625… < 1`, so the sojourn cap is *sublinear in the date*, which is
exactly the regime `TShift.kappa_lt_one_iff` isolates — and `free_kappa_lt_one` puts it there.
Equivalently (`kappa_thetaFree`, `two_thirds_lt_thetaFree`): the free rung is worth as much, for
sojourn purposes, as repulsion at the rate

  `θ* = exp(−log²(3/2)/log 2) = 0.7888478…  >  2/3`.

The payoff is `dyadic_block_visit`: consecutive escape dates satisfy `n_{k+1} < 2·n_k`, so every
dyadic block of dates `[2^m, 2^{m+1})` carries a visit.  The same ceiling, applied at a *fixed*
gap and every length, forbids eventual periodicity of the carry word outright
(`carry_not_eventually_periodic`).

## Where the cap comes from

`carry n = 2·⌊(3/2)^{n+1}⌋ − 3·⌊(3/2)ⁿ⌋` (`TShift.carry`, alphabet `{−1,0,1,2}`) satisfies
`2·m_{n+1} = 3·m_n + carry n`, so equal factors of the carry word accumulate equal circuit sums
and the main terms cancel — **Lemma R in floor convention** (`lemmaR_floor`):

  `3^k (m_c − m_a) = 2^k (m_{c+k} − m_{a+k})`,  hence  `2^k ∣ m_c − m_a`.

For `2 ≤ a < c` the divisibility upgrades to size, `2^k ≤ m_c − m_a < m_c ≤ 3^c/2^c`, which is the
**growth ceiling** `2^(k+c) ≤ 3^c` (`carry_repetition_pow_le`).  A `p`-periodic block on
`[n, n+L)` *is* a repetition of length `L−p` at `(a, c) = (n, n+p)`, and the ceiling reads off the
cap.  No band, no shadowing, no multiplier: the divisibility is read off the *word*, not off the
cycle target.

This is the route WP0 of `plans/plan-Tshift-S11.html` found (note
`plans/note-Tshift-S11-WP0.html`, milestone M0).  The plan's own D5 chain — shadowing → `1/5`
band at multiplier `D_p` → parity cascade → size of `m_n` — is *correct* (re-derived and verified
exactly on 6 752 real periodic blocks) but pays `log D_p` twice for the detour through the target:
same slope, additive constant `6.97` vs `1.585` at `p = 1`.  Its cascade layer survives here on its
own merits as `cascade_step`/`cascade_dvd`, at general multiplier `D`, where it is the sharp run
anatomy of the `‖D(3/2)ⁿ‖ < 1/5` runs (§3 of the note) — but it is no longer on the path to the
headline.

## κ-discipline

Nothing here is a per-`n` **floor**.  `free_sojourn_cap` bounds how long the orbit may *shadow* a
periodic pattern; it says nothing about how close it gets at any single date, and it is not a step
toward `θ > 2/3`.  Report `report-Tshift.html` §1.5's sentence "below `θ = 2/3` no such statement
is available at any position" is what this file corrects (candidate correction **C20**): the
statement is available, for free, at every position — the payoff (`2.1713·ln N` visits by time
`N`) beats every row of that section's table, including the `θ = 3/4` Waring row.

## Cited, not restated

Per the house flag-existing rule, two targets of the plan already exist in the corpus in the
**round** convention (`TH.m n = round((3/2)ⁿ)`, `TH.t n = 2·m(n+1) − 3·m n`) and are **not**
duplicated here:

* aperiodicity of the rounding word — `TH.not_eventually_periodic` (plan target T7);
* the rounding identity and alphabet at `D = 1` — `TH.two_mul_m_succ`, `TH.t_eq_eps`,
  `TH.t_abs_le` (plan target T1).

Both are `std3`.  The round-convention originals of the machinery ported below are
`TH.circuit_sum`, `TH.lemmaR_int`, `TH.two_pow_dvd_of_repetition`, `TH.repetition_pow_le`
(`TH/RepetitionIdentity.lean`), whose novelty gate records the engine in print: [AFS08] eq. (4)
and Lemmas 6/8, [Kop21] Lemma 3.8, [DN05] Lemma 1.  **The port is not a duplicate**: `TH.t` is the
*round* word and `TShift.carry` is the *floor* word — different sequences, and neither one's
periodicity implies the other's.  That is also why the floor aperiodicity statement
(`carry_not_eventually_periodic`) is proved here rather than cited: `TH.not_eventually_periodic`
does not imply it, and the corpus had no statement about the floor word.  The floor convention is
the one the report, `TShift.carry` and
`Z32.x` use, and it is the convention in which the cap is stated; it also has the better constant
(`2^(k+c) ≤ 3^c` here against `2^(k+c+1) ≤ 3^(c+1)` there, since `⌊·⌋ ≤ (3/2)^c` needs no slack).

## Provenance of the statement (plan-S11 gate G‑B, sweep #2, 2026-08-11)

The cap is **not new as mathematics**; the sweep that settled this is
`plans/note-Tshift-S11-WPE.html` §1.  [GY26] Theorem 1.2 (rational case, `q ≥ 2`) proves, for
*every* real `ξ ≠ 0` and every rational `α = p/q > 1` and target `η` with `(p−q)‖η‖ < 1`, that
`k + 1` consecutive dates with `‖ξαⁿ − η‖ < δ`, `δ = (1 − (p−q)‖η‖)/(p+q)`, force
`q^k A_{n+k} = p^k A_n`, hence `q^k ∣ A_n`, hence `k ≤ n·log α/log q + C(ξ, α)`.  At
`(p, q, η) = (3, 2, 0)` that is `δ = 1/5` and `k ≤ 0.585·n + C` — `cascade_dvd` and
`free_sojourn_cap`, same threshold and same slope — and their Lemma 3.1 (a version is [GM17]
Prop. 2.1) turns the cap into `⌊C log N⌋` escape dates, which is report §1.5's payoff, for every
real `ξ`.  [Dub09] Theorem 3 runs the same divisibility-versus-growth count in complexity
clothing at every base, `liminf P(w,n)/n ≥ log q/log(p/q)`; that paper is already formalized in
this corpus as `RB/DubickasFloor.lean`, and its constant is exactly this file's reciprocal:
`κ_free = 1/RB.dubickasConst`, `0.5849625… = 1/1.70951129…`.  Neither file cited the other before
the sweep.

What this file adds is therefore **formalization and convention, not statement**: the cap with
explicit constants in the floor convention the report uses, stated at the level of the *word* (a
`p`-periodic block, any `p`) rather than at a single target, plus the `θ*`-packaging and the
dyadic-block payoff.

## What is not here

No capacity theory, no
Pólya–Carlson/Bertrandias, no Szegő dichotomy, no natural-boundary statement.  No claim at
Dubickas's sharp `0.238117`, and no claim that `1/5` is optimal.  No general-base theorem.  No
per-`n` floor of any kind, and in particular nothing that touches the T-shift problem itself.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`, no kernel `decide` on `ℚ`/`ℝ`.

## References

* `plans/plan-Tshift-S11.html` §1.4 (D1–D5), §2.2 (targets T2, T4, T5, T6, T8), §7 (C20);
  `plans/note-Tshift-S11-WP0.html` (the WP0 audit, milestone M0).
* `report-Tshift.html` §1.5 (Lemma 3, the payoff table), N5 (the record dates), S11.
* [AFS08] Akiyama, Frougny, Sakarovitch, *Powers of rationals modulo 1 and rational base number
  systems*, Israel J. Math. **168** (2008), 53–91.
* [Kop21] Kopra, *On the trace subshifts of fractional multiplication automata*, Theoret. Comput.
  Sci. **851** (2021), 92–110.
* [DN05] Dubickas, Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648.
* [GY26] X. Gao, C. H. Yip, *On the fractional parts of certain sequences of `ξαⁿ`*,
  arXiv:2408.02972v2 (23 May 2026), Theorem 1.2 and Lemma 3.1 — the cap and the `log N` payoff
  for every real `ξ`, at every rational base.
* [GM17] X. Gao, J. H. Ma, *Decay rate of Fourier transforms of some self-similar measures*,
  Acta Math. Sci. Ser. B **37** (2017), 1607–1618, Prop. 2.1 — the escape recursion.
* [Dub09] A. Dubickas, *On integer sequences generated by linear maps*, Glasgow Math. J. **51**
  (2009), 243–252, Thm 3 and Cor 4 — the same ceiling as a complexity floor; formalized here in
  `RB/DubickasFloor.lean`.
-/

namespace TShift

open Real

/-! ## 0. The two cited round-convention statements

These `example`s carry no new declaration — they make the citations of the module docstring
machine-checked, and they are the reason `TH.RepetitionIdentity` is imported. -/

example : ¬ ∃ N p, 0 < p ∧ ∀ n, N ≤ n → TH.t (n + p) = TH.t n :=
  TH.not_eventually_periodic

example (n : ℕ) : 2 * TH.m (n + 1) = 3 * TH.m n + TH.t n := TH.two_mul_m_succ n

example {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c) (h : TH.IsRepetition a c k) :
    (2 : ℤ) ^ (k + c + 1) ≤ 3 ^ (c + 1) := TH.repetition_pow_le ha hac h

/-- `2^k` and `3^k` are coprime in `ℤ` (the round-convention twin is `TH`'s private
`coprime_pow`). -/
private lemma isCoprime_two_three_pow (k : ℕ) : IsCoprime ((2 : ℤ) ^ k) ((3 : ℤ) ^ k) := by
  refine IsCoprime.pow ?_
  rw [Int.isCoprime_iff_gcd_eq_one]
  decide

/-! ## 1. The rounding frame at a general multiplier, and the parity cascade

The cascade is the one layer of the plan's D5 chain that keeps independent value: it is the
mechanism behind the sharp anatomy of the runs of dates with `‖D(3/2)ⁿ‖ < 1/5`.  At `D = 1` the
underlying rounding identity is `TH.two_mul_m_succ`/`TH.t_eq_eps` (cited above, not restated); a
general multiplier `D` is what the cascade needs and what `TH/` does not carry. -/

/-- `m_n(D) = ` the nearest integer to `D·(3/2)ⁿ`. -/
noncomputable def mD (D n : ℕ) : ℤ := round ((D : ℝ) * (3 / 2) ^ n)

/-- `δ_n(D) = D·(3/2)ⁿ − m_n(D) ∈ [−1/2, 1/2)`. -/
noncomputable def deltaD (D n : ℕ) : ℝ := (D : ℝ) * (3 / 2) ^ n - mD D n

/-- `|δ_n(D)| = ‖D·(3/2)ⁿ‖`: the rounding defect *is* the distance to the nearest integer. -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem abs_deltaD_eq_dist (D n : ℕ) :
    |deltaD D n| = distToNearestInt ((D : ℝ) * (3 / 2) ^ n) := by
  simp only [deltaD, mD, distToNearestInt]

/-- `|δ_n(D)| ≤ 1/2`. -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem abs_deltaD_le (D n : ℕ) : |deltaD D n| ≤ 1 / 2 := by
  simpa only [deltaD, mD] using abs_sub_round ((D : ℝ) * (3 / 2) ^ n)

/-- The rounding word at multiplier `D`, in real form: `2m_{n+1} − 3m_n = 3δ_n − 2δ_{n+1}`.  (At
`D = 1` this is `TH.two_mul_m_succ` composed with `TH.t_eq_eps`; only the general-`D` version is
needed here, and it is used solely inside the cascade.) -/
private lemma rounding_word_cast (D n : ℕ) :
    ((2 * mD D (n + 1) - 3 * mD D n : ℤ) : ℝ) = 3 * deltaD D n - 2 * deltaD D (n + 1) := by
  simp only [deltaD]
  push_cast
  ring

/-- **T2 (step) — the parity cascade.**  Two consecutive defects below `1/5 = 1/(3+2)` force the
integer `2m_{n+1} − 3m_n` to vanish: `|3δ_n − 2δ_{n+1}| < 3/5 + 2/5 = 1`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem cascade_step {D n : ℕ} (h1 : |deltaD D n| < 1 / 5) (h2 : |deltaD D (n + 1)| < 1 / 5) :
    2 * mD D (n + 1) = 3 * mD D n := by
  have hb1 := abs_lt.mp h1
  have hb2 := abs_lt.mp h2
  have hcast := rounding_word_cast D n
  have hlt : |((2 * mD D (n + 1) - 3 * mD D n : ℤ) : ℝ)| < 1 := by
    rw [hcast, abs_lt]
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]
  have hz : |2 * mD D (n + 1) - 3 * mD D n| < 1 := by
    have hc : ((|2 * mD D (n + 1) - 3 * mD D n| : ℤ) : ℝ) < 1 := by rwa [Int.cast_abs]
    exact_mod_cast hc
  have hz' := abs_lt.mp hz
  omega

/-- **T2 (run) — cascade divisibility.**  A run `[a, b]` of dates with `‖D(3/2)ʲ‖ < 1/5`
throughout forces `2^{b−a} ∣ m_a(D)`: each step of the run doubles the 2-adic valuation demanded
of the *initial* integer.  With `m_a ≥ 1` this is the divisibility half of the sharp run anatomy
`b − a = min(v₂(m_a), K−1)` of the WP0 note §3. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem cascade_dvd {D a b : ℕ} (hab : a ≤ b)
    (h : ∀ j, a ≤ j → j ≤ b → |deltaD D j| < 1 / 5) :
    (2 : ℤ) ^ (b - a) ∣ mD D a := by
  have key : ∀ k, a + k ≤ b → (2 : ℤ) ^ k * mD D (a + k) = 3 ^ k * mD D a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hstep : 2 * mD D ((a + k) + 1) = 3 * mD D (a + k) :=
        cascade_step (h (a + k) (by omega) (by omega)) (h ((a + k) + 1) (by omega) (by omega))
      have hih := ih (by omega)
      have hsucc : a + (k + 1) = (a + k) + 1 := rfl
      calc (2 : ℤ) ^ (k + 1) * mD D (a + (k + 1))
          = 2 ^ k * (2 * mD D ((a + k) + 1)) := by rw [hsucc]; ring
        _ = 2 ^ k * (3 * mD D (a + k)) := by rw [hstep]
        _ = 3 * (2 ^ k * mD D (a + k)) := by ring
        _ = 3 * (3 ^ k * mD D a) := by rw [hih]
        _ = 3 ^ (k + 1) * mD D a := by ring
  have hk := key (b - a) (by omega)
  have hdvd : (2 : ℤ) ^ (b - a) ∣ 3 ^ (b - a) * mD D a := ⟨mD D (a + (b - a)), hk.symm⟩
  exact (isCoprime_two_three_pow (b - a)).dvd_of_dvd_mul_left hdvd

/-! ## 2. Lemma R in the floor convention

The port announced in the module docstring.  Round-convention originals: `TH.circuit_sum`,
`TH.lemmaR_int`, `TH.two_pow_dvd_of_repetition`, `TH.repetition_pow_le`. -/

/-- The floor-convention circuit sum `W(a,k) = Σ_{i<k} 3^{k−1−i}·2^i·s_{a+i}`. -/
noncomputable def carrySum (a k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, 3 ^ (k - 1 - i) * 2 ^ i * carry (a + i)

/-- The floor-convention orbit recursion: `2·⌊(3/2)^{n+1}⌋ = 3·⌊(3/2)ⁿ⌋ + s_n`. -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem two_mul_intPart_succ (n : ℕ) : 2 * intPart (n + 1) = 3 * intPart n + carry n := by
  simp only [carry]
  ring

@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11", simp]
theorem carrySum_zero (a : ℕ) : carrySum a 0 = 0 := by simp [carrySum]

/-- Circuit-sum recurrence: `W(a,k+1) = 3·W(a,k) + 2^k·s_{a+k}`. -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem carrySum_succ (a k : ℕ) :
    carrySum a (k + 1) = 3 * carrySum a k + 2 ^ k * carry (a + k) := by
  unfold carrySum
  rw [Finset.sum_range_succ]
  have h1 : k + 1 - 1 - k = 0 := by omega
  rw [h1, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i < k := Finset.mem_range.mp hi
  have h2 : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
  rw [h2, pow_succ]
  ring

/-- Integer circuit sum, floor convention: `2^k·m_{a+k} = 3^k·m_a + W(a,k)`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem carry_circuit_sum (a k : ℕ) :
    2 ^ k * intPart (a + k) = 3 ^ k * intPart a + carrySum a k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsucc : a + (k + 1) = (a + k) + 1 := rfl
    rw [hsucc, carrySum_succ]
    calc (2 : ℤ) ^ (k + 1) * intPart ((a + k) + 1)
        = 2 ^ k * (2 * intPart ((a + k) + 1)) := by ring
      _ = 2 ^ k * (3 * intPart (a + k) + carry (a + k)) := by rw [two_mul_intPart_succ]
      _ = 3 * (2 ^ k * intPart (a + k)) + 2 ^ k * carry (a + k) := by ring
      _ = 3 * (3 ^ k * intPart a + carrySum a k) + 2 ^ k * carry (a + k) := by rw [ih]
      _ = 3 ^ (k + 1) * intPart a + (3 * carrySum a k + 2 ^ k * carry (a + k)) := by ring

/-- A length-`k` factor of the **floor** carry word occurring at positions `a` and `c`.
Distinct from `TH.IsRepetition`, which is about the round word `TH.t`. -/
def IsCarryRepetition (a c k : ℕ) : Prop := ∀ i < k, carry (a + i) = carry (c + i)

/-- Equal factors accumulate equal circuit sums. -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem carrySum_eq_of_repetition {a c k : ℕ} (h : IsCarryRepetition a c k) :
    carrySum a k = carrySum c k :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-- **Lemma R, floor convention.**  A repetition of length `k` at `a < c` forces
`3^k (m_c − m_a) = 2^k (m_{c+k} − m_{a+k})`: the main terms of the orbit cancel exactly. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem lemmaR_floor {a c k : ℕ} (h : IsCarryRepetition a c k) :
    3 ^ k * (intPart c - intPart a) = 2 ^ k * (intPart (c + k) - intPart (a + k)) := by
  have ha := carry_circuit_sum a k
  have hc := carry_circuit_sum c k
  have hw := carrySum_eq_of_repetition h
  linear_combination ha - hc + hw

/-- Divisibility shadow of Lemma R: `2^k ∣ m_c − m_a`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem two_pow_dvd_of_carry_repetition {a c k : ℕ} (h : IsCarryRepetition a c k) :
    (2 : ℤ) ^ k ∣ intPart c - intPart a := by
  have hdvd : (2 : ℤ) ^ k ∣ 3 ^ k * (intPart c - intPart a) := by
    rw [lemmaR_floor h]
    exact Dvd.intro _ rfl
  exact (isCoprime_two_three_pow k).dvd_of_dvd_mul_left hdvd

/-- `⌊(3/2)ⁿ⌋ ≥ 1` at every date. -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem intPart_pos (n : ℕ) : 0 < intPart n := by
  rw [intPart_eq]
  have h2 : (2 : ℕ) ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h : 1 ≤ 3 ^ n / 2 ^ n :=
    (Nat.one_le_div_iff (by positivity)).mpr h2
  exact_mod_cast h

/-- `2ⁿ·⌊(3/2)ⁿ⌋ ≤ 3ⁿ` — the floor convention needs no slack term (contrast
`TH.two_pow_mul_m_le`, which carries `+2ⁿ` because `round` may overshoot). -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem two_pow_mul_intPart_le (n : ℕ) : (2 : ℤ) ^ n * intPart n ≤ 3 ^ n := by
  rw [intPart_eq]
  have h : (2 : ℕ) ^ n * (3 ^ n / 2 ^ n) ≤ 3 ^ n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  exact_mod_cast h

/-- `⌊(3/2)ⁿ⌋` increases strictly from date `2` on (`(3/2)ⁿ ≥ 2` makes the step exceed `1`). -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem intPart_lt_succ {n : ℕ} (hn : 2 ≤ n) : intPart n < intPart (n + 1) := by
  have h2 : (2 : ℝ) ≤ (3 / 2 : ℝ) ^ n := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    have hj : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hexp : ((3 : ℝ) / 2) ^ (j + 2) = (3 / 2 : ℝ) ^ j * (9 / 4) := by ring
    rw [hexp]
    linarith
  have hstep : ((3 : ℝ) / 2) ^ n + 1 ≤ ((3 : ℝ) / 2) ^ (n + 1) := by
    have hexp : ((3 : ℝ) / 2) ^ (n + 1) = (3 / 2 : ℝ) ^ n + (1 / 2) * (3 / 2 : ℝ) ^ n := by ring
    rw [hexp]
    linarith
  have hmono := Int.floor_mono hstep
  have hfl : ⌊((3 : ℝ) / 2) ^ n + 1⌋ = ⌊((3 : ℝ) / 2) ^ n⌋ + 1 := by
    simp
  rw [hfl] at hmono
  simp only [intPart]
  omega

/-- Strict monotonicity of `⌊(3/2)ⁿ⌋` from date `2` on. -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem intPart_strictMono {a c : ℕ} (ha : 2 ≤ a) (hac : a < c) : intPart a < intPart c := by
  induction c with
  | zero => omega
  | succ d ih =>
    rcases Nat.lt_or_ge a d with hlt | hge
    · have h1 := ih (by omega)
      have h2 := intPart_lt_succ (n := d) (by omega)
      omega
    · have had : a = d := by omega
      subst had
      exact intPart_lt_succ ha

/-- **The growth ceiling, floor convention.**  A length-`k` repetition of the carry word at
`2 ≤ a < c` forces `2^(k+c) ≤ 3^c`, i.e. `k ≤ log₂(3/2)·c` — pure integer arithmetic, no
logarithms and no Diophantine input.  Round-convention original: `TH.repetition_pow_le`
(`2^(k+c+1) ≤ 3^(c+1)`, one power weaker). -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem carry_repetition_pow_le {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (h : IsCarryRepetition a c k) : (2 : ℤ) ^ (k + c) ≤ 3 ^ c := by
  have hlt : intPart a < intPart c := intPart_strictMono ha hac
  have h1 : (2 : ℤ) ^ k ≤ intPart c - intPart a :=
    Int.le_of_dvd (by omega) (two_pow_dvd_of_carry_repetition h)
  have h2 : 0 < intPart a := intPart_pos a
  have h4 : (2 : ℤ) ^ k ≤ intPart c := by linarith
  calc (2 : ℤ) ^ (k + c) = 2 ^ k * 2 ^ c := pow_add 2 k c
    _ ≤ intPart c * 2 ^ c := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 2 ^ c * intPart c := by ring
    _ ≤ 3 ^ c := two_pow_mul_intPart_le c

/-- `ℕ`-cast of the growth ceiling. -/
@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem carry_repetition_pow_le_nat {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (h : IsCarryRepetition a c k) : 2 ^ (k + c) ≤ 3 ^ c := by
  exact_mod_cast carry_repetition_pow_le ha hac h

/-- **The floor carry word is not eventually periodic.**  A fixed-gap repetition of *every* length
would beat the growth ceiling `2^(k+c) ≤ 3^c` at fixed `c`.

This is the floor-convention companion of `TH.not_eventually_periodic`, and a **different
statement**: that one is about the round word `TH.t n = 2·round((3/2)^{n+1}) − 3·round((3/2)ⁿ)`,
this one about the floor word `carry n = 2·⌊(3/2)^{n+1}⌋ − 3·⌊(3/2)ⁿ⌋`; the two sequences differ
already at `n = 0` (`carry_sanity` against `TH.t_sanity`), and neither one's periodicity implies
the other's.  Both are instances of the family in [DN05] Lemma 1.

Equivalently: the orbit `xₙ = {(3/2)ⁿ}` is not eventually periodic — a periodic carry word forces
`x` itself to cycle, since `2x_{n+1} = 3xₙ − sₙ` determines the orbit from one point and the word. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem carry_not_eventually_periodic :
    ¬ ∃ N p, 0 < p ∧ ∀ n, N ≤ n → carry (n + p) = carry n := by
  rintro ⟨N, p, hp, hper⟩
  set a := max N 2 with ha
  set c := a + p with hc
  have ha2 : 2 ≤ a := le_max_right N 2
  have hac : a < c := by omega
  have hrep : ∀ k, IsCarryRepetition a c k := by
    intro k i _
    have hci : c + i = (a + i) + p := by omega
    rw [hci, hper (a + i) (by have := le_max_left N 2; omega)]
  have hbound := carry_repetition_pow_le_nat ha2 hac (hrep (3 ^ c))
  have hlt : (3 : ℕ) ^ c < 2 ^ (3 ^ c) := Nat.lt_two_pow_self
  have hmono : (2 : ℕ) ^ (3 ^ c) ≤ 2 ^ (3 ^ c + c) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## 3. The free sojourn cap (T4) -/

/-- The carry word is `p`-periodic on the block of dates `[n, n+L)`. -/
def IsPeriodicBlock (n L p : ℕ) : Prop := ∀ i, i + p < L → carry (n + i) = carry (n + p + i)

/-- **T4 — the free sojourn cap, integer form.**  A `p`-periodic block of the carry word of
length `L` starting at date `n ≥ 2` obeys `2^(L+n) ≤ 3^(n+p)`.  Unconditional: no repulsion
hypothesis, no shadowing, no band, no multiplier. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem free_sojourn_cap {n L p : ℕ} (hn : 2 ≤ n) (hp : 1 ≤ p) (hpL : p ≤ L)
    (h : IsPeriodicBlock n L p) : (2 : ℤ) ^ (L + n) ≤ 3 ^ (n + p) := by
  have hrep : IsCarryRepetition n (n + p) (L - p) := fun i hi => h i (by omega)
  have hceil := carry_repetition_pow_le hn (by omega) hrep
  have hexp : (L - p) + (n + p) = L + n := by omega
  rwa [hexp] at hceil

/-- **T4 — the free sojourn cap, logarithmic form.**  `L ≤ log₂(3/2)·n + log₂3·p`, with
`log₂(3/2) = 0.5849625…` the free slope `κ_free` and `log₂3 = 1.5849625…`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem free_sojourn_cap_logb {n L p : ℕ} (hn : 2 ≤ n) (hp : 1 ≤ p) (hpL : p ≤ L)
    (h : IsPeriodicBlock n L p) :
    (L : ℝ) ≤ Real.logb 2 (3 / 2) * n + Real.logb 2 3 * p := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcapR : ((2 : ℝ)) ^ (L + n) ≤ (3 : ℝ) ^ (n + p) := by
    exact_mod_cast free_sojourn_cap hn hp hpL h
  have hlog : ((L : ℝ) + n) * Real.log 2 ≤ ((n : ℝ) + p) * Real.log 3 := by
    have h1 : Real.log ((2 : ℝ) ^ (L + n)) ≤ Real.log ((3 : ℝ) ^ (n + p)) :=
      Real.log_le_log (by positivity) hcapR
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  have key : (L : ℝ) + n
      ≤ (n : ℝ) * (Real.log 3 / Real.log 2) + (p : ℝ) * (Real.log 3 / Real.log 2) := by
    have hrw : (n : ℝ) * (Real.log 3 / Real.log 2) + (p : ℝ) * (Real.log 3 / Real.log 2)
        = (((n : ℝ) + p) * Real.log 3) / Real.log 2 := by
      field_simp
    rw [hrw, le_div_iff₀ hl2]
    linarith
  have hl2' : Real.log 2 ≠ 0 := ne_of_gt hl2
  have hsplit : Real.logb 2 (3 / 2) = Real.log 3 / Real.log 2 - 1 := by
    have hd : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    simp only [Real.logb, hd]
    field_simp
  have hlogb3 : Real.logb 2 3 = Real.log 3 / Real.log 2 := by simp only [Real.logb]
  rw [hsplit, hlogb3]
  linarith

/-! ## 4. κ-discipline: where the free slope sits (T5) -/

/-- **T5 — the free slope is below the threshold.**  `κ_free = log₂(3/2) < 1`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem free_kappa_lt_one : Real.logb 2 (3 / 2) < 1 := by
  simp only [Real.logb]
  rw [div_lt_one (Real.log_pos (by norm_num))]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- `θ* = exp(−log²(3/2)/log 2) = 0.7888478…`: the repulsion rate whose sojourn slope
`TShift.kappa` equals the free slope. -/
noncomputable def thetaFree : ℝ := Real.exp (-(Real.log (3 / 2)) ^ 2 / Real.log 2)

@[category API, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem thetaFree_pos : 0 < thetaFree := Real.exp_pos _

/-- The free rung, in the `κ` API of `TShift.Basic`: `κ(θ*) = log₂(3/2)`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem kappa_thetaFree : kappa thetaFree = Real.logb 2 (3 / 2) := by
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hl32 : Real.log (3 / 2 : ℝ) ≠ 0 := ne_of_gt log_three_halves_pos
  simp only [kappa, thetaFree, Real.log_exp, Real.logb]
  field_simp

/-- **The equivalence that makes the free rung visible.**  For sojourn purposes the free carry-word
ceiling is worth exactly as much as exponential repulsion at rate `θ* > 2/3` — the regime the
report's §1.5 declares unavailable.  It is *not* a repulsion bound: no per-`n` floor is claimed
here, only the same sojourn slope. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem two_thirds_lt_thetaFree : (2 : ℝ) / 3 < thetaFree :=
  (kappa_lt_one_iff thetaFree_pos).mp (by rw [kappa_thetaFree]; exact free_kappa_lt_one)

/-! ## 5. The payoff: every dyadic block of dates carries a visit (T6) -/

/-- **T6 (a) — the escape recursion.**  A sojourn of length `≤ κ_free·n + C` starting at the
escape date `e k` puts the next escape date at `e (k+1) ≤ (1+κ_free)·e k + C`, and then the escape
dates stay below a geometric sequence of ratio `1 + κ_free = 1.5849625…`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem escape_ratio {C : ℝ} {e : ℕ → ℝ}
    (he : ∀ k, e (k + 1) ≤ (1 + Real.logb 2 (3 / 2)) * e k + C) (k : ℕ) :
    e k + C / Real.logb 2 (3 / 2)
      ≤ (1 + Real.logb 2 (3 / 2)) ^ k * (e 0 + C / Real.logb 2 (3 / 2)) := by
  have hpos : 0 < Real.logb 2 (3 / 2) := Real.logb_pos (by norm_num) (by norm_num)
  have hq : (1 : ℝ) < 1 + Real.logb 2 (3 / 2) := by linarith
  have h := geometric_bound hq he k
  rwa [show 1 + Real.logb 2 (3 / 2) - 1 = Real.logb 2 (3 / 2) by ring] at h

/-- **T6 (b) — the dyadic step.**  Because `1 + κ_free < 2`, the escape recursion gives
`e (k+1) < 2·e k` from the point where the date exceeds `C/(1 − κ_free)`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem escape_lt_two_mul {C a b : ℝ} (hab : b ≤ (1 + Real.logb 2 (3 / 2)) * a + C)
    (ha : C / (1 - Real.logb 2 (3 / 2)) < a) : b < 2 * a := by
  refine lt_two_mul_of_lt_two ?_ hab ?_
  · have := free_kappa_lt_one
    linarith
  · rwa [show 2 - (1 + Real.logb 2 (3 / 2)) = 1 - Real.logb 2 (3 / 2) by ring]

/-- **T6 (c) — the advertised payoff, machine-checked.**  An increasing, unbounded sequence of
escape dates whose consecutive ratio is `< 2` from `k₀` on meets **every** dyadic block
`[2^m, 2^{m+1})` above the starting scale.  With `e (k+1) < 2·e k` supplied by
`escape_lt_two_mul`, this is what `κ_free < 1` buys: `2.1713·ln N` visits by time `N`. -/
@[category research solved, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem dyadic_block_visit {e : ℕ → ℝ} {k₀ m : ℕ} (hmono : StrictMono e)
    (hstep : ∀ k, k₀ ≤ k → e (k + 1) < 2 * e k) (hunb : ∀ M : ℝ, ∃ k, M ≤ e k)
    (hm : e k₀ ≤ 2 ^ m) :
    ∃ k, (2 : ℝ) ^ m ≤ e k ∧ e k < 2 ^ (m + 1) := by
  classical
  have hex : ∃ k, (2 : ℝ) ^ m ≤ e k := hunb _
  have hspec : (2 : ℝ) ^ m ≤ e (Nat.find hex) := Nat.find_spec hex
  refine ⟨Nat.find hex, hspec, ?_⟩
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hdouble : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have hk0 : k₀ ≤ Nat.find hex := by
    by_contra hcon
    push Not at hcon
    exact absurd hspec (not_le.mpr (lt_of_lt_of_le (hmono hcon) hm))
  rcases Nat.lt_or_ge k₀ (Nat.find hex) with hlt | hge
  · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hjmin : ¬ ((2 : ℝ) ^ m ≤ e j) := Nat.find_min hex (by omega)
    have hjlt : e j < 2 ^ m := not_le.mp hjmin
    have hs := hstep j (by omega)
    rw [← hj] at hs
    rw [hdouble]
    linarith
  · have heq : Nat.find hex = k₀ := by omega
    rw [heq, hdouble]
    have : e k₀ = 2 ^ m := le_antisymm hm (heq ▸ hspec)
    linarith

/-! ## 6. Sanity (T8) -/

private lemma round_eq_of_bounds {x : ℝ} {z : ℤ} (h1 : (z : ℝ) - 1 / 2 ≤ x)
    (h2 : x < (z : ℝ) + 1 / 2) : round x = z := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

/-- The floor carry word starts `−1, 1, 0, 1, −1`, matching `TShift/tshift_numerics.py` and the
alphabet `TShift.carry_mem`.  (The *round* word starts `1, −2, 0, 1, 1` — `TH.t_sanity`; the two
words differ already at date 0.) -/
@[category test, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem carry_sanity :
    carry 0 = -1 ∧ carry 1 = 1 ∧ carry 2 = 0 ∧ carry 3 = 1 ∧ carry 4 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [carry, intPart_eq]

/-- **T8 — closed instance at the period-2 multiplier `D₂ = 3² − 2² = 5`**: the nearest integers
to `5·(3/2)ⁿ` for `n ≤ 4` are `5, 8, 11, 17, 25`.  Note `2·m₁ = 16 ≠ 15 = 3·m₀`, so no cascade
step fires at `n = 0`: `|δ₁| = 1/2 ≥ 1/5`. -/
@[category test, AMS 11 37, ref "TshiftS11", group "tshift_s11"]
theorem sojourn_sanity :
    mD 5 0 = 5 ∧ mD 5 1 = 8 ∧ mD 5 2 = 11 ∧ mD 5 3 = 17 ∧ mD 5 4 = 25 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · unfold mD
      refine round_eq_of_bounds ?_ ?_ <;> norm_num

end TShift
