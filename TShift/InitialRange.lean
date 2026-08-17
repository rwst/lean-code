/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.HabsiegerTransfer
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The initial range of Theorem A, in the kernel

`TShift/HabsiegerTransfer.lean` proves `‖D·(3/2)^k‖ ≥ (0.57434)^k` from `k ≥ 64 440 001` on.
Below that date the transported chain says nothing, and [Hab03] itself covers its own initial
range `5 ≤ k < 64 440 000` by a PARI computation on binary digit runs of `3^k` (its Lemma 2),
which is outside the corpus.  This file does the same job for the *transported* statement, at the
plan's multiplier `D = 5` and at `D = 1`, in the kernel and with no computation outside it.

## The criterion

`‖D·(3/2)^k‖` is exactly `m_k / 2^k` with `m_k = min(R, 2^k − R)` and `R = D·3^k mod 2^k`
(`TShift.distToNearestInt_eq_windowMin`), and Habsieger's threshold is
`2^{-0.8k} = 2^{k/5}/2^k`.  Clearing the fifth root turns the whole question into a statement
about naturals:

`‖D·(3/2)^k‖ > 2^{-0.8k}` ⟺ `m_k^5 > 2^k`,

which is a comparison of two `k`-bit numbers and nothing else — no `ℚ`, no `ℝ`, no `Real.rpow`,
no `decide` on anything but `ℕ`.  The rate the corpus states is `thetaHab = 0.57434`, and
`thetaHab^5 = 0.062495… < 1/16` (`TShift.thetaHab_pow_five_le`), so the same integer test
delivers `thetaHab^k ≤ ‖D·(3/2)^k‖` — the identical conclusion to
`TShift.le_distToNearestInt_habsieger`, at dates it does not reach.

For odd `D` and `k ≥ 1` the residue `R` is odd, hence so is `m_k` (`TShift.windowMin_odd`), so
`m_k^5 = 2^k` cannot happen and the non-strict test used here is the strict one.

## The certificate

`TShift.sweepFrom T M f` runs the test at `f` consecutive dates from the accumulators
`T = D·3^k`, `M = 2^k`, stepping `T ↦ 3T`, `M ↦ 2M`.  One `rfl` per multiplier discharges
20 000 dates; `TShift.sweep_spec` turns it back into a statement about every date in the range.

The kernel evaluates the accumulators, so no numeral of the certificate appears in the source —
`sweepFrom (5*3^6) (2^6) 20000` is nine characters of data, not a 6 000-digit table.  That is the
whole reason this is affordable: the alternative, a list of witnesses, would be some 60 MB.

## What is covered, and what is not

At `D = 5` the exceptional set is *exactly* `{1,2,3,5}` (`TShift.thetaHab_pow_le_five_iff`), so
Theorem A at `D = 5` starts at `k_min = 6`; at `D = 1` it is `{1,2,4}`, which is exactly the
range `k ≥ 5` of [Hab03] Theorem 2 — so this file also reproves, in the kernel, the initial-range
half of the source's own theorem on `[5, 20004]`.

The dates `20006 ≤ k ≤ 64 440 000` are **not** covered here.  They are covered by the engine of
`plan-Tshift-S1` WP5(a) — `python3 TShift/tshift_numerics.py s1 64440001`, a sliding-register
sweep in which every date is either certified with an explicit error bound or settled by an exact
modpow — but that is a computation outside the kernel, and `TShift.le_dist_five_two_ranges` below
states only what the kernel checks.

## The record lows (report-Tshift.html N5)

`TShift.recSweep` certifies that a date is a *record low* of `‖D·(3/2)^k‖`, and the four
certificates below turn N5's PARI observation — that `n = 3328` and `n = 12429` are record dates
simultaneously at `D = 1` and `D = 5` — into kernel-checked facts.  This is the numeric half of
N1's claim that the record dates inherit from `D = 1`.
-/

namespace TShift

set_option maxRecDepth 400000
set_option exponentiation.threshold 20000

/-! ## 1. The window -/

/-- The residue that measures `‖D·(3/2)^k‖`: `R = D·3^k mod 2^k`. -/
def windowRem (D k : ℕ) : ℕ := D * 3 ^ k % 2 ^ k

/-- The numerator of `‖D·(3/2)^k‖ = m_k/2^k`: `m_k = min(R, 2^k − R)`. -/
def windowMin (D k : ℕ) : ℕ := min (windowRem D k) (2 ^ k - windowRem D k)

/-- **The window identity.**  `‖D·(3/2)^k‖ = m_k / 2^k` exactly, with `m_k` a natural number.
This is `distToNearestInt_natCast_div` at `D·3^k / 2^k`, and it is the only place where the real
statement and the integer certificate meet. -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem distToNearestInt_eq_windowMin (D k : ℕ) :
    distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) = (windowMin D k : ℝ) / 2 ^ k := by
  have hd : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hrw : (D : ℝ) * ((3 : ℝ) / 2) ^ k = ((D * 3 ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
    push_cast
    rw [div_pow]
    ring
  rw [hrw, distToNearestInt_natCast_div _ _ hd]
  congr 1
  push_cast
  ring

/-- For odd `D` and `k ≥ 1` the window numerator is odd — so `m_k^5 = 2^k` is impossible and the
non-strict test of `le_distToNearestInt_of_window` is the strict one. -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem windowMin_odd {D : ℕ} (hD : Odd D) {k : ℕ} (hk : 1 ≤ k) : Odd (windowMin D k) := by
  have hd : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hmod2 : (D * 3 ^ k) % 2 = 1 := by
    have h1 : D % 2 = 1 := Nat.odd_iff.mp hD
    have h2 : (3 ^ k) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    rw [Nat.mul_mod, h1, h2]
  have hlink : (D * 3 ^ k) % 2 ^ k % 2 = (D * 3 ^ k) % 2 :=
    Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))
  have hlt : (D * 3 ^ k) % 2 ^ k < 2 ^ k := Nat.mod_lt _ hd
  have he : 2 ^ k % 2 = 0 := by
    have : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    omega
  rw [Nat.odd_iff, windowMin, windowRem]
  omega

/-! ## 2. The bridge to `thetaHab` -/

/-- `0.57434^5 = 0.062495… ≤ 1/16`.  This single inequality is what lets the integer test
`m_k^5 > 2^k` — which is Habsieger's `2^{-0.8k}` — deliver the corpus rate `thetaHab`. -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem thetaHab_pow_five_le : thetaHab ^ 5 ≤ 1 / 16 := by
  rw [thetaHab]
  norm_num

/-- **The bridge.**  The integer test at one date gives the real bound at that date. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem le_distToNearestInt_of_window {D k : ℕ} (h : 2 ^ k ≤ windowMin D k ^ 5) :
    thetaHab ^ k ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) := by
  have hw : ((2 : ℝ)) ^ k ≤ ((windowMin D k : ℕ) : ℝ) ^ 5 := by
    have h' := (Nat.cast_le (α := ℝ)).2 h
    push_cast at h'
    exact h'
  have hθ0 : (0 : ℝ) ≤ thetaHab := le_of_lt thetaHab_pos
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hb : (thetaHab * 2) ^ 5 ≤ 2 := by
    have h5 := thetaHab_pow_five_le
    have hid : (thetaHab * 2) ^ 5 = thetaHab ^ 5 * 32 := by ring
    rw [hid]
    linarith
  rw [distToNearestInt_eq_windowMin, le_div_iff₀ hpos, ← mul_pow]
  refine le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (Nat.cast_nonneg _) ?_
  calc ((thetaHab * 2) ^ k) ^ 5 = ((thetaHab * 2) ^ 5) ^ k := by
        rw [← pow_mul, ← pow_mul, mul_comm k 5]
    _ ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hb k
    _ ≤ ((windowMin D k : ℕ) : ℝ) ^ 5 := hw

/-! ## 3. The sweep -/

/-- The window test at one date, carried on the two accumulators `T = D·3^k` and `M = 2^k`. -/
def windowOk (T M : ℕ) : Bool := M ≤ (min (T % M) (M - T % M)) ^ 5

/-- `sweepFrom T M f`: the window test at each of the `f` consecutive dates starting from the one
described by `(T, M) = (D·3^k, 2^k)`.  Structural in the fuel, so the kernel evaluates it. -/
def sweepFrom : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => true
  | T, M, (f + 1) => windowOk T M && sweepFrom (3 * T) (2 * M) f

@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem windowOk_iff (D k : ℕ) :
    windowOk (D * 3 ^ k) (2 ^ k) = true ↔ 2 ^ k ≤ windowMin D k ^ 5 := by
  simp [windowOk, windowMin, windowRem]

/-- **The certificate reader.**  A sweep of length `f` from date `k` is the window bound at every
date of `[k, k+f)`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem sweep_spec {D : ℕ} :
    ∀ (f k : ℕ), sweepFrom (D * 3 ^ k) (2 ^ k) f = true →
      ∀ j, j < f → 2 ^ (k + j) ≤ windowMin D (k + j) ^ 5 := by
  intro f
  induction f with
  | zero => intro k _ j hj; omega
  | succ f ih =>
      intro k h j hj
      rw [sweepFrom, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have h3 : 3 * (D * 3 ^ k) = D * 3 ^ (k + 1) := by ring
      have h4 : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      rw [h3, h4] at h2
      match j with
      | 0 => simpa using (windowOk_iff D k).1 h1
      | (i + 1) =>
          have hstep := ih (k + 1) h2 i (by omega)
          have he : k + 1 + i = k + (i + 1) := by omega
          rwa [he] at hstep

/-- The window bound at every date of `[k, k+f)`, in real form. -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem le_dist_of_sweep {D f k : ℕ} (h : sweepFrom (D * 3 ^ k) (2 ^ k) f = true)
    {n : ℕ} (hn : k ≤ n) (hn' : n < k + f) :
    thetaHab ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := by
  have hw := sweep_spec f k h (n - k) (by omega)
  rw [show k + (n - k) = n by omega] at hw
  exact le_distToNearestInt_of_window hw

/-! ## 4. The two certificates -/

/-- **The certificate at `D = 5`**: 20 000 dates from `k = 6`, checked by the kernel. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem sweep_five : sweepFrom (5 * 3 ^ 6) (2 ^ 6) 20000 = true := by rfl

/-- **The certificate at `D = 1`**: 20 000 dates from `k = 5`, checked by the kernel.  This is the
initial-range half of [Hab03] Theorem 2 itself, on `[5, 20004]`. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem sweep_one : sweepFrom (1 * 3 ^ 5) (2 ^ 5) 20000 = true := by rfl

/-! ## 5. What the certificates say -/

/-- **Theorem A at `D = 5`, on the initial range.**  `‖5·(3/2)^k‖ ≥ (0.57434)^k` for every
`6 ≤ k ≤ 20 005`. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem le_dist_five_initial {k : ℕ} (h6 : 6 ≤ k) (hk : k ≤ 20005) :
    thetaHab ^ k ≤ distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ k) := by
  have h := le_dist_of_sweep (D := 5) (f := 20000) (k := 6) sweep_five h6 (by omega)
  simpa using h

/-- **[Hab03] Theorem 2 on its own initial range**, kernel-checked: `‖(3/2)^k‖ ≥ (0.57434)^k`
for every `5 ≤ k ≤ 20 004`. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem le_dist_one_initial {k : ℕ} (h5 : 5 ≤ k) (hk : k ≤ 20004) :
    thetaHab ^ k ≤ distToNearestInt (((3 : ℝ) / 2) ^ k) := by
  have h := le_dist_of_sweep (D := 1) (f := 20000) (k := 5) sweep_one h5 (by omega)
  simpa using h

/-- The four exceptional dates at `D = 5`: the bound *fails* at `k = 1, 2, 3, 5`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem dist_lt_thetaHab_pow_five {k : ℕ} (h : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5) :
    distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ k) < thetaHab ^ k := by
  have hval : ∀ n : ℕ, distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ n)
      = (windowMin 5 n : ℝ) / 2 ^ n := by
    intro n
    have := distToNearestInt_eq_windowMin 5 n
    simpa using this
  rcases h with rfl | rfl | rfl | rfl
  · rw [hval, show windowMin 5 1 = 1 from by decide, thetaHab]; norm_num
  · rw [hval, show windowMin 5 2 = 1 from by decide, thetaHab]; norm_num
  · rw [hval, show windowMin 5 3 = 1 from by decide, thetaHab]; norm_num
  · rw [hval, show windowMin 5 5 = 1 from by decide, thetaHab]; norm_num

/-- **The initial range at `D = 5` is sharp.**  On `1 ≤ k ≤ 20 005` the transported bound holds
at exactly the dates outside `{1,2,3,5}` — so `k_min(5) = 6`, against `k_min(1) = 5` for the
source's own theorem.  (`k = 4` passes: `m_4 = 5` and `5^5 = 3125 > 16`.) -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem thetaHab_pow_le_five_iff {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 20005) :
    thetaHab ^ k ≤ distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ k) ↔
      ¬ (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5) := by
  constructor
  · intro hle hexc
    exact absurd hle (not_le.2 (dist_lt_thetaHab_pow_five hexc))
  · intro hne
    rcases lt_or_ge k 6 with hlt | hge
    · have h4 : k = 4 := by omega
      subst h4
      have : (2 : ℕ) ^ 4 ≤ windowMin 5 4 ^ 5 := by decide
      simpa using le_distToNearestInt_of_window (D := 5) this
    · exact le_dist_five_initial hge hk'

/-- **Both ranges of the machine-checked statement at `D = 5`.**  The rate `0.57434` now holds on
`[6, 20005]` by this file's certificate and on `[64440001, ∞)` by
`TShift.le_distToNearestInt_habsieger`.  The dates in between are the engine range of
`plan-Tshift-S1` WP5(a) and are deliberately *not* claimed here. -/
@[category research solved, AMS 11, ref "Hab03" "TshiftS1", group "tshift_s1"]
theorem le_dist_five_two_ranges {k : ℕ} (h : (6 ≤ k ∧ k ≤ 20005) ∨ kHab ≤ k) :
    thetaHab ^ k ≤ distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ k) := by
  rcases h with ⟨h6, h20⟩ | hk
  · exact le_dist_five_initial h6 h20
  · have := le_distToNearestInt_habsieger (D := 5) (by norm_num) (by rw [dHab]; norm_num) hk
    simpa using this

/-! ## 6. The record lows of report-Tshift.html N5 -/

/-- The record test at one date: `a/E < m_j/M`, i.e. the candidate value `a/E` beats the value at
the date carried by `(T, M)`. -/
def recOk (a E T M : ℕ) : Bool := a * M < (min (T % M) (M - T % M)) * E

/-- `recSweep a E T M f`: the candidate value `a/E` beats each of the `f` consecutive dates from
the one described by `(T, M)`. -/
def recSweep (a E : ℕ) : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => true
  | T, M, (f + 1) => recOk a E T M && recSweep a E (3 * T) (2 * M) f

@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem recOk_iff (a E D k : ℕ) :
    recOk a E (D * 3 ^ k) (2 ^ k) = true ↔ a * 2 ^ k < windowMin D k * E := by
  simp [recOk, windowMin, windowRem]

@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem recSweep_spec {D a E : ℕ} :
    ∀ (f k : ℕ), recSweep a E (D * 3 ^ k) (2 ^ k) f = true →
      ∀ j, j < f → a * 2 ^ (k + j) < windowMin D (k + j) * E := by
  intro f
  induction f with
  | zero => intro k _ j hj; omega
  | succ f ih =>
      intro k h j hj
      rw [recSweep, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have h3 : 3 * (D * 3 ^ k) = D * 3 ^ (k + 1) := by ring
      have h4 : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      rw [h3, h4] at h2
      match j with
      | 0 => simpa using (recOk_iff a E D k).1 h1
      | (i + 1) =>
          have hstep := ih (k + 1) h2 i (by omega)
          have he : k + 1 + i = k + (i + 1) := by omega
          rwa [he] at hstep

/-- Comparison of two dates, in real form. -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem dist_lt_dist_of_window {D m n : ℕ} (h : windowMin D n * 2 ^ m < windowMin D m * 2 ^ n) :
    distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n)
      < distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ m) := by
  have hR : ((windowMin D n * 2 ^ m : ℕ) : ℝ) < ((windowMin D m * 2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hR
  rw [distToNearestInt_eq_windowMin, distToNearestInt_eq_windowMin,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  exact hR

/-- A record certificate read back: date `n` is a record low over `[1, n)`. -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem isRecord_of_recSweep {D n : ℕ} (hn : 1 ≤ n)
    (h : recSweep (windowMin D n) (2 ^ n) (D * 3 ^ 1) (2 ^ 1) (n - 1) = true) :
    ∀ j, 1 ≤ j → j < n →
      distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n)
        < distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ j) := by
  intro j hj hjn
  have hw := recSweep_spec (D := D) (a := windowMin D n) (E := 2 ^ n) (n - 1) 1 h (j - 1)
    (by omega)
  rw [show 1 + (j - 1) = j by omega] at hw
  exact dist_lt_dist_of_window hw

/-- N5's first simultaneous record date, at `D = 1`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem recSweep_one_3328 :
    recSweep (windowMin 1 3328) (2 ^ 3328) (1 * 3 ^ 1) (2 ^ 1) 3327 = true := by rfl

/-- N5's first simultaneous record date, at `D = 5`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem recSweep_five_3328 :
    recSweep (windowMin 5 3328) (2 ^ 3328) (5 * 3 ^ 1) (2 ^ 1) 3327 = true := by rfl

/-- N5's second simultaneous record date, at `D = 1`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem recSweep_one_12429 :
    recSweep (windowMin 1 12429) (2 ^ 12429) (1 * 3 ^ 1) (2 ^ 1) 12428 = true := by rfl

/-- N5's second simultaneous record date, at `D = 5`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem recSweep_five_12429 :
    recSweep (windowMin 5 12429) (2 ^ 12429) (5 * 3 ^ 1) (2 ^ 1) 12428 = true := by rfl

/-- **N5, kernel-checked.**  `n = 3328` and `n = 12429` are record lows of `‖D·(3/2)^n‖` at
`D = 1` *and* at `D = 5` — the numerical content of N1's claim that the record dates inherit from
the classical problem.  Previously these were PARI output quoted in the report. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem record_dates_simultaneous :
    (∀ j, 1 ≤ j → j < 3328 →
        distToNearestInt (((3 : ℝ) / 2) ^ 3328) < distToNearestInt (((3 : ℝ) / 2) ^ j)) ∧
      (∀ j, 1 ≤ j → j < 3328 →
        distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ 3328)
          < distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ j)) ∧
      (∀ j, 1 ≤ j → j < 12429 →
        distToNearestInt (((3 : ℝ) / 2) ^ 12429) < distToNearestInt (((3 : ℝ) / 2) ^ j)) ∧
      (∀ j, 1 ≤ j → j < 12429 →
        distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ 12429)
          < distToNearestInt ((5 : ℝ) * ((3 : ℝ) / 2) ^ j)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj hjn
    have := isRecord_of_recSweep (D := 1) (n := 3328) (by norm_num) recSweep_one_3328 j hj hjn
    simpa using this
  · intro j hj hjn
    have := isRecord_of_recSweep (D := 5) (n := 3328) (by norm_num) recSweep_five_3328 j hj hjn
    simpa using this
  · intro j hj hjn
    have := isRecord_of_recSweep (D := 1) (n := 12429) (by norm_num) recSweep_one_12429 j hj hjn
    simpa using this
  · intro j hj hjn
    have := isRecord_of_recSweep (D := 5) (n := 12429) (by norm_num) recSweep_five_12429 j hj hjn
    simpa using this

/-! ## 7. Sanity -/

/-- The certificate is not vacuous: at `k = 6` the bound is `0.046875 ≥ 0.035897…`, a margin of
`31%`, and at the last certified date the window numerator is a genuine `20 005`-bit datum.  The
orientation check is `k = 5`, where the test *fails* and the file says so. -/
@[category API, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem initial_range_sanity :
    windowMin 5 6 = 3 ∧ windowMin 5 5 = 1 ∧ windowMin 5 4 = 5 ∧
      (2 : ℕ) ^ 6 ≤ windowMin 5 6 ^ 5 ∧ ¬ ((2 : ℕ) ^ 5 ≤ windowMin 5 5 ^ 5) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end TShift
