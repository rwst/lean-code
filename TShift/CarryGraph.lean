/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.FreeSojourn
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The carry graph at the period-2 cycle: forcing, phase, and escape

Report `report-Tshift.html` S13 Idea (iii) asks for "the region `U` on which the symbolic dynamics
is forced eventually 2-periodic after a bounded burn-in".  This file supplies it at the smallest
cycle denominator `D₂ = 3² − 2² = 5`, whose four cycle points

  `T = {1/5, 4/5}` with carry word `(−1, 2)`,   `T = {2/5, 3/5}` with carry word `(0, 1)`

are the targets of `TShift.affine_fixedPoint` at `p = 2`.  The region is
`U_δ = ⋃_{a=1}^{4} {x : |x − a/5| < δ}` at `δ = 1/32` (`InU`), and the burn-in is `0`.

## What is actually true, and what the report's sentence says

At **every** real point exactly two carries are admissible — `⌊3x⌋` and `⌊3x⌋ − 1`
(`admissible_iff`, `admissible_ncard`) — so *no* nonempty region forces the next digit of a point
and the literal reading of S13 (iii) is vacuous.  What holds, and what the report's §1.5 actually
consumes, is **conditional on the orbit staying in `U`**:

  `forcing` — if `|xₙ − a/5| < δ` and `x_{n+1} ∈ U_δ`, then the carry taken is the cycle digit
  `a − 2`, the next point is within `δ` of the *successor* target `(5−a)/5` — the phase is forced
  too — and `|x_{n+1} − (5−a)/5| = (3/2)·|xₙ − a/5|` exactly.

The wrong branch ejects the point: both branches are affine with slope `3/2`, the wrong image of
a target is an odd multiple of `1/10` and therefore at distance exactly `1/10` from `T`
(`tenth_dist`), and `1/10 − (3/2)δ = 17/320 > δ` at `δ = 1/32`.  Forcing holds at every `δ < 1/25`;
`1/32` is the dyadic value chosen for the slack, `7/320`.  The phase is pinned because distinct
targets are `1/5` apart (`tgt_sep`) and `(5/2)δ = 5/64 < 1/5`.

Iterating (`sojourn_chain`) gives both halves at once: along a sojourn the carry word **is** the
cycle word in the correct phase (`sojourn_carry`), so the word is 2-periodic on the block
(`sojourn_isPeriodicBlock`), and the deviation shrinks backwards by `2/3` per step
(`sojourn_shadow`).  No separate appeal to a shadowing lemma is needed.

## The cap, and where its slope comes from

`sojourn_isPeriodicBlock` hands the block straight to `TShift.free_sojourn_cap`
(`TShift/FreeSojourn.lean`, correction **C20**), which caps any `p`-periodic block of the *same*
carry word without any Diophantine input.  At `p = 2`:

  `L − 1 ≤ log₂(3/2)·n + 2·log₂3 = 0.5849625·n + 3.169925`   (`sojourn_cap_free`)

with `κ_free = log₂(3/2) < 1`.  The `−1` is `IsPeriodicBlock`'s index: the last digit of a sojourn
is not forced, because forcing needs the *next* point to be in `U` as well.

This is the slope the plan `plans/plan-Tshift-S1314.html` did not have when it was written (WP0
finding F6, `plans/note-Tshift-S1314-WP0.html` §2).  Its own route — the 2-adic floor
`Z32.dist_odd_denom` at `D = 5` against the shadow bound, i.e. `TShift.sojourn_cap_kappa` at
`θ = 1/2` — is kept here as `sojourn_cap_half`:

  `L − 1 ≤ κ(1/2)·n + log(5/32)/log(3/2) = 1.7095113·n − 4.578`,

and it is the sharper of the two only for integer `n ≤ 6` — the caps cross at `n = 6.8900`, they
tie at `n = 7` (both give `L ≤ 8`), and at `n ≤ 6` the bound is `L ≤ 6` regardless.
Asymptotically the floor route is weaker by the factor `κ(1/2)/κ_free = 2.9224 = 1/κ_free²`, and
`κ_free = 1/κ(1/2)` **exactly**: both arguments oppose the same two quantities in opposite roles.
The floor route spends the dyadic information on a per-`n` floor `1/(5·2ⁿ)` against `(2/3)^L`; the
free route spends it on `2^L ∣ m_{n+2} − m_n` against `(3/2)^{n+2}`, so there the `2`-power scales
with the *length* and the slope inverts.

The same reciprocity retires the transferred-rate variant the plan called Theorem A′: at S1's
`θ_Hab = 0.57434` the sojourn slope is `κ(θ_Hab) = 1.3676 > 1` (`TShift.one_le_kappa_thetaHab`),
`2.34×` the free slope, so a file on the [Hab03] lane would carry a *weaker* capstone than one of
the `std3` theorems it imports.  What the transferred rate buys is the per-`n` **floor**, a
different currency, already formalized in `TShift/HabsiegerTransfer.lean`.

## The payoff

`exists_escape_dyadic`: **every** dyadic block of dates `[2^m, 2^{m+1})` with `m ≥ 4` contains a
date at which the orbit is outside `U_{1/32}`.  The proof is direct — a full block would be a
sojourn of length `2^m` at date `2^m`, and `2^m(1 − κ_free) ≤ 3 + 2κ_free` forces `2^m ≤ 10.05` —
so the burn-in `j₀ = 4` is explicit and no escape-date sequence is needed for it.  The count
follows the recursion currency instead: the enumerated escape dates (`escapeSeq`) satisfy

  `e_{k+1} ≤ (1 + κ_free)·e_k + (κ_free + 2 + 2 log₂3)`   (`escapeSeq_recursion`),

so `TShift.escape_ratio` (C20's T6 (a), first consumed here) puts `e_k` below a geometric sequence
of ratio `1 + κ_free = 1.5849625` — i.e. at least `ln N/ln(1.5849625) = 2.1713·ln N` escape dates
by time `N`.  `escape_card` states the weaker but self-contained block count, `M − 4` escapes below
`2^M`.

Note that this *contradicts* the report's §1.5 remark that the dyadic-block statement is
unavailable at base `3/2`: it is available, for free, and C20 already records why.  What is new
here is not the block statement but the **transport** — Proposition B is the only bridge from the
carry word to the orbit and to a named region, and the free cap knows nothing about `U_{1/32}`,
the targets, or the phase.

## κ-discipline

`κ_free = log₂(3/2) = 0.5849625 < 1`, i.e. on the good side of `TShift.kappa_lt_one_iff`'s
threshold — but this is **not** a per-`n` floor and no instance of the T-shift problem (T0–T4) is
proven or approached here.  `sojourn_cap_half` is the only statement in the file that consumes a
floor, and its `θ = 1/2` is `Z32.dist_odd_denom`, the free 2-adic one, far below `2/3`.  No density
statement, no general-`ξ` statement, and no claim that `δ = 1/32` is the largest workable radius —
that is the question the plan's gated WP7 measures.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`, and no kernel `decide` on `ℚ` or `ℝ` — every numeric side condition is a rational
comparison discharged by `norm_num`, and the two log facts are monotonicity of `Real.log` at
`(3/2)^5 < 2^3`.

## References

* `plans/plan-Tshift-S1314.html` §1.4 (D1, D2), §2 (Proposition B, Theorem A), §3 (file map),
  WP2; `plans/note-Tshift-S1314-WP0.html` (the WP0 audit: F2, F6, and the measured forcing data —
  1 623 real forcing pairs on the orbit to `n ≤ 20 000`, zero digit, phase or identity exceptions).
* `report-Tshift.html` S13 Idea (iii), §1.5 (Lemma 3 and the payoff table), N2 (the cycle-shift
  identity), N3; correction C20 (the free rung).
* `plans/plan-Tshift-S11.html`, `plans/note-Tshift-S11-WP0.html` — `free_sojourn_cap` and the
  dyadic payoff, whose slope this file consumes.
* [GY26] X. Gao, C. H. Yip, *On the fractional parts of certain sequences of `ξαⁿ`*,
  arXiv:2408.02972v2 (23 May 2026), Theorem 1.2 — the cap in print, at every rational base.
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)ᵏ‖`*, Acta Arith. **106** (2003), 299–309
  — the transferred rate discussed above, not consumed here.
-/

namespace TShift

open Real

/-! ## 1. The cycle data at `D₂ = 5`

The four cycle points are indexed by their numerator `a ∈ {1,2,3,4}`, which makes the cycle data
polynomial in `a`: the successor of `a/5` is `(5−a)/5` and its carry digit is `a − 2`, so the two
2-cycles `(1/5, 4/5)` and `(2/5, 3/5)` with words `(−1, 2)` and `(0, 1)` need no case
analysis. -/

/-- The cycle point `ρ_a = a/5`.  For `a ∈ {1,2,3,4}` these are the four fixed points of the
period-2 branches, `TShift.affine_fixedPoint` at `p = 2` and `TShift.cycleDenom 2 = 5`. -/
noncomputable def tgt (a : ℤ) : ℝ := (a : ℝ) / 5

/-- The successor of the target `a/5` along its cycle: `a ↦ 5 − a`, i.e. `1/5 ↦ 4/5 ↦ 1/5` and
`2/5 ↦ 3/5 ↦ 2/5`. -/
def nextNum (a : ℤ) : ℤ := 5 - a

/-- The cycle digit at the target `a/5`: the unique `s` with `2·ρ_{5−a} = 3·ρ_a − s`, namely
`a − 2`.  The two cycle words are `(−1, 2)` and `(0, 1)`. -/
def cycleDigit (a : ℤ) : ℤ := a - 2

/-- The radius of the four balls, `δ = 1/32`.  Forcing needs `1/10 − (3/2)δ > δ`, i.e. `δ < 1/25`;
`1/32` is the dyadic value below that, with slack `17/320 − 1/32 = 7/320`. -/
noncomputable def delta : ℝ := 1 / 32

/-- `U_δ` as a membership predicate rather than a region (the plan-S2 R5 discipline): the union of
the four open balls of radius `δ` around the cycle points. -/
def InU (y : ℝ) : Prop := ∃ a : ℤ, 1 ≤ a ∧ a ≤ 4 ∧ |y - tgt a| < delta

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem delta_pos : (0 : ℝ) < delta := by
  simp only [delta]; norm_num

/-- **Separation.**  Distinct targets are at least `1/5` apart — this is what pins the phase in
`forcing`, since `(5/2)δ = 5/64 < 1/5`. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem tgt_sep {c d : ℤ} (h : c ≠ d) : (1 : ℝ) / 5 ≤ |tgt c - tgt d| := by
  have h1 : (1 : ℤ) ≤ |c - d| := Int.one_le_abs (by omega)
  have h1' : (1 : ℝ) ≤ |(c : ℝ) - (d : ℝ)| := by
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|c - d| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_one, Int.cast_abs, Int.cast_sub] at h2
  have hd : tgt c - tgt d = ((c : ℝ) - (d : ℝ)) / 5 := by
    simp only [tgt]; ring
  rw [hd, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5),
    le_div_iff₀ (by norm_num : (0 : ℝ) < 5)]
  linarith

/-- **The ejection geometry.**  An odd multiple of `1/10` is at distance at least `1/10` from
every target: the wrong branch of a cycle point lands exactly halfway between two consecutive
multiples of `1/5`. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem tenth_dist {c b : ℤ} (hc : Odd c) : (1 : ℝ) / 10 ≤ |(c : ℝ) / 10 - tgt b| := by
  have hne : c - 2 * b ≠ 0 := by
    obtain ⟨k, hk⟩ := hc
    omega
  have h1 : (1 : ℤ) ≤ |c - 2 * b| := Int.one_le_abs hne
  have h1' : (1 : ℝ) ≤ |(c : ℝ) - 2 * (b : ℝ)| := by
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|c - 2 * b| : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Int.cast_one, Int.cast_abs] at h2
    push_cast at h2
    exact h2
  have hd : (c : ℝ) / 10 - tgt b = ((c : ℝ) - 2 * (b : ℝ)) / 10 := by
    simp only [tgt]; ring
  rw [hd, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10),
    le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
  linarith

/-! ## 2. The admissible carries (F2) -/

/-- The carry is the integer of the half-open window `(3xₙ − 2, 3xₙ]`: this is `TShift.carry_cast`
together with `0 ≤ x_{n+1} < 1`. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem carry_window (n : ℕ) :
    3 * Z32.x n - 2 < (carry n : ℝ) ∧ (carry n : ℝ) ≤ 3 * Z32.x n := by
  have hc := carry_cast n
  have h0 : (0 : ℝ) < Z32.x (n + 1) := Z32.x_pos (by omega)
  have h1 : Z32.x (n + 1) < 1 := Z32.x_lt_one _
  constructor <;> rw [hc] <;> linarith

/-- **F2, the exact admissible set.**  At a point `y` the admissible carries are exactly `⌊3y⌋`
and `⌊3y⌋ − 1`: the window `(3y − 2, 3y]` is half-open of length `2`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem admissible_iff (y : ℝ) (s : ℤ) :
    (3 * y - 2 < (s : ℝ) ∧ (s : ℝ) ≤ 3 * y) ↔ (s = ⌊3 * y⌋ ∨ s = ⌊3 * y⌋ - 1) := by
  have hfl : ((⌊3 * y⌋ : ℤ) : ℝ) ≤ 3 * y := Int.floor_le _
  have hfl' : 3 * y - 1 < ((⌊3 * y⌋ : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one (3 * y)
    linarith
  constructor
  · rintro ⟨h1, h2⟩
    have hle : s ≤ ⌊3 * y⌋ := Int.le_floor.mpr h2
    have hgt : ((⌊3 * y⌋ : ℤ) : ℝ) - 2 < (s : ℝ) := by linarith
    have hgt' : ⌊3 * y⌋ - 2 < s := by exact_mod_cast hgt
    omega
  · rintro (rfl | h)
    · exact ⟨by linarith, hfl⟩
    · subst h
      constructor
      · push_cast; linarith
      · push_cast; linarith

/-- **F2.**  Exactly two carries are admissible at *every* real point, so no nonempty region
forces the next digit of a point: forcing can only ever be conditional on where the orbit goes
next (`forcing`). -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem admissible_ncard (y : ℝ) :
    {s : ℤ | 3 * y - 2 < (s : ℝ) ∧ (s : ℝ) ≤ 3 * y}.ncard = 2 := by
  have hset : {s : ℤ | 3 * y - 2 < (s : ℝ) ∧ (s : ℝ) ≤ 3 * y} = {⌊3 * y⌋, ⌊3 * y⌋ - 1} := by
    ext s
    simpa [Set.mem_ofPred_eq] using admissible_iff y s
  rw [hset, Set.ncard_pair (by omega)]

/-- **Digit-set constancy on the balls (D1).**  Within `δ = 1/32` of the cycle point `a/5` the
carry is within `1` of that point's cycle digit `a − 2`: only the cycle digit and one neighbour
are admissible, and which neighbour depends only on the side of `1/2` that `a/5` sits on. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem abs_carry_sub_cycleDigit_le {n : ℕ} {a : ℤ} (h1 : 1 ≤ a) (h4 : a ≤ 4)
    (hx : |Z32.x n - tgt a| < delta) : |carry n - cycleDigit a| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := carry_window n
  rw [abs_lt] at hx
  simp only [tgt, delta] at hx
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
  have ha4 : (a : ℝ) ≤ 4 := by exact_mod_cast h4
  have hup : (carry n : ℝ) < (a : ℝ) := by linarith [hx.1, hx.2]
  have hdn : (a : ℝ) - 4 < (carry n : ℝ) := by linarith [hx.1, hx.2]
  have hup' : carry n < a := by exact_mod_cast hup
  have hdn' : a - 4 < carry n := by
    have : ((a - 4 : ℤ) : ℝ) < (carry n : ℝ) := by push_cast; linarith
    exact_mod_cast this
  rw [abs_le, cycleDigit]
  omega

/-! ## 3. Proposition B: forcing, phase, and the cycle-shift identity -/

/-- **Proposition B.**  If `xₙ` is within `δ = 1/32` of the cycle point `a/5` and the next point
lies in `U_δ` at all, then

* the carry taken is the **cycle digit** `a − 2` (the wrong branch would eject the point);
* the next point is within `δ` of the **successor** target `(5−a)/5` — the phase is forced too;
* the deviation is multiplied by exactly `3/2` (report N2's cycle-shift identity).

Burn-in `0`.  This is the only bridge in the corpus from the carry word to the orbit and to a
named region; everything downstream is a consequence of iterating it. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem forcing {n : ℕ} {a : ℤ} (h1 : 1 ≤ a) (h4 : a ≤ 4)
    (hx : |Z32.x n - tgt a| < delta) (hU : InU (Z32.x (n + 1))) :
    carry n = cycleDigit a ∧
      |Z32.x (n + 1) - tgt (nextNum a)| = 3 / 2 * |Z32.x n - tgt a| ∧
      |Z32.x (n + 1) - tgt (nextNum a)| < delta := by
  obtain ⟨b, -, -, hb⟩ := hU
  have habs : |carry n - cycleDigit a| ≤ 1 := abs_carry_sub_cycleDigit_le h1 h4 hx
  set e : ℤ := carry n - cycleDigit a with he
  have hcast : (carry n : ℝ) = (e : ℝ) + (a : ℝ) - 2 := by
    have hz : carry n = e + (a - 2) := by simp only [he, cycleDigit]; omega
    rw [hz]; push_cast; ring
  -- The identity that holds whichever of the two admissible digits was taken.
  have hid : Z32.x (n + 1) - (tgt (nextNum a) - (e : ℝ) / 2) = 3 / 2 * (Z32.x n - tgt a) := by
    have hc := carry_cast n
    rw [hcast] at hc
    simp only [tgt, nextNum]
    push_cast
    linarith
  have he0 : e = 0 := by
    by_contra hne
    have hpm : e = 1 ∨ e = -1 := by rw [abs_le] at habs; omega
    have hodd : Odd (10 - 2 * a - 5 * e) := by
      rcases hpm with h | h
      · exact ⟨2 - a, by rw [h]; ring⟩
      · exact ⟨7 - a, by rw [h]; ring⟩
    have hw : tgt (nextNum a) - (e : ℝ) / 2 = ((10 - 2 * a - 5 * e : ℤ) : ℝ) / 10 := by
      simp only [tgt, nextNum]; push_cast; ring
    have hfar := tenth_dist (b := b) hodd
    rw [← hw] at hfar
    have h32 : |Z32.x (n + 1) - (tgt (nextNum a) - (e : ℝ) / 2)| = 3 / 2 * |Z32.x n - tgt a| := by
      rw [hid, abs_mul]; norm_num
    have htri : |(tgt (nextNum a) - (e : ℝ) / 2) - tgt b|
        ≤ |(tgt (nextNum a) - (e : ℝ) / 2) - Z32.x (n + 1)| + |Z32.x (n + 1) - tgt b| :=
      abs_sub_le _ _ _
    have hcomm := abs_sub_comm (tgt (nextNum a) - (e : ℝ) / 2) (Z32.x (n + 1))
    simp only [delta] at hx hb
    linarith
  have hcarry : carry n = cycleDigit a := by omega
  have hid0 : Z32.x (n + 1) - tgt (nextNum a) = 3 / 2 * (Z32.x n - tgt a) := by
    rw [he0] at hid; simpa using hid
  have habs2 : |Z32.x (n + 1) - tgt (nextNum a)| = 3 / 2 * |Z32.x n - tgt a| := by
    rw [hid0, abs_mul]; norm_num
  refine ⟨hcarry, habs2, ?_⟩
  rcases eq_or_ne b (nextNum a) with rfl | hbne
  · exact hb
  · exfalso
    have hsep := tgt_sep hbne
    have htri : |tgt b - tgt (nextNum a)|
        ≤ |tgt b - Z32.x (n + 1)| + |Z32.x (n + 1) - tgt (nextNum a)| := abs_sub_le _ _ _
    have hcomm := abs_sub_comm (tgt b) (Z32.x (n + 1))
    simp only [delta] at hx hb
    linarith

/-! ## 4. Sojourns: the phase clock, the carry word, and the shadow -/

/-- The cycle phase at offset `j` from a sojourn's entry target `a`: the involution `a ↦ 5 − a`
iterated `j` times. -/
def idxAt (a : ℤ) (j : ℕ) : ℤ := if j % 2 = 0 then a else 5 - a

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii", simp]
theorem idxAt_zero (a : ℤ) : idxAt a 0 = a := by simp [idxAt]

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem idxAt_succ (a : ℤ) (j : ℕ) : idxAt a (j + 1) = nextNum (idxAt a j) := by
  simp only [idxAt, nextNum]
  split_ifs <;> omega

/-- The phase clock has period `2` — this is what makes a sojourn a `2`-periodic block. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem idxAt_add_two (a : ℤ) (j : ℕ) : idxAt a (j + 2) = idxAt a j := by
  simp only [idxAt, Nat.add_mod_right]

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem idxAt_mem {a : ℤ} (h1 : 1 ≤ a) (h4 : a ≤ 4) (j : ℕ) :
    1 ≤ idxAt a j ∧ idxAt a j ≤ 4 := by
  simp only [idxAt]
  split_ifs <;> omega

/-- A **sojourn of length `L` at date `n`**: every date of `[n, n+L)` sits in `U_δ`. -/
def IsSojourn (n L : ℕ) : Prop := ∀ i, i < L → InU (Z32.x (n + i))

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_entry {n L : ℕ} (hL : 0 < L) (h : IsSojourn n L) :
    ∃ a : ℤ, 1 ≤ a ∧ a ≤ 4 ∧ |Z32.x n - tgt a| < delta := h 0 hL

/-- **The sojourn induction.**  Along a sojourn the orbit stays in the ball of its *current*
phase, and the deviation grows by exactly `3/2` at every step — the shadowing bound comes out of
Proposition B's iteration, with no separate appeal to `TShift.abs_sub_fixed_le`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_chain {n L : ℕ} (h : IsSojourn n L) {a : ℤ} (h1 : 1 ≤ a) (h4 : a ≤ 4)
    (hx : |Z32.x n - tgt a| < delta) :
    ∀ j, j < L → |Z32.x (n + j) - tgt (idxAt a j)| < delta ∧
      |Z32.x (n + j) - tgt (idxAt a j)| = (3 / 2 : ℝ) ^ j * |Z32.x n - tgt a| := by
  intro j
  induction j with
  | zero => intro _; simpa using hx
  | succ j ih =>
      intro hj
      obtain ⟨hlt, heq⟩ := ih (by omega)
      obtain ⟨ha1, ha4⟩ := idxAt_mem h1 h4 j
      have hshift : n + (j + 1) = n + j + 1 := by omega
      have hU : InU (Z32.x (n + j + 1)) := by
        have := h (j + 1) hj
        rwa [hshift] at this
      obtain ⟨-, heq2, hlt2⟩ := forcing ha1 ha4 hlt hU
      rw [← idxAt_succ] at heq2 hlt2
      rw [hshift]
      refine ⟨hlt2, ?_⟩
      rw [heq2, heq]
      ring

/-- Along a sojourn the carry word **is** the cycle word, in the correct phase.  The last date of
a sojourn is excluded: forcing needs the next point to be in `U` as well. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_carry {n L : ℕ} (h : IsSojourn n L) {a : ℤ} (h1 : 1 ≤ a) (h4 : a ≤ 4)
    (hx : |Z32.x n - tgt a| < delta) :
    ∀ j, j + 1 < L → carry (n + j) = cycleDigit (idxAt a j) := by
  intro j hj
  obtain ⟨hlt, -⟩ := sojourn_chain h h1 h4 hx j (by omega)
  obtain ⟨ha1, ha4⟩ := idxAt_mem h1 h4 j
  have hU : InU (Z32.x (n + j + 1)) := by
    have := h (j + 1) hj
    rwa [show n + (j + 1) = n + j + 1 from by omega] at this
  exact (forcing ha1 ha4 hlt hU).1

/-- **The corrected reading of "forced eventually 2-periodic".**  A sojourn of length `L` makes
the carry word `2`-periodic on `[n, n + L − 1)`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_isPeriodicBlock {n L : ℕ} (h : IsSojourn n L) : IsPeriodicBlock n (L - 1) 2 := by
  intro i hi
  obtain ⟨a, ha1, ha4, hxa⟩ := sojourn_entry (show 0 < L by omega) h
  have e1 : carry (n + i) = cycleDigit (idxAt a i) := sojourn_carry h ha1 ha4 hxa i (by omega)
  have e2 : carry (n + (i + 2)) = cycleDigit (idxAt a (i + 2)) :=
    sojourn_carry h ha1 ha4 hxa (i + 2) (by omega)
  rw [show n + 2 + i = n + (i + 2) from by omega, e1, e2, idxAt_add_two]

/-- **The shadow bound.**  A sojourn of length `L` entered the ball of its entry target already
within `δ·(2/3)^{L−1}`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_shadow {n L : ℕ} (hL : 0 < L) (h : IsSojourn n L) :
    ∃ a : ℤ, 1 ≤ a ∧ a ≤ 4 ∧ |Z32.x n - tgt a| < delta * (2 / 3 : ℝ) ^ (L - 1) := by
  obtain ⟨a, ha1, ha4, hxa⟩ := sojourn_entry hL h
  refine ⟨a, ha1, ha4, ?_⟩
  obtain ⟨hlt, heq⟩ := sojourn_chain h ha1 ha4 hxa (L - 1) (by omega)
  rw [heq] at hlt
  have hp : (0 : ℝ) < (3 / 2 : ℝ) ^ (L - 1) := by positivity
  have hinv : (2 / 3 : ℝ) ^ (L - 1) = ((3 / 2 : ℝ) ^ (L - 1))⁻¹ := by
    rw [← inv_pow]; norm_num
  rw [hinv, ← div_eq_mul_inv, lt_div_iff₀ hp, mul_comm]
  exact hlt

/-! ## 5. Theorem A: the cap -/

/-- **Theorem A (S13 (iii) capstone), the cap.**  Every sojourn of length `L ≥ 3` at a date
`n ≥ 2` obeys

  `L − 1 ≤ log₂(3/2)·n + 2·log₂3 = 0.5849625·n + 3.169925`.

The slope is `κ_free < 1` and is *cited*, not re-derived: `sojourn_isPeriodicBlock` hands the
block to `TShift.free_sojourn_cap` (correction C20).  What this file supplies is the transport —
Proposition B — from the carry word to the orbit and to the named region `U_{1/32}`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_cap_free {n L : ℕ} (hn : 2 ≤ n) (hL : 3 ≤ L) (h : IsSojourn n L) :
    (L : ℝ) - 1 ≤ Real.logb 2 (3 / 2) * n + 2 * Real.logb 2 3 := by
  have hcap := free_sojourn_cap_logb (n := n) (L := L - 1) (p := 2) hn (by omega) (by omega)
    (sojourn_isPeriodicBlock h)
  rw [Nat.cast_sub (by omega : 1 ≤ L)] at hcap
  push_cast at hcap
  linarith

/-- The route the plan took before C20, kept for the record: the free 2-adic floor
`Z32.dist_odd_denom` at the odd denominator `5` against the shadow bound, i.e.
`TShift.sojourn_cap_kappa` at `θ = 1/2`.  Its slope is `κ(1/2) = 1.7095113 = 1/κ_free`, so it
beats `sojourn_cap_free` only for integer `n ≤ 6` (the caps cross at `6.8900` and tie at `n = 7`)
— where `L ≤ 6` regardless. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_cap_half {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (h : IsSojourn n L) :
    (L : ℝ) - 1 ≤ kappa (1 / 2) * n + (-Real.log (32 / 5)) / Real.log (3 / 2) := by
  obtain ⟨a, -, -, hsh⟩ := sojourn_shadow (by omega) h
  have hfloor := Z32.dist_odd_denom hn (by decide : Odd 5) a
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hd : (32 / 5 : ℝ) * (1 / 2 : ℝ) ^ n ≤ |Z32.x n - tgt a| / delta := by
    have hA : (32 / 5 : ℝ) * (1 / 2 : ℝ) ^ n = 32 * (1 / ((5 : ℝ) * 2 ^ n)) := by
      rw [div_pow, one_pow]
      field_simp
    have hB : |Z32.x n - tgt a| / delta = 32 * |Z32.x n - tgt a| := by
      simp only [delta]; ring
    rw [hA, hB]
    simp only [tgt]
    linarith
  have hsh' : |Z32.x n - tgt a| / delta ≤ (2 / 3 : ℝ) ^ (L - 1) := by
    rw [div_le_iff₀ delta_pos]
    linarith [mul_comm delta ((2 / 3 : ℝ) ^ (L - 1))]
  have hkap := sojourn_cap_kappa (c := 32 / 5) (θ := 1 / 2) (n := n) (L := L - 1)
    (by norm_num) (by norm_num) hd hsh'
  rw [Nat.cast_sub hL] at hkap
  push_cast at hkap
  exact hkap

/-- The orbit never *is* a cycle point: `Z32.dist_odd_denom` at the odd denominator `5`.  This is
why an infinite sojourn is impossible even without the cap. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem x_ne_tgt {n : ℕ} (hn : 1 ≤ n) (a : ℤ) : Z32.x n ≠ tgt a := by
  intro hEq
  have hf := Z32.dist_odd_denom hn (by decide : Odd 5) a
  push_cast at hf
  rw [hEq] at hf
  simp only [tgt, sub_self, abs_zero] at hf
  have hpos : (0 : ℝ) < 1 / ((5 : ℝ) * 2 ^ n) := by positivity
  linarith

/-! ## 6. Escape dates: infinitude and every dyadic block -/

/-- An **escape date**: a date at which the orbit sits outside `U_δ`. -/
def IsEscape (n : ℕ) : Prop := ¬ InU (Z32.x n)

/-- Two numeric facts about the free slope, isolated because both the block payoff and the escape
recursion need them: `log₂3 = 1 + κ_free` and `κ_free < 3/5` (from `(3/2)^5 = 7.59375 < 8`). -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem logb_three_eq : Real.logb 2 3 = 1 + Real.logb 2 (3 / 2) := by
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hd : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  simp only [Real.logb, hd]
  field_simp
  ring

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem free_kappa_lt_three_fifths : Real.logb 2 (3 / 2) < 3 / 5 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, div_lt_iff₀ hl2]
  have h5 : Real.log ((3 / 2 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 3) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h5
  push_cast at h5
  linarith

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem free_kappa_nonneg : (0 : ℝ) ≤ Real.logb 2 (3 / 2) :=
  Real.logb_nonneg (by norm_num) (by norm_num)

/-- **Escape dates are unbounded.**  An infinite sojourn would violate the cap at every length. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem exists_escape_ge (N : ℕ) : ∃ n, N ≤ n ∧ IsEscape n := by
  by_contra hcon
  simp only [IsEscape, not_exists, not_and, not_not] at hcon
  have hsoj : ∀ L, IsSojourn (max N 2) L := by
    intro L i _
    exact hcon _ (by omega)
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (Real.logb 2 (3 / 2) * (max N 2 : ℕ) + 2 * Real.logb 2 3 + 1)
  have hcap := sojourn_cap_free (n := max N 2) (L := max L₀ 3) (by omega)
    (le_max_right _ _) (hsoj _)
  have hmono : (L₀ : ℝ) ≤ ((max L₀ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left L₀ 3
  linarith

@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escapes_infinite : {n : ℕ | IsEscape n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  obtain ⟨n, hn, hesc⟩ := exists_escape_ge (b + 1)
  have := hb (show n ∈ {n : ℕ | IsEscape n} from hesc)
  omega

/-- **The transported payoff.**  Every dyadic block of dates `[2^m, 2^{m+1})` with `m ≥ 4`
contains a date at which the orbit is outside `U_{1/32}`.

This is report §1.5's N3 payoff, at base `3/2`, with an explicit burn-in `j₀ = 4` and no escape
sequence: a full block would be a sojourn of length `2^m` at date `2^m`, and the cap then forces
`2^m·(1 − κ_free) ≤ 3 + 2κ_free`, i.e. `2^m ≤ 10.05`.  The free cap knows nothing about `U_{1/32}`
— it is Proposition B that puts the orbit and the region into the statement. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem exists_escape_dyadic {m : ℕ} (hm : 4 ≤ m) :
    ∃ n, 2 ^ m ≤ n ∧ n < 2 ^ (m + 1) ∧ IsEscape n := by
  have h16 : (2 : ℕ) ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  by_contra hcon
  simp only [IsEscape, not_exists, not_and, not_not] at hcon
  have hsoj : IsSojourn (2 ^ m) (2 ^ m) := by
    intro i hi
    refine hcon _ (by omega) ?_
    have : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega
  have hcap := sojourn_cap_free (n := 2 ^ m) (L := 2 ^ m) (by omega) (by omega) hsoj
  have ht : (16 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    calc (16 : ℝ) = (((2 : ℕ) ^ 4 : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h16
  have hkt : Real.logb 2 (3 / 2) * ((2 ^ m : ℕ) : ℝ) < 3 / 5 * ((2 ^ m : ℕ) : ℝ) :=
    mul_lt_mul_of_pos_right free_kappa_lt_three_fifths (by linarith)
  rw [logb_three_eq] at hcap
  linarith [free_kappa_lt_three_fifths]

-- anonymous, so that `AxTShift`'s `namespace`/`end` tracker is not thrown off
section

open Classical

/-- The block count, self-contained: at least `M − 4` escape dates below `2^M`, i.e.
`log₂N − 4` (vacuous below `M = 4`, which is `exists_escape_dyadic`'s burn-in).  The sharper
`ln N/ln(1 + κ_free) = 2.1713·ln N` is `escapeSeq_geometric`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escape_card (M : ℕ) :
    M - 4 ≤ ((Finset.range (2 ^ M)).filter (fun n => IsEscape n)).card := by
  have hex : ∀ m ∈ Finset.Ico 4 M, ∃ n, 2 ^ m ≤ n ∧ n < 2 ^ (m + 1) ∧ IsEscape n := by
    intro m hm
    exact exists_escape_dyadic (Finset.mem_Ico.mp hm).1
  choose! g hg1 hg2 hg3 using hex
  have hkey : ∀ p q : ℕ, p ∈ Finset.Ico 4 M → q ∈ Finset.Ico 4 M → p < q → g p ≠ g q := by
    intro p q hp hq hpq
    have hA : g p < 2 ^ (p + 1) := hg2 p hp
    have hB : (2 : ℕ) ^ q ≤ g q := hg1 q hq
    have hC : (2 : ℕ) ^ (p + 1) ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [← Nat.card_Ico 4 M]
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro m hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hg3 m hm⟩
    have hA : g m < 2 ^ (m + 1) := hg2 m hm
    have hB : (2 : ℕ) ^ (m + 1) ≤ 2 ^ M :=
      Nat.pow_le_pow_right (by norm_num) (by have := (Finset.mem_Ico.mp hm).2; omega)
    omega
  · intro p hp q hq hEq
    rcases lt_trichotomy p q with h | h | h
    · exact absurd hEq (hkey p q hp hq h)
    · exact h
    · exact absurd hEq.symm (hkey q p hq hp h)

end

/-! ## 7. The escape sequence and the geometric count -/

private theorem escapeSet_nonempty (N : ℕ) : {n : ℕ | N ≤ n ∧ IsEscape n}.Nonempty := by
  obtain ⟨n, hn, he⟩ := exists_escape_ge N
  exact ⟨n, hn, he⟩

/-- The escape dates, enumerated: `escapeSeq 0` is the first escape date at or after `2`, and
`escapeSeq (k+1)` the first one after `escapeSeq k`. -/
noncomputable def escapeSeq : ℕ → ℕ
  | 0 => sInf {n : ℕ | 2 ≤ n ∧ IsEscape n}
  | k + 1 => sInf {n : ℕ | escapeSeq k + 1 ≤ n ∧ IsEscape n}

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escapeSeq_spec (k : ℕ) : 2 ≤ escapeSeq k ∧ IsEscape (escapeSeq k) := by
  induction k with
  | zero =>
      have hm := Nat.sInf_mem (escapeSet_nonempty 2)
      simpa [escapeSeq, Set.mem_ofPred_eq] using hm
  | succ k ih =>
      have hm := Nat.sInf_mem (escapeSet_nonempty (escapeSeq k + 1))
      have h : escapeSeq k + 1 ≤ escapeSeq (k + 1) ∧ IsEscape (escapeSeq (k + 1)) := by
        simpa [escapeSeq, Set.mem_ofPred_eq] using hm
      have h1 := ih.1
      have h2 := h.1
      exact ⟨by omega, h.2⟩

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escapeSeq_lt (k : ℕ) : escapeSeq k < escapeSeq (k + 1) := by
  have hm := Nat.sInf_mem (escapeSet_nonempty (escapeSeq k + 1))
  have h : escapeSeq k + 1 ≤ escapeSeq (k + 1) ∧ IsEscape (escapeSeq (k + 1)) := by
    simpa [escapeSeq, Set.mem_ofPred_eq] using hm
  omega

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escapeSeq_strictMono : StrictMono escapeSeq :=
  strictMono_nat_of_lt_succ escapeSeq_lt

/-- Between consecutive escape dates the orbit is in `U_δ`: `escapeSeq` really enumerates *all*
the escape dates from `2` on. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escapeSeq_mem_gap {k m : ℕ} (h1 : escapeSeq k < m) (h2 : m < escapeSeq (k + 1)) :
    InU (Z32.x m) := by
  by_contra hcon
  have hmem : m ∈ {n : ℕ | escapeSeq k + 1 ≤ n ∧ IsEscape n} := ⟨by omega, hcon⟩
  have hle := Nat.sInf_le hmem
  simp only [escapeSeq] at h2
  omega

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escapeSeq_sojourn (k : ℕ) :
    IsSojourn (escapeSeq k + 1) (escapeSeq (k + 1) - escapeSeq k - 1) := by
  have hlt := escapeSeq_lt k
  intro i hi
  exact escapeSeq_mem_gap (k := k) (by omega) (by omega)

/-- The additive constant of the escape recursion, `κ_free + 2 + 2 log₂3 = 5.755`. -/
noncomputable def escapeConst : ℝ := Real.logb 2 (3 / 2) + 2 + 2 * Real.logb 2 3

/-- **The escape recursion.**  Consecutive escape dates satisfy
`e_{k+1} ≤ (1 + κ_free)·e_k + escapeConst`, the hypothesis of C20's `TShift.escape_ratio`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escapeSeq_recursion (k : ℕ) :
    (escapeSeq (k + 1) : ℝ) ≤ (1 + Real.logb 2 (3 / 2)) * escapeSeq k + escapeConst := by
  have hlt := escapeSeq_lt k
  have h2 := (escapeSeq_spec k).1
  have hk0 := free_kappa_nonneg
  have hl3 : (1 : ℝ) ≤ Real.logb 2 3 := by rw [logb_three_eq]; linarith
  have hek : (0 : ℝ) ≤ (escapeSeq k : ℝ) := by positivity
  have hprod : (0 : ℝ) ≤ Real.logb 2 (3 / 2) * (escapeSeq k : ℝ) := mul_nonneg hk0 hek
  simp only [escapeConst]
  rcases Nat.lt_or_ge (escapeSeq (k + 1) - escapeSeq k - 1) 3 with hL | hL
  · have hb : (escapeSeq (k + 1) : ℝ) ≤ (escapeSeq k : ℝ) + 3 := by
      have : escapeSeq (k + 1) ≤ escapeSeq k + 3 := by omega
      exact_mod_cast this
    linarith
  · have hcap := sojourn_cap_free (n := escapeSeq k + 1)
      (L := escapeSeq (k + 1) - escapeSeq k - 1) (by omega) hL (escapeSeq_sojourn k)
    have hcast : ((escapeSeq (k + 1) - escapeSeq k - 1 : ℕ) : ℝ)
        = (escapeSeq (k + 1) : ℝ) - (escapeSeq k : ℝ) - 1 := by
      have hsum : escapeSeq (k + 1) - escapeSeq k - 1 + (escapeSeq k + 1) = escapeSeq (k + 1) := by
        omega
      have := congrArg (fun t : ℕ => (t : ℝ)) hsum
      push_cast at this
      linarith
    rw [hcast] at hcap
    push_cast at hcap
    linarith

/-- **The count.**  The `k`-th escape date stays below a geometric sequence of ratio
`1 + κ_free = 1.5849625`, so there are at least `ln N/ln(1.5849625) = 2.1713·ln N − O(1)` escape
dates by time `N`.  This is the first consumer of C20's `TShift.escape_ratio`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem escapeSeq_geometric (k : ℕ) :
    (escapeSeq k : ℝ) + escapeConst / Real.logb 2 (3 / 2)
      ≤ (1 + Real.logb 2 (3 / 2)) ^ k
        * ((escapeSeq 0 : ℝ) + escapeConst / Real.logb 2 (3 / 2)) :=
  escape_ratio (C := escapeConst) (e := fun j => (escapeSeq j : ℝ)) escapeSeq_recursion k

/-! ## 8. Sanity: the first forcing pair on the real orbit -/

/-- **Sanity, against harness block [C] of `TShift/tshift_numerics.py`.**  Dates `5` and `6` are
the orbit's first *forcing pair*: `x₅ = 19/32` sits within `1/160` of the target `3/5` and
`x₆ = 25/64` within `3/320` of its successor `2/5`, so `IsSojourn 5 2` holds and the carry taken
is the cycle digit `cycleDigit 3 = 1`.

The near miss one step earlier is the reason `forcing` has to be conditional (F2): `x₃ = 3/8` is
in `U_{1/32}` too, at the target `2/5`, but the carry taken there is `1`, *not* `cycleDigit 2 = 0`
— and accordingly `x₄ = 1/16` is outside `U`.  Nothing about the point `x₃` distinguishes the two
cases; only where the orbit goes next does. -/
@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem forcing_sanity :
    Z32.x 5 = 19 / 32 ∧ Z32.x 6 = 25 / 64 ∧ IsSojourn 5 2 ∧ carry 5 = cycleDigit 3 := by
  have h5 : Z32.x 5 = 19 / 32 := by rw [Z32.x_eq]; norm_num [Z32.oddNum]
  have h6 : Z32.x 6 = 25 / 64 := by rw [Z32.x_eq]; norm_num [Z32.oddNum]
  refine ⟨h5, h6, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · refine ⟨3, by norm_num, by norm_num, ?_⟩
      rw [show (5 : ℕ) + 0 = 5 from rfl, h5]
      simp only [tgt, delta]
      rw [abs_lt]
      norm_num
    · refine ⟨2, by norm_num, by norm_num, ?_⟩
      rw [show (5 : ℕ) + 1 = 6 from rfl, h6]
      simp only [tgt, delta]
      rw [abs_lt]
      norm_num
  · simp only [carry, cycleDigit, intPart_eq]
    norm_num

/-! ## 9. WP7: the ceiling on `δ` is per *cycle*, not per multiplier

`δ = 1/32` is a certified choice, not the largest workable radius, and the plan's gated WP7 asked
the engine which radius is.  The answer is that the question is per cycle.  Two constraints bound
a forcing radius, and both are `(5/2)δ`-shaped because the wrong image moves at slope `3/2` and
the point itself is `δ` off target:

* **ejection** — the wrong image of `a/5` must miss the region: `(5/2)δ < d`, `d` the distance from
  the wrong images to the targets *kept in the region*;
* **phase** — the successor ball must be identified: `(5/2)δ < g`, `g` the least gap between kept
  targets, always `1/5` here (`tgt_sep`).

Over all four targets `d = 1/10` (`tenth_dist`) and the ejection constraint binds: `δ < 1/25`.
But `1/10` is *cycle `{1/5, 4/5}`'s* number — its wrong images are `3/10` and `7/10`, each `1/10`
from the neighbouring target of the **other** cycle.  Cycle `{2/5, 3/5}` ejects to `1/10` and
`9/10`, at distance `3/10` from its own targets (`three_tenth_dist`), so dropping the other cycle
removes the binding constraint and leaves the phase one: `δ < 2/25`, twice as large.

This section carries that instance at `deltaB = 5/64 = (5/2)·delta`, the whole chain through to the
payoff.  Nothing else changes: the same phase clock `idxAt`, the same `TShift.free_sojourn_cap`,
the same burn-in `j₀ = 4`.  On the real orbit the gain is visible at once — `IsSojournB 8 3` holds
while `IsSojourn 8 3` does not, because `x₉ = 227/512` is `0.0434` from `2/5` (`cycleB_sanity`).

**What the engine adds, and why no certificate is formalized** (gate G‑D, resolved negative).
`Z32/gencert.py` was run on this family: the block graph is functionally deterministic up to
`δ = 0.046` over all four targets, `0.046` at `{1/5, 4/5}` and `0.092` at `{2/5, 3/5}` — and
rank-stratified to `0.047`, `0.049`, `0.099`, the last being where the two balls merge at `1/10`.
So the funnel buys between `18%` and `24%` in radius over the closed forms above, and buys it at
the price of a certificate entry, a `decide` and a finite-sojourn burn-in.  The factor `2` is the
cycle restriction, which is free.  At `deltaB = 5/64` the engine agrees (`FUNC`, depth 1, two
blocks), and at `ρ = 0` the same closed form returns `(2/5)·(1/2) = 1/5`, which is exactly the
frontier the atlas measured for the classical window. -/

/-- The radius for the cycle `{2/5, 3/5}` alone: `δ_B = 5/64`, exactly `(5/2)·delta` and just
under the ceiling `2/25` that the phase constraint imposes (slack `3/1600`). -/
noncomputable def deltaB : ℝ := 5 / 64

/-- `U_δ` restricted to the second cycle: the two balls of radius `δ_B` around `2/5` and `3/5`. -/
def InUB (y : ℝ) : Prop := ∃ a : ℤ, 2 ≤ a ∧ a ≤ 3 ∧ |y - tgt a| < deltaB

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem deltaB_pos : (0 : ℝ) < deltaB := by
  simp only [deltaB]; norm_num

/-- The two ceilings, and the gain: `1/32 < 5/64 < 2/25`, the four-target ceiling being `1/25`
because `(5/2)·(1/25) = 1/10` is the ejection distance there, and the cycle-restricted one `2/25`
because `(5/2)·(2/25) = 1/5` is the target gap. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem ceiling_facts :
    delta < deltaB ∧ deltaB < 2 / 25 ∧ (5 : ℝ) / 2 * (1 / 25) = 1 / 10 ∧
      (5 : ℝ) / 2 * (2 / 25) = 1 / 5 := by
  simp only [delta, deltaB]
  norm_num

/-- **The ejection geometry of the second cycle.**  The wrong branch of `2/5` or `3/5` lands at
`1/10` or `9/10`, and both are `3/10` from `{2/5, 3/5}` — three times the distance `tenth_dist`
gives against all four targets.  Stated in the shifted-target form `forcingB` consumes. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem three_tenth_dist {a b e : ℤ} (ha2 : 2 ≤ a) (ha3 : a ≤ 3) (hb2 : 2 ≤ b) (hb3 : b ≤ 3)
    (he : e = 1 ∨ e = -1) :
    (3 : ℝ) / 10 ≤ |tgt (nextNum a) - (e : ℝ) / 2 - tgt b| := by
  have hint : (3 : ℤ) ≤ |10 - 2 * a - 5 * e - 2 * b| := by
    rcases he with rfl | rfl <;> rw [le_abs'] <;> omega
  have hint' : (3 : ℝ) ≤ |10 - 2 * (a : ℝ) - 5 * (e : ℝ) - 2 * (b : ℝ)| := by
    have h2 : ((3 : ℤ) : ℝ) ≤ ((|10 - 2 * a - 5 * e - 2 * b| : ℤ) : ℝ) := by exact_mod_cast hint
    rw [Int.cast_abs] at h2
    push_cast at h2
    exact h2
  have hd : tgt (nextNum a) - (e : ℝ) / 2 - tgt b
      = (10 - 2 * (a : ℝ) - 5 * (e : ℝ) - 2 * (b : ℝ)) / 10 := by
    simp only [tgt, nextNum]; push_cast; ring
  rw [hd, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10),
    le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
  linarith

/-- Digit-set constancy at the larger radius: `3δ_B = 15/64` still fits inside the margin
`min (2a/5, 2 − 2a/5) = 4/5` available at `a ∈ {2,3}`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem abs_carry_sub_cycleDigit_leB {n : ℕ} {a : ℤ} (h2 : 2 ≤ a) (h3 : a ≤ 3)
    (hx : |Z32.x n - tgt a| < deltaB) : |carry n - cycleDigit a| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := carry_window n
  rw [abs_lt] at hx
  simp only [tgt, deltaB] at hx
  have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h2
  have ha3 : (a : ℝ) ≤ 3 := by exact_mod_cast h3
  have hup : (carry n : ℝ) < (a : ℝ) := by linarith [hx.1, hx.2]
  have hdn : (a : ℝ) - 4 < (carry n : ℝ) := by linarith [hx.1, hx.2]
  have hup' : carry n < a := by exact_mod_cast hup
  have hdn' : a - 4 < carry n := by
    have : ((a - 4 : ℤ) : ℝ) < (carry n : ℝ) := by push_cast; linarith
    exact_mod_cast this
  rw [abs_le, cycleDigit]
  omega

/-- **Proposition B at the second cycle.**  Same statement as `forcing`, at `2.5×` the radius. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem forcingB {n : ℕ} {a : ℤ} (h2 : 2 ≤ a) (h3 : a ≤ 3)
    (hx : |Z32.x n - tgt a| < deltaB) (hU : InUB (Z32.x (n + 1))) :
    carry n = cycleDigit a ∧
      |Z32.x (n + 1) - tgt (nextNum a)| = 3 / 2 * |Z32.x n - tgt a| ∧
      |Z32.x (n + 1) - tgt (nextNum a)| < deltaB := by
  obtain ⟨b, hb2, hb3, hb⟩ := hU
  have habs : |carry n - cycleDigit a| ≤ 1 := abs_carry_sub_cycleDigit_leB h2 h3 hx
  set e : ℤ := carry n - cycleDigit a with he
  have hcast : (carry n : ℝ) = (e : ℝ) + (a : ℝ) - 2 := by
    have hz : carry n = e + (a - 2) := by simp only [he, cycleDigit]; omega
    rw [hz]; push_cast; ring
  have hid : Z32.x (n + 1) - (tgt (nextNum a) - (e : ℝ) / 2) = 3 / 2 * (Z32.x n - tgt a) := by
    have hc := carry_cast n
    rw [hcast] at hc
    simp only [tgt, nextNum]
    push_cast
    linarith
  have he0 : e = 0 := by
    by_contra hne
    have hpm : e = 1 ∨ e = -1 := by rw [abs_le] at habs; omega
    have hfar := three_tenth_dist h2 h3 hb2 hb3 hpm
    have h32 : |Z32.x (n + 1) - (tgt (nextNum a) - (e : ℝ) / 2)| = 3 / 2 * |Z32.x n - tgt a| := by
      rw [hid, abs_mul]; norm_num
    have htri : |tgt (nextNum a) - (e : ℝ) / 2 - tgt b|
        ≤ |tgt (nextNum a) - (e : ℝ) / 2 - Z32.x (n + 1)| + |Z32.x (n + 1) - tgt b| :=
      abs_sub_le _ _ _
    have hcomm := abs_sub_comm (tgt (nextNum a) - (e : ℝ) / 2) (Z32.x (n + 1))
    simp only [deltaB] at hx hb
    linarith
  have hcarry : carry n = cycleDigit a := by omega
  have hid0 : Z32.x (n + 1) - tgt (nextNum a) = 3 / 2 * (Z32.x n - tgt a) := by
    rw [he0] at hid; simpa using hid
  have habs2 : |Z32.x (n + 1) - tgt (nextNum a)| = 3 / 2 * |Z32.x n - tgt a| := by
    rw [hid0, abs_mul]; norm_num
  refine ⟨hcarry, habs2, ?_⟩
  rcases eq_or_ne b (nextNum a) with rfl | hbne
  · exact hb
  · exfalso
    have hsep := tgt_sep hbne
    have htri : |tgt b - tgt (nextNum a)|
        ≤ |tgt b - Z32.x (n + 1)| + |Z32.x (n + 1) - tgt (nextNum a)| := abs_sub_le _ _ _
    have hcomm := abs_sub_comm (tgt b) (Z32.x (n + 1))
    simp only [deltaB] at hx hb
    linarith

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem idxAtB_mem {a : ℤ} (h2 : 2 ≤ a) (h3 : a ≤ 3) (j : ℕ) :
    2 ≤ idxAt a j ∧ idxAt a j ≤ 3 := by
  simp only [idxAt]
  split_ifs <;> omega

/-- A sojourn in the cycle-restricted region. -/
def IsSojournB (n L : ℕ) : Prop := ∀ i, i < L → InUB (Z32.x (n + i))

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_entryB {n L : ℕ} (hL : 0 < L) (h : IsSojournB n L) :
    ∃ a : ℤ, 2 ≤ a ∧ a ≤ 3 ∧ |Z32.x n - tgt a| < deltaB := h 0 hL

@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_chainB {n L : ℕ} (h : IsSojournB n L) {a : ℤ} (h2 : 2 ≤ a) (h3 : a ≤ 3)
    (hx : |Z32.x n - tgt a| < deltaB) :
    ∀ j, j < L → |Z32.x (n + j) - tgt (idxAt a j)| < deltaB ∧
      |Z32.x (n + j) - tgt (idxAt a j)| = (3 / 2 : ℝ) ^ j * |Z32.x n - tgt a| := by
  intro j
  induction j with
  | zero => intro _; simpa using hx
  | succ j ih =>
      intro hj
      obtain ⟨hlt, heq⟩ := ih (by omega)
      obtain ⟨ha2, ha3⟩ := idxAtB_mem h2 h3 j
      have hshift : n + (j + 1) = n + j + 1 := by omega
      have hU : InUB (Z32.x (n + j + 1)) := by
        have := h (j + 1) hj
        rwa [hshift] at this
      obtain ⟨-, heq2, hlt2⟩ := forcingB ha2 ha3 hlt hU
      rw [← idxAt_succ] at heq2 hlt2
      rw [hshift]
      refine ⟨hlt2, ?_⟩
      rw [heq2, heq]
      ring

@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_carryB {n L : ℕ} (h : IsSojournB n L) {a : ℤ} (h2 : 2 ≤ a) (h3 : a ≤ 3)
    (hx : |Z32.x n - tgt a| < deltaB) :
    ∀ j, j + 1 < L → carry (n + j) = cycleDigit (idxAt a j) := by
  intro j hj
  obtain ⟨hlt, -⟩ := sojourn_chainB h h2 h3 hx j (by omega)
  obtain ⟨ha2, ha3⟩ := idxAtB_mem h2 h3 j
  have hU : InUB (Z32.x (n + j + 1)) := by
    have := h (j + 1) hj
    rwa [show n + (j + 1) = n + j + 1 from by omega] at this
  exact (forcingB ha2 ha3 hlt hU).1

@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_isPeriodicBlockB {n L : ℕ} (h : IsSojournB n L) : IsPeriodicBlock n (L - 1) 2 := by
  intro i hi
  obtain ⟨a, ha2, ha3, hxa⟩ := sojourn_entryB (show 0 < L by omega) h
  have e1 : carry (n + i) = cycleDigit (idxAt a i) := sojourn_carryB h ha2 ha3 hxa i (by omega)
  have e2 : carry (n + (i + 2)) = cycleDigit (idxAt a (i + 2)) :=
    sojourn_carryB h ha2 ha3 hxa (i + 2) (by omega)
  rw [show n + 2 + i = n + (i + 2) from by omega, e1, e2, idxAt_add_two]

/-- **Theorem A at `2.5×` the radius.**  Same cap, same slope, on the larger region. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem sojourn_cap_freeB {n L : ℕ} (hn : 2 ≤ n) (hL : 3 ≤ L) (h : IsSojournB n L) :
    (L : ℝ) - 1 ≤ Real.logb 2 (3 / 2) * n + 2 * Real.logb 2 3 := by
  have hcap := free_sojourn_cap_logb (n := n) (L := L - 1) (p := 2) hn (by omega) (by omega)
    (sojourn_isPeriodicBlockB h)
  rw [Nat.cast_sub (by omega : 1 ≤ L)] at hcap
  push_cast at hcap
  linarith

/-- An escape from the cycle-restricted region. -/
def IsEscapeB (n : ℕ) : Prop := ¬ InUB (Z32.x n)

@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem exists_escape_geB (N : ℕ) : ∃ n, N ≤ n ∧ IsEscapeB n := by
  by_contra hcon
  simp only [IsEscapeB, not_exists, not_and, not_not] at hcon
  have hsoj : ∀ L, IsSojournB (max N 2) L := by
    intro L i _
    exact hcon _ (by omega)
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (Real.logb 2 (3 / 2) * (max N 2 : ℕ) + 2 * Real.logb 2 3 + 1)
  have hcap := sojourn_cap_freeB (n := max N 2) (L := max L₀ 3) (by omega)
    (le_max_right _ _) (hsoj _)
  have hmono : (L₀ : ℝ) ≤ ((max L₀ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left L₀ 3
  linarith

/-- **The payoff at `2.5×` the radius**, with the same explicit burn-in `j₀ = 4`: every dyadic
block of dates `[2^m, 2^{m+1})`, `m ≥ 4`, contains a date at which the orbit is outside the two
balls of radius `5/64` around `2/5` and `3/5` — a set of measure `5/16`, against `1/4` for
`U_{1/32}`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem exists_escape_dyadicB {m : ℕ} (hm : 4 ≤ m) :
    ∃ n, 2 ^ m ≤ n ∧ n < 2 ^ (m + 1) ∧ IsEscapeB n := by
  have h16 : (2 : ℕ) ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  by_contra hcon
  simp only [IsEscapeB, not_exists, not_and, not_not] at hcon
  have hsoj : IsSojournB (2 ^ m) (2 ^ m) := by
    intro i hi
    refine hcon _ (by omega) ?_
    have : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega
  have hcap := sojourn_cap_freeB (n := 2 ^ m) (L := 2 ^ m) (by omega) (by omega) hsoj
  have ht : (16 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    calc (16 : ℝ) = (((2 : ℕ) ^ 4 : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h16
  have hkt : Real.logb 2 (3 / 2) * ((2 ^ m : ℕ) : ℝ) < 3 / 5 * ((2 ^ m : ℕ) : ℝ) :=
    mul_lt_mul_of_pos_right free_kappa_lt_three_fifths (by linarith)
  rw [logb_three_eq] at hcap
  linarith [free_kappa_lt_three_fifths]

/-- The two regions are genuinely different: `2/5 + 1/16` is in `U_B` and in none of the four
balls of radius `1/32`. -/
@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem inUB_not_inU : InUB (2 / 5 + 1 / 16) ∧ ¬ InU (2 / 5 + 1 / 16) := by
  constructor
  · exact ⟨2, by norm_num, by norm_num, by simp only [tgt, deltaB]; rw [abs_lt]; norm_num⟩
  · rintro ⟨a, ha1, ha4, h⟩
    simp only [tgt, delta] at h
    rw [abs_lt] at h
    interval_cases a <;> norm_num at h

/-- **Sanity, on the real orbit: the gain is not vacuous.**  Dates `8, 9, 10` form a sojourn in
`U_B` — phase `3/5, 2/5, 3/5`, carries `1, 0` — and they are *not* a sojourn in `U_{1/32}`, since
`x₉ = 227/512` is `111/2560 = 0.0434` from `2/5`, outside `1/32` and inside `5/64`.  So the
cycle-restricted region sees a length-`3` sojourn that the four-target region at the old radius
does not. -/
@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s13iii"]
theorem cycleB_sanity :
    Z32.x 8 = 161 / 256 ∧ Z32.x 9 = 227 / 512 ∧ Z32.x 10 = 681 / 1024 ∧
      IsSojournB 8 3 ∧ ¬ InU (Z32.x 9) ∧ carry 8 = cycleDigit 3 ∧ carry 9 = cycleDigit 2 := by
  have h8 : Z32.x 8 = 161 / 256 := by rw [Z32.x_eq]; norm_num [Z32.oddNum]
  have h9 : Z32.x 9 = 227 / 512 := by rw [Z32.x_eq]; norm_num [Z32.oddNum]
  have h10 : Z32.x 10 = 681 / 1024 := by rw [Z32.x_eq]; norm_num [Z32.oddNum]
  refine ⟨h8, h9, h10, ?_, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · exact ⟨3, by norm_num, by norm_num, by
        rw [show (8 : ℕ) + 0 = 8 from rfl, h8]
        simp only [tgt, deltaB]; rw [abs_lt]; norm_num⟩
    · exact ⟨2, by norm_num, by norm_num, by
        rw [show (8 : ℕ) + 1 = 9 from rfl, h9]
        simp only [tgt, deltaB]; rw [abs_lt]; norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by
        rw [show (8 : ℕ) + 2 = 10 from rfl, h10]
        simp only [tgt, deltaB]; rw [abs_lt]; norm_num⟩
  · rintro ⟨a, ha1, ha4, h⟩
    rw [h9] at h
    simp only [tgt, delta] at h
    rw [abs_lt] at h
    interval_cases a <;> norm_num at h
  · simp only [carry, cycleDigit, intPart_eq]
    norm_num
  · simp only [carry, cycleDigit, intPart_eq]
    norm_num

end TShift
