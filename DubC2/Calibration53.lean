/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.DubickasWord
import Mathlib.Analysis.SpecificLimits.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Calibration: [DN05] Theorem 4(ii) — the base `5/3` at `𝒫 = {2,3}`

Target T3 of `plans/plan-dubC2.html`, the first of the three calibrations, and the first
formalisation of a nearest-integer divisor-set theorem from the literature.

> **[DN05] Thm 4(ii).**  For every real `ξ ≠ 0`, infinitely many of `[ξ(5/3)ⁿ + ½]` are
> divisible by `2` or by `3`.

The proof runs on the same two rails as the `3/2` capstone (`DubC2/Nearest.lean`) — an alphabet
collapsed by arithmetic, then a funnel on the residual `yₙ` — but the two rails are weighted
differently, and the difference is worth recording.

* **At `3/2` the arithmetic does the interval's work.**  The two letters `[0,½)`, `[½,1)`
  partition `[0,1)` exactly, so the interval alone forbids nothing at the top level; every
  reduction came from the residues mod `5`.
* **At `5/3` it is the other way round.**  The residues are spent entirely on the alphabet:
  `2 ∤ xₙ` makes `sₙ` even, `3 ∤ xₙ` makes it prime to `3`, and with `|sₙ| ≤ 3` only `sₙ = ±2`
  survive.  After that the residues say nothing more — `sₙ ≡ xₙ (mod 3)` merely *reads off*
  the residue from the letter — and the two windows `[0,⅖)`, `[⅗,1)` leave a **gap**
  `[⅖,⅗)` that no admissible `yₙ` may enter.  That gap is the whole engine: the funnel below
  uses it five times.

## The two cycles

Unlike `3/2`, where a single word `(AABB)^∞` survives, `5/3` has **two** surviving periodic
words, and both are realised by actual `y`-orbits: `(AB)^∞` at `y = 1/4` and `(AABB)^∞` at
`y = 1/34`.  The dichotomy is decided by a single threshold: `DubC2.cycle53_four` shows
`yₙ < 1/9` is self-reproducing with period `4`, and `DubC2.cycle53_two` shows that an orbit
that never goes below `1/9` is trapped in `[1/9, 2/5)` with period `2`.

This is the point at which `plans/plan-dubC2.html` §0 must not be transcribed.  Its paraphrase
of [DN05] §6 — "the intervals alone force `A² → B² → A² ⋯`" — drops the `(AB)^∞` case.  The
paper itself is correct and lists it (p. 646, verbatim: *"If the sequence is not `A^∞`, `B^∞`
or `(AB)^∞` … then we must have either `A²` or `B²`"*); the M1 engine found both orbits.

## Main results

* `DubC2.round_divisor_set_five_thirds` — the theorem above.
* `DubC2.round_composite_five_thirds` — the composite corollary for `ξ > 0`.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Theorem 4(ii) and §6.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — Lemma 2.
-/

namespace DubC2

open Filter ForMathlib.SubwordComplexity

variable {ξ : ℝ} {N n : ℕ}

/-! ## The model at `(p, q, ν) = (5, 3, 1/2)` -/

/-- `xₙ = [ξ(5/3)ⁿ + ½]`. -/
noncomputable def x53 (ξ : ℝ) (n : ℕ) : ℤ := Z32.xInt 5 3 ξ (1 / 2) n

/-- `yₙ = {ξ(5/3)ⁿ + ½}`. -/
noncomputable def y53 (ξ : ℝ) (n : ℕ) : ℝ := Z32.yFract 5 3 ξ (1 / 2) n

/-- `sₙ = 3x_{n+1} − 5xₙ`. -/
noncomputable def s53 (ξ : ℝ) (n : ℕ) : ℤ := Z32.carry 5 3 ξ (1 / 2) n

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem x53_eq_round (ξ : ℝ) (n : ℕ) : x53 ξ n = round (ξ * ((5 : ℝ) / 3) ^ n) := by
  rw [x53, Z32.xInt, Z32.orb, round_eq]
  norm_num

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_53"]
theorem y53_nonneg (ξ : ℝ) (n : ℕ) : 0 ≤ y53 ξ n := Z32.yFract_nonneg n

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_53"]
theorem y53_lt_one (ξ : ℝ) (n : ℕ) : y53 ξ n < 1 := Z32.yFract_lt_one n

/-- [Dub09AA] (3) at `(5, 3, 1/2)`: `sₙ = 5yₙ − 3y_{n+1} − 1`. -/
@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_53"]
theorem s53_eq (ξ : ℝ) (n : ℕ) : (s53 ξ n : ℝ) = 5 * y53 ξ n - 3 * y53 ξ (n + 1) - 1 := by
  have h := Z32.carry_eq (p := 5) (q := 3) (ξ := ξ) (ν := 1 / 2) (by norm_num) n
  simp only [s53, y53]
  push_cast at h ⊢
  linarith

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_53"]
theorem three_mul_x53_succ (ξ : ℝ) (n : ℕ) : 3 * x53 ξ (n + 1) = 5 * x53 ξ n + s53 ξ n := by
  simp only [s53, x53, Z32.carry]
  push_cast
  ring

/-- **Avoidance of `𝒫 = {2,3}`.** -/
def Avoids53 (ξ : ℝ) (n : ℕ) : Prop := ¬ (2 : ℤ) ∣ x53 ξ n ∧ ¬ (3 : ℤ) ∣ x53 ξ n

/-! ## The alphabet collapses to `{−2, +2}` -/

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_53"]
theorem abs_s53_le_three (ξ : ℝ) (n : ℕ) : -3 ≤ s53 ξ n ∧ s53 ξ n ≤ 3 := by
  have h := s53_eq ξ n
  have h0 := y53_nonneg ξ n
  have h1 := y53_lt_one ξ n
  have h2 := y53_nonneg ξ (n + 1)
  have h3 := y53_lt_one ξ (n + 1)
  have hup : s53 ξ n < 4 := by
    by_contra hc
    push Not at hc
    have : (4 : ℝ) ≤ (s53 ξ n : ℝ) := by exact_mod_cast hc
    linarith
  have hlo : -4 < s53 ξ n := by
    by_contra hc
    push Not at hc
    have : (s53 ξ n : ℝ) ≤ -4 := by exact_mod_cast hc
    linarith
  omega

/-- **Two letters.**  `2 ∤ xₙ` and `2 ∤ x_{n+1}` make `sₙ` even; `3 ∤ xₙ` makes `sₙ` prime to
`3`; with `|sₙ| ≤ 3` only `±2` remain. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem s53_eq_neg_two_or_two (h : Avoids53 ξ n) (h' : Avoids53 ξ (n + 1)) :
    s53 ξ n = -2 ∨ s53 ξ n = 2 := by
  have hrec := three_mul_x53_succ ξ n
  have hb := abs_s53_le_three ξ n
  obtain ⟨h2, h3⟩ := h
  obtain ⟨h2', -⟩ := h'
  omega

/-! ## The branch table, and the forbidden gap `[2/5, 3/5)` -/

/-- Letter `A` (`yₙ < 2/5`) forces `sₙ = −2`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem s53_eq_neg_two (h : Avoids53 ξ n) (h' : Avoids53 ξ (n + 1)) (hy : y53 ξ n < 2 / 5) :
    s53 ξ n = -2 := by
  rcases s53_eq_neg_two_or_two h h' with hs | hs
  · exact hs
  · exfalso
    have he := s53_eq ξ n
    rw [hs] at he
    have := y53_nonneg ξ (n + 1)
    push_cast at he
    linarith

/-- Letter `B` (`yₙ ≥ 3/5`) forces `sₙ = +2`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem s53_eq_two (h : Avoids53 ξ n) (h' : Avoids53 ξ (n + 1)) (hy : 3 / 5 ≤ y53 ξ n) :
    s53 ξ n = 2 := by
  rcases s53_eq_neg_two_or_two h h' with hs | hs
  · exfalso
    have he := s53_eq ξ n
    rw [hs] at he
    have := y53_lt_one ξ (n + 1)
    push_cast at he
    linarith
  · exact hs

/-- **The gap.**  No admissible `yₙ` lies in `[2/5, 3/5)`: letter `A` would push `y_{n+1}` to
`1` or beyond, letter `B` would push it below `0`.  This is the sole source of pruning at
`5/3`, and it has no analogue at `3/2`, where the two windows partition `[0,1)`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem y53_lt_or_ge (h : Avoids53 ξ n) (h' : Avoids53 ξ (n + 1)) :
    y53 ξ n < 2 / 5 ∨ 3 / 5 ≤ y53 ξ n := by
  by_contra hc
  push Not at hc
  obtain ⟨hlo, hhi⟩ := hc
  have he := s53_eq ξ n
  have h0 := y53_nonneg ξ (n + 1)
  have h1 := y53_lt_one ξ (n + 1)
  rcases s53_eq_neg_two_or_two h h' with hs | hs <;> rw [hs] at he <;> push_cast at he <;>
    linarith

/-- Branch `A`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem stepA53 (h : Avoids53 ξ n) (h' : Avoids53 ξ (n + 1)) (hy : y53 ξ n < 2 / 5) :
    s53 ξ n = -2 ∧ 3 * y53 ξ (n + 1) = 5 * y53 ξ n + 1 := by
  have hs := s53_eq_neg_two h h' hy
  refine ⟨hs, ?_⟩
  have he := s53_eq ξ n
  rw [hs] at he
  push_cast at he
  linarith

/-- Branch `B`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem stepB53 (h : Avoids53 ξ n) (h' : Avoids53 ξ (n + 1)) (hy : 3 / 5 ≤ y53 ξ n) :
    s53 ξ n = 2 ∧ 3 * y53 ξ (n + 1) = 5 * y53 ξ n - 3 := by
  have hs := s53_eq_two h h' hy
  refine ⟨hs, ?_⟩
  have he := s53_eq ξ n
  rw [hs] at he
  push_cast at he
  linarith

/-! ## The two cycles -/

/-- **The period-4 cycle `(AABB)^∞`.**  The cell `yₙ < 1/9` reproduces itself after four steps,
and the four carries are `−2, −2, +2, +2`.  Both intermediate letters are pinned by the gap:
`y_{n+1} < 14/27 < 3/5` forces `A`, and `y_{n+3} ≥ 13/27 > 2/5` forces `B`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem cycle53_four (hav : ∀ m, N ≤ m → Avoids53 ξ m) (hn : N ≤ n) (hy : y53 ξ n < 1 / 9) :
    s53 ξ n = -2 ∧ s53 ξ (n + 1) = -2 ∧ s53 ξ (n + 2) = 2 ∧ s53 ξ (n + 3) = 2 ∧
      y53 ξ (n + 4) < 1 / 9 := by
  have a0 := hav n hn
  have a1 := hav (n + 1) (by omega)
  have a2 := hav (n + 2) (by omega)
  have a3 := hav (n + 3) (by omega)
  have a4 := hav (n + 4) (by omega)
  have hy0 := y53_nonneg ξ n
  obtain ⟨s0, hy1⟩ := stepA53 a0 a1 (by linarith)
  have hy1lo : 1 / 3 ≤ y53 ξ (n + 1) := by linarith
  have hy1hi : y53 ξ (n + 1) < 14 / 27 := by linarith
  have hy1' : y53 ξ (n + 1) < 2 / 5 := by
    rcases y53_lt_or_ge a1 a2 with h | h
    · exact h
    · linarith
  obtain ⟨s1, hy2⟩ := stepA53 a1 a2 hy1'
  have hy2lo : 8 / 9 ≤ y53 ξ (n + 2) := by linarith
  have hy2hi := y53_lt_one ξ (n + 2)
  obtain ⟨s2, hy3⟩ := stepB53 a2 a3 (by linarith)
  have hy3lo : 13 / 27 ≤ y53 ξ (n + 3) := by linarith
  have hy3hi : y53 ξ (n + 3) < 2 / 3 := by linarith
  have hy3' : 3 / 5 ≤ y53 ξ (n + 3) := by
    rcases y53_lt_or_ge a3 a4 with h | h
    · linarith
    · exact h
  obtain ⟨s3, hy4⟩ := stepB53 a3 a4 hy3'
  exact ⟨s0, s1, s2, s3, by linarith⟩

/-- **The period-2 cycle `(AB)^∞`.**  An orbit that never dips below `1/9` is trapped in
`[1/9, 2/5)` with carries `−2, +2`: the gap forces the `B`, and dipping below `2/5` after the
`B` is the only alternative to a `y` below `1/9` two steps later. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem cycle53_two (hav : ∀ m, N ≤ m → Avoids53 ξ m) (hlow : ∀ m, N ≤ m → 1 / 9 ≤ y53 ξ m)
    (hn : N ≤ n) (hy : y53 ξ n < 2 / 5) :
    s53 ξ n = -2 ∧ s53 ξ (n + 1) = 2 ∧ y53 ξ (n + 2) < 2 / 5 := by
  have a0 := hav n hn
  have a1 := hav (n + 1) (by omega)
  have a2 := hav (n + 2) (by omega)
  have a3 := hav (n + 3) (by omega)
  have hy0 := hlow n hn
  obtain ⟨s0, hy1⟩ := stepA53 a0 a1 hy
  have hy1lo : 14 / 27 ≤ y53 ξ (n + 1) := by linarith
  have hy1' : 3 / 5 ≤ y53 ξ (n + 1) := by
    rcases y53_lt_or_ge a1 a2 with h | h
    · linarith
    · exact h
  obtain ⟨s1, hy2⟩ := stepB53 a1 a2 hy1'
  have hy1hi := y53_lt_one ξ (n + 1)
  refine ⟨s0, s1, ?_⟩
  rcases y53_lt_or_ge a2 a3 with h | h
  · exact h
  · exfalso
    obtain ⟨-, hy3⟩ := stepB53 a2 a3 h
    have := hlow (n + 3) (by omega)
    linarith

/-! ## Eventual periodicity, and the theorem -/

/-- The carry word of an orbit avoiding `{2,3}` is eventually periodic — with period `4` if the
orbit ever dips below `1/9`, and with period `2` otherwise. -/
@[category research solved, AMS 11 68, ref "DN05", group "dn05_nearest_53"]
theorem isEventuallyPeriodic_s53 (hav : ∀ m, N ≤ m → Avoids53 ξ m) :
    IsEventuallyPeriodic (s53 ξ) := by
  by_cases hex : ∃ M, N ≤ M ∧ y53 ξ M < 1 / 9
  · obtain ⟨M, hMN, hM⟩ := hex
    have hbase : ∀ k, y53 ξ (M + 4 * k) < 1 / 9 := by
      intro k
      induction k with
      | zero => simpa using hM
      | succ k ih =>
        obtain ⟨-, -, -, -, h4⟩ := cycle53_four hav (N := N) (by omega) ih
        have he : M + 4 * (k + 1) = M + 4 * k + 4 := by ring
        rw [he]; exact h4
    have hpat : ∀ k j, j < 4 → s53 ξ (M + 4 * k + j) = (if j < 2 then (-2 : ℤ) else 2) := by
      intro k j hj
      obtain ⟨s0, s1, s2, s3, -⟩ := cycle53_four hav (N := N) (by omega) (hbase k)
      interval_cases j
      · simpa using s0
      · simpa using s1
      · simpa using s2
      · simpa using s3
    refine ⟨M, 4, by norm_num, ?_⟩
    intro m hm
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 4 ∧ m = M + 4 * k + j :=
      ⟨(m - M) / 4, (m - M) % 4, by omega, by omega⟩
    rw [show M + 4 * k + j + 4 = M + 4 * (k + 1) + j by ring, hpat (k + 1) j hj, hpat k j hj]
  · push Not at hex
    have hlow : ∀ m, N ≤ m → 1 / 9 ≤ y53 ξ m := hex
    -- an `A` position exists within two steps of `N`
    obtain ⟨M, hMN, hM⟩ : ∃ M, N ≤ M ∧ y53 ξ M < 2 / 5 := by
      rcases y53_lt_or_ge (hav N le_rfl) (hav (N + 1) (by omega)) with h | h
      · exact ⟨N, le_rfl, h⟩
      · obtain ⟨-, hy1⟩ := stepB53 (hav N le_rfl) (hav (N + 1) (by omega)) h
        have hN1 := y53_lt_one ξ N
        rcases y53_lt_or_ge (hav (N + 1) (by omega)) (hav (N + 2) (by omega)) with h1 | h1
        · exact ⟨N + 1, by omega, h1⟩
        · exfalso
          obtain ⟨-, hy2⟩ := stepB53 (hav (N + 1) (by omega)) (hav (N + 2) (by omega)) h1
          have := hlow (N + 2) (by omega)
          have hN2 := y53_lt_one ξ (N + 1)
          linarith
    have hbase : ∀ k, y53 ξ (M + 2 * k) < 2 / 5 := by
      intro k
      induction k with
      | zero => simpa using hM
      | succ k ih =>
        obtain ⟨-, -, h2⟩ := cycle53_two hav hlow (N := N) (by omega) ih
        have he : M + 2 * (k + 1) = M + 2 * k + 2 := by ring
        rw [he]; exact h2
    have hpat : ∀ k j, j < 2 → s53 ξ (M + 2 * k + j) = (if j < 1 then (-2 : ℤ) else 2) := by
      intro k j hj
      obtain ⟨s0, s1, -⟩ := cycle53_two hav hlow (N := N) (by omega) (hbase k)
      interval_cases j
      · simpa using s0
      · simpa using s1
    refine ⟨M, 2, by norm_num, ?_⟩
    intro m hm
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 2 ∧ m = M + 2 * k + j :=
      ⟨(m - M) / 2, (m - M) % 2, by omega, by omega⟩
    rw [show M + 2 * k + j + 2 = M + 2 * (k + 1) + j by ring, hpat (k + 1) j hj, hpat k j hj]

/-- **[DN05] Theorem 4(ii), formalised.**  For every real `ξ ≠ 0`, infinitely many of the
nearest integers `[ξ(5/3)ⁿ + ½]` are divisible by `2` or by `3`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem round_divisor_set_five_thirds (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ round (ξ * ((5 : ℝ) / 3) ^ n) ∨
      (3 : ℤ) ∣ round (ξ * ((5 : ℝ) / 3) ^ n) := by
  rw [Filter.frequently_atTop]
  intro N
  by_contra hc
  push Not at hc
  have hav : ∀ m, N ≤ m → Avoids53 ξ m := by
    intro m hm
    have := hc m hm
    rw [← x53_eq_round] at this
    exact this
  have hper : IsEventuallyPeriodic (Z32.carry 5 3 ξ (1 / 2)) := isEventuallyPeriodic_s53 hav
  exact Z32.not_isEventuallyPeriodic_carry (p := 5) (q := 3) (ξ := ξ) (ν := 1 / 2)
    (by norm_num) (by norm_num) (by decide) hξ hper

/-- The composite corollary at `5/3`, for `ξ > 0`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_53"]
theorem round_composite_five_thirds (hξ : 0 < ξ) :
    ∃ᶠ n in atTop, ¬ Prime (round (ξ * ((5 : ℝ) / 3) ^ n)) ∧
      1 < round (ξ * ((5 : ℝ) / 3) ^ n) := by
  have hgrow : ∀ᶠ n in atTop, (3 : ℤ) < round (ξ * ((5 : ℝ) / 3) ^ n) := by
    have h1 : Tendsto (fun n : ℕ => ξ * ((5 : ℝ) / 3) ^ n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hξ (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    refine (h1.eventually_gt_atTop 4).mono fun n hn => ?_
    have hr : |ξ * ((5 : ℝ) / 3) ^ n - round (ξ * ((5 : ℝ) / 3) ^ n)| ≤ 1 / 2 := abs_sub_round _
    have : (3 : ℝ) < (round (ξ * ((5 : ℝ) / 3) ^ n) : ℝ) := by
      cases abs_le.mp hr with
      | intro hlo hhi => linarith
    exact_mod_cast this
  refine ((round_divisor_set_five_thirds hξ.ne').and_eventually hgrow).mono ?_
  rintro n ⟨hdvd, hgt⟩
  set x : ℤ := round (ξ * ((5 : ℝ) / 3) ^ n) with hx
  have hnat : (3 : ℕ) < x.natAbs := by omega
  refine ⟨fun hp => ?_, by omega⟩
  have hpn : Nat.Prime x.natAbs := Int.prime_iff_natAbs_prime.mp hp
  rcases hdvd with h | h
  · have h2 : (2 : ℕ) ∣ x.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; simpa using this
    rcases hpn.eq_one_or_self_of_dvd 2 h2 with h1 | h1 <;> omega
  · have h3 : (3 : ℕ) ∣ x.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; simpa using this
    rcases hpn.eq_one_or_self_of_dvd 3 h3 with h1 | h1 <;> omega

end DubC2
