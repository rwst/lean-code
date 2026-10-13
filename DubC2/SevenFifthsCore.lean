/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.InfiniteComplexity
import Mathlib.Tactic.Linarith
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The `A,C` subshift at base `7/5`: every admissible word is eventually periodic

Target T3(ii) of `plans/plan-dubC2.html`, the combinatorial core of [DN05] Theorem 4(iii).

At `(p, q, ν) = (7, 5, ½)` the primes `2, 5` cut the carry alphabet down to `{−4,−2,2,4}` and the
prime `3` then splits it into two **orientations**: an orbit with `xₙ ≡ 2 (mod 3)` uses only the
letters `A = −4` and `C = 2`, one with `xₙ ≡ 1 (mod 3)` only `B = −2` and `D = 4`.  The two are
exchanged by `x ↦ −x`, `y ↦ 1 − y`, which turns `D` into `A` and `B` into `C` but replaces the
half-open windows `[0,2/7)`, `[3/7,1)` by `(0,2/7]`, `(3/7,1]`.  [DN05] dismisses the second
orientation with "this makes no difference in our argument".

This file makes that remark into a theorem instead of repeating the argument: everything below is
proved for an **abstract** `DubC2.AC.Data`, whose window hypotheses are stated with `≤` on *both*
sides and are therefore satisfied by both orientations.  `DubC2/Calibration75.lean` builds the two
instances and applies `DubC2.AC.isEventuallyPeriodic` twice.

## The argument

Write `A : y ↦ (7y+3)/5` on `y ≤ 2/7` and `C : y ↦ (7y−3)/5` on `y ≥ 3/7`.  The interval
`(2/7, 3/7)` is forbidden, and this **gap** is the only source of interval pruning.

* `C⁴` is impossible (`DubC2.AC.exists_A`), so `A` positions are never more than three apart, and
  every `A` is followed by a run of one, two or three `C`s — the blocks `AC`, `AC²`, `AC³`.
* A **3-position** (`DubC2.AC.Three`) is an `A` position with `y ∈ [606/2401, 2/7]`, i.e. one
  whose block is `AC³`.  From a 3-position the word continues in exactly one of two ways
  (`DubC2.AC.threeStep`): `V = AC³·AC` of length `6`, or `U = AC³·AC²·AC` of length `9`, and the
  position reached is a 3-position again.  Both `AC` and `AC³AC²` are forced to be followed by
  `AC³`; that is where the gap does its work.
* Modulo `11` the letters act by `A : r ↦ 8r+8` and `C : r ↦ 8r+7`, so the blocks act by
  `r ↦ 3r+9` (`V`) and `r ↦ 7r+1` (`U`), with some residues killed inside the block.  Peeling
  the resulting ten-vertex graph (`DubC2.AC.peel`) leaves exactly `r = 1`, which must take `V`
  forever, and `r = 9`, which must take `U` forever — periods `6` and `9`.
* If no 3-position ever occurs the word is `(ACC)^∞`, of period `3` (`DubC2.AC.cycleACC`).

So the carry word is eventually periodic in every case, which [Dub09AA] Lemma 2
(`Z32.not_isEventuallyPeriodic_carry`) forbids.

## Why no certificate machinery appears

§6.2 of the plan budgeted a product state, a soundness lemma and a determinization check, all of
which are artifacts of working on a *grid*: an expanding branch surrounds each periodic orbit by
a tube of `q/(p−q)` cells that refinement does not narrow (M1's central finding; at `7/5` the
tube is `5/2` cells wide and the core sat at 27 nodes / 44 edges for every `k` and `K` tried).
The proof below carries the real `yₙ`, so there is no tube, nothing to determinize and no
over-approximating graph whose soundness would have to be proved.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Theorem 4(iii) and §6.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — Lemma 2.
-/

namespace DubC2.AC

open ForMathlib.SubwordComplexity

variable {x : ℕ → ℤ} {y : ℕ → ℝ} {s : ℕ → ℤ}

/-! ## The abstract data -/

/-- An **`A,C` orbit at base `7/5`**: an integer sequence `x`, a residual `y` in `[0,1]` and a
carry word `s` linked by the two branch maps of [DN05] Theorem 4(iii), with `11 ∤ xₙ`.

The windows are stated with `≤` on both sides so that both orientations of the paper's `x ↦ −x`,
`y ↦ 1 − y` symmetry satisfy them: an `A,C` orbit has `y < 2/7` or `y ≥ 3/7`, the mirrored `B,D`
orbit has `y ≤ 2/7` or `y > 3/7`, and neither ever attains `2/7` or `3/7`, so `stepA` and `stepC`
hold for both. -/
structure Data (x : ℕ → ℤ) (y : ℕ → ℝ) (s : ℕ → ℤ) : Prop where
  /-- `yₙ ≥ 0`. -/
  nonneg : ∀ n, 0 ≤ y n
  /-- `yₙ ≤ 1`. -/
  le_one : ∀ n, y n ≤ 1
  /-- **The gap**: no `yₙ` lies strictly between `2/7` and `3/7`. -/
  dich : ∀ n, y n ≤ 2 / 7 ∨ 3 / 7 ≤ y n
  /-- **Letter `A`**, on `y ≤ 2/7`. -/
  stepA : ∀ n, y n ≤ 2 / 7 →
    s n = -4 ∧ 5 * y (n + 1) = 7 * y n + 3 ∧ 5 * x (n + 1) = 7 * x n - 4
  /-- **Letter `C`**, on `y ≥ 3/7`. -/
  stepC : ∀ n, 3 / 7 ≤ y n →
    s n = 2 ∧ 5 * y (n + 1) = 7 * y n - 3 ∧ 5 * x (n + 1) = 7 * x n + 2
  /-- The orbit avoids `11`. -/
  avoid : ∀ n, ¬ (11 : ℤ) ∣ x n

/-- A **3-position**: an `A` position whose `C`-run has length `3`, i.e. whose block is `AC³`. -/
def Three (y : ℕ → ℝ) (n : ℕ) : Prop := 606 / 2401 ≤ y n ∧ y n ≤ 2 / 7

/-! ## Blocks -/

/-- **`C⁴` is impossible**, so an `A` position occurs at or within three steps of any index:
four consecutive `C`s would need `y ≥ 2664/2401 > 1`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem exists_A (h : Data x y s) (n : ℕ) : ∃ m, n ≤ m ∧ y m ≤ 2 / 7 := by
  by_contra hc
  push Not at hc
  have g : ∀ m, n ≤ m → 3 / 7 ≤ y m := fun m hm =>
    (h.dich m).resolve_left (not_le.mpr (hc m hm))
  obtain ⟨-, e0, -⟩ := h.stepC n (g n le_rfl)
  obtain ⟨-, e1, -⟩ := h.stepC (n + 1) (g (n + 1) (by omega))
  obtain ⟨-, e2, -⟩ := h.stepC (n + 2) (g (n + 2) (by omega))
  obtain ⟨-, e3, -⟩ := h.stepC (n + 3) (g (n + 3) (by omega))
  rw [show n + 1 + 1 = n + 2 from rfl] at e1
  rw [show n + 2 + 1 = n + 3 from rfl] at e2
  rw [show n + 3 + 1 = n + 4 from rfl] at e3
  have h4 := h.nonneg (n + 4)
  have h1 := h.le_one n
  linarith only [e0, e1, e2, e3, h4, h1]

/-- The two-letter prefix `AC` common to every block. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem pre2 (h : Data x y s) (n : ℕ) (hy : y n ≤ 2 / 7) :
    s n = -4 ∧ s (n + 1) = 2 ∧ 25 * y (n + 2) = 49 * y n + 6 ∧
      5 * x (n + 1) = 7 * x n - 4 ∧ 5 * x (n + 2) = 7 * x (n + 1) + 2 := by
  have hy0 := h.nonneg n
  obtain ⟨hs0, e0, f0⟩ := h.stepA n hy
  have hy1 : (3 : ℝ) / 7 ≤ y (n + 1) := by linarith only [e0, hy0]
  obtain ⟨hs1, e1, f1⟩ := h.stepC (n + 1) hy1
  rw [show n + 1 + 1 = n + 2 from rfl] at e1 f1
  exact ⟨hs0, hs1, by linarith only [e0, e1], f0, f1⟩

/-- **First fork.**  The gap at `n+2` splits an `A` position into "the block is `AC`" and "the
`C`-run continues". -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem fork2 (h : Data x y s) (n : ℕ) (hy : y n ≤ 2 / 7) :
    y n ≤ 8 / 343 ∨ 33 / 343 ≤ y n := by
  obtain ⟨-, -, e, -, -⟩ := pre2 h n hy
  rcases h.dich (n + 2) with hd | hd
  · exact Or.inl (by linarith only [e, hd])
  · exact Or.inr (by linarith only [e, hd])

/-- The three-letter prefix `ACC`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem pre3 (h : Data x y s) (n : ℕ) (hy : y n ≤ 2 / 7) (hy' : 33 / 343 ≤ y n) :
    s n = -4 ∧ s (n + 1) = 2 ∧ s (n + 2) = 2 ∧ 125 * y (n + 3) = 343 * y n - 33 ∧
      5 * x (n + 1) = 7 * x n - 4 ∧ 5 * x (n + 2) = 7 * x (n + 1) + 2 ∧
      5 * x (n + 3) = 7 * x (n + 2) + 2 := by
  obtain ⟨hs0, hs1, e, f0, f1⟩ := pre2 h n hy
  have hy2 : (3 : ℝ) / 7 ≤ y (n + 2) := by linarith only [e, hy']
  obtain ⟨hs2, e2, f2⟩ := h.stepC (n + 2) hy2
  rw [show n + 2 + 1 = n + 3 from rfl] at e2 f2
  exact ⟨hs0, hs1, hs2, by linarith only [e, e2], f0, f1, f2⟩

/-- **Second fork.**  The gap at `n+3` splits a continuing run into "the block is `AC²`" and
"the block is `AC³`". -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem fork3 (h : Data x y s) (n : ℕ) (hy : y n ≤ 2 / 7) (hy' : 33 / 343 ≤ y n) :
    y n ≤ 481 / 2401 ∨ 606 / 2401 ≤ y n := by
  obtain ⟨-, -, -, e, -, -, -⟩ := pre3 h n hy hy'
  rcases h.dich (n + 3) with hd | hd
  · exact Or.inl (by linarith only [e, hd])
  · exact Or.inr (by linarith only [e, hd])

/-- **The look-ahead.**  A block `AC` lands in `[6/25, 2/7]`, and `6/25 = 0.24` is *below* the
3-position threshold `606/2401 = 0.2523…`; two more letters and the gap close the difference.
This is [DN05]'s "each `AC` should be followed by `AC³`". -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem three_of_ge (h : Data x y s) (n : ℕ) (hlo : 6 / 25 ≤ y n) (hhi : y n ≤ 2 / 7) :
    Three y n := by
  refine ⟨?_, hhi⟩
  rcases fork2 h n hhi with hd | hd
  · linarith only [hlo, hd]
  · rcases fork3 h n hhi hd with hd3 | hd3
    · linarith only [hlo, hd3]
    · exact hd3

/-- **The block `AC³` at a 3-position**, with the four carries, the residual map
`625y_{n+4} = 2401yₙ − 606` and the `x`-steps that the peel modulo `11` reads. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem blk3 (h : Data x y s) (n : ℕ) (hn : Three y n) :
    (s n = -4 ∧ s (n + 1) = 2 ∧ s (n + 2) = 2 ∧ s (n + 3) = 2) ∧
      (625 * y (n + 4) = 2401 * y n - 606 ∧ y (n + 4) ≤ 16 / 125) ∧
      (5 * x (n + 1) = 7 * x n - 4 ∧ 5 * x (n + 2) = 7 * x (n + 1) + 2 ∧
        5 * x (n + 3) = 7 * x (n + 2) + 2 ∧ 5 * x (n + 4) = 7 * x (n + 3) + 2) := by
  obtain ⟨hlo, hhi⟩ := hn
  obtain ⟨hs0, hs1, hs2, e, f0, f1, f2⟩ := pre3 h n hhi (by linarith only [hlo])
  have hy3 : (3 : ℝ) / 7 ≤ y (n + 3) := by linarith only [e, hlo]
  obtain ⟨hs3, e3, f3⟩ := h.stepC (n + 3) hy3
  rw [show n + 3 + 1 = n + 4 from rfl] at e3 f3
  exact ⟨⟨hs0, hs1, hs2, hs3⟩, ⟨by linarith only [e, e3], by linarith only [e, e3, hhi]⟩,
    ⟨f0, f1, f2, f3⟩⟩

/-! ## The two blocks that can follow a 3-position -/

/-- **The `V`/`U` dichotomy.**  From a 3-position the word continues either as `V = A C³ A C`
(six letters) or as `U = A C³ A C² A C` (nine letters), and lands on a 3-position again.  The
first component is the `x`-step chain through `n+6`, which is common to both branches: positions
`n+1 … n+6` carry the same letters either way. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem threeStep (h : Data x y s) (n : ℕ) (hn : Three y n) :
    (5 * x (n + 1) = 7 * x n - 4 ∧ 5 * x (n + 2) = 7 * x (n + 1) + 2 ∧
        5 * x (n + 3) = 7 * x (n + 2) + 2 ∧ 5 * x (n + 4) = 7 * x (n + 3) + 2 ∧
        5 * x (n + 5) = 7 * x (n + 4) - 4 ∧ 5 * x (n + 6) = 7 * x (n + 5) + 2) ∧
      ((Three y (n + 6) ∧ s n = -4 ∧ s (n + 1) = 2 ∧ s (n + 2) = 2 ∧ s (n + 3) = 2 ∧
          s (n + 4) = -4 ∧ s (n + 5) = 2)
        ∨ (Three y (n + 9) ∧
            (5 * x (n + 7) = 7 * x (n + 6) + 2 ∧ 5 * x (n + 8) = 7 * x (n + 7) - 4 ∧
              5 * x (n + 9) = 7 * x (n + 8) + 2) ∧
            s n = -4 ∧ s (n + 1) = 2 ∧ s (n + 2) = 2 ∧ s (n + 3) = 2 ∧ s (n + 4) = -4 ∧
              s (n + 5) = 2 ∧ s (n + 6) = 2 ∧ s (n + 7) = -4 ∧ s (n + 8) = 2)) := by
  obtain ⟨⟨hs0, hs1, hs2, hs3⟩, ⟨ey4, ey4hi⟩, ⟨f1, f2, f3, f4⟩⟩ := blk3 h n hn
  have hy4nn := h.nonneg (n + 4)
  have hy4A : y (n + 4) ≤ 2 / 7 := by linarith only [ey4hi]
  obtain ⟨sA4, sC5, ey6, f5, f6⟩ := pre2 h (n + 4) hy4A
  rw [show n + 4 + 1 = n + 5 from rfl] at sC5 f5 f6
  rw [show n + 4 + 2 = n + 6 from rfl] at ey6 f6
  refine ⟨⟨f1, f2, f3, f4, f5, f6⟩, ?_⟩
  rcases fork2 h (n + 4) hy4A with hd | hd
  · -- `V = A C³ A C`
    have hy6lo : (6 : ℝ) / 25 ≤ y (n + 6) := by linarith only [ey6, hy4nn]
    have hy6hi : y (n + 6) ≤ 2 / 7 := by linarith only [ey6, hd]
    exact Or.inl ⟨three_of_ge h (n + 6) hy6lo hy6hi, hs0, hs1, hs2, hs3, sA4, sC5⟩
  · -- `U = A C³ A C² A C`
    obtain ⟨-, -, sC6, ey7, -, -, f7⟩ := pre3 h (n + 4) hy4A hd
    rw [show n + 4 + 2 = n + 6 from rfl] at sC6 f7
    rw [show n + 4 + 3 = n + 7 from rfl] at ey7 f7
    have hy7nn := h.nonneg (n + 7)
    have hy7hi : y (n + 7) ≤ 1363 / 15625 := by linarith only [ey7, ey4hi]
    have hy7A : y (n + 7) ≤ 2 / 7 := by linarith only [hy7hi]
    have hd7 : y (n + 7) ≤ 8 / 343 := by
      rcases fork2 h (n + 7) hy7A with hd7 | hd7
      · exact hd7
      · linarith only [hd7, hy7hi]
    obtain ⟨sA7, sC8, ey9, f8, f9⟩ := pre2 h (n + 7) hy7A
    rw [show n + 7 + 1 = n + 8 from rfl] at sC8 f8 f9
    rw [show n + 7 + 2 = n + 9 from rfl] at ey9 f9
    have hy9lo : (6 : ℝ) / 25 ≤ y (n + 9) := by linarith only [ey9, hy7nn]
    have hy9hi : y (n + 9) ≤ 2 / 7 := by linarith only [ey9, hd7]
    exact Or.inr ⟨three_of_ge h (n + 9) hy9lo hy9hi, ⟨f7, f8, f9⟩,
      hs0, hs1, hs2, hs3, sA4, sC5, sC6, sA7, sC8⟩

/-! ## The peel modulo `11`

`A` acts by `r ↦ 8r + 8` and `C` by `r ↦ 8r + 7`, so `A` kills `r = 10` and `C` kills `r = 6`.
The four helpers below are the only place where arithmetic modulo `11` happens; each one sees a
*single* step of the recurrence, which is what keeps `omega` cheap (a chain of `5x' = 7x + c`
constraints makes it exact-divide five times over and blow up). -/

private theorem resA {a b : ℤ} (hab : 5 * b = 7 * a - 4) {u v : ℤ} (hu : a % 11 = u)
    (hv : (8 * u + 8) % 11 = v) : b % 11 = v := by omega

private theorem resC {a b : ℤ} (hab : 5 * b = 7 * a + 2) {u v : ℤ} (hu : a % 11 = u)
    (hv : (8 * u + 7) % 11 = v) : b % 11 = v := by omega

private theorem dvdA {a b : ℤ} (hab : 5 * b = 7 * a - 4) (hu : a % 11 = 10) :
    (11 : ℤ) ∣ b := by omega

private theorem dvdC {a b : ℤ} (hab : 5 * b = 7 * a + 2) (hu : a % 11 = 6) :
    (11 : ℤ) ∣ b := by omega

/-- Five residues die inside the common prefix `A C³ A`: `10` at `n+1`, `8` at `n+2`, `5` at
`n+3`, `6` at `n+4` and `3` at `n+5`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem dead_of_three (h : Data x y s) {n : ℕ} (hn : Three y n) :
    x n % 11 ≠ 10 ∧ x n % 11 ≠ 8 ∧ x n % 11 ≠ 5 ∧ x n % 11 ≠ 6 ∧ x n % 11 ≠ 3 := by
  obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := threeStep h n hn
  refine ⟨fun hr => h.avoid (n + 1) (dvdA g1 hr), fun hr => ?_, fun hr => ?_, fun hr => ?_,
    fun hr => ?_⟩
  · have r1 : x (n + 1) % 11 = 6 := resA g1 hr (by norm_num)
    exact h.avoid (n + 2) (dvdC g2 r1)
  · have r1 : x (n + 1) % 11 = 4 := resA g1 hr (by norm_num)
    have r2 : x (n + 2) % 11 = 6 := resC g2 r1 (by norm_num)
    exact h.avoid (n + 3) (dvdC g3 r2)
  · have r1 : x (n + 1) % 11 = 1 := resA g1 hr (by norm_num)
    have r2 : x (n + 2) % 11 = 4 := resC g2 r1 (by norm_num)
    have r3 : x (n + 3) % 11 = 6 := resC g3 r2 (by norm_num)
    exact h.avoid (n + 4) (dvdC g4 r3)
  · have r1 : x (n + 1) % 11 = 10 := resA g1 hr (by norm_num)
    have r2 : x (n + 2) % 11 = 10 := resC g2 r1 (by norm_num)
    have r3 : x (n + 3) % 11 = 10 := resC g3 r2 (by norm_num)
    have r4 : x (n + 4) % 11 = 10 := resC g4 r3 (by norm_num)
    exact h.avoid (n + 5) (dvdA g5 r4)

/-- `r = 4` dies at depth two: `U` kills it at `n+8`, and `V` sends it to `10`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem peel4 (h : Data x y s) {n : ℕ} (hn : Three y n) : x n % 11 ≠ 4 := by
  intro hr
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, hbr⟩ := threeStep h n hn
  have r1 : x (n + 1) % 11 = 7 := resA g1 hr (by norm_num)
  have r2 : x (n + 2) % 11 = 8 := resC g2 r1 (by norm_num)
  have r3 : x (n + 3) % 11 = 5 := resC g3 r2 (by norm_num)
  have r4 : x (n + 4) % 11 = 3 := resC g4 r3 (by norm_num)
  have r5 : x (n + 5) % 11 = 10 := resA g5 r4 (by norm_num)
  have r6 : x (n + 6) % 11 = 10 := resC g6 r5 (by norm_num)
  rcases hbr with ⟨h6, -⟩ | ⟨-, ⟨g7, g8, -⟩, -⟩
  · exact (dead_of_three h h6).1 r6
  · have r7 : x (n + 7) % 11 = 10 := resC g7 r6 (by norm_num)
    exact h.avoid (n + 8) (dvdA g8 r7)

/-- `r = 7` dies at depth two: `V` sends it to `8`, `U` to `6`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem peel7 (h : Data x y s) {n : ℕ} (hn : Three y n) : x n % 11 ≠ 7 := by
  intro hr
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, hbr⟩ := threeStep h n hn
  have r1 : x (n + 1) % 11 = 9 := resA g1 hr (by norm_num)
  have r2 : x (n + 2) % 11 = 2 := resC g2 r1 (by norm_num)
  have r3 : x (n + 3) % 11 = 1 := resC g3 r2 (by norm_num)
  have r4 : x (n + 4) % 11 = 4 := resC g4 r3 (by norm_num)
  have r5 : x (n + 5) % 11 = 7 := resA g5 r4 (by norm_num)
  have r6 : x (n + 6) % 11 = 8 := resC g6 r5 (by norm_num)
  rcases hbr with ⟨h6, -⟩ | ⟨h9, ⟨g7, g8, g9⟩, -⟩
  · exact (dead_of_three h h6).2.1 r6
  · have r7 : x (n + 7) % 11 = 5 := resC g7 r6 (by norm_num)
    have r8 : x (n + 8) % 11 = 4 := resA g8 r7 (by norm_num)
    exact (dead_of_three h h9).2.2.2.1 (resC g9 r8 (by norm_num))

/-- `r = 2` dies at depth three: both branches send it to `4`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem peel2 (h : Data x y s) {n : ℕ} (hn : Three y n) : x n % 11 ≠ 2 := by
  intro hr
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, hbr⟩ := threeStep h n hn
  have r1 : x (n + 1) % 11 = 2 := resA g1 hr (by norm_num)
  have r2 : x (n + 2) % 11 = 1 := resC g2 r1 (by norm_num)
  have r3 : x (n + 3) % 11 = 4 := resC g3 r2 (by norm_num)
  have r4 : x (n + 4) % 11 = 6 := resC g4 r3 (by norm_num)
  have r5 : x (n + 5) % 11 = 1 := resA g5 r4 (by norm_num)
  have r6 : x (n + 6) % 11 = 4 := resC g6 r5 (by norm_num)
  rcases hbr with ⟨h6, -⟩ | ⟨h9, ⟨g7, g8, g9⟩, -⟩
  · exact peel4 h h6 r6
  · have r7 : x (n + 7) % 11 = 6 := resC g7 r6 (by norm_num)
    have r8 : x (n + 8) % 11 = 1 := resA g8 r7 (by norm_num)
    exact peel4 h h9 (resC g9 r8 (by norm_num))

/-- **The peel.**  Of the ten residues available at a 3-position only `1` and `9` have an
infinite forward path; every other one runs into a multiple of `11` within three blocks. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem peel (h : Data x y s) {n : ℕ} (hn : Three y n) : x n % 11 = 1 ∨ x n % 11 = 9 := by
  obtain ⟨d10, d8, d5, d6, d3⟩ := dead_of_three h hn
  have h4 := peel4 h hn
  have h7 := peel7 h hn
  have h2 := peel2 h hn
  have h0 := h.avoid n
  omega

/-! ## The two cycles -/

/-- **The `V` cycle**, period `6`.  At residue `1` the branch `U` would land on residue `8`,
which the peel forbids; so `V` is forced, and it reproduces the residue. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem cycleV (h : Data x y s) {n : ℕ} (hn : Three y n) (hr : x n % 11 = 1) :
    Three y (n + 6) ∧ x (n + 6) % 11 = 1 ∧ s n = -4 ∧ s (n + 1) = 2 ∧ s (n + 2) = 2 ∧
      s (n + 3) = 2 ∧ s (n + 4) = -4 ∧ s (n + 5) = 2 := by
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, hbr⟩ := threeStep h n hn
  have r1 : x (n + 1) % 11 = 5 := resA g1 hr (by norm_num)
  have r2 : x (n + 2) % 11 = 3 := resC g2 r1 (by norm_num)
  have r3 : x (n + 3) % 11 = 9 := resC g3 r2 (by norm_num)
  have r4 : x (n + 4) % 11 = 2 := resC g4 r3 (by norm_num)
  have r5 : x (n + 5) % 11 = 2 := resA g5 r4 (by norm_num)
  have r6 : x (n + 6) % 11 = 1 := resC g6 r5 (by norm_num)
  rcases hbr with ⟨h6, p0, p1, p2, p3, p4, p5⟩ | ⟨h9, ⟨g7, g8, g9⟩, -⟩
  · exact ⟨h6, r6, p0, p1, p2, p3, p4, p5⟩
  · have r7 : x (n + 7) % 11 = 4 := resC g7 r6 (by norm_num)
    have r8 : x (n + 8) % 11 = 7 := resA g8 r7 (by norm_num)
    exact absurd (resC g9 r8 (by norm_num)) (dead_of_three h h9).2.1

/-- **The `U` cycle**, period `9`.  At residue `9` the branch `V` would land on residue `3`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem cycleU (h : Data x y s) {n : ℕ} (hn : Three y n) (hr : x n % 11 = 9) :
    Three y (n + 9) ∧ x (n + 9) % 11 = 9 ∧ s n = -4 ∧ s (n + 1) = 2 ∧ s (n + 2) = 2 ∧
      s (n + 3) = 2 ∧ s (n + 4) = -4 ∧ s (n + 5) = 2 ∧ s (n + 6) = 2 ∧ s (n + 7) = -4 ∧
      s (n + 8) = 2 := by
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, hbr⟩ := threeStep h n hn
  have r1 : x (n + 1) % 11 = 3 := resA g1 hr (by norm_num)
  have r2 : x (n + 2) % 11 = 9 := resC g2 r1 (by norm_num)
  have r3 : x (n + 3) % 11 = 2 := resC g3 r2 (by norm_num)
  have r4 : x (n + 4) % 11 = 1 := resC g4 r3 (by norm_num)
  have r5 : x (n + 5) % 11 = 5 := resA g5 r4 (by norm_num)
  have r6 : x (n + 6) % 11 = 3 := resC g6 r5 (by norm_num)
  rcases hbr with ⟨h6, -⟩ | ⟨h9, ⟨g7, g8, g9⟩, p0, p1, p2, p3, p4, p5, p6, p7, p8⟩
  · exact absurd r6 (dead_of_three h h6).2.2.2.2
  · have r7 : x (n + 7) % 11 = 9 := resC g7 r6 (by norm_num)
    have r8 : x (n + 8) % 11 = 3 := resA g8 r7 (by norm_num)
    exact ⟨h9, resC g9 r8 (by norm_num), p0, p1, p2, p3, p4, p5, p6, p7, p8⟩

/-- **The `(ACC)^∞` cycle**, period `3`.  If no 3-position ever occurs then every block is `AC²`:
a block `AC` would land in `[6/25, 2/7]`, which the look-ahead turns into a 3-position, and a
block `AC³` starts at a 3-position by definition. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem cycleACC (h : Data x y s) {M n : ℕ} (hno : ∀ m, M ≤ m → ¬ Three y m) (hn : M ≤ n)
    (hy : y n ≤ 2 / 7) :
    s n = -4 ∧ s (n + 1) = 2 ∧ s (n + 2) = 2 ∧ y (n + 3) ≤ 2 / 7 := by
  have hy0 := h.nonneg n
  rcases fork2 h n hy with hd | hd
  · exfalso
    obtain ⟨-, -, e, -, -⟩ := pre2 h n hy
    exact hno (n + 2) (by omega)
      (three_of_ge h (n + 2) (by linarith only [e, hy0]) (by linarith only [e, hd]))
  · rcases fork3 h n hy hd with hd3 | hd3
    · obtain ⟨hs0, hs1, hs2, e, -, -, -⟩ := pre3 h n hy hd
      exact ⟨hs0, hs1, hs2, by linarith only [e, hd3]⟩
    · exact absurd ⟨hd3, hy⟩ (hno n hn)

/-! ## Eventual periodicity -/

/-- **The core theorem.**  Every `A,C` orbit at base `7/5` that avoids `11` has an eventually
periodic carry word — of period `6` (the word `V^∞`), `9` (the word `U^∞`) or `3` (the word
`(ACC)^∞`). -/
@[category research solved, AMS 11 68, ref "DN05", group "dn05_nearest_75"]
theorem isEventuallyPeriodic (h : Data x y s) : IsEventuallyPeriodic s := by
  obtain ⟨M, -, hM⟩ := exists_A h 0
  by_cases hex : ∃ n, M ≤ n ∧ Three y n
  · obtain ⟨n₀, hn₀M, hn₀⟩ := hex
    rcases peel h hn₀ with hr | hr
    · -- `V^∞`, period `6`
      have key : ∀ k, Three y (n₀ + 6 * k) ∧ x (n₀ + 6 * k) % 11 = 1 := by
        intro k
        induction k with
        | zero => simp only [Nat.mul_zero, Nat.add_zero]; exact ⟨hn₀, hr⟩
        | succ k ih =>
          obtain ⟨t1, t2, -⟩ := cycleV h ih.1 ih.2
          rw [show n₀ + 6 * (k + 1) = n₀ + 6 * k + 6 by ring]
          exact ⟨t1, t2⟩
      have hpat : ∀ k j, j < 6 →
          s (n₀ + 6 * k + j) = if j = 0 ∨ j = 4 then (-4 : ℤ) else 2 := by
        intro k j hj
        obtain ⟨-, -, p0, p1, p2, p3, p4, p5⟩ := cycleV h (key k).1 (key k).2
        interval_cases j
        · simpa using p0
        · simpa using p1
        · simpa using p2
        · simpa using p3
        · simpa using p4
        · simpa using p5
      refine ⟨n₀, 6, by norm_num, ?_⟩
      intro m hm
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 6 ∧ m = n₀ + 6 * k + j :=
        ⟨(m - n₀) / 6, (m - n₀) % 6, by omega, by omega⟩
      rw [show n₀ + 6 * k + j + 6 = n₀ + 6 * (k + 1) + j by ring, hpat (k + 1) j hj,
        hpat k j hj]
    · -- `U^∞`, period `9`
      have key : ∀ k, Three y (n₀ + 9 * k) ∧ x (n₀ + 9 * k) % 11 = 9 := by
        intro k
        induction k with
        | zero => simp only [Nat.mul_zero, Nat.add_zero]; exact ⟨hn₀, hr⟩
        | succ k ih =>
          obtain ⟨t1, t2, -⟩ := cycleU h ih.1 ih.2
          rw [show n₀ + 9 * (k + 1) = n₀ + 9 * k + 9 by ring]
          exact ⟨t1, t2⟩
      have hpat : ∀ k j, j < 9 →
          s (n₀ + 9 * k + j) = if j = 0 ∨ j = 4 ∨ j = 7 then (-4 : ℤ) else 2 := by
        intro k j hj
        obtain ⟨-, -, p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := cycleU h (key k).1 (key k).2
        interval_cases j
        · simpa using p0
        · simpa using p1
        · simpa using p2
        · simpa using p3
        · simpa using p4
        · simpa using p5
        · simpa using p6
        · simpa using p7
        · simpa using p8
      refine ⟨n₀, 9, by norm_num, ?_⟩
      intro m hm
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 9 ∧ m = n₀ + 9 * k + j :=
        ⟨(m - n₀) / 9, (m - n₀) % 9, by omega, by omega⟩
      rw [show n₀ + 9 * k + j + 9 = n₀ + 9 * (k + 1) + j by ring, hpat (k + 1) j hj,
        hpat k j hj]
  · -- `(ACC)^∞`, period `3`
    have hno : ∀ n, M ≤ n → ¬ Three y n := fun n hn ht => hex ⟨n, hn, ht⟩
    have key : ∀ k, y (M + 3 * k) ≤ 2 / 7 := by
      intro k
      induction k with
      | zero => simp only [Nat.mul_zero, Nat.add_zero]; exact hM
      | succ k ih =>
        obtain ⟨-, -, -, t⟩ := cycleACC h hno (M := M) (by omega) ih
        rw [show M + 3 * (k + 1) = M + 3 * k + 3 by ring]
        exact t
    have hpat : ∀ k j, j < 3 → s (M + 3 * k + j) = if j = 0 then (-4 : ℤ) else 2 := by
      intro k j hj
      obtain ⟨t0, t1, t2, -⟩ := cycleACC h hno (M := M) (by omega) (key k)
      interval_cases j
      · simpa using t0
      · simpa using t1
      · simpa using t2
    refine ⟨M, 3, by norm_num, ?_⟩
    intro m hm
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 ∧ m = M + 3 * k + j :=
      ⟨(m - M) / 3, (m - M) % 3, by omega, by omega⟩
    rw [show M + 3 * k + j + 3 = M + 3 * (k + 1) + j by ring, hpat (k + 1) j hj, hpat k j hj]

end DubC2.AC
