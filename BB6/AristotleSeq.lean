/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB6.Runs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Proposition B — the historical block sequence

The sequence of this file is **not ours**: it is the counterexample produced on 2026-05-24 by
Aristotle (Harmonic), run `43adb707-6915-45d6-9f05-65cbedb43109`, when the first formalization of
Problem 10.6 read "very rapidly increasing" as *sublacunary and superpolynomial*.  The construction
is a concatenation of runs of consecutive integers, block `k` being
`blockStart k, blockStart k + 1, …, blockStart k + k`, placed at the triangular indices.  The
proofs below are adapted, not copied: the original project is Lean/Mathlib `v4.28.0` and carried
two `sorry`s, one of them load-bearing.

## Contents

* `BB6.blockStart`, `BB6.tri`, `BB6.blockIdx`, `BB6.blockOff`, `BB6.mySeq` — the construction;
* `BB6.mySeq_strictMono` — the first of the two original `sorry`s, closed;
* `BB6.mySeq_hasLongRuns`, `BB6.mySeq_universallyDensifying` — density, now a one-line consequence
  of Lemma R (`BB6/Runs.lean`), which is how the second `sorry` (`fract_step_cover`) is bypassed;
* `BB6.mySeq_ratio_tendsto` — `mₙ₊₁/mₙ → 1`;
* `BB6.two_pow_le_blockStart` / `BB6.blockStart_le`, and their consequences
  `BB6.mySeq_hasIntermediateGrowth` (R1 for every `α < 1/2`) and
  `BB6.not_hasIntermediateGrowth` (R1 fails for every `α > 1/2`);
* `BB6.mySeq_superPoly` — superpolynomial growth;
* `BB6.not_isGenuinelySublacunary` — R3 fails, for every `c > 0`;
* `BB6.proposition_B` — the package.

*Attribution:* construction due to Aristotle (Harmonic), run
`43adb707-6915-45d6-9f05-65cbedb43109`, 2026-05-24; proofs adapted.  The original project carried
no licence header.
-/

namespace BB6

open Filter Set

/-! ## The construction -/

/-- Block starting values.  The step `blockStart k / (Nat.log 2 (k + 2) + 1)` is a *natural*
division, so the growth factor is `1 + 1/(log₂ k + 1)`: fast enough to be superpolynomial, slow
enough that the ratios tend to one. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def blockStart : ℕ → ℕ
  | 0 => 2
  | k + 1 => blockStart k + (k + 1) + blockStart k / (Nat.log 2 (k + 2) + 1)

/-- The triangular numbers `tri k = k(k+1)/2`, the starting *indices* of the blocks. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- The block index of the position `n`: the unique `k` with `tri k ≤ n < tri (k+1)`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def blockIdx (n : ℕ) : ℕ := (Nat.sqrt (8 * n + 1) - 1) / 2

/-- The offset of the position `n` inside its block. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def blockOff (n : ℕ) : ℕ := n - tri (blockIdx n)

/-- Aristotle's sequence: `mySeq n = blockStart (blockIdx n) + blockOff n`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def mySeq (n : ℕ) : ℕ := blockStart (blockIdx n) + blockOff n

/-! ## Block algebra -/

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockStart_succ (k : ℕ) :
    blockStart (k + 1) = blockStart k + (k + 1) + blockStart k / (Nat.log 2 (k + 2) + 1) := rfl

/-- `k + 1 ≤ blockStart k`; in particular `blockStart` is positive. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem succ_le_blockStart : ∀ k, k + 1 ≤ blockStart k
  | 0 => by norm_num [blockStart]
  | k + 1 => by
      rw [blockStart_succ]
      have := succ_le_blockStart k
      generalize blockStart k / (Nat.log 2 (k + 2) + 1) = q
      omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockStart_pos (k : ℕ) : 0 < blockStart k := by have := succ_le_blockStart k; omega

/-- The room that keeps the sequence increasing across a block boundary. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockStart_add_lt_succ (k : ℕ) : blockStart k + k < blockStart (k + 1) := by
  rw [blockStart_succ]
  generalize blockStart k / (Nat.log 2 (k + 2) + 1) = q
  omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockStart_strictMono : StrictMono blockStart :=
  strictMono_nat_of_lt_succ fun k => by have := blockStart_add_lt_succ k; omega

/-! ### The triangular indexing -/

@[category API, AMS 11, group "bugeaud_10_6"]
theorem two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self k)

@[category API, AMS 11, group "bugeaud_10_6"]
theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  have h1 := two_mul_tri k
  have h2 := two_mul_tri (k + 1)
  nlinarith

@[category API, AMS 11, group "bugeaud_10_6"]
theorem tri_strictMono : StrictMono tri :=
  strictMono_nat_of_lt_succ fun k => by rw [tri_succ]; omega

/-- The lower half of the sandwich `tri (blockIdx n) ≤ n < tri (blockIdx n + 1)`.

With `s = Nat.sqrt (8n+1)` and `k = (s-1)/2` one has `2k + 1 ≤ s`, so
`8 · tri k + 1 = (2k+1)² ≤ s² ≤ 8n + 1`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem tri_le_blockIdx (n : ℕ) : tri (blockIdx n) ≤ n := by
  set s := Nat.sqrt (8 * n + 1) with hs
  have hsq : s * s ≤ 8 * n + 1 := Nat.sqrt_le (8 * n + 1)
  have hs1 : 1 ≤ s := Nat.sqrt_pos.2 (by omega)
  have hk : 2 * blockIdx n + 1 ≤ s := by simp only [blockIdx, ← hs]; omega
  have h2 := two_mul_tri (blockIdx n)
  nlinarith

/-- The upper half of the sandwich.

With `s = Nat.sqrt (8n+1)` and `k = (s-1)/2` one has `s + 1 ≤ 2k + 3`, so
`8n + 1 < (s+1)² ≤ (2k+3)² = 8 · tri (k+1) + 1`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem lt_tri_succ_blockIdx (n : ℕ) : n < tri (blockIdx n + 1) := by
  set s := Nat.sqrt (8 * n + 1) with hs
  have hsq : 8 * n + 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (8 * n + 1)
  have hk : s + 1 ≤ 2 * blockIdx n + 3 := by simp only [blockIdx, ← hs]; omega
  have h2 := two_mul_tri (blockIdx n + 1)
  nlinarith

/-- The sandwich characterises `blockIdx`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockIdx_eq_of {n k : ℕ} (h₁ : tri k ≤ n) (h₂ : n < tri (k + 1)) : blockIdx n = k := by
  have hlo := tri_le_blockIdx n
  have hhi := lt_tri_succ_blockIdx n
  rcases lt_trichotomy (blockIdx n) k with h | h | h
  · have : tri (blockIdx n + 1) ≤ tri k := tri_strictMono.monotone (by omega)
    omega
  · exact h
  · have : tri (k + 1) ≤ tri (blockIdx n) := tri_strictMono.monotone (by omega)
    omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockOff_le (n : ℕ) : blockOff n ≤ blockIdx n := by
  have h₁ := tri_le_blockIdx n
  have h₂ := lt_tri_succ_blockIdx n
  rw [tri_succ] at h₂
  simp only [blockOff]; omega

/-- Inside block `k` the sequence is an arithmetic progression of difference one — this is the
statement that `BB6.Runs` consumes. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem mySeq_tri_add (k j : ℕ) (hj : j ≤ k) : mySeq (tri k + j) = blockStart k + j := by
  have hidx : blockIdx (tri k + j) = k :=
    blockIdx_eq_of (Nat.le_add_right _ _) (by rw [tri_succ]; omega)
  simp [mySeq, blockOff, hidx]

/-- Stepping the index either stays inside the block or opens the next one. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockIdx_succ (n : ℕ) :
    blockIdx (n + 1) = blockIdx n ∨ (blockIdx (n + 1) = blockIdx n + 1 ∧ n + 1 = tri (blockIdx n + 1)) := by
  have h₁ := tri_le_blockIdx n
  have h₂ := lt_tri_succ_blockIdx n
  rcases lt_or_ge (n + 1) (tri (blockIdx n + 1)) with h | h
  · exact Or.inl (blockIdx_eq_of (by omega) h)
  · have heq : n + 1 = tri (blockIdx n + 1) := by omega
    refine Or.inr ⟨blockIdx_eq_of (by omega) ?_, heq⟩
    have := tri_succ (blockIdx n + 1)
    omega

/-! ## Strict monotonicity — the first of the two inherited `sorry`s -/

/-- **`mySeq` is strictly increasing.**  This is the `sorry` left open at `Main.lean:29` of the
inherited project, and it is load-bearing there: `mySeq_ratio_tendsto` invokes it.  The proof is
the case split of `blockIdx_succ`, which in the original was inlined inside the ratio argument. -/
@[category research solved, AMS 11, group "bugeaud_10_6"]
theorem mySeq_strictMono : StrictMono mySeq := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hoff := blockOff_le n
  rcases blockIdx_succ n with h | ⟨_, hn⟩
  · have h₁ := tri_le_blockIdx n
    simp only [mySeq, blockOff, h]
    omega
  · have hb : mySeq (n + 1) = blockStart (blockIdx n + 1) := by
      rw [hn]
      simpa using mySeq_tri_add (blockIdx n + 1) 0 (Nat.zero_le _)
    have hs := blockStart_add_lt_succ (blockIdx n)
    simp only [mySeq] at *
    omega

/-! ## Density — Lemma R does the work -/

/-- The blocks are runs, so `mySeq` has arbitrarily long runs of consecutive integers. -/
@[category research solved, AMS 11, group "bugeaud_10_6", formal_uses mySeq_tri_add]
theorem mySeq_hasLongRuns : HasLongRuns mySeq := by
  refine fun L => ⟨tri L, fun j hj => ?_⟩
  have h0 : mySeq (tri L) = blockStart L := by
    simpa using mySeq_tri_add L 0 (Nat.zero_le _)
  rw [mySeq_tri_add L j hj, h0]

/-- **`mySeq` is universally densifying.**  Immediate from Lemma R.

This is where the inherited project's second `sorry` (`fract_step_cover`) is bypassed rather than
closed: Lemma R gets density from the irrational rotation on `AddCircle` and a compactness bound,
so neither `fract_step_cover` nor the hand-rolled pigeonhole/Dirichlet pair of the original
`Density.lean` is needed. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses universallyDensifying_of_hasLongRuns mySeq_hasLongRuns]
theorem mySeq_universallyDensifying : UniversallyDensifying mySeq :=
  universallyDensifying_of_hasLongRuns mySeq_hasLongRuns

/-! ## Elementary size bounds -/

@[category API, AMS 11, group "bugeaud_10_6"]
theorem mySeq_zero : mySeq 0 = 2 := by
  simp [mySeq, blockIdx, blockOff, tri, blockStart]

/-- `mySeq` starts at `2` and rises by at least one per step. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem add_two_le_mySeq (n : ℕ) : n + 2 ≤ mySeq n := by
  induction n with
  | zero => simp [mySeq_zero]
  | succ n ih =>
      have h : mySeq n < mySeq (n + 1) := mySeq_strictMono (by omega)
      omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem mySeq_pos (n : ℕ) : 0 < mySeq n := by have := add_two_le_mySeq n; omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockStart_le_mySeq (n : ℕ) : blockStart (blockIdx n) ≤ mySeq n := Nat.le_add_right _ _

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockIdx_mono : Monotone blockIdx := fun _ _ h =>
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.sqrt_le_sqrt (by omega)) 1)

/-- `blockIdx n ≤ √(2n)`: the block index is at most the square root, since
`(blockIdx n)² ≤ 2 · tri (blockIdx n) ≤ 2n`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockIdx_le_sqrt (n : ℕ) : blockIdx n ≤ Nat.sqrt (2 * n) := by
  refine Nat.le_sqrt.2 ?_
  have h := tri_le_blockIdx n
  have h2 := two_mul_tri (blockIdx n)
  nlinarith

/-- and `√(2n) ≤ blockIdx n + 1`, since `2n < 2 · tri (blockIdx n + 1) ≤ (blockIdx n + 2)²`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem sqrt_le_blockIdx_succ (n : ℕ) : Nat.sqrt (2 * n) ≤ blockIdx n + 1 := by
  have h := lt_tri_succ_blockIdx n
  have h2 := two_mul_tri (blockIdx n + 1)
  have : Nat.sqrt (2 * n) < blockIdx n + 2 := Nat.sqrt_lt.2 (by nlinarith)
  omega

/-! ### The lower bound on `blockStart`

The recursion multiplies by at least `1 + 1/(log₂ k + 1)` per step, so over a run of `k` steps
with a *uniform* denominator `D` it multiplies by at least `(1 + 1/D)^k ≥ 2^{⌊k/D⌋}`.  Taking
`D = log₂(k+1) + 1`, which dominates every denominator met on the way, gives
`blockStart k ≥ 2^{⌊k/(log₂(k+1)+1)⌋}`, i.e. `log blockStart k ≫ k/log k`. -/

/-- One step of the recursion with the natural division cleared away. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockStart_step (k : ℕ) :
    (Nat.log 2 (k + 2) + 2) * blockStart k ≤ (Nat.log 2 (k + 2) + 1) * blockStart (k + 1) := by
  rw [blockStart_succ]
  set d := Nat.log 2 (k + 2) + 1 with hd
  have hd0 : 0 < d := by omega
  have hdm : d * (blockStart k / d) + blockStart k % d = blockStart k := Nat.div_add_mod _ _
  have hmod : blockStart k % d < d := Nat.mod_lt _ hd0
  have hle : d ≤ d * (k + 1) := Nat.le_mul_of_pos_right d (by omega)
  set q := blockStart k / d
  set r := blockStart k % d
  nlinarith

/-- The same step with a uniform denominator `D`.  Raising the denominator only weakens the
factor, so any `D` dominating `log₂(i+2) + 1` will do. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockStart_step_uniform {D i : ℕ} (hD : Nat.log 2 (i + 2) + 1 ≤ D) :
    (D + 1) * blockStart i ≤ D * blockStart (i + 1) := by
  set d := Nat.log 2 (i + 2) + 1 with hd
  have hd0 : 0 < d := by omega
  refine Nat.le_of_mul_le_mul_left ?_ hd0
  have h1 : d * ((D + 1) * blockStart i) ≤ D * ((d + 1) * blockStart i) := by
    have : d * (D + 1) ≤ D * (d + 1) := by nlinarith
    calc d * ((D + 1) * blockStart i) = (d * (D + 1)) * blockStart i := by ring
      _ ≤ (D * (d + 1)) * blockStart i := Nat.mul_le_mul_right _ this
      _ = D * ((d + 1) * blockStart i) := by ring
  have h2 : D * ((d + 1) * blockStart i) ≤ D * (d * blockStart (i + 1)) :=
    Nat.mul_le_mul_left _ (blockStart_step i)
  calc d * ((D + 1) * blockStart i) ≤ D * (d * blockStart (i + 1)) := le_trans h1 h2
    _ = d * (D * blockStart (i + 1)) := by ring

/-- The compounded form: `(D+1)^k · 2 ≤ D^k · blockStart k`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem pow_le_pow_mul_blockStart {D : ℕ} :
    ∀ k, (∀ i < k, Nat.log 2 (i + 2) + 1 ≤ D) → (D + 1) ^ k * 2 ≤ D ^ k * blockStart k
  | 0, _ => by norm_num [blockStart]
  | k + 1, h => by
      have ih := pow_le_pow_mul_blockStart k fun i hi => h i (by omega)
      have hstep := blockStart_step_uniform (h k (by omega))
      calc (D + 1) ^ (k + 1) * 2 = (D + 1) * ((D + 1) ^ k * 2) := by ring
        _ ≤ (D + 1) * (D ^ k * blockStart k) := Nat.mul_le_mul_left _ ih
        _ = D ^ k * ((D + 1) * blockStart k) := by ring
        _ ≤ D ^ k * (D * blockStart (k + 1)) := Nat.mul_le_mul_left _ hstep
        _ = D ^ (k + 1) * blockStart (k + 1) := by ring

/-- **The lower bound.**  `2^{⌊k/(log₂(k+1)+1)⌋} ≤ blockStart k`. -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  formal_uses pow_le_pow_mul_blockStart]
theorem two_pow_le_blockStart (k : ℕ) :
    (2 : ℝ) ^ (k / (Nat.log 2 (k + 1) + 1)) ≤ (blockStart k : ℝ) := by
  set D := Nat.log 2 (k + 1) + 1 with hD
  have hD0 : 0 < D := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  -- the compounded natural-number inequality, cast to `ℝ`
  have hnat : ((D + 1) ^ k * 2 : ℕ) ≤ ((D ^ k * blockStart k : ℕ) : ℕ) :=
    pow_le_pow_mul_blockStart k fun i hi => by
      have : Nat.log 2 (i + 2) ≤ Nat.log 2 (k + 1) := Nat.log_mono_right (by omega)
      omega
  have hcast : ((D : ℝ) + 1) ^ k * 2 ≤ (D : ℝ) ^ k * blockStart k := by exact_mod_cast hnat
  -- divide by `D ^ k` to get the factor form
  have hfac : 2 * (1 + 1 / (D : ℝ)) ^ k ≤ (blockStart k : ℝ) := by
    have hpow : (0 : ℝ) < (D : ℝ) ^ k := by positivity
    have hrw : (1 : ℝ) + 1 / (D : ℝ) = ((D : ℝ) + 1) / D := by field_simp
    rw [hrw, div_pow, ← mul_div_assoc, div_le_iff₀ hpow]
    nlinarith [hcast]
  -- Bernoulli: `(1 + 1/D)^D ≥ 2`
  have hinv : (0 : ℝ) ≤ 1 / (D : ℝ) := by positivity
  have hbern : (2 : ℝ) ≤ (1 + 1 / (D : ℝ)) ^ D := by
    have h := one_add_mul_le_pow (a := 1 / (D : ℝ)) (by linarith) D
    rw [mul_one_div, div_self (ne_of_gt hDR)] at h
    linarith
  have hone : (1 : ℝ) ≤ 1 + 1 / (D : ℝ) := by linarith
  have hstep : (2 : ℝ) ^ (k / D) ≤ (1 + 1 / (D : ℝ)) ^ k := by
    calc (2 : ℝ) ^ (k / D) ≤ ((1 + 1 / (D : ℝ)) ^ D) ^ (k / D) :=
          pow_le_pow_left₀ (by norm_num) hbern _
      _ = (1 + 1 / (D : ℝ)) ^ (D * (k / D)) := by rw [← pow_mul]
      _ ≤ (1 + 1 / (D : ℝ)) ^ k := by
            refine pow_le_pow_right₀ hone ?_
            rw [Nat.mul_comm]; exact Nat.div_mul_le_self k D
  linarith [hstep, hfac]

/-- The lower bound transported to `mySeq`, in terms of `n` alone. -/
@[category research solved, AMS 11, group "bugeaud_10_6", formal_uses two_pow_le_blockStart]
theorem two_pow_le_mySeq (n : ℕ) :
    (2 : ℝ) ^ ((Nat.sqrt (2 * n) - 1) / (Nat.log 2 (2 * n + 1) + 1)) ≤ (mySeq n : ℝ) := by
  have hnum : Nat.sqrt (2 * n) - 1 ≤ blockIdx n := by have := sqrt_le_blockIdx_succ n; omega
  have hden : Nat.log 2 (blockIdx n + 1) + 1 ≤ Nat.log 2 (2 * n + 1) + 1 := by
    have h1 : blockIdx n ≤ 2 * n := le_trans (blockIdx_le_sqrt n) (Nat.sqrt_le_self _)
    have := Nat.log_mono_right (b := 2) (show blockIdx n + 1 ≤ 2 * n + 1 by omega)
    omega
  have hexp : (Nat.sqrt (2 * n) - 1) / (Nat.log 2 (2 * n + 1) + 1)
      ≤ blockIdx n / (Nat.log 2 (blockIdx n + 1) + 1) :=
    le_trans (Nat.div_le_div_right hnum) (Nat.div_le_div_left hden (by omega))
  calc (2 : ℝ) ^ ((Nat.sqrt (2 * n) - 1) / (Nat.log 2 (2 * n + 1) + 1))
      ≤ (2 : ℝ) ^ (blockIdx n / (Nat.log 2 (blockIdx n + 1) + 1)) :=
        pow_le_pow_right₀ (by norm_num) hexp
    _ ≤ (blockStart (blockIdx n) : ℝ) := two_pow_le_blockStart _
    _ ≤ (mySeq n : ℝ) := by exact_mod_cast blockStart_le_mySeq n

/-! ### The upper bound on `blockStart`

Crude, and deliberately so: the growth factor never exceeds `3`, which is all the note needs.
(§5.1 of the plan asked for `mₙ ≤ exp(c√n/log n)`.  That sharper bound is *not* required: the
only use of an upper bound is to defeat `R1` for `α > 1/2`, and `exp(c√n)` already does that,
since `n^α ≫ √n` there.  Recorded as a WP3 finding.) -/

/-- `blockStart k ≤ 2 · 3^k`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockStart_le : ∀ k, blockStart k ≤ 2 * 3 ^ k
  | 0 => by norm_num [blockStart]
  | k + 1 => by
      have ih := blockStart_le k
      have h1 := succ_le_blockStart k
      have h2 : blockStart k / (Nat.log 2 (k + 2) + 1) ≤ blockStart k := Nat.div_le_self _ _
      rw [blockStart_succ, pow_succ]
      omega

/-- `mySeq n ≤ 3^{√(2n)+1}`. -/
@[category API, AMS 11, group "bugeaud_10_6", formal_uses blockStart_le]
theorem mySeq_le (n : ℕ) : mySeq n ≤ 3 ^ (Nat.sqrt (2 * n) + 1) := by
  have h1 : mySeq n ≤ 2 * 3 ^ blockIdx n + blockIdx n := by
    have := blockStart_le (blockIdx n)
    have := blockOff_le n
    simp only [mySeq]; omega
  have h2 : blockIdx n < 3 ^ blockIdx n := Nat.lt_pow_self (by norm_num)
  have h3 : (3 : ℕ) ^ (blockIdx n + 1) ≤ 3 ^ (Nat.sqrt (2 * n) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := blockIdx_le_sqrt n; omega)
  rw [pow_succ] at h3
  omega

/-! ## The analytic bridge

Three conversions (`Nat.log` and `Nat.sqrt` to their real counterparts, and a natural division
to a real one), then one little-o fact used three times. -/

/-- `Nat.log b m ≤ log m / log b`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem natLog_le_log {m : ℕ} (hm : 0 < m) : (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h : (2 : ℕ) ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hR : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by exact_mod_cast h
  rw [le_div_iff₀ hlog2, ← Real.log_pow]
  exact Real.log_le_log (by positivity) hR

/-- `√m ≤ Nat.sqrt m + 1`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem sqrt_le_natSqrt_add_one (m : ℕ) : Real.sqrt m ≤ (Nat.sqrt m : ℝ) + 1 := by
  have h : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
  have h' : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) * ((Nat.sqrt m : ℝ) + 1) := by exact_mod_cast h
  have hR : (m : ℝ) ≤ ((Nat.sqrt m : ℝ) + 1) ^ 2 := by nlinarith
  calc Real.sqrt m ≤ Real.sqrt (((Nat.sqrt m : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hR
    _ = (Nat.sqrt m : ℝ) + 1 := Real.sqrt_sq (by positivity)

/-- A natural division loses at most one. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem sub_one_le_natDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b - 1 ≤ ((a / b : ℕ) : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have hmod : a % b < b := Nat.mod_lt _ hb
  have hR : (a : ℝ) < (b : ℝ) * ((a / b : ℕ) : ℝ) + b := by
    have h1 : ((b * (a / b) + a % b : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast h
    have h2 : ((a % b : ℕ) : ℝ) < (b : ℝ) := by exact_mod_cast hmod
    push_cast at h1
    linarith
  rw [sub_le_iff_le_add, div_le_iff₀ hbR]
  linarith

/-! ## The master lower bound

`log mₙ ≫ √n / log n`.  Every growth statement below is read off from this one line. -/

/-- **The lower bound on the sequence.**  Eventually `√n / (10 log n) ≤ log mₙ`.

The constant `10` is generous: the true constant is about `0.68`, from
`log mₙ ≳ (√(2n)/log₂ n) · log 2`.  Nothing below needs the sharp value. -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  formal_uses two_pow_le_mySeq eventually_log_le]
theorem log_mySeq_lower :
    ∀ᶠ (n : ℕ) in atTop, Real.sqrt n / (10 * Real.log n) ≤ Real.log (mySeq n) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  filter_upwards [eventually_log_le (c := (1 : ℝ) / 10) (r := (1 : ℝ) / 2)
      (by norm_num) (by norm_num), Filter.eventually_ge_atTop 10000] with n hn hn0
  -- the basic real estimates on `n`
  have hnR : (10000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hsq : (100 : ℝ) ≤ Real.sqrt n := by
    have h : Real.sqrt (10000 : ℝ) ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
    rwa [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hsq0 : (0 : ℝ) < Real.sqrt n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hn10 : 10 * Real.log n ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]; linarith [hn]
  -- the two natural-number quantities
  set s := Nat.sqrt (2 * n) with hs
  set E := Nat.log 2 (2 * n + 1) + 1 with hE
  have hE0 : 0 < E := by omega
  have hE0R : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE0
  have hs1 : 1 ≤ s := Nat.le_sqrt.2 (by omega)
  -- `s - 1 ≥ √n - 2`
  have hsge : Real.sqrt n - 2 ≤ ((s - 1 : ℕ) : ℝ) := by
    have hmono : Nat.sqrt n ≤ s := Nat.sqrt_le_sqrt (by omega)
    have h1 : Real.sqrt n ≤ (Nat.sqrt n : ℝ) + 1 := sqrt_le_natSqrt_add_one n
    have h2 : ((Nat.sqrt n : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hmono
    have h3 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub hs1]; norm_num
    rw [h3]; linarith
  have hsge0 : (0 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- `E ≤ 4 log n`
  have hEle : (E : ℝ) ≤ 4 * Real.log n := by
    have hsmall : 2 * n + 1 ≤ n * n := by nlinarith [hn0]
    have hcast : ((2 * n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h : ((2 * n + 1 : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hsmall
      push_cast at h ⊢; nlinarith
    have hlogle : Real.log ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * Real.log n :=
      calc Real.log ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) hcast
        _ = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring
    have hnl := natLog_le_log (m := 2 * n + 1) (by omega)
    rw [le_div_iff₀ hlog2] at hnl
    have h2 : (E : ℝ) = (Nat.log 2 (2 * n + 1) : ℝ) + 1 := by rw [hE]; push_cast; ring
    rw [h2]
    nlinarith
  -- the floor of the division
  have hdiv : (Real.sqrt n - 2) / (4 * Real.log n) ≤ ((s - 1 : ℕ) : ℝ) / (E : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hE0R]
    have h1 : (Real.sqrt n - 2) * (E : ℝ) ≤ ((s - 1 : ℕ) : ℝ) * (E : ℝ) := by nlinarith
    have h2 : ((s - 1 : ℕ) : ℝ) * (E : ℝ) ≤ ((s - 1 : ℕ) : ℝ) * (4 * Real.log n) :=
      mul_le_mul_of_nonneg_left hEle hsge0
    linarith
  have hfloor := sub_one_le_natDiv (s - 1) hE0
  have hchain : (Real.sqrt n - 2) / (4 * Real.log n) - 1 ≤ (((s - 1) / E : ℕ) : ℝ) := by
    linarith [hdiv, hfloor]
  -- the numeric endgame
  have hkey : Real.sqrt n / (10 * Real.log n)
      ≤ ((Real.sqrt n - 2) / (4 * Real.log n) - 1) * Real.log 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 * Real.log n)]
    have hexp : ((Real.sqrt n - 2) / (4 * Real.log n) - 1) * Real.log 2 * (10 * Real.log n)
        = (5 * (Real.sqrt n - 2) - 20 * Real.log n) * Real.log 2 / 2 := by
      field_simp; ring
    rw [hexp]
    have hpos : (0 : ℝ) ≤ 5 * (Real.sqrt n - 2) - 20 * Real.log n := by linarith
    have := mul_le_mul_of_nonneg_left hlog2'.le hpos
    nlinarith [this]
  have hmul : ((Real.sqrt n - 2) / (4 * Real.log n) - 1) * Real.log 2
      ≤ (((s - 1) / E : ℕ) : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hchain hlog2.le
  -- and the transport back to `mySeq`
  have hlogpow : (((s - 1) / E : ℕ) : ℝ) * Real.log 2
      = Real.log ((2 : ℝ) ^ ((s - 1) / E : ℕ)) := by rw [Real.log_pow]
  have hfin : Real.log ((2 : ℝ) ^ ((s - 1) / E : ℕ)) ≤ Real.log (mySeq n) :=
    Real.log_le_log (by positivity) (two_pow_le_mySeq n)
  rw [hlogpow] at hmul
  linarith

/-! ## The two growth readings

`R1` is `Bugeaud06.HasIntermediateGrowth α`, i.e. `exp(nᵅ) ≤ mₙ` eventually.  The block sequence
sits exactly at the threshold `α = 1/2`: it satisfies R1 below it and fails R1 above it.  That is
the calibration Proposition B is for — the repair "`α > 1/2`" excluded this sequence, and the
recorded weakening to "`0 < α < 1`" readmits it. -/

/-- **R1 holds for every `α < 1/2`.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses log_mySeq_lower]
theorem mySeq_hasIntermediateGrowth {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) :
    Bugeaud06.HasIntermediateGrowth α mySeq := by
  have hr : (0 : ℝ) < 1 / 2 - α := by linarith
  filter_upwards [log_mySeq_lower,
    eventually_log_le (c := (1 : ℝ) / 10) (r := 1 / 2 - α) (by norm_num) hr,
    Filter.eventually_ge_atTop 2] with n hlow hlo hn2
  have hn1R : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn2
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos hn1R
  have hstep : (n : ℝ) ^ α ≤ Real.sqrt n / (10 * Real.log n) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (n : ℝ) ^ α * (10 * Real.log n) ≤ (n : ℝ) ^ α * (n : ℝ) ^ (1 / 2 - α) := by
      have : (10 : ℝ) * Real.log n ≤ (n : ℝ) ^ (1 / 2 - α) := by linarith
      exact mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hn0R.le α)
    rw [← Real.rpow_add hn0R] at h1
    rw [show α + (1 / 2 - α) = 1 / 2 by ring, ← Real.sqrt_eq_rpow] at h1
    exact h1
  have hfin : (n : ℝ) ^ α ≤ Real.log (mySeq n) := le_trans hstep hlow
  calc Real.exp ((n : ℝ) ^ α) ≤ Real.exp (Real.log (mySeq n)) := Real.exp_le_exp.2 hfin
    _ = (mySeq n : ℝ) := Real.exp_log (by exact_mod_cast mySeq_pos n)

/-- `Nat.sqrt m ≤ √m`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem natSqrt_le_sqrt (m : ℕ) : (Nat.sqrt m : ℝ) ≤ Real.sqrt m := by
  have h : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
  have hR : ((Nat.sqrt m : ℝ)) ^ 2 ≤ (m : ℝ) := by
    have : ((Nat.sqrt m * Nat.sqrt m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    push_cast at this; nlinarith
  calc (Nat.sqrt m : ℝ) = Real.sqrt (((Nat.sqrt m : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hR

/-- The upper bound in logarithmic form: `log mₙ ≤ 3√n` eventually.  Crude on purpose — see the
note above `blockStart_le`. -/
@[category research solved, AMS 11, group "bugeaud_10_6", formal_uses mySeq_le]
theorem log_mySeq_upper : ∀ᶠ (n : ℕ) in atTop, Real.log (mySeq n) ≤ 3 * Real.sqrt n := by
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have h : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    push_cast at h; linarith
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq2 : (2 : ℝ) ≤ Real.sqrt n := by
    have h : Real.sqrt (4 : ℝ) ≤ Real.sqrt n := Real.sqrt_le_sqrt hnR
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  -- `mySeq n ≤ 3 ^ (Nat.sqrt (2n) + 1)`
  have hup : (mySeq n : ℝ) ≤ (3 : ℝ) ^ (Nat.sqrt (2 * n) + 1) := by exact_mod_cast mySeq_le n
  have hlogup : Real.log (mySeq n) ≤ ((Nat.sqrt (2 * n) : ℝ) + 1) * Real.log 3 := by
    have h := Real.log_le_log (by exact_mod_cast mySeq_pos n) hup
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
  -- `Nat.sqrt (2n) ≤ √(2n) ≤ 1.5 √n`
  have hs2 : (Nat.sqrt (2 * n) : ℝ) ≤ 1.5 * Real.sqrt n := by
    have h1 : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt ((2 * n : ℕ) : ℝ) := natSqrt_le_sqrt _
    have h2 : Real.sqrt ((2 * n : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt n := by
      push_cast; rw [Real.sqrt_mul (by norm_num)]
    have h3 : Real.sqrt 2 ≤ 1.5 := by
      have h : Real.sqrt (2 : ℝ) ≤ Real.sqrt (1.5 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      rwa [Real.sqrt_sq (by norm_num)] at h
    have h4 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    nlinarith
  have hlog3pos : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  nlinarith [hlogup, hs2, hlog3, hlog2, hsq2]

/-- **R1 fails for every `α > 1/2`.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses log_mySeq_upper]
theorem not_hasIntermediateGrowth {α : ℝ} (hα : 1 / 2 < α) :
    ¬ Bugeaud06.HasIntermediateGrowth α mySeq := by
  intro H
  have hr : (0 : ℝ) < α - 1 / 2 := by linarith
  have hbig : ∀ᶠ (n : ℕ) in atTop, (4 : ℝ) ≤ (n : ℝ) ^ (α - 1 / 2) :=
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  obtain ⟨n, ⟨⟨hH, hup⟩, hb, hn2⟩⟩ :=
    ((H.and log_mySeq_upper).and (hbig.and (Filter.eventually_ge_atTop 2))).exists
  have hn0R : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hsq0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0R
  -- `nᵅ = √n · n^{α-1/2} ≥ 4√n > 3√n ≥ log mₙ`
  have hsplit : (n : ℝ) ^ α = Real.sqrt n * (n : ℝ) ^ (α - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0R]
    ring_nf
  have hlt : 3 * Real.sqrt n < (n : ℝ) ^ α := by
    rw [hsplit]; nlinarith
  have hcon : Real.log (mySeq n) < (n : ℝ) ^ α := lt_of_le_of_lt hup hlt
  have hexp : (mySeq n : ℝ) < Real.exp ((n : ℝ) ^ α) := by
    calc (mySeq n : ℝ) = Real.exp (Real.log (mySeq n)) :=
          (Real.exp_log (by exact_mod_cast mySeq_pos n)).symm
      _ < Real.exp ((n : ℝ) ^ α) := Real.exp_lt_exp.2 hcon
  linarith [hH]

/-- **Superpolynomial growth.** -/
@[category research solved, AMS 11, group "bugeaud_10_6", formal_uses log_mySeq_lower]
theorem mySeq_superPoly (j : ℕ) : ∀ᶠ (n : ℕ) in atTop, (n : ℝ) ^ j ≤ (mySeq n : ℝ) := by
  set c : ℝ := 1 / (10 * (j + 1)) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  filter_upwards [log_mySeq_lower, eventually_log_le (c := c) (r := (1 : ℝ) / 4) hc0 (by norm_num),
    Filter.eventually_ge_atTop 2] with n hlow hlo hn2
  have hn1R : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn2
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos hn1R
  -- `10 j (log n)² ≤ √n`
  have hsq : Real.log n ^ 2 ≤ c ^ 2 * Real.sqrt n := by
    have h1 : Real.log n ^ 2 ≤ (c * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by nlinarith [hlogpos.le]
    have h2 : (c * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = c ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hn0R.le]
      norm_num
    rw [h2, ← Real.sqrt_eq_rpow] at h1
    exact h1
  have hcj : (10 : ℝ) * j * c ^ 2 ≤ 1 := by
    rw [hc]
    have hj : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
    nlinarith
  have hstep : (j : ℝ) * Real.log n ≤ Real.sqrt n / (10 * Real.log n) := by
    rw [le_div_iff₀ (by positivity)]
    have hj : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    nlinarith [hsq, hcj, Real.sqrt_nonneg (n : ℝ)]
  have hfin : Real.log ((n : ℝ) ^ j) ≤ Real.log (mySeq n) := by
    rw [Real.log_pow]
    exact le_trans hstep hlow
  calc (n : ℝ) ^ j = Real.exp (Real.log ((n : ℝ) ^ j)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (Real.log (mySeq n)) := Real.exp_le_exp.2 hfin
    _ = (mySeq n : ℝ) := Real.exp_log (by exact_mod_cast mySeq_pos n)

/-! ## The ratio tends to one -/

/-- A single step never adds more than `1 + mₙ/(log₂ k + 1)`: inside a block it adds exactly one,
and at a block boundary it adds `1 + ⌊blockStart k/(log₂(k+2)+1)⌋`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem mySeq_succ_le (n : ℕ) :
    (mySeq (n + 1) : ℝ)
      ≤ (mySeq n : ℝ) + 1 + (mySeq n : ℝ) / ((Nat.log 2 (blockIdx n + 2) : ℝ) + 1) := by
  have hd : (0 : ℝ) < (Nat.log 2 (blockIdx n + 2) : ℝ) + 1 := by positivity
  have hmpos : (0 : ℝ) < (mySeq n : ℝ) := by exact_mod_cast mySeq_pos n
  rcases blockIdx_succ n with h | ⟨_, hn⟩
  · have heq : mySeq (n + 1) = mySeq n + 1 := by
      have h₁ := tri_le_blockIdx n
      simp only [mySeq, blockOff, h]
      omega
    have : (0 : ℝ) ≤ (mySeq n : ℝ) / ((Nat.log 2 (blockIdx n + 2) : ℝ) + 1) := by positivity
    rw [heq]; push_cast; linarith
  · set k := blockIdx n with hk
    have hn1 : n = tri k + k := by have := tri_succ k; omega
    have hmn : mySeq n = blockStart k + k := by rw [hn1]; exact mySeq_tri_add k k le_rfl
    have hm1 : mySeq (n + 1) = blockStart (k + 1) := by
      rw [hn]; simpa using mySeq_tri_add (k + 1) 0 (Nat.zero_le _)
    have hq : ((blockStart k / (Nat.log 2 (k + 2) + 1) : ℕ) : ℝ)
        ≤ (blockStart k : ℝ) / ((Nat.log 2 (k + 2) : ℝ) + 1) := by
      have h := Nat.cast_div_le (α := ℝ) (m := blockStart k) (n := Nat.log 2 (k + 2) + 1)
      push_cast at h; exact h
    have hmono : (blockStart k : ℝ) / ((Nat.log 2 (k + 2) : ℝ) + 1)
        ≤ ((blockStart k : ℝ) + k) / ((Nat.log 2 (k + 2) : ℝ) + 1) := by
      have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      rw [div_le_div_iff₀ hd hd]
      nlinarith
    rw [hm1, blockStart_succ, hmn]
    push_cast
    linarith

@[category API, AMS 11, group "bugeaud_10_6"]
theorem mySeq_ratio_le (n : ℕ) :
    (mySeq (n + 1) : ℝ) / mySeq n
      ≤ 1 + 1 / ((n : ℝ) + 2) + 1 / ((Nat.log 2 (blockIdx n + 2) : ℝ) + 1) := by
  have hmpos : (0 : ℝ) < (mySeq n : ℝ) := by exact_mod_cast mySeq_pos n
  have hd : (0 : ℝ) < (Nat.log 2 (blockIdx n + 2) : ℝ) + 1 := by positivity
  have hge : ((n : ℝ) + 2) ≤ (mySeq n : ℝ) := by exact_mod_cast add_two_le_mySeq n
  rw [div_le_iff₀ hmpos]
  have hstep := mySeq_succ_le n
  have h1 : (1 : ℝ) ≤ (mySeq n : ℝ) * (1 / ((n : ℝ) + 2)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    linarith
  have h2 : (mySeq n : ℝ) / ((Nat.log 2 (blockIdx n + 2) : ℝ) + 1)
      = (mySeq n : ℝ) * (1 / ((Nat.log 2 (blockIdx n + 2) : ℝ) + 1)) := by ring
  nlinarith [hstep, h1, h2]

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blockIdx_tendsto : Tendsto blockIdx atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨tri b, fun a ha => ?_⟩
  have h := blockIdx_mono ha
  rwa [blockIdx_eq_of (le_refl (tri b)) (tri_strictMono (Nat.lt_succ_self b))] at h

@[category API, AMS 11, group "bugeaud_10_6"]
theorem logBlockIdx_tendsto : Tendsto (fun n => Nat.log 2 (blockIdx n + 2)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨tri (2 ^ b), fun a ha => ?_⟩
  have h := blockIdx_mono ha
  rw [blockIdx_eq_of (le_refl (tri (2 ^ b))) (tri_strictMono (Nat.lt_succ_self _))] at h
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

/-- **The ratios tend to one.**  This is the sublacunarity half of the counterexample; in the
inherited project it was the statement that invoked the missing `mySeq_strictMono`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses mySeq_ratio_le logBlockIdx_tendsto]
theorem mySeq_ratio_tendsto :
    Tendsto (fun n => (mySeq (n + 1) : ℝ) / mySeq n) atTop (nhds 1) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ 2
      (tendsto_natCast_atTop_atTop))
  have h2 : Tendsto (fun n : ℕ => 1 / ((Nat.log 2 (blockIdx n + 2) : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.comp logBlockIdx_tendsto))
  have hub : Tendsto
      (fun n : ℕ => 1 + 1 / ((n : ℝ) + 2) + 1 / ((Nat.log 2 (blockIdx n + 2) : ℝ) + 1))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add h1).add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards with n
    rw [le_div_iff₀ (by exact_mod_cast mySeq_pos n)]
    have : mySeq n ≤ mySeq (n + 1) := mySeq_strictMono.monotone (Nat.le_succ n)
    have : (mySeq n : ℝ) ≤ (mySeq (n + 1) : ℝ) := by exact_mod_cast this
    linarith
  · filter_upwards with n using mySeq_ratio_le n

/-! ## R3 fails -/

/-- **`mySeq` is not genuinely sublacunary.**  Inside a block the ratio is `1 + 1/mₙ`, and
`mₙ ≥ n + 2` dwarfs `log n`, so no floor `1 + c/log n` can hold eventually.  This is the half of
the calibration that matters: the block sequence defeats R1 *and* R2, but R3 sees it. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6"]
theorem not_isGenuinelySublacunary : ¬ Bugeaud06.IsGenuinelySublacunary mySeq := by
  rintro ⟨c, hc, H⟩
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 H
  obtain ⟨N₂, hN₂⟩ :=
    Filter.eventually_atTop.1 (eventually_log_le (c := c) (r := (1 : ℝ)) hc one_pos)
  set L := max (max N₁ N₂) 2 with hL
  have hL2 : 2 ≤ L := le_max_right _ _
  set n := tri L with hn
  have hLn : L ≤ n := by
    have h := two_mul_tri L
    rw [hn]; nlinarith
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 2)) hLn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 2)) hLn
  -- the two consecutive terms lie in the same block
  have h0 : mySeq n = blockStart L := by rw [hn]; simpa using mySeq_tri_add L 0 (Nat.zero_le _)
  have h1 : mySeq (n + 1) = blockStart L + 1 := by
    rw [hn]; exact mySeq_tri_add L 1 (by omega)
  have hstep : (mySeq (n + 1) : ℝ) / mySeq n = 1 + 1 / (mySeq n : ℝ) := by
    rw [h0, h1]
    have : (0 : ℝ) < (blockStart L : ℝ) := by exact_mod_cast blockStart_pos L
    push_cast; field_simp
  -- the numbers
  have hmpos : (0 : ℝ) < (mySeq n : ℝ) := by exact_mod_cast mySeq_pos n
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hL2 hLn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hgen := hN₁ n hnN₁
  rw [hstep] at hgen
  have hcmp : c / Real.log n ≤ 1 / (mySeq n : ℝ) := by linarith
  have hkey : c * (mySeq n : ℝ) ≤ Real.log n := by
    rw [div_le_div_iff₀ hlogpos hmpos] at hcmp
    linarith
  -- but `log n ≤ c·n < c·mₙ`
  have hup := hN₂ n hnN₂
  rw [Real.rpow_one] at hup
  have hge : ((n : ℝ) + 2) ≤ (mySeq n : ℝ) := by exact_mod_cast add_two_le_mySeq n
  nlinarith [hkey, hup, hge, hc]

/-! ## Proposition B -/

/-- **Proposition B.**  Aristotle's block sequence is strictly increasing, has ratios tending to
one, is superpolynomial, is universally densifying, satisfies R1 for every `α < 1/2` and fails it
for every `α > 1/2`, and fails R3 for every `c > 0`.

The calibration this is for: the reading it was built to defeat demanded exactly sublacunarity and
superpolynomiality; the repair "`mₙ ≥ exp(nᵅ)` with `α > 1/2`" excludes it, and the recorded
weakening to "`0 < α < 1`" readmits it.  By Theorem A even `α > 1/2` was never enough. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses mySeq_strictMono mySeq_ratio_tendsto mySeq_superPoly mySeq_universallyDensifying
    mySeq_hasIntermediateGrowth not_hasIntermediateGrowth not_isGenuinelySublacunary]
theorem proposition_B :
    StrictMono mySeq ∧
    Tendsto (fun n => (mySeq (n + 1) : ℝ) / mySeq n) atTop (nhds 1) ∧
    (∀ j : ℕ, ∀ᶠ (n : ℕ) in atTop, (n : ℝ) ^ j ≤ (mySeq n : ℝ)) ∧
    UniversallyDensifying mySeq ∧
    (∀ α : ℝ, 0 < α → α < 1 / 2 → Bugeaud06.HasIntermediateGrowth α mySeq) ∧
    (∀ α : ℝ, 1 / 2 < α → ¬ Bugeaud06.HasIntermediateGrowth α mySeq) ∧
    ¬ Bugeaud06.IsGenuinelySublacunary mySeq :=
  ⟨mySeq_strictMono, mySeq_ratio_tendsto, mySeq_superPoly, mySeq_universallyDensifying,
    fun _ h₀ h₁ => mySeq_hasIntermediateGrowth h₀ h₁, fun _ h => not_hasIntermediateGrowth h,
    not_isGenuinelySublacunary⟩

end BB6
