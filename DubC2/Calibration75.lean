/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.SevenFifthsCore
import Z32.DubickasWord
import Mathlib.Analysis.SpecificLimits.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Calibration: [DN05] Theorem 4(iii) — the base `7/5` at `𝒫 = {2,3,5,11}`

Target T3(ii) of `plans/plan-dubC2.html`, the second of the three calibrations.

> **[DN05] Thm 4(iii).**  For every real `ξ ≠ 0`, infinitely many of `[ξ(7/5)ⁿ + ½]` are
> divisible by `2`, `3`, `5` or `11`.

This is the deepest of the three shifted-integer-part theorems of [DN05] §6, and the one whose
shape is closest to the `3/2` capstone of `DubC2/Nearest.lean` — but it is the first in which
the two rails, arithmetic and interval, must be interleaved rather than run in sequence.

* **`2` and `5` cut the alphabet.**  `2 ∤ xₙ` makes `sₙ` even and `5 ∤ xₙ` makes it prime to `5`;
  with `|sₙ| ≤ 5` that leaves `sₙ ∈ {−4,−2,2,4}` (`DubC2.s75_mem`).
* **`3` splits the four letters into two orientations.**  `sₙ ≡ 2 (mod 3)` for `−4` and `2`,
  `sₙ ≡ 1 (mod 3)` for `−2` and `4`, and each forces a residue of `xₙ` mod `3` that the step map
  then preserves (`DubC2.res3_const`).  So an avoiding orbit uses either `A = −4`, `C = 2` only,
  or `B = −2`, `D = 4` only.  This is what makes a branch table possible at all: the four raw
  windows `[0,2/7)`, `[0,4/7)`, `[3/7,1)`, `[5/7,1)` overlap, so the letter is *not* a function
  of `yₙ`; within one orientation the two windows are disjoint and it is.
* **The intervals then force the word into two blocks**, and `11` finishes.  Both steps live in
  `DubC2/SevenFifthsCore.lean`, which proves them once for an abstract orbit satisfying the
  window hypotheses with `≤` on both sides — so the mirror `x ↦ −x`, `y ↦ 1 − y` that [DN05]
  dispatches with "this makes no difference in our argument" is discharged by applying the same
  theorem to `DubC2.data_BD` instead of `DubC2.data_AC`, rather than by repeating the argument
  with reversed endpoints.

## Where this sits among the three calibrations

| base | `𝒫` | what prunes | surviving words |
|---|---|---|---|
| `3/2` (capstone) | `{2,5}` | residues mod `5` only; the windows partition `[0,1)` | `(AABB)^∞` |
| `5/3` (T3(i)) | `{2,3}` | the gap `[2/5,3/5)` only; residues are spent on the alphabet | `(A²B²)^∞`, `(AB)^∞` |
| `7/5` (here) | `{2,3,5,11}` | `2,5` on the alphabet, `3` on the orientation, then gap **and** `11` | `V^∞`, `U^∞`, `(ACC)^∞` |

## Main results

* `DubC2.round_divisor_set_seven_fifths` — the theorem above.
* `DubC2.round_composite_seven_fifths` — the composite corollary for `ξ > 0`.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Theorem 4(iii) and §6.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — Lemma 2.
-/

namespace DubC2

open Filter ForMathlib.SubwordComplexity

variable {ξ : ℝ} {N n : ℕ}

/-! ## The model at `(p, q, ν) = (7, 5, 1/2)` -/

/-- `xₙ = [ξ(7/5)ⁿ + ½]`. -/
noncomputable def x75 (ξ : ℝ) (n : ℕ) : ℤ := Z32.xInt 7 5 ξ (1 / 2) n

/-- `yₙ = {ξ(7/5)ⁿ + ½}`. -/
noncomputable def y75 (ξ : ℝ) (n : ℕ) : ℝ := Z32.yFract 7 5 ξ (1 / 2) n

/-- `sₙ = 5x_{n+1} − 7xₙ`. -/
noncomputable def s75 (ξ : ℝ) (n : ℕ) : ℤ := Z32.carry 7 5 ξ (1 / 2) n

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem x75_eq_round (ξ : ℝ) (n : ℕ) : x75 ξ n = round (ξ * ((7 : ℝ) / 5) ^ n) := by
  rw [x75, Z32.xInt, Z32.orb, round_eq]
  norm_num

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_75"]
theorem y75_nonneg (ξ : ℝ) (n : ℕ) : 0 ≤ y75 ξ n := Z32.yFract_nonneg n

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_75"]
theorem y75_lt_one (ξ : ℝ) (n : ℕ) : y75 ξ n < 1 := Z32.yFract_lt_one n

/-- [Dub09AA] (3) at `(7, 5, 1/2)`: `sₙ = 7yₙ − 5y_{n+1} − 1`. -/
@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_75"]
theorem s75_eq (ξ : ℝ) (n : ℕ) : (s75 ξ n : ℝ) = 7 * y75 ξ n - 5 * y75 ξ (n + 1) - 1 := by
  have h := Z32.carry_eq (p := 7) (q := 5) (ξ := ξ) (ν := 1 / 2) (by norm_num) n
  simp only [s75, y75]
  push_cast at h ⊢
  linarith

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_75"]
theorem five_mul_x75_succ (ξ : ℝ) (n : ℕ) :
    5 * x75 ξ (n + 1) = 7 * x75 ξ n + s75 ξ n := by
  simp only [s75, x75, Z32.carry]
  push_cast
  ring

/-- **Avoidance of `𝒫 = {2,3,5,11}`.** -/
def Avoids75 (ξ : ℝ) (n : ℕ) : Prop :=
  ¬ (2 : ℤ) ∣ x75 ξ n ∧ ¬ (3 : ℤ) ∣ x75 ξ n ∧ ¬ (5 : ℤ) ∣ x75 ξ n ∧ ¬ (11 : ℤ) ∣ x75 ξ n

/-! ## `2` and `5` cut the alphabet to `{−4,−2,2,4}` -/

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_75"]
theorem abs_s75_le_five (ξ : ℝ) (n : ℕ) : -5 ≤ s75 ξ n ∧ s75 ξ n ≤ 5 := by
  have h := s75_eq ξ n
  have h0 := y75_nonneg ξ n
  have h1 := y75_lt_one ξ n
  have h2 := y75_nonneg ξ (n + 1)
  have h3 := y75_lt_one ξ (n + 1)
  have hup : s75 ξ n < 6 := by
    by_contra hc
    push Not at hc
    have : (6 : ℝ) ≤ (s75 ξ n : ℝ) := by exact_mod_cast hc
    linarith
  have hlo : -6 < s75 ξ n := by
    by_contra hc
    push Not at hc
    have : (s75 ξ n : ℝ) ≤ -6 := by exact_mod_cast hc
    linarith
  omega

/-- **Four letters.**  `2 ∤ xₙ` and `2 ∤ x_{n+1}` make `sₙ` even, `5 ∤ xₙ` makes it prime to `5`;
with `|sₙ| ≤ 5` only `±2, ±4` remain. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem s75_mem (h : Avoids75 ξ n) (h' : Avoids75 ξ (n + 1)) :
    s75 ξ n = -4 ∨ s75 ξ n = -2 ∨ s75 ξ n = 2 ∨ s75 ξ n = 4 := by
  have hrec := five_mul_x75_succ ξ n
  have hb := abs_s75_le_five ξ n
  obtain ⟨h2, -, h5, -⟩ := h
  obtain ⟨h2', -, -, -⟩ := h'
  omega

/-! ## `3` fixes the orientation -/

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem res3_mem (h : Avoids75 ξ n) : x75 ξ n % 3 = 1 ∨ x75 ξ n % 3 = 2 := by
  obtain ⟨-, h3, -, -⟩ := h
  omega

/-- **The residue mod `3` is an invariant.**  Every one of the four letters kills one of the two
nonzero residues, so the surviving one is reproduced. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem res3_succ (h : Avoids75 ξ n) (h' : Avoids75 ξ (n + 1)) :
    x75 ξ (n + 1) % 3 = x75 ξ n % 3 := by
  have hrec := five_mul_x75_succ ξ n
  have hs := s75_mem h h'
  obtain ⟨-, h3, -, -⟩ := h
  obtain ⟨-, h3', -, -⟩ := h'
  have hx : x75 ξ n % 3 = 1 ∨ x75 ξ n % 3 = 2 := by omega
  have hx' : x75 ξ (n + 1) % 3 = 1 ∨ x75 ξ (n + 1) % 3 = 2 := by omega
  rcases hs with hs | hs | hs | hs <;> rw [hs] at hrec <;>
    rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;> omega

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem res3_const (hav : ∀ m, N ≤ m → Avoids75 ξ m) (k : ℕ) :
    x75 ξ (N + k) % 3 = x75 ξ N % 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hst := res3_succ (hav (N + k) (by omega)) (hav (N + k + 1) (by omega))
    rw [show N + (k + 1) = N + k + 1 from rfl]
    omega

/-- **Orientation `A,C`**: `xₙ ≡ 2 (mod 3)` admits only `sₙ = −4` and `sₙ = 2`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem s75_AC (h : Avoids75 ξ n) (h' : Avoids75 ξ (n + 1)) (h3 : x75 ξ n % 3 = 2) :
    s75 ξ n = -4 ∨ s75 ξ n = 2 := by
  have hrec := five_mul_x75_succ ξ n
  have hs := s75_mem h h'
  obtain ⟨-, h3', -, -⟩ := h'
  rcases hs with hs | hs | hs | hs
  · exact Or.inl hs
  · exfalso; rw [hs] at hrec; omega
  · exact Or.inr hs
  · exfalso; rw [hs] at hrec; omega

/-- **Orientation `B,D`**: `xₙ ≡ 1 (mod 3)` admits only `sₙ = −2` and `sₙ = 4`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem s75_BD (h : Avoids75 ξ n) (h' : Avoids75 ξ (n + 1)) (h3 : x75 ξ n % 3 = 1) :
    s75 ξ n = -2 ∨ s75 ξ n = 4 := by
  have hrec := five_mul_x75_succ ξ n
  have hs := s75_mem h h'
  obtain ⟨-, h3', -, -⟩ := h'
  rcases hs with hs | hs | hs | hs
  · exfalso; rw [hs] at hrec; omega
  · exact Or.inl hs
  · exfalso; rw [hs] at hrec; omega
  · exact Or.inr hs

/-! ## The four windows

`sₙ = −4` needs `y_{n+1} < 1`, `sₙ = 2` needs `y_{n+1} ≥ 0`, and so on; each letter pins `yₙ` to
one half-line.  The four half-lines overlap — which is why the orientation has to be fixed
before a branch table exists. -/

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem window_A (hs : s75 ξ n = -4) :
    y75 ξ n < 2 / 7 ∧ 5 * y75 ξ (n + 1) = 7 * y75 ξ n + 3 := by
  have he := s75_eq ξ n
  rw [hs] at he
  push_cast at he
  exact ⟨by have := y75_lt_one ξ (n + 1); linarith, by linarith⟩

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem window_C (hs : s75 ξ n = 2) :
    3 / 7 ≤ y75 ξ n ∧ 5 * y75 ξ (n + 1) = 7 * y75 ξ n - 3 := by
  have he := s75_eq ξ n
  rw [hs] at he
  push_cast at he
  exact ⟨by have := y75_nonneg ξ (n + 1); linarith, by linarith⟩

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem window_B (hs : s75 ξ n = -2) :
    y75 ξ n < 4 / 7 ∧ 5 * y75 ξ (n + 1) = 7 * y75 ξ n + 1 := by
  have he := s75_eq ξ n
  rw [hs] at he
  push_cast at he
  exact ⟨by have := y75_lt_one ξ (n + 1); linarith, by linarith⟩

@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem window_D (hs : s75 ξ n = 4) :
    5 / 7 ≤ y75 ξ n ∧ 5 * y75 ξ (n + 1) = 7 * y75 ξ n - 5 := by
  have he := s75_eq ξ n
  rw [hs] at he
  push_cast at he
  exact ⟨by have := y75_nonneg ξ (n + 1); linarith, by linarith⟩

/-! ## The two instances of the abstract core -/

/-- **The `A,C` orientation is an `AC.Data`.**  The two windows `[0,2/7)` and `[3/7,1)` are
disjoint, so the letter is a function of `yₙ`, and the gap `[2/7,3/7)` is empty. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem data_AC (hav : ∀ m, N ≤ m → Avoids75 ξ m) (h3 : x75 ξ N % 3 = 2) :
    AC.Data (fun n => x75 ξ (N + n)) (fun n => y75 ξ (N + n)) (fun n => s75 ξ (N + n)) := by
  have hres : ∀ k, x75 ξ (N + k) % 3 = 2 := fun k => by rw [res3_const hav k]; exact h3
  have hlet : ∀ n, s75 ξ (N + n) = -4 ∨ s75 ξ (N + n) = 2 := fun n =>
    s75_AC (hav (N + n) (Nat.le_add_right N n)) (hav (N + n + 1) (by omega)) (hres n)
  have hd : ∀ n, y75 ξ (N + n) ≤ 2 / 7 ∨ 3 / 7 ≤ y75 ξ (N + n) := by
    intro n
    rcases hlet n with hs | hs
    · exact Or.inl (window_A hs).1.le
    · exact Or.inr (window_C hs).1
  have hA : ∀ n, y75 ξ (N + n) ≤ 2 / 7 →
      s75 ξ (N + n) = -4 ∧ 5 * y75 ξ (N + (n + 1)) = 7 * y75 ξ (N + n) + 3 ∧
        5 * x75 ξ (N + (n + 1)) = 7 * x75 ξ (N + n) - 4 := by
    intro n hy
    have hs : s75 ξ (N + n) = -4 := by
      rcases hlet n with hs | hs
      · exact hs
      · exfalso; have := (window_C hs).1; linarith
    have hrec := five_mul_x75_succ ξ (N + n)
    rw [show N + (n + 1) = N + n + 1 from rfl]
    exact ⟨hs, (window_A hs).2, by omega⟩
  have hC : ∀ n, 3 / 7 ≤ y75 ξ (N + n) →
      s75 ξ (N + n) = 2 ∧ 5 * y75 ξ (N + (n + 1)) = 7 * y75 ξ (N + n) - 3 ∧
        5 * x75 ξ (N + (n + 1)) = 7 * x75 ξ (N + n) + 2 := by
    intro n hy
    have hs : s75 ξ (N + n) = 2 := by
      rcases hlet n with hs | hs
      · exfalso; have := (window_A hs).1; linarith
      · exact hs
    have hrec := five_mul_x75_succ ξ (N + n)
    rw [show N + (n + 1) = N + n + 1 from rfl]
    exact ⟨hs, (window_C hs).2, by omega⟩
  exact ⟨fun n => y75_nonneg ξ _, fun n => (y75_lt_one ξ _).le, hd, hA, hC,
    fun n => (hav (N + n) (Nat.le_add_right N n)).2.2.2⟩

/-- **The `B,D` orientation is an `AC.Data` after the mirror** `x ↦ −x`, `y ↦ 1 − y`, `s ↦ −s`:
`D` becomes `A` and `B` becomes `C`.  The mirrored windows are `(0,2/7]` and `(3/7,1]`, which is
exactly why `AC.Data` states them with `≤` on both sides. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem data_BD (hav : ∀ m, N ≤ m → Avoids75 ξ m) (h3 : x75 ξ N % 3 = 1) :
    AC.Data (fun n => -x75 ξ (N + n)) (fun n => 1 - y75 ξ (N + n))
      (fun n => -s75 ξ (N + n)) := by
  have hres : ∀ k, x75 ξ (N + k) % 3 = 1 := fun k => by rw [res3_const hav k]; exact h3
  have hlet : ∀ n, s75 ξ (N + n) = -2 ∨ s75 ξ (N + n) = 4 := fun n =>
    s75_BD (hav (N + n) (Nat.le_add_right N n)) (hav (N + n + 1) (by omega)) (hres n)
  have hd : ∀ n, 1 - y75 ξ (N + n) ≤ 2 / 7 ∨ 3 / 7 ≤ 1 - y75 ξ (N + n) := by
    intro n
    rcases hlet n with hs | hs
    · exact Or.inr (by have := (window_B hs).1; linarith)
    · exact Or.inl (by have := (window_D hs).1; linarith)
  have hA : ∀ n, 1 - y75 ξ (N + n) ≤ 2 / 7 →
      -s75 ξ (N + n) = -4 ∧ 5 * (1 - y75 ξ (N + (n + 1))) = 7 * (1 - y75 ξ (N + n)) + 3 ∧
        5 * -x75 ξ (N + (n + 1)) = 7 * -x75 ξ (N + n) - 4 := by
    intro n hy
    have hs : s75 ξ (N + n) = 4 := by
      rcases hlet n with hs | hs
      · exfalso; have := (window_B hs).1; linarith
      · exact hs
    have hrec := five_mul_x75_succ ξ (N + n)
    rw [show N + (n + 1) = N + n + 1 from rfl]
    exact ⟨by omega, by have := (window_D hs).2; linarith, by omega⟩
  have hC : ∀ n, 3 / 7 ≤ 1 - y75 ξ (N + n) →
      -s75 ξ (N + n) = 2 ∧ 5 * (1 - y75 ξ (N + (n + 1))) = 7 * (1 - y75 ξ (N + n)) - 3 ∧
        5 * -x75 ξ (N + (n + 1)) = 7 * -x75 ξ (N + n) + 2 := by
    intro n hy
    have hs : s75 ξ (N + n) = -2 := by
      rcases hlet n with hs | hs
      · exact hs
      · exfalso; have := (window_D hs).1; linarith
    have hrec := five_mul_x75_succ ξ (N + n)
    rw [show N + (n + 1) = N + n + 1 from rfl]
    exact ⟨by omega, by have := (window_B hs).2; linarith, by omega⟩
  have hnn : ∀ n, (0 : ℝ) ≤ 1 - y75 ξ (N + n) := fun n => by
    have := y75_lt_one ξ (N + n); linarith
  have hle : ∀ n, 1 - y75 ξ (N + n) ≤ 1 := fun n => by
    have := y75_nonneg ξ (N + n); linarith
  have hav11 : ∀ n, ¬ (11 : ℤ) ∣ -x75 ξ (N + n) := fun n => by
    have := (hav (N + n) (Nat.le_add_right N n)).2.2.2; omega
  exact ⟨hnn, hle, hd, hA, hC, hav11⟩

/-! ## Eventual periodicity, and the theorem -/

/-- The carry word of an orbit avoiding `{2,3,5,11}` is eventually periodic — with period `6` or
`9` if a 3-position ever occurs and `3` otherwise, in whichever of the two orientations the
residue mod `3` selects. -/
@[category research solved, AMS 11 68, ref "DN05", group "dn05_nearest_75"]
theorem isEventuallyPeriodic_s75 (hav : ∀ m, N ≤ m → Avoids75 ξ m) :
    IsEventuallyPeriodic (s75 ξ) := by
  have hshift : IsEventuallyPeriodic (fun n => s75 ξ (N + n)) := by
    rcases res3_mem (hav N le_rfl) with h3 | h3
    · obtain ⟨M, P, hP, hper⟩ := AC.isEventuallyPeriodic (data_BD hav h3)
      refine ⟨M, P, hP, fun k hk => ?_⟩
      have h2 : -s75 ξ (N + (k + P)) = -s75 ξ (N + k) := hper k hk
      exact neg_injective h2
    · exact AC.isEventuallyPeriodic (data_AC hav h3)
  obtain ⟨M, P, hP, hper⟩ := hshift
  refine ⟨N + M, P, hP, fun m hm => ?_⟩
  have h2 : s75 ξ (N + (m - N + P)) = s75 ξ (N + (m - N)) := hper (m - N) (by omega)
  rw [show N + (m - N + P) = m + P by omega, show N + (m - N) = m by omega] at h2
  exact h2

/-- **[DN05] Theorem 4(iii), formalised.**  For every real `ξ ≠ 0`, infinitely many of the
nearest integers `[ξ(7/5)ⁿ + ½]` are divisible by `2`, `3`, `5` or `11`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem round_divisor_set_seven_fifths (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ round (ξ * ((7 : ℝ) / 5) ^ n) ∨
      (3 : ℤ) ∣ round (ξ * ((7 : ℝ) / 5) ^ n) ∨ (5 : ℤ) ∣ round (ξ * ((7 : ℝ) / 5) ^ n) ∨
      (11 : ℤ) ∣ round (ξ * ((7 : ℝ) / 5) ^ n) := by
  rw [Filter.frequently_atTop]
  intro N
  by_contra hc
  push Not at hc
  have hav : ∀ m, N ≤ m → Avoids75 ξ m := by
    intro m hm
    have := hc m hm
    rw [← x75_eq_round] at this
    exact this
  have hper : IsEventuallyPeriodic (Z32.carry 7 5 ξ (1 / 2)) := isEventuallyPeriodic_s75 hav
  exact Z32.not_isEventuallyPeriodic_carry (p := 7) (q := 5) (ξ := ξ) (ν := 1 / 2)
    (by norm_num) (by norm_num) (by decide) hξ hper

/-- The same statement in the `∃ p ∈ 𝒫` shape of the plan. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem round_divisor_set_mem_seven_fifths (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ p ∈ ({2, 3, 5, 11} : Set ℕ),
      (p : ℤ) ∣ round (ξ * ((7 : ℝ) / 5) ^ n) := by
  refine (round_divisor_set_seven_fifths hξ).mono ?_
  rintro n (h | h | h | h)
  · exact ⟨2, by simp, by exact_mod_cast h⟩
  · exact ⟨3, by simp, by exact_mod_cast h⟩
  · exact ⟨5, by simp, by exact_mod_cast h⟩
  · exact ⟨11, by simp, by exact_mod_cast h⟩

/-- The composite corollary at `7/5`, for `ξ > 0`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_75"]
theorem round_composite_seven_fifths (hξ : 0 < ξ) :
    ∃ᶠ n in atTop, ¬ Prime (round (ξ * ((7 : ℝ) / 5) ^ n)) ∧
      1 < round (ξ * ((7 : ℝ) / 5) ^ n) := by
  have hgrow : ∀ᶠ n in atTop, (11 : ℤ) < round (ξ * ((7 : ℝ) / 5) ^ n) := by
    have h1 : Tendsto (fun n : ℕ => ξ * ((7 : ℝ) / 5) ^ n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hξ (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    refine (h1.eventually_gt_atTop 12).mono fun n hn => ?_
    have hr : |ξ * ((7 : ℝ) / 5) ^ n - round (ξ * ((7 : ℝ) / 5) ^ n)| ≤ 1 / 2 := abs_sub_round _
    have : (11 : ℝ) < (round (ξ * ((7 : ℝ) / 5) ^ n) : ℝ) := by
      cases abs_le.mp hr with
      | intro hlo hhi => linarith
    exact_mod_cast this
  refine ((round_divisor_set_seven_fifths hξ.ne').and_eventually hgrow).mono ?_
  rintro n ⟨hdvd, hgt⟩
  set z : ℤ := round (ξ * ((7 : ℝ) / 5) ^ n) with hz
  have hnat : (11 : ℕ) < z.natAbs := by omega
  refine ⟨fun hp => ?_, by omega⟩
  have hpn : Nat.Prime z.natAbs := Int.prime_iff_natAbs_prime.mp hp
  rcases hdvd with h | h | h | h
  · have h2 : (2 : ℕ) ∣ z.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; simpa using this
    rcases hpn.eq_one_or_self_of_dvd 2 h2 with h1 | h1 <;> omega
  · have h3 : (3 : ℕ) ∣ z.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; simpa using this
    rcases hpn.eq_one_or_self_of_dvd 3 h3 with h1 | h1 <;> omega
  · have h5 : (5 : ℕ) ∣ z.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; simpa using this
    rcases hpn.eq_one_or_self_of_dvd 5 h5 with h1 | h1 <;> omega
  · have h11 : (11 : ℕ) ∣ z.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; simpa using this
    rcases hpn.eq_one_or_self_of_dvd 11 h11 with h1 | h1 <;> omega

end DubC2
