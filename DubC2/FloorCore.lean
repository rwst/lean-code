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
# The Forman–Shapiro subshift at base `3/2`: every admissible word is eventually periodic

Target T3(iii) of `plans/plan-dubC2.html`, the combinatorial core of [FS67] Theorem 4.1 —
equivalently of [DN05] Theorem 1 at `a = 3/2`.

This file is **pure arithmetic**: no real numbers occur in it.  The object is an integer
sequence `x` together with a sign word `s` obeying

* `2x_{n+1} = 3xₙ + sₙ` with `sₙ = ±1` (what the floor orbit gives once `xₙ` is odd),
* `sₙ = −1 ⇒ s_{n+1} = +1` (the letter `A` cannot repeat — the *only* input from the
  archimedean side), and
* `xₙ` divisible by none of `5, 7, 11`.

`DubC2.FS.isEventuallyPeriodic` says that any such word is eventually periodic.  Combined with
[DN05] Lemma 2 (`Z32.not_isEventuallyPeriodic_carry`, a theorem in this corpus) this is exactly
[FS67]'s theorem, and it is the shape [SS72] §7 conjectured for its *pseudo-difference
equations*: a finite alphabet `S`, a recursion `bu_{n+1} = au_n + e_n` with `e_n ∈ S`, and a
divisibility conclusion.

## The argument

Write `A` for `sₙ = −1` and `B` for `sₙ = +1`.  `A` is not repeatable, so the word is a
concatenation of blocks `A Bᵏ`, `k ≥ 1`, and `k` is **unbounded** on the archimedean side —
there is no finite block decomposition and no hand funnel of the kind that closes `3/2` at
`ν = ½` (`DubC2/NearestCert.lean`) or `7/5` (`DubC2/SevenFifthsCore.lean`).  The three odd
primes replace it:

* **mod 5** — `A : r ↦ 2 − r` kills `r = 2`, `B : r ↦ 3 − r` kills `r = 3`.  The pairs `{1,2}`
  and `{3,4}` are invariant.  In `{3,4}` the word is forced to `B^∞`; in `{1,2}` every `A`
  sits at `r = 1` and `B` swaps `1 ↔ 2`, so **every `B`-run has even length** ([FS67] Lemma
  4.1, there obtained from the backward sets `Sₙ(5)`).
* **mod 7** — at an `A` position `r ∈ {2,3,6}`; `r = 3` forces `k = 4`, `r = 6` forces `k = 2`,
  and `r = 2` — the `B`-fixed point after one `A` — leaves `k` free.  So `A` positions
  alternate `2, 6, 2, 6, …` after at most one block.
* **mod 11** — the remaining freedom.  At an `r = 2 (mod 7)` position the residue mod `11`
  fixes the admissible run lengths, and the resulting graph on six states has exactly two
  cycles: `10 ↦ 10` (the word `(A B⁴ A B²)^∞`, period `8`) and `1 ↦ 3 ↦ 1` (the word
  `(A B² A B² A B⁶ A B²)^∞`, period `16`).  The first is absorbing and the second has a single
  exit into it.

Both survivors are periodic, so Lemma 2 finishes.  [FS67] needed `p = 13` twice (its Lemmas 4.5
and 4.6); the forward automaton does not — see `plans/note-dubC2-T3iii.html` §2.

## References

* [FS67] W. Forman, H. N. Shapiro, *An arithmetic property of certain rational powers*, Comm.
  Pure Appl. Math. **20** (1967), 561–573 — §4.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Theorem 1 and Lemma 2.
* [SS72] H. N. Shapiro, G. H. Sparer, *Composite values of exponential and related sequences*,
  Comm. Pure Appl. Math. **25** (1972), 569–615 — §7, pseudo-difference equations.
-/

namespace DubC2.FS

open ForMathlib.SubwordComplexity

variable {x s : ℕ → ℤ} {n : ℕ} {c d : ℤ}

/-! ## The abstract data -/

/-- A **Forman–Shapiro word**: integers `x` and signs `s` with `2x_{n+1} = 3xₙ + sₙ`,
`sₙ = ±1`, no two consecutive `−1`s, and `xₙ` prime to `5`, `7` and `11`. -/
structure Data (x s : ℕ → ℤ) : Prop where
  /-- The recursion `2x_{n+1} = 3xₙ + sₙ`. -/
  recur : ∀ n, 2 * x (n + 1) = 3 * x n + s n
  /-- Two letters. -/
  mem : ∀ n, s n = -1 ∨ s n = 1
  /-- **`A²` is impossible** — the one archimedean input. -/
  noAA : ∀ n, s n = -1 → s (n + 1) = 1
  /-- `5 ∤ xₙ`. -/
  av5 : ∀ n, ¬ (5 : ℤ) ∣ x n
  /-- `7 ∤ xₙ`. -/
  av7 : ∀ n, ¬ (7 : ℤ) ∣ x n
  /-- `11 ∤ xₙ`. -/
  av11 : ∀ n, ¬ (11 : ℤ) ∣ x n

/-! ## One step -/

@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem stepA (h : Data x s) (hn : s n = -1) : 2 * x (n + 1) = 3 * x n - 1 := by
  have := h.recur n; omega

@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem stepB (h : Data x s) (hn : s n = 1) : 2 * x (n + 1) = 3 * x n + 1 := by
  have := h.recur n; omega

/-- Residue transport under `A`, modulo `5`: `r ↦ 4r + 2 = 2 − r`. -/
private theorem rA5 {a b : ℤ} (h : 2 * b = 3 * a - 1) {u v : ℤ} (hu : a % 5 = u)
    (hv : (4 * u + 2) % 5 = v) : b % 5 = v := by omega

/-- Residue transport under `A`, modulo `7`: `r ↦ 5r + 3`. -/
private theorem rA7 {a b : ℤ} (h : 2 * b = 3 * a - 1) {u v : ℤ} (hu : a % 7 = u)
    (hv : (5 * u + 3) % 7 = v) : b % 7 = v := by omega

/-- Residue transport under `A`, modulo `11`: `r ↦ 7r + 5`. -/
private theorem rA11 {a b : ℤ} (h : 2 * b = 3 * a - 1) {u v : ℤ} (hu : a % 11 = u)
    (hv : (7 * u + 5) % 11 = v) : b % 11 = v := by omega

/-- Residue transport under `B`, modulo `5`: `r ↦ 4r + 3 = 3 − r`. -/
private theorem rB5 {a b : ℤ} (h : 2 * b = 3 * a + 1) {u v : ℤ} (hu : a % 5 = u)
    (hv : (4 * u + 3) % 5 = v) : b % 5 = v := by omega

/-- Residue transport under `B`, modulo `7`: `r ↦ 5r + 4`. -/
private theorem rB7 {a b : ℤ} (h : 2 * b = 3 * a + 1) {u v : ℤ} (hu : a % 7 = u)
    (hv : (5 * u + 4) % 7 = v) : b % 7 = v := by omega

/-- Residue transport under `B`, modulo `11`: `r ↦ 7r + 6`. -/
private theorem rB11 {a b : ℤ} (h : 2 * b = 3 * a + 1) {u v : ℤ} (hu : a % 11 = u)
    (hv : (7 * u + 6) % 11 = v) : b % 11 = v := by omega

/-- Residue transport across a whole `A B²` block, modulo `11`: `8x_{n+3} = 27xₙ + 1`, so
`r ↦ 2r + 7`.  Stated as one linear relation to keep `omega` away from nested `%`. -/
private theorem rAB2_11 {a b : ℤ} (h : 8 * b = 27 * a + 1) {u v : ℤ} (hu : a % 11 = u)
    (hv : (2 * u + 7) % 11 = v) : b % 11 = v := by omega

/-! ## Runs -/

/-- Under a run of `B`s the residue `4 (mod 5)` — the `B`-fixed point — is preserved. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem run5 (h : Data x s) {k : ℕ} (hs : ∀ j, j < k → s (n + j) = 1) (h1 : x n % 5 = 4) :
    x (n + k) % 5 = 4 := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hk : x (n + k) % 5 = 4 := ih fun j hj => hs j (by omega)
    exact rB5 (stepB h (hs k (by omega))) hk (by norm_num)

/-- Under a run of `B`s the residue `6 (mod 7)` — the `B`-fixed point — is preserved. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem run7 (h : Data x s) {k : ℕ} (hs : ∀ j, j < k → s (n + j) = 1) (h1 : x n % 7 = 6) :
    x (n + k) % 7 = 6 := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hk : x (n + k) % 7 = 6 := ih fun j hj => hs j (by omega)
    exact rB7 (stepB h (hs k (by omega))) hk (by norm_num)

/-- Under a run of `B`s the residue `10 (mod 11)` — the `B`-fixed point — is preserved. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem run11 (h : Data x s) {k : ℕ} (hs : ∀ j, j < k → s (n + j) = 1) (h1 : x n % 11 = 10) :
    x (n + k) % 11 = 10 := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hk : x (n + k) % 11 = 10 := ih fun j hj => hs j (by omega)
    exact rB11 (stepB h (hs k (by omega))) hk (by norm_num)

/-- Under a run of `B`s the residue mod `5` alternates between `1` and `2`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem run5alt (h : Data x s) {k : ℕ} (hs : ∀ j, j < k → s (n + j) = 1) (h1 : x n % 5 = 1) :
    (k % 2 = 0 ∧ x (n + k) % 5 = 1) ∨ (k % 2 = 1 ∧ x (n + k) % 5 = 2) := by
  induction k with
  | zero => exact Or.inl ⟨by norm_num, by simpa using h1⟩
  | succ k ih =>
    have hb := stepB h (hs k (by omega))
    rcases ih (fun j hj => hs j (by omega)) with ⟨hk, hr⟩ | ⟨hk, hr⟩
    · exact Or.inr ⟨by omega, rB5 hb hr (by norm_num)⟩
    · exact Or.inl ⟨by omega, rB5 hb hr (by norm_num)⟩

/-- **The next `A`.**  If `−1` occurs infinitely often, every `A` position is followed by a
first later one, with a nonempty run of `B`s in between. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem nextA (h : Data x s) (hinf : ∀ N, ∃ m, N ≤ m ∧ s m = -1) (hA : s n = -1) :
    ∃ k, 1 ≤ k ∧ (∀ j, j < k → s (n + 1 + j) = 1) ∧ s (n + 1 + k) = -1 := by
  classical
  obtain ⟨m, hm, hsm⟩ := hinf (n + 1)
  have hex : ∃ j, s (n + 1 + j) = -1 :=
    ⟨m - (n + 1), by rw [show n + 1 + (m - (n + 1)) = m by omega]; exact hsm⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · exfalso
      have := Nat.find_spec hex
      rw [h0] at this
      have hb := h.noAA n hA
      simp only [Nat.add_zero] at this
      omega
    · exact h0
  · intro j hj
    have := Nat.find_min hex hj
    rcases h.mem (n + 1 + j) with hc | hc
    · exact absurd hc this
    · exact hc

/-! ## The residue modulo 5 -/

/-- At an `A` position the residue `4 (mod 5)` is impossible: `A` sends `4` to `3` and the
forced `B` sends `3` to `0`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem res5_ne_four (h : Data x s) (hA : s n = -1) : x n % 5 ≠ 4 := by
  intro h4
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 3 := rA5 b1 h4 (by norm_num)
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h (h.noAA n hA)
  have e2 : x (n + 2) % 5 = 0 := rB5 b2 e1 (by norm_num)
  exact h.av5 (n + 2) (Int.dvd_of_emod_eq_zero e2)

/-- **Every `A` position sits at `xₙ ≡ 1 (mod 5)`** ([FS67] Lemma 4.1, forward form).  The
component `{3,4}` of the mod-`5` action is a `B`-trap: it is compatible only with `B^∞`, which
the hypothesis `hinf` excludes. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem res5 (h : Data x s) (hinf : ∀ N, ∃ m, N ≤ m ∧ s m = -1) (hA : s n = -1) :
    x n % 5 = 1 := by
  have hb : 0 ≤ x n % 5 ∧ x n % 5 < 5 := ⟨Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num)⟩
  have h0 : x n % 5 ≠ 0 := fun hc => h.av5 n (Int.dvd_of_emod_eq_zero hc)
  have h4 := res5_ne_four h hA
  have h2 : x n % 5 ≠ 2 := by
    intro hc
    have e1 : x (n + 1) % 5 = 0 := rA5 (stepA h hA) hc (by norm_num)
    exact h.av5 (n + 1) (Int.dvd_of_emod_eq_zero e1)
  have h3 : x n % 5 ≠ 3 := by
    intro hc
    obtain ⟨k, -, hrun, hend⟩ := nextA h hinf hA
    have e1 : x (n + 1) % 5 = 4 := rA5 (stepA h hA) hc (by norm_num)
    exact res5_ne_four h hend (run5 h hrun e1)
  omega

/-! ## `A` positions and their phase -/

/-- An **`A` position** with its three residues recorded: `sₙ = −1`, `xₙ ≡ 1 (mod 5)`,
`xₙ ≡ u (mod 7)`, `xₙ ≡ c (mod 11)`. -/
def At (x s : ℕ → ℤ) (n : ℕ) (u c : ℤ) : Prop :=
  s n = -1 ∧ x n % 5 = 1 ∧ x n % 7 = u ∧ x n % 11 = c

/-- Every `A` position is an `At`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem at_of_A (h : Data x s) (hinf : ∀ N, ∃ m, N ≤ m ∧ s m = -1) (hA : s n = -1) :
    At x s n (x n % 7) (x n % 11) :=
  ⟨hA, res5 h hinf hA, rfl, rfl⟩

/-- **The phase mod 7 is one of three.**  `u = 0` is excluded by avoidance, `u = 5` dies at the
`A` itself, `u = 4` at the next letter and `u = 1` two letters later. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem phase7 (h : Data x s) (hat : At x s n c d) : c = 2 ∨ c = 3 ∨ c = 6 := by
  obtain ⟨hA, h5, h7, -⟩ := hat
  have hb : 0 ≤ c ∧ c < 7 := by omega
  have h0 : c ≠ 0 := fun hc => h.av7 n (Int.dvd_of_emod_eq_zero (hc ▸ h7))
  have b1 := stepA h hA
  have h5' : c ≠ 5 := by
    intro hc
    subst hc
    exact h.av7 (n + 1) (Int.dvd_of_emod_eq_zero (rA7 b1 h7 (by norm_num)))
  have h4' : c ≠ 4 := by
    intro hc
    subst hc
    have g1 : x (n + 1) % 7 = 2 := rA7 b1 h7 (by norm_num)
    have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h (h.noAA n hA)
    exact h.av7 (n + 2) (Int.dvd_of_emod_eq_zero (rB7 b2 g1 (by norm_num)))
  have h1' : c ≠ 1 := by
    intro hc
    subst hc
    have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
    have g1 : x (n + 1) % 7 = 1 := rA7 b1 h7 (by norm_num)
    have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h (h.noAA n hA)
    have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
    have g2 : x (n + 2) % 7 = 2 := rB7 b2 g1 (by norm_num)
    rcases h.mem (n + 2) with hs | hs
    · exact h.av5 (n + 3) (Int.dvd_of_emod_eq_zero
        (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h hs) e2 (by norm_num)))
    · exact h.av7 (n + 3) (Int.dvd_of_emod_eq_zero
        (rB7 (show 2 * x (n + 3) = 3 * x (n + 2) + 1 from stepB h hs) g2 (by norm_num)))
  omega

/-! ## The two forced blocks -/

/-- **The `6`-block.**  At an `A` position with `xₙ ≡ 6 (mod 7)` the run has length exactly
`2`: length `1` dies mod `5`, length `≥ 3` dies mod `7`.  The next `A` position is a
`2`-position, and mod `11` the whole block acts by `c ↦ 2c + 7`. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem sixStep (h : Data x s) (hat : At x s n 6 c) (hd : (2 * c + 7) % 11 = d) :
    s n = -1 ∧ s (n + 1) = 1 ∧ s (n + 2) = 1 ∧ At x s (n + 3) 2 d := by
  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 5 := rA7 b1 h7 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have g2 : x (n + 2) % 7 = 1 := rB7 b2 g1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2) e2 (by norm_num)))
      (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    have e3 : x (n + 3) % 5 = 1 := rB5 b3 e2 (by norm_num)
    have g3 : x (n + 3) % 7 = 2 := rB7 b3 g2 (by norm_num)
    have f3 : x (n + 3) % 11 = d :=
      rAB2_11 (show 8 * x (n + 3) = 27 * x n + 1 by linarith only [b1, b2, b3]) h11 hd
    rcases h.mem (n + 3) with s3 | s3
    · exact ⟨hA, s1, s2, s3, e3, g3, f3⟩
    · exact absurd (Int.dvd_of_emod_eq_zero
        (rB7 (show 2 * x (n + 4) = 3 * x (n + 3) + 1 from stepB h s3) g3 (by norm_num)))
        (h.av7 (n + 4))

/-- **The `3`-block.**  At an `A` position with `xₙ ≡ 3 (mod 7)` the run has length exactly `4`,
and the next `A` position is a `2`-position. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem threeStep (h : Data x s) (hat : At x s n 3 c) : ∃ d, At x s (n + 5) 2 d := by
  obtain ⟨hA, h5, h7, -⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 4 := rA7 b1 h7 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have g2 : x (n + 2) % 7 = 3 := rB7 b2 g1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2) e2 (by norm_num)))
      (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    have e3 : x (n + 3) % 5 = 1 := rB5 b3 e2 (by norm_num)
    have g3 : x (n + 3) % 7 = 5 := rB7 b3 g2 (by norm_num)
    rcases h.mem (n + 3) with s3 | s3
    · exact absurd (Int.dvd_of_emod_eq_zero
        (rA7 (show 2 * x (n + 4) = 3 * x (n + 3) - 1 from stepA h s3) g3 (by norm_num)))
        (h.av7 (n + 4))
    · have b4 : 2 * x (n + 4) = 3 * x (n + 3) + 1 := stepB h s3
      have e4 : x (n + 4) % 5 = 2 := rB5 b4 e3 (by norm_num)
      have g4 : x (n + 4) % 7 = 1 := rB7 b4 g3 (by norm_num)
      rcases h.mem (n + 4) with s4 | s4
      · exact absurd (Int.dvd_of_emod_eq_zero
          (rA5 (show 2 * x (n + 5) = 3 * x (n + 4) - 1 from stepA h s4) e4 (by norm_num)))
          (h.av5 (n + 5))
      · have b5 : 2 * x (n + 5) = 3 * x (n + 4) + 1 := stepB h s4
        have e5 : x (n + 5) % 5 = 1 := rB5 b5 e4 (by norm_num)
        have g5 : x (n + 5) % 7 = 2 := rB7 b5 g4 (by norm_num)
        rcases h.mem (n + 5) with s5 | s5
        · exact ⟨_, s5, e5, g5, rfl⟩
        · exact absurd (Int.dvd_of_emod_eq_zero
            (rB7 (show 2 * x (n + 6) = 3 * x (n + 5) + 1 from stepB h s5) g5 (by norm_num)))
            (h.av7 (n + 6))

/-! ## Positions that cannot occur

The residue `c = xₙ (mod 11)` at an `A` position is heavily constrained.  Four values die
whatever the phase mod `7`, and two more die at a `6`-position; the survivors are `{1,6,7,8,9}`
at a `6`-position and `{1,3,6,8,9,10}` at a `2`-position. -/

/-- `c = 0` is `11 ∣ xₙ`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem dead0 {u : ℤ} (h : Data x s) (hat : At x s n u 0) : False :=
  h.av11 n (Int.dvd_of_emod_eq_zero hat.2.2.2)

/-- `c = 4` dies at the `A` itself: `7·4 + 5 ≡ 0 (mod 11)`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem dead4 {u : ℤ} (h : Data x s) (hat : At x s n u 4) : False := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  exact absurd (Int.dvd_of_emod_eq_zero (rA11 b1 h11 (by norm_num)))
    (h.av11 (n + 1))


/-- `c = 5` dies at the first `B`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem dead5 {u : ℤ} (h : Data x s) (hat : At x s n u 5) : False := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have f1 : x (n + 1) % 11 = 7 := rA11 b1 h11 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  exact absurd (Int.dvd_of_emod_eq_zero
    (rB11 b2 f1 (by norm_num))) (h.av11 (n + 2))


/-- `c = 2` dies at the second `B`; the run cannot stop after one `B`, because mod `5` that
would put the next `A` at the residue `2` it kills. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem dead2 {u : ℤ} (h : Data x s) (hat : At x s n u 2) : False := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have f1 : x (n + 1) % 11 = 8 := rA11 b1 h11 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have f2 : x (n + 2) % 11 = 7 := rB11 b2 f1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2)
        e2 (by norm_num))) (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    exact absurd (Int.dvd_of_emod_eq_zero
      (rB11 b3 f2 (by norm_num))) (h.av11 (n + 3))


/-- At a `6`-position `c = 3` is impossible: the block `A B²` lands on a `2`-position with
`c = 2`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem six3 (h : Data x s) (hat : At x s n 6 3) : False :=
  dead2 h (sixStep h hat (by norm_num)).2.2.2

/-- At a `6`-position `c = 10` is impossible: the block `A B²` lands on a `2`-position with
`c = 5`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem six10 (h : Data x s) (hat : At x s n 6 10) : False :=
  dead5 h (sixStep h hat (by norm_num)).2.2.2

/-- **The live residues at a `6`-position.** -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem sixLive (h : Data x s) (hat : At x s n 6 c) :
    c = 1 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 := by
  have hb : 0 ≤ c ∧ c < 11 := by have := hat.2.2.2; omega
  have k0 : c ≠ 0 := by rintro rfl; exact dead0 h hat
  have k2 : c ≠ 2 := by rintro rfl; exact dead2 h hat
  have k3 : c ≠ 3 := by rintro rfl; exact six3 h hat
  have k4 : c ≠ 4 := by rintro rfl; exact dead4 h hat
  have k5 : c ≠ 5 := by rintro rfl; exact dead5 h hat
  have k10 : c ≠ 10 := by rintro rfl; exact six10 h hat
  omega

/-- At a `2`-position `c = 7` is impossible.  After the `A` all three residues sit at their
`B`-fixed points `(1|2, 6, 10)`, so the run is unconstrained — but however long it is, the next
`A` position is a `6`-position with `c = 10`. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem zero7 (h : Data x s) (hinf : ∀ N, ∃ m, N ≤ m ∧ s m = -1) (hat : At x s n 2 7) :
    False := by
  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 6 := rA7 b1 h7 (by norm_num)
  have f1 : x (n + 1) % 11 = 10 := rA11 b1 h11 (by norm_num)
  obtain ⟨k, -, hrun, hend⟩ := nextA h hinf hA
  have hg : x (n + 1 + k) % 7 = 6 := run7 h hrun g1
  have hf : x (n + 1 + k) % 11 = 10 := run11 h hrun f1
  rcases run5alt h hrun e1 with ⟨-, he⟩ | ⟨-, he⟩
  · exact six10 h ⟨hend, he, hg, hf⟩
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 1 + k + 1) = 3 * x (n + 1 + k) - 1 from stepA h hend) he
        (by norm_num))) (h.av5 (n + 1 + k + 1))

/-! ## The six live blocks at a `2`-position

Mod `7` a `2`-position places `xₙ₊₁` at the `B`-fixed point `6`, so the run length is decided
entirely by the residue mod `11`: it must be even (mod `5`), it must stop before the mod-`11`
walk reaches `7`, and the `6`-position it lands on must itself be live. -/

/-- `c = 1`: run `2` — landing on `9` — or run `6`, landing on `7`.  Run `4` would land on the
dead `6`-position `5`. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem zero1 (h : Data x s) (hat : At x s n 2 1) :
    (s n = -1 ∧ s (n + 1) = 1 ∧ s (n + 2) = 1 ∧ At x s (n + 3) 6 9) ∨
      At x s (n + 7) 6 7 := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 6 := rA7 b1 h7 (by norm_num)
  have f1 : x (n + 1) % 11 = 1 := rA11 b1 h11 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have g2 : x (n + 2) % 7 = 6 := rB7 b2 g1 (by norm_num)
  have f2 : x (n + 2) % 11 = 2 := rB11 b2 f1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2)
        e2 (by norm_num))) (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    have e3 : x (n + 3) % 5 = 1 := rB5 b3 e2 (by norm_num)
    have g3 : x (n + 3) % 7 = 6 := rB7 b3 g2 (by norm_num)
    have f3 : x (n + 3) % 11 = 9 := rB11 b3 f2 (by norm_num)
    rcases h.mem (n + 3) with s3 | s3
    · exact Or.inl ⟨hA, s1, s2, ⟨s3, e3, g3, f3⟩⟩
    · have b4 : 2 * x (n + 4) = 3 * x (n + 3) + 1 := stepB h s3
      have e4 : x (n + 4) % 5 = 2 := rB5 b4 e3 (by norm_num)
      have g4 : x (n + 4) % 7 = 6 := rB7 b4 g3 (by norm_num)
      have f4 : x (n + 4) % 11 = 3 := rB11 b4 f3 (by norm_num)
      rcases h.mem (n + 4) with s4 | s4
      · exact absurd (Int.dvd_of_emod_eq_zero
          (rA5 (show 2 * x (n + 5) = 3 * x (n + 4) - 1 from stepA h s4)
            e4 (by norm_num))) (h.av5 (n + 5))
      · have b5 : 2 * x (n + 5) = 3 * x (n + 4) + 1 := stepB h s4
        have e5 : x (n + 5) % 5 = 1 := rB5 b5 e4 (by norm_num)
        have g5 : x (n + 5) % 7 = 6 := rB7 b5 g4 (by norm_num)
        have f5 : x (n + 5) % 11 = 5 := rB11 b5 f4 (by norm_num)
        rcases h.mem (n + 5) with s5 | s5
        · exact (dead5 h ⟨s5, e5, g5, f5⟩).elim
        · have b6 : 2 * x (n + 6) = 3 * x (n + 5) + 1 := stepB h s5
          have e6 : x (n + 6) % 5 = 2 := rB5 b6 e5 (by norm_num)
          have g6 : x (n + 6) % 7 = 6 := rB7 b6 g5 (by norm_num)
          have f6 : x (n + 6) % 11 = 8 := rB11 b6 f5 (by norm_num)
          rcases h.mem (n + 6) with s6 | s6
          · exact absurd (Int.dvd_of_emod_eq_zero
              (rA5 (show 2 * x (n + 7) = 3 * x (n + 6) - 1 from stepA h s6)
                e6 (by norm_num))) (h.av5 (n + 7))
          · have b7 : 2 * x (n + 7) = 3 * x (n + 6) + 1 := stepB h s6
            have e7 : x (n + 7) % 5 = 1 := rB5 b7 e6 (by norm_num)
            have g7 : x (n + 7) % 7 = 6 := rB7 b7 g6 (by norm_num)
            have f7 : x (n + 7) % 11 = 7 := rB11 b7 f6 (by norm_num)
            rcases h.mem (n + 7) with s7 | s7
            · exact Or.inr ⟨s7, e7, g7, f7⟩
            · have b8 : 2 * x (n + 8) = 3 * x (n + 7) + 1 := stepB h s7
              exact absurd (Int.dvd_of_emod_eq_zero
                (rB11 b8 f7 (by norm_num))) (h.av11 (n + 8))


/-- `c = 3`: the run is `6`, landing on `8`. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem zero3 (h : Data x s) (hat : At x s n 2 3) :
    s n = -1 ∧ s (n + 1) = 1 ∧ s (n + 2) = 1 ∧ s (n + 3) = 1 ∧ s (n + 4) = 1 ∧
      s (n + 5) = 1 ∧ s (n + 6) = 1 ∧ At x s (n + 7) 6 8 := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 6 := rA7 b1 h7 (by norm_num)
  have f1 : x (n + 1) % 11 = 4 := rA11 b1 h11 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have g2 : x (n + 2) % 7 = 6 := rB7 b2 g1 (by norm_num)
  have f2 : x (n + 2) % 11 = 1 := rB11 b2 f1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2)
        e2 (by norm_num))) (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    have e3 : x (n + 3) % 5 = 1 := rB5 b3 e2 (by norm_num)
    have g3 : x (n + 3) % 7 = 6 := rB7 b3 g2 (by norm_num)
    have f3 : x (n + 3) % 11 = 2 := rB11 b3 f2 (by norm_num)
    rcases h.mem (n + 3) with s3 | s3
    · exact (dead2 h ⟨s3, e3, g3, f3⟩).elim
    · have b4 : 2 * x (n + 4) = 3 * x (n + 3) + 1 := stepB h s3
      have e4 : x (n + 4) % 5 = 2 := rB5 b4 e3 (by norm_num)
      have g4 : x (n + 4) % 7 = 6 := rB7 b4 g3 (by norm_num)
      have f4 : x (n + 4) % 11 = 9 := rB11 b4 f3 (by norm_num)
      rcases h.mem (n + 4) with s4 | s4
      · exact absurd (Int.dvd_of_emod_eq_zero
          (rA5 (show 2 * x (n + 5) = 3 * x (n + 4) - 1 from stepA h s4)
            e4 (by norm_num))) (h.av5 (n + 5))
      · have b5 : 2 * x (n + 5) = 3 * x (n + 4) + 1 := stepB h s4
        have e5 : x (n + 5) % 5 = 1 := rB5 b5 e4 (by norm_num)
        have g5 : x (n + 5) % 7 = 6 := rB7 b5 g4 (by norm_num)
        have f5 : x (n + 5) % 11 = 3 := rB11 b5 f4 (by norm_num)
        rcases h.mem (n + 5) with s5 | s5
        · exact (six3 h ⟨s5, e5, g5, f5⟩).elim
        · have b6 : 2 * x (n + 6) = 3 * x (n + 5) + 1 := stepB h s5
          have e6 : x (n + 6) % 5 = 2 := rB5 b6 e5 (by norm_num)
          have g6 : x (n + 6) % 7 = 6 := rB7 b6 g5 (by norm_num)
          have f6 : x (n + 6) % 11 = 5 := rB11 b6 f5 (by norm_num)
          rcases h.mem (n + 6) with s6 | s6
          · exact absurd (Int.dvd_of_emod_eq_zero
              (rA5 (show 2 * x (n + 7) = 3 * x (n + 6) - 1 from stepA h s6)
                e6 (by norm_num))) (h.av5 (n + 7))
          · have b7 : 2 * x (n + 7) = 3 * x (n + 6) + 1 := stepB h s6
            have e7 : x (n + 7) % 5 = 1 := rB5 b7 e6 (by norm_num)
            have g7 : x (n + 7) % 7 = 6 := rB7 b7 g6 (by norm_num)
            have f7 : x (n + 7) % 11 = 8 := rB11 b7 f6 (by norm_num)
            rcases h.mem (n + 7) with s7 | s7
            · exact ⟨hA, s1, s2, s3, s4, s5, s6, ⟨s7, e7, g7, f7⟩⟩
            · have b8 : 2 * x (n + 8) = 3 * x (n + 7) + 1 := stepB h s7
              have e8 : x (n + 8) % 5 = 2 := rB5 b8 e7 (by norm_num)
              have g8 : x (n + 8) % 7 = 6 := rB7 b8 g7 (by norm_num)
              have f8 : x (n + 8) % 11 = 7 := rB11 b8 f7 (by norm_num)
              rcases h.mem (n + 8) with s8 | s8
              · exact absurd (Int.dvd_of_emod_eq_zero
                  (rA5 (show 2 * x (n + 9) = 3 * x (n + 8) - 1 from stepA h s8)
                    e8 (by norm_num))) (h.av5 (n + 9))
              · have b9 : 2 * x (n + 9) = 3 * x (n + 8) + 1 := stepB h s8
                exact absurd (Int.dvd_of_emod_eq_zero
                  (rB11 b9 f8 (by norm_num))) (h.av11 (n + 9))


/-- `c = 6`: the run is `2`, landing on `8`. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem zero6 (h : Data x s) (hat : At x s n 2 6) : At x s (n + 3) 6 8 := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 6 := rA7 b1 h7 (by norm_num)
  have f1 : x (n + 1) % 11 = 3 := rA11 b1 h11 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have g2 : x (n + 2) % 7 = 6 := rB7 b2 g1 (by norm_num)
  have f2 : x (n + 2) % 11 = 5 := rB11 b2 f1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2)
        e2 (by norm_num))) (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    have e3 : x (n + 3) % 5 = 1 := rB5 b3 e2 (by norm_num)
    have g3 : x (n + 3) % 7 = 6 := rB7 b3 g2 (by norm_num)
    have f3 : x (n + 3) % 11 = 8 := rB11 b3 f2 (by norm_num)
    rcases h.mem (n + 3) with s3 | s3
    · exact ⟨s3, e3, g3, f3⟩
    · have b4 : 2 * x (n + 4) = 3 * x (n + 3) + 1 := stepB h s3
      have e4 : x (n + 4) % 5 = 2 := rB5 b4 e3 (by norm_num)
      have g4 : x (n + 4) % 7 = 6 := rB7 b4 g3 (by norm_num)
      have f4 : x (n + 4) % 11 = 7 := rB11 b4 f3 (by norm_num)
      rcases h.mem (n + 4) with s4 | s4
      · exact absurd (Int.dvd_of_emod_eq_zero
          (rA5 (show 2 * x (n + 5) = 3 * x (n + 4) - 1 from stepA h s4)
            e4 (by norm_num))) (h.av5 (n + 5))
      · have b5 : 2 * x (n + 5) = 3 * x (n + 4) + 1 := stepB h s4
        exact absurd (Int.dvd_of_emod_eq_zero
          (rB11 b5 f4 (by norm_num))) (h.av11 (n + 5))


/-- `c = 8`: three live runs, `2`, `4` and `8`. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem zero8 (h : Data x s) (hat : At x s n 2 8) :
    At x s (n + 3) 6 1 ∨ At x s (n + 5) 6 9 ∨ At x s (n + 9) 6 7 := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 6 := rA7 b1 h7 (by norm_num)
  have f1 : x (n + 1) % 11 = 6 := rA11 b1 h11 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have g2 : x (n + 2) % 7 = 6 := rB7 b2 g1 (by norm_num)
  have f2 : x (n + 2) % 11 = 4 := rB11 b2 f1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2)
        e2 (by norm_num))) (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    have e3 : x (n + 3) % 5 = 1 := rB5 b3 e2 (by norm_num)
    have g3 : x (n + 3) % 7 = 6 := rB7 b3 g2 (by norm_num)
    have f3 : x (n + 3) % 11 = 1 := rB11 b3 f2 (by norm_num)
    rcases h.mem (n + 3) with s3 | s3
    · exact Or.inl ⟨s3, e3, g3, f3⟩
    · have b4 : 2 * x (n + 4) = 3 * x (n + 3) + 1 := stepB h s3
      have e4 : x (n + 4) % 5 = 2 := rB5 b4 e3 (by norm_num)
      have g4 : x (n + 4) % 7 = 6 := rB7 b4 g3 (by norm_num)
      have f4 : x (n + 4) % 11 = 2 := rB11 b4 f3 (by norm_num)
      rcases h.mem (n + 4) with s4 | s4
      · exact absurd (Int.dvd_of_emod_eq_zero
          (rA5 (show 2 * x (n + 5) = 3 * x (n + 4) - 1 from stepA h s4)
            e4 (by norm_num))) (h.av5 (n + 5))
      · have b5 : 2 * x (n + 5) = 3 * x (n + 4) + 1 := stepB h s4
        have e5 : x (n + 5) % 5 = 1 := rB5 b5 e4 (by norm_num)
        have g5 : x (n + 5) % 7 = 6 := rB7 b5 g4 (by norm_num)
        have f5 : x (n + 5) % 11 = 9 := rB11 b5 f4 (by norm_num)
        rcases h.mem (n + 5) with s5 | s5
        · exact Or.inr (Or.inl ⟨s5, e5, g5, f5⟩)
        · have b6 : 2 * x (n + 6) = 3 * x (n + 5) + 1 := stepB h s5
          have e6 : x (n + 6) % 5 = 2 := rB5 b6 e5 (by norm_num)
          have g6 : x (n + 6) % 7 = 6 := rB7 b6 g5 (by norm_num)
          have f6 : x (n + 6) % 11 = 3 := rB11 b6 f5 (by norm_num)
          rcases h.mem (n + 6) with s6 | s6
          · exact absurd (Int.dvd_of_emod_eq_zero
              (rA5 (show 2 * x (n + 7) = 3 * x (n + 6) - 1 from stepA h s6)
                e6 (by norm_num))) (h.av5 (n + 7))
          · have b7 : 2 * x (n + 7) = 3 * x (n + 6) + 1 := stepB h s6
            have e7 : x (n + 7) % 5 = 1 := rB5 b7 e6 (by norm_num)
            have g7 : x (n + 7) % 7 = 6 := rB7 b7 g6 (by norm_num)
            have f7 : x (n + 7) % 11 = 5 := rB11 b7 f6 (by norm_num)
            rcases h.mem (n + 7) with s7 | s7
            · exact (dead5 h ⟨s7, e7, g7, f7⟩).elim
            · have b8 : 2 * x (n + 8) = 3 * x (n + 7) + 1 := stepB h s7
              have e8 : x (n + 8) % 5 = 2 := rB5 b8 e7 (by norm_num)
              have g8 : x (n + 8) % 7 = 6 := rB7 b8 g7 (by norm_num)
              have f8 : x (n + 8) % 11 = 8 := rB11 b8 f7 (by norm_num)
              rcases h.mem (n + 8) with s8 | s8
              · exact absurd (Int.dvd_of_emod_eq_zero
                  (rA5 (show 2 * x (n + 9) = 3 * x (n + 8) - 1 from stepA h s8)
                    e8 (by norm_num))) (h.av5 (n + 9))
              · have b9 : 2 * x (n + 9) = 3 * x (n + 8) + 1 := stepB h s8
                have e9 : x (n + 9) % 5 = 1 := rB5 b9 e8 (by norm_num)
                have g9 : x (n + 9) % 7 = 6 := rB7 b9 g8 (by norm_num)
                have f9 : x (n + 9) % 11 = 7 := rB11 b9 f8 (by norm_num)
                rcases h.mem (n + 9) with s9 | s9
                · exact Or.inr (Or.inr ⟨s9, e9, g9, f9⟩)
                · have b10 : 2 * x (n + 10) = 3 * x (n + 9) + 1 := stepB h s9
                  exact absurd (Int.dvd_of_emod_eq_zero
                    (rB11 b10 f9 (by norm_num))) (h.av11 (n + 10))


/-- `c = 9`: the run is `4`, landing on `8`. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem zero9 (h : Data x s) (hat : At x s n 2 9) : At x s (n + 5) 6 8 := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 6 := rA7 b1 h7 (by norm_num)
  have f1 : x (n + 1) % 11 = 2 := rA11 b1 h11 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have g2 : x (n + 2) % 7 = 6 := rB7 b2 g1 (by norm_num)
  have f2 : x (n + 2) % 11 = 9 := rB11 b2 f1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2)
        e2 (by norm_num))) (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    have e3 : x (n + 3) % 5 = 1 := rB5 b3 e2 (by norm_num)
    have g3 : x (n + 3) % 7 = 6 := rB7 b3 g2 (by norm_num)
    have f3 : x (n + 3) % 11 = 3 := rB11 b3 f2 (by norm_num)
    rcases h.mem (n + 3) with s3 | s3
    · exact (six3 h ⟨s3, e3, g3, f3⟩).elim
    · have b4 : 2 * x (n + 4) = 3 * x (n + 3) + 1 := stepB h s3
      have e4 : x (n + 4) % 5 = 2 := rB5 b4 e3 (by norm_num)
      have g4 : x (n + 4) % 7 = 6 := rB7 b4 g3 (by norm_num)
      have f4 : x (n + 4) % 11 = 5 := rB11 b4 f3 (by norm_num)
      rcases h.mem (n + 4) with s4 | s4
      · exact absurd (Int.dvd_of_emod_eq_zero
          (rA5 (show 2 * x (n + 5) = 3 * x (n + 4) - 1 from stepA h s4)
            e4 (by norm_num))) (h.av5 (n + 5))
      · have b5 : 2 * x (n + 5) = 3 * x (n + 4) + 1 := stepB h s4
        have e5 : x (n + 5) % 5 = 1 := rB5 b5 e4 (by norm_num)
        have g5 : x (n + 5) % 7 = 6 := rB7 b5 g4 (by norm_num)
        have f5 : x (n + 5) % 11 = 8 := rB11 b5 f4 (by norm_num)
        rcases h.mem (n + 5) with s5 | s5
        · exact ⟨s5, e5, g5, f5⟩
        · have b6 : 2 * x (n + 6) = 3 * x (n + 5) + 1 := stepB h s5
          have e6 : x (n + 6) % 5 = 2 := rB5 b6 e5 (by norm_num)
          have g6 : x (n + 6) % 7 = 6 := rB7 b6 g5 (by norm_num)
          have f6 : x (n + 6) % 11 = 7 := rB11 b6 f5 (by norm_num)
          rcases h.mem (n + 6) with s6 | s6
          · exact absurd (Int.dvd_of_emod_eq_zero
              (rA5 (show 2 * x (n + 7) = 3 * x (n + 6) - 1 from stepA h s6)
                e6 (by norm_num))) (h.av5 (n + 7))
          · have b7 : 2 * x (n + 7) = 3 * x (n + 6) + 1 := stepB h s6
            exact absurd (Int.dvd_of_emod_eq_zero
              (rB11 b7 f6 (by norm_num))) (h.av11 (n + 7))


/-- `c = 10`: the run is `4`, landing on `7` — the first half of the period-`8` cycle. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem zero10 (h : Data x s) (hat : At x s n 2 10) :
    (s n = -1 ∧ s (n + 1) = 1 ∧ s (n + 2) = 1 ∧ s (n + 3) = 1 ∧ s (n + 4) = 1) ∧
      At x s (n + 5) 6 7 := by

  obtain ⟨hA, h5, h7, h11⟩ := hat
  have b1 := stepA h hA
  have e1 : x (n + 1) % 5 = 1 := rA5 b1 h5 (by norm_num)
  have g1 : x (n + 1) % 7 = 6 := rA7 b1 h7 (by norm_num)
  have f1 : x (n + 1) % 11 = 9 := rA11 b1 h11 (by norm_num)
  have s1 : s (n + 1) = 1 := h.noAA n hA
  have b2 : 2 * x (n + 2) = 3 * x (n + 1) + 1 := stepB h s1
  have e2 : x (n + 2) % 5 = 2 := rB5 b2 e1 (by norm_num)
  have g2 : x (n + 2) % 7 = 6 := rB7 b2 g1 (by norm_num)
  have f2 : x (n + 2) % 11 = 3 := rB11 b2 f1 (by norm_num)
  rcases h.mem (n + 2) with s2 | s2
  · exact absurd (Int.dvd_of_emod_eq_zero
      (rA5 (show 2 * x (n + 3) = 3 * x (n + 2) - 1 from stepA h s2)
        e2 (by norm_num))) (h.av5 (n + 3))
  · have b3 : 2 * x (n + 3) = 3 * x (n + 2) + 1 := stepB h s2
    have e3 : x (n + 3) % 5 = 1 := rB5 b3 e2 (by norm_num)
    have g3 : x (n + 3) % 7 = 6 := rB7 b3 g2 (by norm_num)
    have f3 : x (n + 3) % 11 = 5 := rB11 b3 f2 (by norm_num)
    rcases h.mem (n + 3) with s3 | s3
    · exact (dead5 h ⟨s3, e3, g3, f3⟩).elim
    · have b4 : 2 * x (n + 4) = 3 * x (n + 3) + 1 := stepB h s3
      have e4 : x (n + 4) % 5 = 2 := rB5 b4 e3 (by norm_num)
      have g4 : x (n + 4) % 7 = 6 := rB7 b4 g3 (by norm_num)
      have f4 : x (n + 4) % 11 = 8 := rB11 b4 f3 (by norm_num)
      rcases h.mem (n + 4) with s4 | s4
      · exact absurd (Int.dvd_of_emod_eq_zero
          (rA5 (show 2 * x (n + 5) = 3 * x (n + 4) - 1 from stepA h s4)
            e4 (by norm_num))) (h.av5 (n + 5))
      · have b5 : 2 * x (n + 5) = 3 * x (n + 4) + 1 := stepB h s4
        have e5 : x (n + 5) % 5 = 1 := rB5 b5 e4 (by norm_num)
        have g5 : x (n + 5) % 7 = 6 := rB7 b5 g4 (by norm_num)
        have f5 : x (n + 5) % 11 = 7 := rB11 b5 f4 (by norm_num)
        rcases h.mem (n + 5) with s5 | s5
        · exact ⟨⟨hA, s1, s2, s3, s4⟩, ⟨s5, e5, g5, f5⟩⟩
        · have b6 : 2 * x (n + 6) = 3 * x (n + 5) + 1 := stepB h s5
          exact absurd (Int.dvd_of_emod_eq_zero
            (rB11 b6 f5 (by norm_num))) (h.av11 (n + 6))


/-- **The live residues at a `2`-position.** -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem zeroLive (h : Data x s) (hinf : ∀ N, ∃ m, N ≤ m ∧ s m = -1) (hat : At x s n 2 c) :
    c = 1 ∨ c = 3 ∨ c = 6 ∨ c = 8 ∨ c = 9 ∨ c = 10 := by
  have hb : 0 ≤ c ∧ c < 11 := by have := hat.2.2.2; omega
  have k0 : c ≠ 0 := by rintro rfl; exact dead0 h hat
  have k2 : c ≠ 2 := by rintro rfl; exact dead2 h hat
  have k4 : c ≠ 4 := by rintro rfl; exact dead4 h hat
  have k5 : c ≠ 5 := by rintro rfl; exact dead5 h hat
  have k7 : c ≠ 7 := by rintro rfl; exact zero7 h hinf hat
  omega

/-! ## The funnel

The `2`-positions form a six-state graph under the super-block `A Bᵏ A B²`.  Two of its states,
`1` and `10`, carry the two cycles; the other four reach them in at most two super-blocks. -/

/-- **Every `A` position is followed by a `2`-position** within five letters. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem toZero (h : Data x s) (hinf : ∀ N, ∃ m, N ≤ m ∧ s m = -1) (hA : s n = -1) :
    ∃ m d, At x s m 2 d := by
  have hat := at_of_A h hinf hA
  rcases phase7 h hat with h2 | h3 | h6
  · exact ⟨n, _, h2 ▸ hat⟩
  · obtain ⟨d, hd⟩ := threeStep h (h3 ▸ hat)
    exact ⟨n + 5, d, hd⟩
  · exact ⟨n + 3, _, (sixStep h (h6 ▸ hat) rfl).2.2.2⟩

/-- **The funnel.**  From any `2`-position the orbit reaches one of the two cycle states. -/
@[category research solved, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem toCycle (h : Data x s) (hinf : ∀ N, ∃ m, N ≤ m ∧ s m = -1) (hat : At x s n 2 c) :
    (∃ m, At x s m 2 1) ∨ (∃ m, At x s m 2 10) := by
  rcases zeroLive h hinf hat with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨n, hat⟩
  · exact Or.inl ⟨_, (sixStep h (zero3 h hat).2.2.2.2.2.2.2 (by norm_num)).2.2.2⟩
  · exact Or.inl ⟨_, (sixStep h (zero6 h hat) (by norm_num)).2.2.2⟩
  · rcases zero8 h hat with h1 | h9 | h7
    · exact Or.inl ⟨_, (sixStep h (zero9 h (sixStep h h1 (by norm_num)).2.2.2)
        (by norm_num)).2.2.2⟩
    · exact Or.inl ⟨_, (sixStep h (zero3 h (sixStep h h9 (by norm_num)).2.2.2).2.2.2.2.2.2.2
        (by norm_num)).2.2.2⟩
    · exact Or.inr ⟨_, (sixStep h h7 (by norm_num)).2.2.2⟩
  · exact Or.inl ⟨_, (sixStep h (zero9 h hat) (by norm_num)).2.2.2⟩
  · exact Or.inr ⟨n, hat⟩

/-! ## The two cycles -/

/-- The period-`8` word `A B⁴ A B²`. -/
def pat8 (j : ℕ) : ℤ := if j = 0 ∨ j = 5 then -1 else 1

/-- The period-`16` word `A B² A B² A B⁶ A B²`. -/
def pat16 (j : ℕ) : ℤ := if j = 0 ∨ j = 3 ∨ j = 6 ∨ j = 13 then -1 else 1

/-- **The absorbing cycle.**  A `2`-position with `c = 10` repeats after eight letters, and the
eight letters are `A B⁴ A B²`. -/
@[category research solved, AMS 11 68, ref "FS67", group "fs67_floor_32"]
theorem cyc10 (h : Data x s) (hat : At x s n 2 10) :
    (∀ j, j < 8 → s (n + j) = pat8 j) ∧ At x s (n + 8) 2 10 := by
  obtain ⟨⟨q0, q1, q2, q3, q4⟩, hsix⟩ := zero10 h hat
  obtain ⟨q5, q6, q7, hz⟩ := sixStep (d := 10) h hsix (by norm_num)
  have e5 : s (n + 5) = -1 := q5
  have e6 : s (n + 6) = 1 := q6
  have e7 : s (n + 7) = 1 := q7
  have hz' : At x s (n + 8) 2 10 := hz
  refine ⟨fun j hj => ?_, hz'⟩
  interval_cases j <;> simp only [pat8] <;> norm_num [q0, q1, q2, q3, q4, e5, e6, e7]

/-- **The second cycle, and its single exit.**  A `2`-position with `c = 1` either repeats after
sixteen letters — the word `A B² A B² A B⁶ A B²` — or the run of length `6` is taken instead and
the orbit falls into the absorbing cycle. -/
@[category research solved, AMS 11 68, ref "FS67", group "fs67_floor_32"]
theorem cyc1 (h : Data x s) (hat : At x s n 2 1) :
    ((∀ j, j < 16 → s (n + j) = pat16 j) ∧ At x s (n + 16) 2 1) ∨ (∃ m, At x s m 2 10) := by
  rcases zero1 h hat with ⟨q0, q1, q2, hsix⟩ | hexit
  · obtain ⟨q3, q4, q5, hz3⟩ := sixStep (d := 3) h hsix (by norm_num)
    have hz3' : At x s (n + 6) 2 3 := hz3
    obtain ⟨q6, q7, q8, q9, q10, q11, q12, hsix8⟩ := zero3 h hz3'
    have hsix8' : At x s (n + 13) 6 8 := hsix8
    obtain ⟨q13, q14, q15, hz1⟩ := sixStep (d := 1) h hsix8' (by norm_num)
    have hz1' : At x s (n + 16) 2 1 := hz1
    have e3 : s (n + 3) = -1 := q3
    have e4 : s (n + 4) = 1 := q4
    have e5 : s (n + 5) = 1 := q5
    have e6 : s (n + 6) = -1 := q6
    have e7 : s (n + 7) = 1 := q7
    have e8 : s (n + 8) = 1 := q8
    have e9 : s (n + 9) = 1 := q9
    have e10 : s (n + 10) = 1 := q10
    have e11 : s (n + 11) = 1 := q11
    have e12 : s (n + 12) = 1 := q12
    have e13 : s (n + 13) = -1 := q13
    have e14 : s (n + 14) = 1 := q14
    have e15 : s (n + 15) = 1 := q15
    refine Or.inl ⟨fun j hj => ?_, hz1'⟩
    interval_cases j <;>
      norm_num [pat16, q0, q1, q2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  · exact Or.inr ⟨_, (sixStep h hexit (by norm_num)).2.2.2⟩

/-! ## Eventual periodicity -/

/-- The absorbing cycle gives period `8`. -/
@[category research solved, AMS 11 68, ref "FS67", group "fs67_floor_32"]
theorem periodic8 (h : Data x s) {N : ℕ} (hat : At x s N 2 10) : IsEventuallyPeriodic s := by
  have hall : ∀ i, At x s (N + 8 * i) 2 10 := by
    intro i
    induction i with
    | zero => simpa using hat
    | succ i ih =>
      have := (cyc10 h ih).2
      rw [show N + 8 * (i + 1) = N + 8 * i + 8 by ring]
      exact this
  have hpat : ∀ i j, j < 8 → s (N + 8 * i + j) = pat8 j := fun i j hj => (cyc10 h (hall i)).1 j hj
  refine ⟨N, 8, by norm_num, fun m hm => ?_⟩
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 8 ∧ m = N + 8 * i + j :=
    ⟨(m - N) / 8, (m - N) % 8, by omega, by omega⟩
  rw [show N + 8 * i + j + 8 = N + 8 * (i + 1) + j by ring, hpat (i + 1) j hj, hpat i j hj]

/-- If the absorbing cycle is never reached, the second cycle gives period `16`. -/
@[category research solved, AMS 11 68, ref "FS67", group "fs67_floor_32"]
theorem periodic16 (h : Data x s) (hno : ∀ m, ¬ At x s m 2 10) {N : ℕ} (hat : At x s N 2 1) :
    IsEventuallyPeriodic s := by
  have hall : ∀ i, At x s (N + 16 * i) 2 1 := by
    intro i
    induction i with
    | zero => simpa using hat
    | succ i ih =>
      have := (cyc1 h ih).resolve_right (fun ⟨m, hm⟩ => hno m hm)
      rw [show N + 16 * (i + 1) = N + 16 * i + 16 by ring]
      exact this.2
  have hpat : ∀ i j, j < 16 → s (N + 16 * i + j) = pat16 j := fun i j hj =>
    ((cyc1 h (hall i)).resolve_right (fun ⟨m, hm⟩ => hno m hm)).1 j hj
  refine ⟨N, 16, by norm_num, fun m hm => ?_⟩
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 16 ∧ m = N + 16 * i + j :=
    ⟨(m - N) / 16, (m - N) % 16, by omega, by omega⟩
  rw [show N + 16 * i + j + 16 = N + 16 * (i + 1) + j by ring, hpat (i + 1) j hj, hpat i j hj]

/-- **The Forman–Shapiro subshift is finite.**  Every word satisfying `Data` is eventually
periodic: `B^∞`, or `(A B⁴ A B²)^∞`, or `(A B² A B² A B⁶ A B²)^∞`. -/
@[category research solved, AMS 11 68, ref "FS67" "DN05", group "fs67_floor_32"]
theorem isEventuallyPeriodic (h : Data x s) : IsEventuallyPeriodic s := by
  by_cases hinf : ∀ N, ∃ m, N ≤ m ∧ s m = -1
  · obtain ⟨m0, -, hA⟩ := hinf 0
    obtain ⟨m1, d, hz⟩ := toZero h hinf hA
    by_cases hten : ∃ m, At x s m 2 10
    · obtain ⟨m, hm⟩ := hten
      exact periodic8 h hm
    · have hno : ∀ m, ¬ At x s m 2 10 := fun m hm => hten ⟨m, hm⟩
      rcases toCycle h hinf hz with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact periodic16 h hno hm
      · exact absurd hm (hno m)
  · push Not at hinf
    obtain ⟨N, hN⟩ := hinf
    refine ⟨N, 1, by norm_num, fun k hk => ?_⟩
    have h1 : s (k + 1) = 1 := (h.mem (k + 1)).resolve_left (hN (k + 1) (by omega))
    have h2 : s k = 1 := (h.mem k).resolve_left (hN k hk)
    rw [h1, h2]

end DubC2.FS
