/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The coupled-Cantor cover game at `m = 3`

The constructive half of `plans/plan-dubD1O5.html`: an explicit greedy that solves

`x + √3 y = σ`,  `σ = 3√3 - 4`,

with `x, y` in the middle-thirds Cantor set `K₃ = {∑ aᵢ 3^{-i} : aᵢ ∈ {0,2}}`, **and** with
digit streams whose tails are not stuck at the extreme digit (the plan's lemma L1).

## The game

Rescaling the residual by `3^{k+1}` turns the greedy into an integer dynamical system on
`ℤ[√3]`.  The state `W k = P k + Q k √3` lives in `[0, 3U]`, `U = 1 + √3`, starts at
`W 0 = -12 + 9√3 = 3σ`, and steps by

`W (k+1) = 3 (W k - (aₖ + bₖ √3))`,  `(aₖ, bₖ) ∈ {0,2}²`.

Feasibility is the **Cover Lemma** (plan §1.3): the four intervals `[c, c+U]`,
`c ∈ {0, 2, 2√3, 2+2√3}`, cover `[0, 3U]`, the top being reached with exact equality
`2 + 2√3 + U = 3U`.  At `m = 3` this statement — and the induction proving it — is
**Utz's theorem**: W. R. Utz, *The distance set for the Cantor discontinuum*, Amer. Math.
Monthly **58** (6) (1951), 407–408.  It is reproved here rather than cited, so the file
carries no literature axiom.

## The selection rule, and why it makes L1 free

`pick` chooses, among the admissible offsets, one with `a = 0` if any, and then one with
`b = 2` if any.  The resulting four regions are

| region | `W k` | `(aₖ, bₖ)` |
|---|---|---|
| 1 | `[0, U]` | `(0,0)` |
| 2 | `(U, 2√3)` | `(2,0)` |
| 3 | `[2√3, 2√3+U]` | `(0,2)` |
| 4 | `(2√3+U, 3U]` | `(2,2)` |

so `aₖ = 2` exactly on the trap set `A = (U,2√3) ∪ (2√3+U, 3U]` and `bₖ = 0` exactly on
`L = [0, 2√3)`.  The rule is therefore simultaneously optimal for both of L1's goals, and
the interleaving argument of `plans/note-dubD1O5-M1.html` §1.4 is not needed: it suffices
to show that the orbit is not eventually confined to `A`, and not eventually confined
to `L`.

Different preference orders solve the same equation at different points — the solution set
is a Cantor set — so the witness this file produces is *not* the one the X0/X1 scripts
print.  See the "Which witness?" section of `SZ/SqrtThree.lean`.

Both confinements are excluded by the same two ingredients:

* `eq_fixed_of_trapped` — a `3`-expanding affine map cannot keep an orbit in a bounded
  set unless the orbit sits at the fixed point;
* `coverState_snd_lower` — `Q k ≥ 6·3ᵏ + 3`, so no state is ever one of the three
  candidate fixed points `0`, `3`, `3 + 3√3` (note M1 §1.2: *growth*, not mere
  irrationality, is what excludes the right-hand strip).

For `L` a third ingredient replaces the plan's three-case analysis: under the assumption
`bₖ = 0` forever, region 1 forces `W k < 2√3/3` and region 2 forces `W k < 2 + 2√3/3`, and
the second of those two zones turns out to be **absorbing** — see `exists_digitB_eq_two`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
* [Utz51] W. R. Utz, *The distance set for the Cantor discontinuum*, Amer. Math. Monthly
  **58** (1951), 407–408.
-/

namespace SZ

open Filter Topology

/-! ## `√3`, and the arithmetic of `ℤ[√3]` -/

private theorem s3_nonneg : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3

private theorem s3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private theorem s3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem irrational_sqrt_three : Irrational (Real.sqrt 3) := by
  have h : Nat.Prime 3 := Nat.prime_three
  simpa using h.irrational_sqrt

/-- `ℤ[√3]` is free on `1, √3`: the coordinates of a state are well defined. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem val_inj {p q p' q' : ℤ}
    (h : (p : ℝ) + (q : ℝ) * Real.sqrt 3 = (p' : ℝ) + (q' : ℝ) * Real.sqrt 3) :
    p = p' ∧ q = q' := by
  have hq : q = q' := by
    by_contra hne
    have hd : (q - q' : ℤ) ≠ 0 := sub_ne_zero.mpr hne
    have he : ((q - q' : ℤ) : ℝ) * Real.sqrt 3 = ((p' - p : ℤ) : ℝ) := by push_cast; linarith
    exact (irrational_sqrt_three.intCast_mul hd).ne_int (p' - p) he
  refine ⟨?_, hq⟩
  subst hq
  have : (p : ℝ) = (p' : ℝ) := by linarith
  exact_mod_cast this

/-! ## The selection rule -/

/-- **The greedy's digit choice** at state value `w`.  Prefer `a = 0`, then `b = 2`; the
four branches are exactly the four regions of the module docstring. -/
noncomputable def pick (w : ℝ) : ℤ × ℤ :=
  if w ≤ 1 + Real.sqrt 3 then (0, 0)
  else if w < 2 * Real.sqrt 3 then (2, 0)
  else if w ≤ 1 + 3 * Real.sqrt 3 then (0, 2)
  else (2, 2)

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem pick_cases (w : ℝ) :
    (w ≤ 1 + Real.sqrt 3 ∧ pick w = (0, 0)) ∨
    (1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3 ∧ pick w = (2, 0)) ∨
    (2 * Real.sqrt 3 ≤ w ∧ w ≤ 1 + 3 * Real.sqrt 3 ∧ pick w = (0, 2)) ∨
    (1 + 3 * Real.sqrt 3 < w ∧ pick w = (2, 2)) := by
  unfold pick
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨not_le.mp h1, h2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨not_lt.mp h2, h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨not_le.mp h3, rfl⟩))

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem pick_eq_00 {w : ℝ} (h : w ≤ 1 + Real.sqrt 3) : pick w = (0, 0) := by
  unfold pick; rw [ite_eq_left h]

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem pick_eq_20 {w : ℝ} (h1 : 1 + Real.sqrt 3 < w) (h2 : w < 2 * Real.sqrt 3) :
    pick w = (2, 0) := by
  unfold pick; rw [ite_eq_right (not_le.mpr h1), ite_eq_left h2]

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem pick_eq_22 {w : ℝ} (h : 1 + 3 * Real.sqrt 3 < w) : pick w = (2, 2) := by
  have hne1 : ¬ (w ≤ 1 + Real.sqrt 3) := by intro hx; linarith [s3_lb]
  have hne2 : ¬ (w < 2 * Real.sqrt 3) := by intro hx; linarith [s3_lb]
  unfold pick; rw [ite_eq_right hne1, ite_eq_right hne2, ite_eq_right (not_le.mpr h)]

/-- The digits produced are always `0` or `2`: the even-digit alphabet `Ev₃`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem pick_fst_mem (w : ℝ) : (pick w).1 = 0 ∨ (pick w).1 = 2 := by
  rcases pick_cases w with ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩ <;> rw [hp] <;> simp

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem pick_snd_mem (w : ℝ) : (pick w).2 = 0 ∨ (pick w).2 = 2 := by
  rcases pick_cases w with ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩ <;> rw [hp] <;> simp

/-- `b = 2` is chosen exactly when it is available: outside `L = [0, 2√3)`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem pick_snd_eq_two_iff (w : ℝ) : (pick w).2 = 2 ↔ 2 * Real.sqrt 3 ≤ w := by
  rcases pick_cases w with ⟨hw, hp⟩ | ⟨h1, h2, hp⟩ | ⟨h1, h2, hp⟩ | ⟨hw, hp⟩ <;> rw [hp]
  · constructor
    · intro h; exact absurd h (by norm_num)
    · intro h; linarith [s3_lb]
  · constructor
    · intro h; exact absurd h (by norm_num)
    · intro h; linarith
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun _ => by linarith [s3_lb], fun _ => rfl⟩

/-- `a = 2` is chosen exactly on the trap set `A = (U, 2√3) ∪ (2√3+U, 3U]`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem pick_fst_eq_two_iff (w : ℝ) :
    (pick w).1 = 2 ↔ ((1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3) ∨ 1 + 3 * Real.sqrt 3 < w) := by
  rcases pick_cases w with ⟨hw, hp⟩ | ⟨h1, h2, hp⟩ | ⟨h1, h2, hp⟩ | ⟨hw, hp⟩ <;> rw [hp]
  · constructor
    · intro h; exact absurd h (by norm_num)
    · rintro (⟨hx, _⟩ | hx) <;> linarith [s3_lb]
  · exact ⟨fun _ => Or.inl ⟨h1, h2⟩, fun _ => rfl⟩
  · constructor
    · intro h; exact absurd h (by norm_num)
    · rintro (⟨_, hx⟩ | hx) <;> linarith
  · exact ⟨fun _ => Or.inr hw, fun _ => rfl⟩

/-- **The Cover Lemma at `m = 3`** ([Utz51]; plan §1.3).  Whatever the state `w ∈ [0, 3U]`,
the chosen offset lands the residual back in `[0, U]`.  The four gap inequalities are
`2 ≤ U`, `2√3 - 2 ≤ U`, `2 + 2√3 - 2√3 ≤ U`, and the top identity `2 + 2√3 + U = 3U`. -/
@[category research solved, AMS 11, ref "Utz51", group "dub06_cover_game"]
theorem pick_residual_mem {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 3 + 3 * Real.sqrt 3) :
    0 ≤ w - (((pick w).1 : ℝ) + ((pick w).2 : ℝ) * Real.sqrt 3) ∧
      w - (((pick w).1 : ℝ) + ((pick w).2 : ℝ) * Real.sqrt 3) ≤ 1 + Real.sqrt 3 := by
  rcases pick_cases w with ⟨hw, hp⟩ | ⟨ha, hb, hp⟩ | ⟨ha, hb, hp⟩ | ⟨hw, hp⟩ <;> rw [hp] <;>
    norm_num <;> constructor <;> linarith [s3_lb, s3_ub]

/-! ## The state -/

/-- The rescaled greedy state, as a pair of integers `(P k, Q k)` standing for
`P k + Q k √3`.  The seed is `3 σ = -12 + 9√3` with `σ = 3√3 - 4` the translate
`(j, k₀) = (2, 1)` of plan §1.2. -/
noncomputable def coverState : ℕ → ℤ × ℤ
  | 0 => (-12, 9)
  | k + 1 =>
      (3 * ((coverState k).1 - (pick (((coverState k).1 : ℝ)
              + ((coverState k).2 : ℝ) * Real.sqrt 3)).1),
       3 * ((coverState k).2 - (pick (((coverState k).1 : ℝ)
              + ((coverState k).2 : ℝ) * Real.sqrt 3)).2))

/-- The real value `P k + Q k √3` of the state. -/
noncomputable def W (k : ℕ) : ℝ :=
  ((coverState k).1 : ℝ) + ((coverState k).2 : ℝ) * Real.sqrt 3

/-- The `x`-digit chosen at step `k`. -/
noncomputable def digitA (k : ℕ) : ℤ := (pick (W k)).1

/-- The `y`-digit chosen at step `k`. -/
noncomputable def digitB (k : ℕ) : ℤ := (pick (W k)).2

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem coverState_succ (k : ℕ) :
    coverState (k + 1) = (3 * ((coverState k).1 - digitA k), 3 * ((coverState k).2 - digitB k)) :=
  rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_zero : W 0 = -12 + 9 * Real.sqrt 3 := by
  simp [W, coverState]

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_succ (k : ℕ) :
    W (k + 1) = 3 * (W k - ((digitA k : ℝ) + (digitB k : ℝ) * Real.sqrt 3)) := by
  rw [W, coverState_succ, W]
  push_cast
  ring

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem digitA_mem (k : ℕ) : digitA k = 0 ∨ digitA k = 2 := pick_fst_mem (W k)

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem digitB_mem (k : ℕ) : digitB k = 0 ∨ digitB k = 2 := pick_snd_mem (W k)

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem digitA_even (k : ℕ) : Even (digitA k) := by
  rcases digitA_mem k with h | h <;> rw [h] <;> decide

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem digitB_even (k : ℕ) : Even (digitB k) := by
  rcases digitB_mem k with h | h <;> rw [h] <;> decide

/-- **The invariant** (Cover Lemma, by induction): the state never leaves `[0, 3U]`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_mem (k : ℕ) : 0 ≤ W k ∧ W k ≤ 3 + 3 * Real.sqrt 3 := by
  induction k with
  | zero =>
    rw [W_zero]
    constructor <;> linarith [s3_lb, s3_ub]
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := pick_residual_mem ih.1 ih.2
    rw [W_succ, digitA, digitB]
    constructor <;> linarith

/-! ## Growth of the `√3`-coordinate (note M1 §1.2, Lemma L1.1) -/

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem coverState_snd_lower (k : ℕ) : 6 * 3 ^ k + 3 ≤ (coverState k).2 := by
  induction k with
  | zero => norm_num [coverState]
  | succ k ih =>
    have hb : digitB k ≤ 2 := by rcases digitB_mem k with h | h <;> omega
    rw [coverState_succ]
    simp only
    have h3 : (3:ℤ) ^ (k + 1) = 3 * 3 ^ k := by ring
    omega

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem coverState_snd_ge_nine (k : ℕ) : 9 ≤ (coverState k).2 := by
  have h := coverState_snd_lower k
  have h1 : (1:ℤ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  omega

/-- No state is ever a candidate trap fixed point: `W k = p + q√3` forces `q` to be the
state's `√3`-coordinate, which is `≥ 9`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_ne_val (k : ℕ) {p q : ℤ} (hq : q < 9) :
    W k ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by
  intro h
  have h1 := (val_inj h).2
  have h2 := coverState_snd_ge_nine k
  omega

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_ne_zero (k : ℕ) : W k ≠ 0 := by
  have h := W_ne_val k (p := 0) (q := 0) (by norm_num)
  simpa using h

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_pos (k : ℕ) : 0 < W k := lt_of_le_of_ne (W_mem k).1 (Ne.symm (W_ne_zero k))

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_ne_three (k : ℕ) : W k ≠ 3 := by
  have h := W_ne_val k (p := 3) (q := 0) (by norm_num)
  simpa using h

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_ne_top (k : ℕ) : W k ≠ 3 + 3 * Real.sqrt 3 := by
  have h := W_ne_val k (p := 3) (q := 3) (by norm_num)
  simpa using h

/-! ## Expanding maps cannot trap an orbit -/

/-- If from step `K` on the orbit obeys one affine `3`-expanding map and stays bounded,
it sits at that map's fixed point `c/2`.  This is the whole dynamical input of L1. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem eq_fixed_of_trapped {f : ℕ → ℝ} {c D : ℝ} {K : ℕ}
    (hrec : ∀ k, K ≤ k → f (k + 1) = 3 * f k - c)
    (hbd : ∀ k, K ≤ k → |f k - c / 2| ≤ D) : f K = c / 2 := by
  by_contra hne
  have hpos : 0 < |f K - c / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hpow : ∀ j : ℕ, f (K + j) - c / 2 = 3 ^ j * (f K - c / 2) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep := hrec (K + j) (Nat.le_add_right _ _)
      have e : K + (j + 1) = (K + j) + 1 := by omega
      rw [e, hstep, pow_succ]
      linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D / |f K - c / 2|) (by norm_num : (1:ℝ) < 3)
  have hb := hbd (K + n) (Nat.le_add_right _ _)
  rw [hpow n, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)] at hb
  have hlt := (div_lt_iff₀ hpos).mp hn
  linarith

/-! ## L1, the `b`-side: the orbit leaves `L = [0, 2√3)` infinitely often -/

/-- **L1(b)** (note M1 §1.4).  Under the selection rule of `pick`, `bₖ = 0` exactly on
`L = [0, 2√3)`.  Were `bₖ = 0` from some point on, the state would be confined to
`[0, 2√3/3) ∪ (U, 2 + 2√3/3)`; the second zone is absorbing and carries the expanding map
`w ↦ 3w - 6` with fixed point `3`, excluded by `W_ne_three`, while on the first zone the
state is multiplied by `3` forever, contradicting `W_pos`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem exists_digitB_eq_two (N : ℕ) : ∃ k, N ≤ k ∧ digitB k = 2 := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ k, N ≤ k → W k < 2 * Real.sqrt 3 := by
    intro k hk
    by_contra h
    exact hcon k hk ((pick_snd_eq_two_iff (W k)).mpr (not_lt.mp h))
  have claim1 : ∀ k, N ≤ k → W k ≤ 1 + Real.sqrt 3 → W k < 2 * Real.sqrt 3 / 3 := by
    intro k hk hle
    have hp : pick (W k) = (0, 0) := pick_eq_00 hle
    have hs : W (k + 1) = 3 * W k := by
      rw [W_succ, digitA, digitB, hp]; push_cast; ring
    have h2 := hlt (k + 1) (by omega)
    rw [hs] at h2
    linarith
  have claim2 : ∀ k, N ≤ k → 1 + Real.sqrt 3 < W k → W k < 2 + 2 * Real.sqrt 3 / 3 := by
    intro k hk hgt
    have hp : pick (W k) = (2, 0) := pick_eq_20 hgt (hlt k hk)
    have hs : W (k + 1) = 3 * W k - 6 := by
      rw [W_succ, digitA, digitB, hp]; push_cast; ring
    have h2 := hlt (k + 1) (by omega)
    rw [hs] at h2
    linarith
  by_cases hex : ∃ j, N ≤ j ∧ 1 + Real.sqrt 3 < W j
  · obtain ⟨j, hjN, hj⟩ := hex
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < W k ∧ W k < 2 + 2 * Real.sqrt 3 / 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj, claim2 j hjN hj⟩
      | succ k hk ih =>
        have hkN : N ≤ k := le_trans hjN hk
        have hp : pick (W k) = (2, 0) := pick_eq_20 ih.1 (hlt k hkN)
        have hs : W (k + 1) = 3 * W k - 6 := by
          rw [W_succ, digitA, digitB, hp]; push_cast; ring
        have hgt : 1 + Real.sqrt 3 < W (k + 1) := by
          by_contra hle
          have h3 := claim1 (k + 1) (by omega) (not_lt.mp hle)
          rw [hs] at h3
          linarith [s3_lb, ih.1]
        exact ⟨hgt, claim2 (k + 1) (by omega) hgt⟩
    have hfix : W j = 6 / 2 := by
      refine eq_fixed_of_trapped (c := 6) (D := 1) (K := j) (fun k hk => ?_) (fun k hk => ?_)
      · have hkN : N ≤ k := le_trans hjN hk
        have hp : pick (W k) = (2, 0) := pick_eq_20 (habs k hk).1 (hlt k hkN)
        rw [W_succ, digitA, digitB, hp]; push_cast; ring
      · obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]
        constructor <;> linarith [s3_lb, s3_ub]
    exact W_ne_three j (by rw [hfix]; norm_num)
  · push Not at hex
    have hzone : ∀ k, N ≤ k → W k ≤ 1 + Real.sqrt 3 := fun k hk => hex k hk
    have htriple : ∀ n : ℕ, W (N + n) = 3 ^ n * W N := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hk : N ≤ N + n := Nat.le_add_right _ _
        have hp : pick (W (N + n)) = (0, 0) := pick_eq_00 (hzone _ hk)
        have e : N + (n + 1) = (N + n) + 1 := by omega
        rw [e, W_succ, digitA, digitB, hp]
        push_cast
        rw [ih, pow_succ]
        ring
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 + Real.sqrt 3) / W N) (by norm_num : (1:ℝ) < 3)
    have hb := hzone (N + n) (Nat.le_add_right _ _)
    rw [htriple n] at hb
    have hlt2 := (div_lt_iff₀ (W_pos N)).mp hn
    linarith

/-! ## L1, the `a`-side: the orbit leaves `A` infinitely often -/

/-- **L1(a)** (note M1 §1.3).  `aₖ = 2` exactly on `A = A₁ ∪ A₂` with `A₁ = (U, 2√3)`,
`A₂ = (2√3+U, 3U]`.  `A₁` is absorbing inside `A` (its image misses `A₂`), so an infinite
stay in `A` is eventually confined to a single component; the fixed points `3` (of `A₁`)
and `3 + 3√3` (of `A₂`) are excluded by `W_ne_three` and `W_ne_top`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem exists_digitA_eq_zero (N : ℕ) : ∃ k, N ≤ k ∧ digitA k = 0 := by
  by_contra hcon
  push Not at hcon
  have htwo : ∀ k, N ≤ k → digitA k = 2 := by
    intro k hk
    rcases digitA_mem k with h | h
    · exact absurd h (hcon k hk)
    · exact h
  have hA : ∀ k, N ≤ k →
      (1 + Real.sqrt 3 < W k ∧ W k < 2 * Real.sqrt 3) ∨ 1 + 3 * Real.sqrt 3 < W k := by
    intro k hk
    exact (pick_fst_eq_two_iff (W k)).mp (htwo k hk)
  by_cases hex : ∃ j, N ≤ j ∧ 1 + Real.sqrt 3 < W j ∧ W j < 2 * Real.sqrt 3
  · obtain ⟨j, hjN, hj1, hj2⟩ := hex
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < W k ∧ W k < 2 * Real.sqrt 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj1, hj2⟩
      | succ k hk ih =>
        have hp : pick (W k) = (2, 0) := pick_eq_20 ih.1 ih.2
        have hs : W (k + 1) = 3 * W k - 6 := by
          rw [W_succ, digitA, digitB, hp]; push_cast; ring
        rcases hA (k + 1) (by omega) with h | h
        · exact h
        · exfalso
          rw [hs] at h
          linarith [s3_lb, s3_ub, ih.2]
    have hfix : W j = 6 / 2 := by
      refine eq_fixed_of_trapped (c := 6) (D := 1) (K := j) (fun k hk => ?_) (fun k hk => ?_)
      · have hp : pick (W k) = (2, 0) := pick_eq_20 (habs k hk).1 (habs k hk).2
        rw [W_succ, digitA, digitB, hp]; push_cast; ring
      · obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]
        constructor <;> linarith [s3_lb, s3_ub]
    exact W_ne_three j (by rw [hfix]; norm_num)
  · push Not at hex
    have hA2 : ∀ k, N ≤ k → 1 + 3 * Real.sqrt 3 < W k := by
      intro k hk
      rcases hA k hk with ⟨h1, h2⟩ | h
      · exact absurd h2 (not_lt.mpr (hex k hk h1))
      · exact h
    have hfix : W N = (6 + 6 * Real.sqrt 3) / 2 := by
      refine eq_fixed_of_trapped (c := 6 + 6 * Real.sqrt 3) (D := 2) (K := N)
        (fun k hk => ?_) (fun k hk => ?_)
      · have hp : pick (W k) = (2, 2) := pick_eq_22 (hA2 k hk)
        rw [W_succ, digitA, digitB, hp]; push_cast; ring
      · have h1 := hA2 k hk
        have h2 := (W_mem k).2
        rw [abs_le]
        constructor <;> linarith
    exact W_ne_top N (by rw [hfix]; ring)

/-! ## Convergence: the greedy solves the translate equation -/

/-- The residual identity: `W k = 3^{k+1} (σ - Xₖ - √3 Yₖ)` with `σ = 3√3 - 4`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem W_eq_residual (k : ℕ) :
    W k = 3 ^ (k + 1) * ((3 * Real.sqrt 3 - 4) - digitSum 3 digitA k
      - Real.sqrt 3 * digitSum 3 digitB k) := by
  induction k with
  | zero => rw [W_zero, digitSum_zero, digitSum_zero]; ring
  | succ k ih =>
    rw [W_succ, ih, digitSum_succ, digitSum_succ]
    have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3]
    have hne : (3 : ℝ) ^ (k + 1) ≠ 0 := by positivity
    field_simp
    ring

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem isDigits_digitA : IsDigits 3 digitA :=
  { two_le := by norm_num
    nonneg := fun i => by rcases digitA_mem i with h | h <;> omega
    le_sub_one := fun i => by rcases digitA_mem i with h | h <;> omega }

@[category API, AMS 11, ref "Dub06EO", group "dub06_cover_game"]
theorem isDigits_digitB : IsDigits 3 digitB :=
  { two_le := by norm_num
    nonneg := fun i => by rcases digitB_mem i with h | h <;> omega
    le_sub_one := fun i => by rcases digitB_mem i with h | h <;> omega }

/-- **The greedy converges to a solution of the translate equation** — the constructive
form of Utz's theorem at slope `√3` and target `σ = 3√3 - 4`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem digitReal_translate :
    digitReal 3 digitA + Real.sqrt 3 * digitReal 3 digitB = 3 * Real.sqrt 3 - 4 := by
  have hlim : Tendsto (fun k => digitSum 3 digitA k + Real.sqrt 3 * digitSum 3 digitB k)
      atTop (𝓝 (digitReal 3 digitA + Real.sqrt 3 * digitReal 3 digitB)) :=
    (digitSum_tendsto isDigits_digitA).add
      (tendsto_const_nhds.mul (digitSum_tendsto isDigits_digitB))
  have hzero : Tendsto (fun k : ℕ => (3 * Real.sqrt 3 - 4)
      - (digitSum 3 digitA k + Real.sqrt 3 * digitSum 3 digitB k)) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun k : ℕ => (3 + 3 * Real.sqrt 3) / 3 ^ (k + 1))
      (fun k => ?_) (fun k => ?_) ?_
    · have h := (W_mem k).1
      rw [W_eq_residual k] at h
      have hp : (0:ℝ) < 3 ^ (k + 1) := by positivity
      nlinarith
    · have h := (W_mem k).2
      rw [W_eq_residual k] at h
      have hp : (0:ℝ) < 3 ^ (k + 1) := by positivity
      rw [le_div_iff₀ hp]
      nlinarith
    · have hmain : Tendsto (fun k : ℕ => (3 + 3 * Real.sqrt 3) * (1 / 3 : ℝ) ^ (k + 1))
          atTop (𝓝 0) := by
        have hg : Tendsto (fun k : ℕ => (1 / 3 : ℝ) ^ (k + 1)) atTop (𝓝 0) := by
          have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/3 : ℝ))
            (by norm_num) (by norm_num)
          exact h0.comp (Filter.tendsto_add_atTop_nat 1)
        simpa using hg.const_mul (3 + 3 * Real.sqrt 3)
      refine hmain.congr fun k => ?_
      rw [div_pow, one_pow]
      ring
  have hlim2 : Tendsto (fun k => digitSum 3 digitA k + Real.sqrt 3 * digitSum 3 digitB k)
      atTop (𝓝 (3 * Real.sqrt 3 - 4)) := by
    have h := (tendsto_const_nhds (x := (3 * Real.sqrt 3 - 4)) (f := atTop (α := ℕ))).sub hzero
    simpa using h
  exact tendsto_nhds_unique hlim hlim2

end SZ
