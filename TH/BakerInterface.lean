/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.BakerWustholz
import CITED.Matveev
import ForMathlib.NumberTheory.RatHeight
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Fin
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The shared Baker–Wüstholz-over-ℚ interface

The digit / repetition theorems of the `(3/2)ⁿ` program ([W2] §7 A4; [M4A3] §6)
all reduce an arithmetic obstruction to a nonzero linear form
`Λ = ∑ᵢ bᵢ·log αᵢ` in logarithms of **positive rationals** `αᵢ` (of the shapes
`2, 3, u, 2^p − 1`) and feed it to `BakerWustholz.linearForms_logs`
(`CITED/BakerWustholz.lean`).  Doing so twice already
(`TH/StewartDigits.lean`, `TH/ExtremalBaker.lean`) duplicated a fixed block of
plumbing `private`: the value of the Baker–Wüstholz *modified height* on a
rational, the three height evaluations `h'(2), h'(3), h'(u)`, a handful of
numeric `log` facts, and the `ℂ`-cast / `Fin.sum_univ` dance that turns the
axiom's complex statement into a real inequality.

This file (§5.1 of `plan-A4+.html`, milestone M-1) promotes that block to a
public, `ref "BW93"` interface so that no future consumer redoes it:

* the numeric `log` facts and the constant-nonnegativity `C_one_nonneg`;
* `modifiedHeight_rat`, `norm_log_ratCast`, and the evaluations `mh_two`,
  `mh_three`, `mh_intCast` of `BakerWustholz.modifiedHeight (Rat.castHom ℂ)`
  (all with `d = Module.finrank ℚ ℚ = 1`, so the modified height is the plain
  `max(log Weil height, |log|, 1)`);
* the **packaged bound** `log_linearForm_rat_ge`: from a nonzero real form
  `Λ = ∑ᵢ bᵢ·log αᵢ` over positive rationals with `|bᵢ| ≤ B`, `2 ≤ B`,
  directly
  `log Λ ≥ −C(n,1)·max(log B, 1)·∏ᵢ h'(αᵢ)`,
  with the complex-log bridge discharged internally.

`ForMathlib/NumberTheory/RatHeight.lean` supplies the height evaluations
(`Rat.logHeight₁_natCast`, `Rat.logHeight₁_intCast`) this interface rests on.

## The Matveev twin (`plan-formalize-logforms.html` M-4, F-5a)

The same over-ℚ plumbing, backed by Matveev's `CITED/Matveev.lean` engine
(Corollary 2.3) instead of Baker–Wüstholz, is provided by
`log_linearForm_rat_ge_matveev`.  A consumer swaps engines by replacing one
`log_linearForm_rat_ge` call with `log_linearForm_rat_ge_matveev` and bounding
the height product with `clampHeight_two`/`clampHeight_three`/`clampHeight_intCast`
in place of `mh_two`/`mh_three`/`mh_intCast`.  The two visible differences that
make Matveev sharper: the modified height carries the `0.16` Lehmer floor (not
BW's `1`), so `clampHeight 2 = log 2` where BW rounds `h'(2)` up to `1`; and the
`B`-factor is `log(eB) = 1 + log B` in place of `max(log B, 1)`.

## Contents

* `one_le_log_three`, `log_two_le_one`, `log_two_pos'`, `log_three_pos'` —
  numeric `log` facts.
* `C_one_nonneg` — `0 ≤ BakerWustholz.C n 1` for every `n` (the `d = 1`
  constant is nonnegative).
* `modifiedHeight_rat` — `h'(q) = max(logHeight₁ q, max ‖Complex.log q‖ 1)`
  at `d = 1`.
* `norm_log_ratCast` — `‖Complex.log q‖ = |Real.log q|` for `q > 0`.
* `mh_two`, `mh_three` — `h'(2) ≤ 1`, `h'(3) ≤ log 3`.
* `mh_intCast` — `h'(u) ≤ max(log u, 1)` for an integer `u ≥ 1`.
* `complex_log_ratCast_pos` — `Complex.log q = ↑(Real.log q)` for `q > 0`.
* `log_linearForm_rat_ge` — **the packaged Baker–Wüstholz lower bound over ℚ**.
* `log_two_ge_sixteenth`, `log_three_ge_sixteenth` — the `0.16` Lehmer floor
  sits below `log 2` and `log 3`.
* `clampHeight_two`, `clampHeight_three`, `clampHeight_intCast`,
  `clampHeight_nonneg` — the Matveev modified-height evaluations over ℚ.
* `log_linearForm_rat_ge_matveev` — **the packaged Matveev lower bound over ℚ**.

## References

* [BW93] Baker, Wüstholz. *Logarithmic forms and group varieties.* J. reine
  angew. Math. **442** (1993), 19–62.  (Via `CITED/BakerWustholz.lean`.)
* [Mat00] E. M. Matveev, *An explicit lower bound …, II.* Izv. Math. **64**:6
  (2000), 1217–1269.  (Via `CITED/Matveev.lean`.)
* [W2] `report2-weyl.html` (this repository, 2026-07): §7 angle A4.
* [M4A3] `plan-M4A3.html`; [A4+] `plan-A4+.html` §5.1 (this refactor);
  [LF] `plan-formalize-logforms.html` M-4/F-5a (the Matveev twin).
-/

open Complex

namespace TH

/-! ## Numeric log facts -/

/-- `1 ≤ log 3`. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact le_trans Real.exp_one_lt_d9.le (by norm_num)

/-- `log 2 ≤ 1`. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma log_two_le_one : Real.log 2 ≤ 1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  exact le_trans (by norm_num) Real.exp_one_gt_d9.le

/-- `0 < log 2`. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma log_two_pos' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- `0 < log 3`. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma log_three_pos' : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)

/-- The Baker–Wüstholz constant `C(n, 1)` is nonnegative (all its factors are,
`log (2n) ≥ 0` and the vanishing `n = 0` case included). -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma C_one_nonneg (n : ℕ) : 0 ≤ BakerWustholz.C n 1 := by
  unfold BakerWustholz.C
  simp only [Nat.cast_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : (0 : ℝ) ≤ Real.log (2 * (n : ℝ) * 1) :=
      Real.log_nonneg (by nlinarith [hn1])
    exact mul_nonneg (by positivity) hlog

/-! ## The Baker–Wüstholz modified height over ℚ (`d = 1`) -/

/-- Over `K = ℚ` (degree `1`), the Baker–Wüstholz modified height unfolds to
`max(logHeight₁ q, max ‖Complex.log q‖ 1)`. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma modifiedHeight_rat (q : ℚ) :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ) q
      = max (Height.logHeight₁ q) (max ‖Complex.log ((q : ℂ))‖ 1) := by
  unfold BakerWustholz.modifiedHeight
  rw [eq_ratCast]
  norm_num [Module.finrank_self]

/-- For a positive rational, the complex-log norm is the real-log absolute
value. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma norm_log_ratCast {q : ℚ} (hq : 0 < q) :
    ‖Complex.log ((q : ℂ))‖ = |Real.log ((q : ℝ))| := by
  have hcast : ((q : ℚ) : ℂ) = (((q : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, ← Complex.ofReal_log (by exact_mod_cast hq.le : (0 : ℝ) ≤ (q : ℝ)),
    Complex.norm_real, Real.norm_eq_abs]

/-- `h'(3) ≤ log 3`. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma mh_three : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (3 : ℚ)
    ≤ Real.log 3 := by
  rw [modifiedHeight_rat, norm_log_ratCast (by norm_num)]
  have h1 : Height.logHeight₁ (3 : ℚ) = Real.log 3 := by
    have h := Rat.logHeight₁_natCast 3
    simpa using h
  have h2 : |Real.log (((3 : ℚ) : ℝ))| = Real.log 3 := by
    rw [show ((3 : ℚ) : ℝ) = 3 by norm_num,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
  rw [h1, h2]
  exact max_le le_rfl (max_le le_rfl one_le_log_three)

/-- `h'(2) ≤ 1`. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma mh_two : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (2 : ℚ)
    ≤ 1 := by
  rw [modifiedHeight_rat, norm_log_ratCast (by norm_num)]
  have h1 : Height.logHeight₁ (2 : ℚ) = Real.log 2 := by
    have h := Rat.logHeight₁_natCast 2
    simpa using h
  have h2 : |Real.log (((2 : ℚ) : ℝ))| = Real.log 2 := by
    rw [show ((2 : ℚ) : ℝ) = 2 by norm_num,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
  rw [h1, h2]
  exact max_le log_two_le_one (max_le log_two_le_one le_rfl)

/-- `h'(u) ≤ max(log u, 1)` for an integer `u ≥ 1` (cast to `ℚ`). -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma mh_intCast {u : ℤ} (hu : 1 ≤ u) :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ) ((u : ℤ) : ℚ)
      ≤ max (Real.log ((u : ℤ) : ℝ)) 1 := by
  have huQ : (0 : ℚ) < (u : ℚ) := by exact_mod_cast lt_of_lt_of_le one_pos hu
  have huR : (1 : ℝ) ≤ ((u : ℤ) : ℝ) := by exact_mod_cast hu
  rw [modifiedHeight_rat, norm_log_ratCast huQ]
  have h1 : Height.logHeight₁ ((u : ℤ) : ℚ) = Real.log ((u : ℤ) : ℝ) := by
    rw [Rat.logHeight₁_intCast u, abs_of_pos (by linarith)]
  have h2 : |Real.log ((((u : ℤ) : ℚ)) : ℝ)| = Real.log ((u : ℤ) : ℝ) := by
    rw [show ((((u : ℤ) : ℚ)) : ℝ) = ((u : ℤ) : ℝ) by push_cast; ring,
      abs_of_nonneg (Real.log_nonneg huR)]
  rw [h1, h2]
  exact max_le (le_max_left _ _) (max_le (le_max_left _ _) (le_max_right _ _))

/-! ## The packaged rational `n`-log lower bound -/

/-- For a positive rational, the complex principal log is the real log, cast. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
lemma complex_log_ratCast_pos {q : ℚ} (hq : 0 < q) :
    Complex.log ((Rat.castHom ℂ) q) = ((Real.log (q : ℝ) : ℝ) : ℂ) := by
  rw [eq_ratCast, show ((q : ℚ) : ℂ) = (((q : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by exact_mod_cast hq.le)]

/-- **The packaged Baker–Wüstholz lower bound over ℚ** ([BW93], via
`CITED/BakerWustholz.lean`): let `α₁, …, αₙ` (`1 ≤ n`) be **positive** rationals,
`b₁, …, bₙ` integers with `|bᵢ| ≤ B` and `2 ≤ B`.  If the real linear form
`Λ = ∑ᵢ bᵢ·log αᵢ` is nonzero, then

  `log Λ ≥ −C(n, 1) · max(log B, 1) · ∏ᵢ h'(αᵢ)`,

where `C(n, 1) = BakerWustholz.C n 1` and `h'(αᵢ)` is
`BakerWustholz.modifiedHeight (Rat.castHom ℂ) (αᵢ)`.

This discharges the complex-log / `Fin.sum_univ` bridge once and for all: a
consumer supplies the vectors `α, b`, the coefficient bound, and the real
identity `Λ = ∑ bᵢ log αᵢ`, then bounds the height product `∏ᵢ h'(αᵢ)` with
`mh_two`/`mh_three`/`mh_intCast`.  (Since `Real.log Λ = Real.log |Λ|` the sign
of `Λ` is irrelevant.)  Footprint std3 + [BW93]. -/
@[category API, AMS 11, ref "BW93", group "three_halves_m4"]
theorem log_linearForm_rat_ge {n : ℕ} (hn : 0 < n) (α : Fin n → ℚ)
    (hα : ∀ i, 0 < α i) (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B)
    (hbB : ∀ i, (b i).natAbs ≤ B) {Λ : ℝ}
    (hΛeq : Λ = ∑ i, (b i : ℝ) * Real.log (α i : ℝ)) (hΛ : Λ ≠ 0) :
    -(BakerWustholz.C n 1 * max (Real.log B) 1
        * ∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (α i))
      ≤ Real.log Λ := by
  have hαne : ∀ i, α i ≠ 0 := fun i => (hα i).ne'
  have hsum : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) = ((Λ : ℝ) : ℂ) := by
    rw [hΛeq]; push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [complex_log_ratCast_pos (hα i)]
  have hΛneC : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) ≠ 0 := by
    rw [hsum]; exact Complex.ofReal_ne_zero.mpr hΛ
  have hBW := BakerWustholz.linearForms_logs (n := n) hn
    (Rat.castHom ℂ) α hαne b (B := B) hB hbB hΛneC
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, Real.log_abs,
    Module.finrank_self, Nat.cast_one] at hBW
  rw [show (1 : ℝ) / (1 : ℝ) = 1 by norm_num] at hBW
  exact hBW

/-! ## The Matveev modified height over ℚ (`0.16` floor, `D = 1`)

Matveev's `CITED/Matveev.lean` modified height `clampHeight` clamps
`logHeight₁ α` (the *unnormalized* `D·h`, so **no division**) with a `0.16`
Lehmer floor.  Over `K = ℚ` (`D = 1`) it evaluates to `log 2`, `log 3`,
`max(log u, 0.16)` on `2`, `3`, `u` — the `0.16`-vs-`1` floor is exactly where
Matveev beats Baker–Wüstholz on the small logs (`log 2 ≈ 0.69 < 1`). -/

/-- `0.16 ≤ log 2` — Matveev's Lehmer floor sits below `log 2`, so it never
bites at `α = 2` (`clampHeight_two`). -/
@[category API, AMS 11, ref "Mat00", group "three_halves_m4"]
lemma log_two_ge_sixteenth : (0.16 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

/-- `0.16 ≤ log 3`. -/
@[category API, AMS 11, ref "Mat00", group "three_halves_m4"]
lemma log_three_ge_sixteenth : (0.16 : ℝ) ≤ Real.log 3 :=
  le_trans (by norm_num) one_le_log_three

/-- Over `K = ℚ`, Matveev's `0.16`-floored modified height at `α = 2` is `log 2`
(the Weil term `logHeight₁ 2 = log 2` beats the `0.16` floor).  This is the key
sharpening over Baker–Wüstholz, whose floor `1` forces `h'(2) = 1` (`mh_two`). -/
@[category API, AMS 11, ref "Mat00", group "three_halves_m4"]
lemma clampHeight_two : Matveev.clampHeight (Rat.castHom ℂ) (2 : ℚ) = Real.log 2 := by
  unfold Matveev.clampHeight
  have h1 : Height.logHeight₁ (2 : ℚ) = Real.log 2 := by
    have h := Rat.logHeight₁_natCast 2; simpa using h
  have h2 : ‖Complex.log ((Rat.castHom ℂ) (2 : ℚ))‖ = Real.log 2 := by
    rw [eq_ratCast, norm_log_ratCast (by norm_num),
      show ((2 : ℚ) : ℝ) = 2 by norm_num, abs_of_nonneg (Real.log_nonneg (by norm_num))]
  rw [h1, h2, max_eq_left log_two_ge_sixteenth, max_self]

/-- Over `K = ℚ`, Matveev's modified height at `α = 3` is `log 3`. -/
@[category API, AMS 11, ref "Mat00", group "three_halves_m4"]
lemma clampHeight_three : Matveev.clampHeight (Rat.castHom ℂ) (3 : ℚ) = Real.log 3 := by
  unfold Matveev.clampHeight
  have h1 : Height.logHeight₁ (3 : ℚ) = Real.log 3 := by
    have h := Rat.logHeight₁_natCast 3; simpa using h
  have h2 : ‖Complex.log ((Rat.castHom ℂ) (3 : ℚ))‖ = Real.log 3 := by
    rw [eq_ratCast, norm_log_ratCast (by norm_num),
      show ((3 : ℚ) : ℝ) = 3 by norm_num, abs_of_nonneg (Real.log_nonneg (by norm_num))]
  rw [h1, h2, max_eq_left log_three_ge_sixteenth, max_self]

/-- Over `K = ℚ`, Matveev's modified height at an integer `u ≥ 1` is
`≤ max(log u, 0.16)` — where BW gives `max(log u, 1)` (`mh_intCast`). -/
@[category API, AMS 11, ref "Mat00", group "three_halves_m4"]
lemma clampHeight_intCast {u : ℤ} (hu : 1 ≤ u) :
    Matveev.clampHeight (Rat.castHom ℂ) ((u : ℤ) : ℚ)
      ≤ max (Real.log ((u : ℤ) : ℝ)) 0.16 := by
  have huQ : (0 : ℚ) < (u : ℚ) := by exact_mod_cast lt_of_lt_of_le one_pos hu
  have huR : (1 : ℝ) ≤ ((u : ℤ) : ℝ) := by exact_mod_cast hu
  unfold Matveev.clampHeight
  have h1 : Height.logHeight₁ ((u : ℤ) : ℚ) = Real.log ((u : ℤ) : ℝ) := by
    rw [Rat.logHeight₁_intCast u, abs_of_pos (by linarith)]
  have h2 : ‖Complex.log ((Rat.castHom ℂ) ((u : ℤ) : ℚ))‖ = Real.log ((u : ℤ) : ℝ) := by
    rw [eq_ratCast, norm_log_ratCast huQ,
      show ((((u : ℤ) : ℚ)) : ℝ) = ((u : ℤ) : ℝ) by push_cast; ring,
      abs_of_nonneg (Real.log_nonneg huR)]
  rw [h1, h2]
  exact max_le (le_max_left _ _) le_rfl

/-- Every Matveev modified height over ℚ is nonnegative (the `0.16` floor). -/
@[category API, AMS 11, ref "Mat00", group "three_halves_m4"]
lemma clampHeight_nonneg (q : ℚ) : 0 ≤ Matveev.clampHeight (Rat.castHom ℂ) q := by
  unfold Matveev.clampHeight
  exact le_trans (by norm_num : (0 : ℝ) ≤ (0.16 : ℝ))
    (le_max_of_le_right (le_max_right _ _))

/-- Matveev's modified height never exceeds Baker–Wüstholz's over ℚ: the only
difference is the Lehmer floor (`0.16 ≤ 1`), so `clampHeight q ≤ h'(q)` for every
rational `q`.  Lets a Matveev height bound be discharged from an existing BW one
(used for the moving multiplier `λ'_s`, whose Weil term dominates the floor). -/
@[category API, AMS 11, ref "Mat00", group "three_halves_m4"]
lemma clampHeight_le_modifiedHeight (q : ℚ) :
    Matveev.clampHeight (Rat.castHom ℂ) q
      ≤ BakerWustholz.modifiedHeight (Rat.castHom ℂ) q := by
  rw [modifiedHeight_rat]
  unfold Matveev.clampHeight
  exact max_le_max le_rfl (max_le_max le_rfl (by norm_num))

/-! ## The packaged Matveev `n`-log lower bound over ℚ -/

/-- **The packaged Matveev lower bound over ℚ** ([Mat00], via `CITED/Matveev.lean`,
Corollary 2.3): let `α₁, …, αₙ` (`2 ≤ n`) be **positive** rationals, `b₁, …, bₙ`
integers with `|bᵢ| ≤ B` and `2 ≤ B`.  If the real linear form
`Λ = ∑ᵢ bᵢ·log αᵢ` is nonzero, then

  `log Λ ≥ −C₁(n, 1) · log(eB) · ∏ᵢ A(αᵢ)`,

where `C₁(n, 1) = Matveev.C₁ n 1` and `A(αᵢ) = Matveev.clampHeight (Rat.castHom ℂ) αᵢ`
is the `0.16`-floored modified height.  The Matveev twin of `log_linearForm_rat_ge`:
same hypotheses and complex-log bridge, sharper engine (`κ = 1` — the rational
embedding is real; `D = [ℚ:ℚ] = 1`, so `D² = 1` and `log(eD) = 1` collapse).
Footprint std3 + [Mat00]. -/
@[category API, AMS 11, ref "Mat00", group "three_halves_m4"]
theorem log_linearForm_rat_ge_matveev {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℚ)
    (hα : ∀ i, 0 < α i) (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B)
    (hbB : ∀ i, (b i).natAbs ≤ B) {Λ : ℝ}
    (hΛeq : Λ = ∑ i, (b i : ℝ) * Real.log (α i : ℝ)) (hΛ : Λ ≠ 0) :
    -(Matveev.C₁ n 1 * Real.log (Real.exp 1 * (B : ℝ))
        * ∏ i, Matveev.clampHeight (Rat.castHom ℂ) (α i))
      ≤ Real.log Λ := by
  have hαne : ∀ i, α i ≠ 0 := fun i => (hα i).ne'
  have hsum : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) = ((Λ : ℝ) : ℂ) := by
    rw [hΛeq]; push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [complex_log_ratCast_pos (hα i)]
  have hΛneC : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) ≠ 0 := by
    rw [hsum]; exact Complex.ofReal_ne_zero.mpr hΛ
  -- `κ = 1`: the rational embedding `Rat.castHom ℂ` is real.
  have hκ : ((1 : ℕ) = 1 ∧ ∀ x : ℚ, ((Rat.castHom ℂ) x).im = 0) ∨ (1 : ℕ) = 2 :=
    Or.inl ⟨rfl, fun x => by rw [eq_ratCast]; simp⟩
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 1 ≤ B)
  have hbBR : ∀ i, (|b i| : ℝ) ≤ (B : ℝ) := by
    intro i
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast hbB i
  have hM := Matveev.linearForms_logs (n := n) hn (Rat.castHom ℂ) 1 hκ α hαne b
    (B := (B : ℝ)) hBR hbBR hΛneC
  have he : Real.log (Real.exp 1 * (1 : ℝ)) = 1 := by rw [mul_one, Real.log_exp]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, Real.log_abs,
    Module.finrank_self, Nat.cast_one, one_pow, he] at hM
  exact le_trans (le_of_eq (by ring)) (le_of_lt hM)

end TH
