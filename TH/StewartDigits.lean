/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.BakerInterface
import CITED.BugeaudKaneko
import ForMathlib.Data.Nat.BinaryDigits
import Mathlib.Data.Nat.Log

/-!
# Stewart's theorem: the binary digit sum of `3^m` grows (rung M3½)

The first formalized result of the **Baker digit program** (angle A4 of
[W2] §7, corpus item [W2] §9(1)): Stewart's effective lower bound for the
binary digit sum of `3^m`,

  `s₂(3^m) ≥ log m / (log log m + C) − 1`   for all `m ≥ 2`,

with `C` an (effectively computable, here existentially quantified) constant.
This is **Theorem 2 of [Ste80]** specialized to the linear recurrence
`u_n = 3^n` and base `a = 2` (equivalently Theorem 1 of [Ste80] at `n = 3^m`,
where the base-3 side has a single digit); it is the only kind of quantitative
unconditional statement known about the bottom bits of `3^n`, and the M3½ rung
of the milestone ladder of [W2] §5.

## Proof (Stewart's, ℚ-specialized — two simplifications)

Suppose the binary expansion of `N = 3^m` (top bit `M := ⌊log₂ 3^m⌋`) has a
run of zero bits in positions `[x, y)`, `1 ≤ x < y ≤ M`.  Splitting the
expansion at the run, `3^m = A₁·2^y + A₂` with `1 ≤ A₂ < 2^x` (the low part is
odd since `3^m` is) and `2^{M-y} ≤ A₁ < 2^{M+1-y}`.  The three-log linear form

  `Λ := m·log 3 − y·log 2 − log A₁ = log (3^m / (A₁·2^y)) = log (1 + A₂/(A₁2^y))`

satisfies `0 < Λ ≤ 2^x/2^M`, while `BakerWustholz.linearForms_logs` gives
`log Λ ≥ −C(3,1)·max(log B, 1)·h'(3)h'(2)h'(A₁)` with coefficient bound
`B = 2m` and `h'(A₁) ≤ M+1−y`.  Hence the **gap principle** (`gap_bound`):

  `(M − x)·log 2 ≤ C(3,1)·log 3·(M + 1 − y)·max(log 2m, 1)`.

With `θ ≈ C'·log m` chosen just above the resulting threshold, no window of
bit positions `[M − θ^{j+1}, M − θ^j)` can be all zeros (`window_hit`), so the
windows `j = 0, …, k−1`, `k = ⌊log_θ M⌋`, each contain a set bit — pairwise
distinct, whence `s₂(3^m) ≥ k ≥ log m/log θ − 1` (`log_le_sum_digits` and the
main theorem).

Two simplifications over [Ste80] §3–4, specific to the ℚ-instance:

* **The degenerate case `Λ = 0` is impossible by parity**: `A₂ ≥ 1` because
  `3^m` is odd, so `3^m > A₁·2^y` strictly.  Stewart's Lemma 2
  (Loxton–van der Poorten) and the irrationality of `log 2/log 3` are not
  needed; the only cited input is the Baker-type lower bound, here [BW93].
* **No "`n` sufficiently large"**: the one-sided `log(1+u) ≤ u` replaces
  Stewart's inequality (10), removing both of his largeness conditions; the
  final bound holds for every `m ≥ 2`.

Axiom footprint: std3 + `BakerWustholz.linearForms_logs` ([BW93]).
Second consumer of the [BW93] axiom (after `TH.ExtremalBaker`).

## Contents

* `stewart_digitSum_three_pow` — **Stewart's theorem** for `3^m`:
  `∃ C > 0, ∀ m ≥ 2, log m/(log log m + C) − 1 ≤ s₂(3^m)`.
* `digitSum_three_pow_tendsto_atTop` — corollary: `s₂(3^m) → ∞`.
* `stewart_digitSum_three_pow_sharp` — the **Bugeaud–Kaneko sharpening** ([BK17],
  `CITED/BugeaudKaneko.lean`): the same bound with the constant improved from `1/2`
  to `1 − ε` (footprint std3 + [BK17], the sole use of that axiom here).
* `digitSum_three_pow_five` — sanity: `s₂(243) = 6`.

## References

* [Ste80] Stewart, C. L. *On the representation of an integer in two
  different bases.* J. reine angew. Math. **319** (1980), 63–72.  (Theorem 2
  with `u_n = 3^n`, `a = 2`, `α = 0`; Lemma 1 replaced by [BW93].)
* [Sha23] Sharma, Divyum. *On the representation of an imaginary quadratic
  integer in two different bases.* arXiv:2311.17348 (2023).  (The same
  Stewart skeleton for canonical number systems in imaginary quadratic
  fields, via Matveev; state of the art of the A4 angle.)
* [BW93] Baker, Wüstholz. *Logarithmic forms and group varieties.* J. reine
  angew. Math. **442** (1993), 19–62.  (Via `CITED/BakerWustholz.lean`.)
* [BK17] Bugeaud, Kaneko. *On the digital representation of smooth numbers.*
  arXiv:1704.00432 (2017).  (Cor. 1.5, via `CITED/BugeaudKaneko.lean`; the
  effective sharpening of Stewart's constant used by
  `stewart_digitSum_three_pow_sharp`.)
* [W2] `report2-weyl.html` (this repository, 2026-07): §5 (ladder, M3½),
  §7 angle A4, §9 item 1 (this formalization target).
-/

namespace TH

/-! The numeric `log` facts (`one_le_log_three`, `log_two_le_one`,
`log_two_pos'`, `log_three_pos'`), the constant-nonnegativity `C_one_nonneg`,
and the Baker–Wüstholz modified-height evaluations over ℚ (`modifiedHeight_rat`,
`norm_log_ratCast`, `mh_two`, `mh_three`, `mh_intCast`) now live in
`TH/BakerInterface.lean` (§5.1 of `plan-A4+.html`). -/

/-! ## The binary expansion of `3^m`: elementary facts -/

private lemma three_pow_mod_two (m : ℕ) : 3 ^ m % 2 = 1 := by
  rw [Nat.pow_mod]
  norm_num

private lemma le_log_two_three_pow {m : ℕ} : m ≤ Nat.log 2 (3 ^ m) := by
  have h : (2 : ℕ) ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by norm_num) m
  calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow (by norm_num) m).symm
    _ ≤ Nat.log 2 (3 ^ m) := Nat.log_mono_right h

private lemma log_two_three_pow_le {m : ℕ} : Nat.log 2 (3 ^ m) ≤ 2 * m := by
  have h : (3 : ℕ) ^ m ≤ 2 ^ (2 * m) := by
    calc (3 : ℕ) ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
      _ = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  calc Nat.log 2 (3 ^ m) ≤ Nat.log 2 (2 ^ (2 * m)) := Nat.log_mono_right h
    _ = 2 * m := Nat.log_pow (by norm_num) _

/-! ## The gap principle -/

set_option maxHeartbeats 800000 in
/-- **The gap principle** ([Ste80] §3, ℚ-specialized): a run of zero bits in
positions `[x, y)` of the binary expansion of `3^m` (with
`1 ≤ x < y ≤ M := ⌊log₂ 3^m⌋`) forces

  `(M − x)·log 2 ≤ C(3,1)·log 3·(M + 1 − y)·max(log 2m, 1)`.

Writing `3^m = A₁·2^y + A₂` with `1 ≤ A₂ < 2^x` (parity: `3^m` is odd — this
kills Stewart's degenerate case) and `A₁ < 2^{M+1−y}`, the linear form
`Λ = m·log 3 − y·log 2 − log A₁ ∈ (0, 2^{x−M}]` is Baker–Wüstholz small. -/
private lemma gap_bound {m x y : ℕ} (hm : 1 ≤ m) (hx : 1 ≤ x) (hxy : x < y)
    (hyM : y ≤ Nat.log 2 (3 ^ m))
    (hgap : ∀ i, x ≤ i → i < y → (3 ^ m).testBit i = false) :
    ((Nat.log 2 (3 ^ m) : ℝ) - x) * Real.log 2
      ≤ BakerWustholz.C 3 1 * Real.log 3
        * ((Nat.log 2 (3 ^ m) : ℝ) + 1 - y) * max (Real.log ((2 * m : ℕ) : ℝ)) 1 := by
  set N : ℕ := 3 ^ m with hNdef
  set M : ℕ := Nat.log 2 N with hMdef
  have hM2m : M ≤ 2 * m := by rw [hMdef, hNdef]; exact log_two_three_pow_le
  -- ## the integer decomposition N = A₁·2^y + A₂ at the zero run
  set A₁ : ℕ := N / 2 ^ y with hA₁def
  set A₂ : ℕ := N % 2 ^ y with hA₂def
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have htop : 2 ^ M ≤ N := Nat.pow_log_le_self 2 hNpos.ne'
  have hlt : N < 2 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hsplit : A₁ * 2 ^ y + A₂ = N := by
    rw [hA₁def, hA₂def, mul_comm]
    exact Nat.div_add_mod N (2 ^ y)
  have hmodx : A₂ = N % 2 ^ x := by
    rw [hA₂def, hNdef]
    exact Nat.mod_two_pow_eq_of_testBit_eq_false hxy.le hgap
  have hA₂lt : A₂ < 2 ^ x := by
    rw [hmodx]
    exact Nat.mod_lt _ (by positivity)
  have hA₂odd : A₂ % 2 = 1 := by
    rw [hmodx, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : x ≠ 0)), hNdef]
    exact three_pow_mod_two m
  have hA₂pos : 1 ≤ A₂ := by omega
  have hA₁2y : 2 ^ M ≤ A₁ * 2 ^ y := by
    have h1 : 2 ^ (M - y) ≤ A₁ := by
      rw [hA₁def, ← Nat.pow_div hyM (by norm_num)]
      exact Nat.div_le_div_right htop
    calc 2 ^ M = 2 ^ (M - y) * 2 ^ y := by rw [← pow_add, Nat.sub_add_cancel hyM]
      _ ≤ A₁ * 2 ^ y := Nat.mul_le_mul h1 le_rfl
  have hA₁pos : 1 ≤ A₁ := by
    rw [hA₁def, Nat.one_le_div_iff (by positivity)]
    calc 2 ^ y ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hyM
      _ ≤ N := htop
  have hA₁ub : A₁ < 2 ^ (M + 1 - y) := by
    have h1 : A₁ * 2 ^ y < 2 ^ (M + 1 - y) * 2 ^ y := by
      calc A₁ * 2 ^ y ≤ N := by omega
        _ < 2 ^ (M + 1) := hlt
        _ = 2 ^ (M + 1 - y) * 2 ^ y := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
  -- ## real versions
  have hA₁R : (1 : ℝ) ≤ (A₁ : ℝ) := by exact_mod_cast hA₁pos
  have hA₂R : (1 : ℝ) ≤ (A₂ : ℝ) := by exact_mod_cast hA₂pos
  have hden : (0 : ℝ) < (A₁ : ℝ) * 2 ^ y := by positivity
  have hsplitR : (A₁ : ℝ) * 2 ^ y + (A₂ : ℝ) = (3 : ℝ) ^ m := by
    have h := hsplit
    rw [hNdef] at h
    exact_mod_cast h
  have hA₁2yR : (2 : ℝ) ^ M ≤ (A₁ : ℝ) * 2 ^ y := by exact_mod_cast hA₁2y
  have hA₂ltR : (A₂ : ℝ) ≤ (2 : ℝ) ^ x := by exact_mod_cast hA₂lt.le
  -- ## the linear form Λ and its elementary bounds
  set Λ : ℝ := (m : ℝ) * Real.log 3 - (y : ℝ) * Real.log 2 - Real.log (A₁ : ℝ)
    with hΛdef
  have hratio : Λ = Real.log ((3 : ℝ) ^ m / ((A₁ : ℝ) * 2 ^ y)) := by
    rw [Real.log_div (by positivity) hden.ne',
      Real.log_mul (by linarith : ((A₁ : ℕ) : ℝ) ≠ 0) (by positivity),
      Real.log_pow, Real.log_pow, hΛdef]
    ring
  have hgt : (A₁ : ℝ) * 2 ^ y < (3 : ℝ) ^ m := by linarith
  have hΛpos : 0 < Λ := by
    rw [hratio]
    apply Real.log_pos
    rw [lt_div_iff₀ hden]
    linarith
  have hΛub : Λ ≤ (2 : ℝ) ^ x / 2 ^ M := by
    have h1 : Λ ≤ (3 : ℝ) ^ m / ((A₁ : ℝ) * 2 ^ y) - 1 := by
      rw [hratio]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have h2 : (3 : ℝ) ^ m / ((A₁ : ℝ) * 2 ^ y) - 1 = (A₂ : ℝ) / ((A₁ : ℝ) * 2 ^ y) := by
      field_simp
      linarith
    have h3 : (A₂ : ℝ) / ((A₁ : ℝ) * 2 ^ y) ≤ (2 : ℝ) ^ x / 2 ^ M := by
      apply div_le_div₀ (by positivity) hA₂ltR (by positivity) hA₁2yR
    linarith
  have hlogΛub : Real.log Λ ≤ (x : ℝ) * Real.log 2 - (M : ℝ) * Real.log 2 := by
    calc Real.log Λ ≤ Real.log ((2 : ℝ) ^ x / 2 ^ M) := Real.log_le_log hΛpos hΛub
      _ = (x : ℝ) * Real.log 2 - (M : ℝ) * Real.log 2 := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  -- ## the Baker–Wüstholz lower bound
  set α : Fin 3 → ℚ := ![3, 2, (((A₁ : ℕ) : ℤ) : ℚ)] with hαdef
  set b : Fin 3 → ℤ := ![(m : ℤ), -(y : ℤ), -1] with hbdef
  have e0 : α 0 = 3 := rfl
  have e1 : α 1 = 2 := rfl
  have e2 : α 2 = (((A₁ : ℕ) : ℤ) : ℚ) := rfl
  have f0 : b 0 = (m : ℤ) := rfl
  have f1 : b 1 = -(y : ℤ) := rfl
  have f2 : b 2 = -1 := rfl
  have hA₁Z : (1 : ℤ) ≤ ((A₁ : ℕ) : ℤ) := by exact_mod_cast hA₁pos
  have hα : ∀ i, α i ≠ 0 := by
    intro i
    fin_cases i
    · exact (by norm_num : (3 : ℚ) ≠ 0)
    · exact (by norm_num : (2 : ℚ) ≠ 0)
    · exact Int.cast_ne_zero.mpr (by omega)
  have hbB : ∀ i, (b i).natAbs ≤ 2 * m := by
    intro i
    fin_cases i
    · show ((m : ℕ) : ℤ).natAbs ≤ 2 * m
      rw [Int.natAbs_natCast]
      omega
    · show (-((y : ℕ) : ℤ)).natAbs ≤ 2 * m
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      omega
    · show ((-1 : ℤ)).natAbs ≤ 2 * m
      simp only [Int.natAbs_neg, Int.natAbs_one]
      omega
  have hlog3 : Complex.log (((3 : ℚ) : ℂ)) = ((Real.log 3 : ℝ) : ℂ) := by
    rw [show ((3 : ℚ) : ℂ) = (((3 : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_log (by norm_num)]
  have hlog2 : Complex.log (((2 : ℚ) : ℂ)) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show ((2 : ℚ) : ℂ) = (((2 : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_log (by norm_num)]
  have hlogA : Complex.log (((((A₁ : ℕ) : ℤ) : ℚ)) : ℂ)
      = ((Real.log ((A₁ : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [show (((((A₁ : ℕ) : ℤ) : ℚ)) : ℂ) = ((((A₁ : ℕ) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  have hsum : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) = ((Λ : ℝ) : ℂ) := by
    rw [Fin.sum_univ_three, e0, e1, e2, f0, f1, f2, eq_ratCast, eq_ratCast, eq_ratCast,
      hlog3, hlog2, hlogA, hΛdef]
    push_cast
    ring
  have hΛneC : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) ≠ 0 := by
    rw [hsum]
    exact Complex.ofReal_ne_zero.mpr hΛpos.ne'
  have hBW := BakerWustholz.linearForms_logs (n := 3) (by norm_num)
    (Rat.castHom ℂ) α hα b (B := 2 * m) (by omega) hbB hΛneC
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, Real.log_abs, Module.finrank_self,
    Nat.cast_one] at hBW
  rw [show (1 : ℝ) / (1 : ℝ) = 1 by norm_num] at hBW
  -- ## the height product
  have hmhA : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (((A₁ : ℕ) : ℤ) : ℚ)
      ≤ (M : ℝ) + 1 - y := by
    refine le_trans (mh_intCast hA₁Z) ?_
    have hMy1 : (1 : ℝ) ≤ (M : ℝ) + 1 - y := by
      have hyR : (y : ℝ) ≤ (M : ℝ) := by exact_mod_cast hyM
      linarith
    have hlogA₁ : Real.log (((A₁ : ℕ) : ℤ) : ℝ) ≤ (M : ℝ) + 1 - y := by
      have hcast : (((A₁ : ℕ) : ℤ) : ℝ) = ((A₁ : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      have hub : ((A₁ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (M + 1 - y) := by exact_mod_cast hA₁ub.le
      have hMy : ((M + 1 - y : ℕ) : ℝ) = (M : ℝ) + 1 - y := by
        rw [Nat.cast_sub (by omega : y ≤ M + 1)]
        push_cast
        ring
      calc Real.log ((A₁ : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (M + 1 - y)) :=
            Real.log_le_log (by linarith) hub
        _ = ((M + 1 - y : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ ((M + 1 - y : ℕ) : ℝ) * 1 := by
            have h0 : (0 : ℝ) ≤ ((M + 1 - y : ℕ) : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_left log_two_le_one h0
        _ = (M : ℝ) + 1 - y := by rw [mul_one, hMy]
    exact max_le hlogA₁ hMy1
  have hmhnn : ∀ q : ℚ, 0 ≤ BakerWustholz.modifiedHeight (Rat.castHom ℂ) q := by
    intro q
    rw [modifiedHeight_rat]
    positivity
  have hprod : (∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (α i))
      ≤ Real.log 3 * 1 * ((M : ℝ) + 1 - y) := by
    rw [Fin.prod_univ_three, e0, e1, e2]
    have m01 : BakerWustholz.modifiedHeight (Rat.castHom ℂ) 3
        * BakerWustholz.modifiedHeight (Rat.castHom ℂ) 2 ≤ Real.log 3 * 1 :=
      mul_le_mul mh_three mh_two (hmhnn _) log_three_pos'.le
    exact mul_le_mul m01 hmhA (hmhnn _) (mul_nonneg log_three_pos'.le zero_le_one)
  -- ## combine
  have hCmax : 0 ≤ BakerWustholz.C 3 1 * max (Real.log ((2 * m : ℕ) : ℝ)) 1 :=
    mul_nonneg (C_one_nonneg 3) (le_trans zero_le_one (le_max_right _ _))
  have hlower : -(BakerWustholz.C 3 1 * max (Real.log ((2 * m : ℕ) : ℝ)) 1
      * (Real.log 3 * 1 * ((M : ℝ) + 1 - y))) ≤ Real.log Λ := by
    refine le_trans (neg_le_neg ?_) hBW
    exact mul_le_mul_of_nonneg_left hprod hCmax
  have hexpand : ((M : ℝ) - x) * Real.log 2
      = (M : ℝ) * Real.log 2 - (x : ℝ) * Real.log 2 := by ring
  have harr : BakerWustholz.C 3 1 * max (Real.log ((2 * m : ℕ) : ℝ)) 1
      * (Real.log 3 * 1 * ((M : ℝ) + 1 - y))
      = BakerWustholz.C 3 1 * Real.log 3 * ((M : ℝ) + 1 - y)
        * max (Real.log ((2 * m : ℕ) : ℝ)) 1 := by ring
  rw [harr] at hlower
  rw [hexpand]
  linarith

/-! ## The window pigeonhole -/

/-- No depth window `(θ^j, θ^{j+1}]` below the top bit of `3^m` is all zeros,
once `θ` exceeds the gap-principle threshold: the window
`[M − θ^{j+1}, M − θ^j)` of bit positions contains a set bit.  (Exposed for the
digit-block program `TH/DigitBlocks/*`, where it is the "no all-zeros window"
half of the transition lemma B1.) -/
lemma window_hit {m θ : ℕ} (hm : 1 ≤ m) (hθ2 : 2 ≤ θ)
    (hθbig : 2 * (BakerWustholz.C 3 1 * Real.log 3 * max (Real.log ((2 * m : ℕ) : ℝ)) 1)
      < (θ : ℝ) * Real.log 2)
    {j : ℕ} (hj : θ ^ (j + 1) ≤ Nat.log 2 (3 ^ m)) :
    ∃ i, Nat.log 2 (3 ^ m) - θ ^ (j + 1) ≤ i ∧ i < Nat.log 2 (3 ^ m) - θ ^ j
      ∧ (3 ^ m).testBit i = true := by
  set M : ℕ := Nat.log 2 (3 ^ m) with hMdef
  have hpowlt : θ ^ j < θ ^ (j + 1) := by
    have h1 : θ ^ (j + 1) = θ ^ j * θ := pow_succ θ j
    have h2 : 1 ≤ θ ^ j := Nat.one_le_pow _ _ (by omega)
    nlinarith
  by_contra hc
  push Not at hc
  simp only [Bool.not_eq_true] at hc
  -- `hc : ∀ i, M − θ^(j+1) ≤ i → i < M − θ^j → (3^m).testBit i = false`
  rcases Nat.eq_zero_or_pos (M - θ ^ (j + 1)) with hx0 | hxpos
  · -- the window reaches bit 0, which is set (`3^m` is odd)
    have h0 : (3 ^ m).testBit 0 = false := hc 0 (by omega) (by omega)
    have h1 : (3 ^ m).testBit 0 = true := by
      simp [Nat.testBit_zero, three_pow_mod_two m]
    rw [h0] at h1
    exact Bool.false_ne_true h1
  · -- interior window: contradict the gap principle
    have hxy : M - θ ^ (j + 1) < M - θ ^ j := by omega
    have hgb := gap_bound hm hxpos hxy (Nat.sub_le _ _) hc
    rw [← hMdef] at hgb
    have hjM : θ ^ j ≤ M := by omega
    have hXcast : ((M : ℝ) - ((M - θ ^ (j + 1) : ℕ) : ℝ)) = ((θ : ℕ) : ℝ) ^ (j + 1) := by
      rw [Nat.cast_sub hj]
      push_cast
      ring
    have hYcast : ((M : ℝ) + 1 - ((M - θ ^ j : ℕ) : ℝ)) = ((θ : ℕ) : ℝ) ^ j + 1 := by
      rw [Nat.cast_sub hjM]
      push_cast
      ring
    rw [hXcast, hYcast] at hgb
    -- divide by θ^j
    have hθj1 : (1 : ℝ) ≤ ((θ : ℕ) : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ θ))
    have hCnn : (0 : ℝ) ≤ BakerWustholz.C 3 1 * Real.log 3
        * max (Real.log ((2 * m : ℕ) : ℝ)) 1 :=
      mul_nonneg (mul_nonneg (C_one_nonneg 3) log_three_pos'.le)
        (le_trans zero_le_one (le_max_right _ _))
    have hkey : ((θ : ℕ) : ℝ) * Real.log 2 * ((θ : ℕ) : ℝ) ^ j
        ≤ (2 * (BakerWustholz.C 3 1 * Real.log 3 * max (Real.log ((2 * m : ℕ) : ℝ)) 1))
          * ((θ : ℕ) : ℝ) ^ j := by
      have hlhs : ((θ : ℕ) : ℝ) * Real.log 2 * ((θ : ℕ) : ℝ) ^ j
          = ((θ : ℕ) : ℝ) ^ (j + 1) * Real.log 2 := by ring
      rw [hlhs]
      nlinarith [hgb, hθj1, hCnn]
    have hθpos : (0 : ℝ) < ((θ : ℕ) : ℝ) ^ j := by positivity
    have hfin := le_of_mul_le_mul_right hkey hθpos
    linarith

/-- The interval pigeonhole ([Ste80] (21)–(22) analogue): with `θ` above the
gap-principle threshold, the `k = ⌊log_θ M⌋` windows are disjoint and each
contains a set bit, so `⌊log_θ ⌊log₂ 3^m⌋⌋ ≤ s₂(3^m)`. -/
private lemma log_le_sum_digits {m θ : ℕ} (hm : 1 ≤ m) (hθ2 : 2 ≤ θ)
    (hθbig : 2 * (BakerWustholz.C 3 1 * Real.log 3 * max (Real.log ((2 * m : ℕ) : ℝ)) 1)
      < (θ : ℝ) * Real.log 2) :
    Nat.log θ (Nat.log 2 (3 ^ m)) ≤ (Nat.digits 2 (3 ^ m)).sum := by
  set M : ℕ := Nat.log 2 (3 ^ m) with hMdef
  set k : ℕ := Nat.log θ M with hkdef
  have hMpos : 1 ≤ M := le_trans hm (by rw [hMdef]; exact le_log_two_three_pow)
  -- each window `[M − θ^(j+1), M − θ^j)` contains a set bit
  have hwin : ∀ j : ℕ, ∃ i : ℕ, j < k →
      (M - θ ^ (j + 1) ≤ i ∧ i < M - θ ^ j ∧ (3 ^ m).testBit i = true) := by
    intro j
    by_cases hj : j < k
    · have hpow : θ ^ (j + 1) ≤ M := by
        calc θ ^ (j + 1) ≤ θ ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ M := by
              rw [hkdef]
              exact Nat.pow_log_le_self θ (by omega)
      obtain ⟨i, h1, h2, h3⟩ := window_hit hm hθ2 hθbig (by rw [← hMdef]; exact hpow)
      rw [← hMdef] at h1 h2
      exact ⟨i, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose f hf using hwin
  -- the chosen bits are distinct members of the set-bit positions
  have hfmem : ∀ j ∈ Finset.range k, f j ∈ (Finset.range (M + 1)).filter
      (fun i => (3 ^ m).testBit i) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hf j (Finset.mem_range.mp hj)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h3⟩
  have hmono : ∀ a b : ℕ, a < b → b < k → f b < f a := by
    intro a b hab hbk
    obtain ⟨ha1, _, _⟩ := hf a (by omega)
    obtain ⟨_, hb2, _⟩ := hf b hbk
    have hpow : θ ^ (a + 1) ≤ θ ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hinj : Set.InjOn f (Finset.range k) := by
    intro a ha b hb heq
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · have := hmono a b h hb
      omega
    · exact h
    · have := hmono b a h ha
      omega
  have hcard : k ≤ ((Finset.range (M + 1)).filter (fun i => (3 ^ m).testBit i)).card := by
    calc k = (Finset.range k).card := (Finset.card_range k).symm
      _ ≤ _ := Finset.card_le_card_of_injOn f hfmem hinj
  -- ... and the digit sum counts the set bits
  have hlt2 : 3 ^ m < 2 ^ (M + 1) := by
    rw [hMdef]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hsum : (Nat.digits 2 (3 ^ m)).sum
      = ∑ i ∈ Finset.range (M + 1), ((3 ^ m).testBit i).toNat :=
    Nat.sum_digits_two_eq_sum_testBit hlt2
  have hPcard : ((Finset.range (M + 1)).filter (fun i => (3 ^ m).testBit i)).card
      = ∑ i ∈ Finset.range (M + 1), ((3 ^ m).testBit i).toNat := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases (3 ^ m).testBit i <;> simp
  omega

/-! ## Stewart's theorem -/

/-- **Stewart's theorem for `3^m`** ([Ste80], Theorem 2 with `u_n = 3^n`,
`a = 2`, `α = 0`; the M3½ rung of [W2] §5): the binary digit sum of `3^m`
satisfies

  `s₂(3^m) ≥ log m / (log log m + C) − 1`   for every `m ≥ 2`,

with `C > 0` a constant (effectively computable — the proof exhibits
`C = max (log ((4·C(3,1)·log 3 + 4)/log 2)) 1` with `C(3,1)` the
Baker–Wüstholz constant — though the statement quantifies it
existentially).  This is the only quantitative unconditional genre of
lower bound known for the bottom binary digits of `3^n`.
Footprint std3 + [BW93]. -/
@[category research solved, AMS 11, ref "Ste80", group "stewart_digits"]
theorem stewart_digitSum_three_pow :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      Real.log m / (Real.log (Real.log m) + C) - 1 ≤ ((Nat.digits 2 (3 ^ m)).sum : ℝ) := by
  have hCl3 : (0 : ℝ) ≤ BakerWustholz.C 3 1 * Real.log 3 :=
    mul_nonneg (C_one_nonneg 3) log_three_pos'.le
  set c₈ : ℝ := (4 * (BakerWustholz.C 3 1 * Real.log 3) + 4) / Real.log 2 with hc₈def
  have hc₈pos : 0 < c₈ := by
    rw [hc₈def]
    exact div_pos (by linarith) log_two_pos'
  refine ⟨max (Real.log c₈) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro m hm
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  -- ## the threshold and the window size θ
  set L : ℝ := max (Real.log ((2 * m : ℕ) : ℝ)) 1 with hLdef
  have hL1 : 1 ≤ L := le_max_right _ _
  have hCl3L : 0 ≤ BakerWustholz.C 3 1 * Real.log 3 * L :=
    mul_nonneg hCl3 (le_trans zero_le_one hL1)
  set T : ℝ := 2 * (BakerWustholz.C 3 1 * Real.log 3 * L) with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; linarith
  set θ : ℕ := ⌊T / Real.log 2⌋₊ + 2 with hθdef
  have hθ2 : 2 ≤ θ := by rw [hθdef]; omega
  have hθval : ((θ : ℕ) : ℝ) = ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) + 2 := by
    rw [hθdef]; push_cast; ring
  have hθbig : T < (θ : ℝ) * Real.log 2 := by
    have h1 : T / Real.log 2 < ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ log_two_pos'] at h1
    rw [hθval]
    nlinarith [log_two_pos']
  -- ## θ ≤ c₈·log m
  have hl2m : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2R
  have hlog2m : Real.log ((2 * m : ℕ) : ℝ) ≤ 2 * Real.log m := by
    have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [hcast, Real.log_mul (by norm_num) (by linarith)]
    linarith
  have hL2 : L ≤ 2 * Real.log m := by
    rw [hLdef]
    refine max_le hlog2m ?_
    nlinarith [Real.log_two_gt_d9]
  have hT4 : T ≤ 4 * (BakerWustholz.C 3 1 * Real.log 3) * Real.log m := by
    rw [hTdef]
    nlinarith [hCl3, hL2, hL1]
  have hθle : (θ : ℝ) ≤ c₈ * Real.log m := by
    have hfloor : ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) ≤ T / Real.log 2 :=
      Nat.floor_le (by positivity)
    have hmul : T + 2 * Real.log 2
        ≤ (4 * (BakerWustholz.C 3 1 * Real.log 3) + 4) * Real.log m := by
      linarith
    have hgoal : T / Real.log 2 + 2 ≤ c₈ * Real.log m := by
      rw [hc₈def, div_mul_eq_mul_div, le_div_iff₀ log_two_pos', add_mul,
        div_mul_cancel₀ _ log_two_pos'.ne']
      exact hmul
    rw [hθval]
    linarith
  -- ## the pigeonhole gives `⌊log_θ M⌋ ≤ s₂(3^m)`
  have hθbig' : 2 * (BakerWustholz.C 3 1 * Real.log 3
      * max (Real.log ((2 * m : ℕ) : ℝ)) 1) < (θ : ℝ) * Real.log 2 := by
    rw [hTdef, hLdef] at hθbig
    exact hθbig
  have hk : Nat.log θ (Nat.log 2 (3 ^ m)) ≤ (Nat.digits 2 (3 ^ m)).sum :=
    log_le_sum_digits (by omega) hθ2 hθbig'
  -- ## `log m ≤ (k+1)·log θ` and `log θ ≤ log log m + C`
  have hlogθ_pos : 0 < Real.log θ := Real.log_pos (by exact_mod_cast (by omega : 1 < θ))
  have hmM : (m : ℝ) ≤ (Nat.log 2 (3 ^ m) : ℝ) := by
    exact_mod_cast le_log_two_three_pow (m := m)
  have hMk : (Nat.log 2 (3 ^ m) : ℝ)
      < ((θ : ℕ) : ℝ) ^ (Nat.log θ (Nat.log 2 (3 ^ m)) + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by omega : 1 < θ) (Nat.log 2 (3 ^ m))
  have hlogm_le : Real.log m
      ≤ ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1) * Real.log θ := by
    calc Real.log m ≤ Real.log (Nat.log 2 (3 ^ m) : ℝ) :=
          Real.log_le_log (by linarith) hmM
      _ ≤ Real.log (((θ : ℕ) : ℝ) ^ (Nat.log θ (Nat.log 2 (3 ^ m)) + 1)) :=
          Real.log_le_log (by linarith) hMk.le
      _ = ((Nat.log θ (Nat.log 2 (3 ^ m)) + 1 : ℕ) : ℝ) * Real.log θ := by
          rw [Real.log_pow]
      _ = ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1) * Real.log θ := by
          push_cast
          ring
  have hlogθ_le : Real.log θ ≤ Real.log (Real.log m) + max (Real.log c₈) 1 := by
    have h1 : Real.log ((θ : ℕ) : ℝ) ≤ Real.log (c₈ * Real.log m) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < θ)) hθle
    rw [Real.log_mul hc₈pos.ne' hlogm_pos.ne'] at h1
    have h2 : Real.log c₈ ≤ max (Real.log c₈) 1 := le_max_left _ _
    linarith
  -- ## the denominator is positive: `log log m ≥ log log 2 > −1`
  have hinv_le : (Real.log 2)⁻¹ ≤ 1.45 := by
    have hcancel : Real.log 2 * (Real.log 2)⁻¹ = 1 := mul_inv_cancel₀ log_two_pos'.ne'
    nlinarith [Real.log_two_gt_d9, inv_nonneg.mpr log_two_pos'.le]
  have hloglog2 : (-1 : ℝ) < Real.log (Real.log 2) := by
    have h1 : Real.log (Real.log 2)⁻¹ ≤ (Real.log 2)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr log_two_pos')
    rw [Real.log_inv] at h1
    linarith
  have hloglogm : Real.log (Real.log 2) ≤ Real.log (Real.log m) :=
    Real.log_le_log log_two_pos' hl2m
  have hden_pos : 0 < Real.log (Real.log m) + max (Real.log c₈) 1 := by
    have h1 : (1 : ℝ) ≤ max (Real.log c₈) 1 := le_max_right _ _
    linarith
  -- ## combine
  have hk1nn : (0 : ℝ) ≤ (Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1 := by positivity
  have hstep : Real.log m ≤ ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1)
      * (Real.log (Real.log m) + max (Real.log c₈) 1) :=
    le_trans hlogm_le (mul_le_mul_of_nonneg_left hlogθ_le hk1nn)
  have hfrac : Real.log m / (Real.log (Real.log m) + max (Real.log c₈) 1)
      ≤ (Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1 := by
    rw [div_le_iff₀ hden_pos]
    exact hstep
  have hkR : ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℕ) : ℝ)
      ≤ ((Nat.digits 2 (3 ^ m)).sum : ℝ) := by exact_mod_cast hk
  linarith

/-- **Corollary**: the binary digit sum of `3^m` tends to infinity
(effectively, via `stewart_digitSum_three_pow`) — no power of 3 eventually
has sparse binary digits.  Footprint std3 + [BW93]. -/
@[category research solved, AMS 11, ref "Ste80", group "stewart_digits"]
theorem digitSum_three_pow_tendsto_atTop :
    Filter.Tendsto (fun m : ℕ => (Nat.digits 2 (3 ^ m)).sum)
      Filter.atTop Filter.atTop := by
  obtain ⟨C, hC, hbound⟩ := stewart_digitSum_three_pow
  rw [Filter.tendsto_atTop_atTop]
  intro bd
  refine ⟨max 2 (⌈Real.exp (((bd + 1 : ℝ) * (2 + C)) ^ 2)⌉₊ + 1), fun m hm => ?_⟩
  set t : ℝ := ((bd + 1 : ℝ) * (2 + C)) ^ 2 with htdef
  have hm2 : 2 ≤ m := le_trans (le_max_left _ _) hm
  have hfm := hbound m hm2
  have hmt : Real.exp t ≤ (m : ℝ) := by
    have h1 : ⌈Real.exp t⌉₊ + 1 ≤ m := le_trans (le_max_right _ _) hm
    calc Real.exp t ≤ (⌈Real.exp t⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (m : ℝ) := by exact_mod_cast Nat.le_of_succ_le h1
  have hbd1 : (1 : ℝ) ≤ (bd : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (bd : ℝ) := Nat.cast_nonneg bd
    linarith
  have h2C : (2 : ℝ) ≤ 2 + C := by linarith
  have hP2 : (2 : ℝ) ≤ (bd + 1 : ℝ) * (2 + C) := by nlinarith [Nat.cast_nonneg (α := ℝ) bd]
  have ht4 : (4 : ℝ) ≤ t := by
    rw [htdef]
    nlinarith [hP2, sq_nonneg ((bd + 1 : ℝ) * (2 + C) - 2)]
  have htL : t ≤ Real.log m := by
    rw [← Real.log_exp t]
    exact Real.log_le_log (Real.exp_pos t) hmt
  set L : ℝ := Real.log m with hLdef
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLnn : (0 : ℝ) ≤ L := by linarith
  -- `log L ≤ 2√L`, so the denominator is at most `(2 + C)·√L`
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hsqrt1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hL1
  have hloglog : Real.log L ≤ 2 * Real.sqrt L := by
    have h1 : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    have h2 : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hLnn
    linarith
  have hmulself : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLnn
  have hsqrt_t : (bd + 1 : ℝ) * (2 + C) ≤ Real.sqrt L := by
    have h1 : Real.sqrt t = (bd + 1 : ℝ) * (2 + C) := by
      rw [htdef]
      exact Real.sqrt_sq (by linarith)
    rw [← h1]
    exact Real.sqrt_le_sqrt htL
  have hdenpos : 0 < Real.log L + C := by
    have h0 : 0 ≤ Real.log L := Real.log_nonneg hL1
    linarith
  -- the lower bound beats `bd + 1`
  have hratio : (bd : ℝ) + 1 ≤ L / (Real.log L + C) := by
    rw [le_div_iff₀ hdenpos]
    have hden2 : Real.log L + C ≤ (2 + C) * Real.sqrt L := by
      have h1 : C ≤ C * Real.sqrt L := le_mul_of_one_le_right hC.le hsqrt1
      nlinarith
    calc ((bd : ℝ) + 1) * (Real.log L + C)
        ≤ ((bd : ℝ) + 1) * ((2 + C) * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hden2 (by linarith)
      _ = ((bd : ℝ) + 1) * (2 + C) * Real.sqrt L := by ring
      _ ≤ Real.sqrt L * Real.sqrt L :=
          mul_le_mul_of_nonneg_right hsqrt_t (Real.sqrt_nonneg L)
      _ = L := hmulself
  have hfinal : (bd : ℝ) ≤ ((Nat.digits 2 (3 ^ m)).sum : ℝ) := by linarith
  exact_mod_cast hfinal

/-- Sanity: `3^5 = 243 = 11110011₂` has binary digit sum `6`. -/
@[category test, AMS 11, ref "Ste80", group "stewart_digits"]
lemma digitSum_three_pow_five : (Nat.digits 2 (3 ^ 5)).sum = 6 := by decide

/-! ## The Bugeaud–Kaneko sharpening (Stewart and beyond)

`CITED/BugeaudKaneko.lean` transcribes Bugeaud–Kaneko Corollary 1.5, whose `3^m` /
base-`2` instance sharpens the constant of `stewart_digitSum_three_pow` from `1/2` to
`1 − ε`.  Re-exposing it in the `TH` namespace both surfaces the sharper bound for the
digit-block program ([A4+], where it is the effective form of rung B5) and wires the
cited axiom `BK.nonzeroDigits_sUnit_lower` into the corpus via this file's import graph. -/

/-- **The Bugeaud–Kaneko sharpening of Stewart** for `3^m` ([BK17] Cor. 1.5, via
`BK.digitSum_three_pow_base_two_lower`): for every `ε > 0`, beyond an effective threshold
in `m`,

  `(1 − ε) · (log log 3^m) / (log log log 3^m) < s₂(3^m)`.

Since `log 3^m = m · log 3`, the left side is asymptotically `(1 − ε)·log m / log log m`,
improving the `1/2` constant implicit in `stewart_digitSum_three_pow`.  Rests on the cited
axiom `BK.nonzeroDigits_sUnit_lower`; footprint std3 + [BK17]. -/
@[category research solved, AMS 11, ref "BK17", group "stewart_digits"]
theorem stewart_digitSum_three_pow_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m →
      (1 - ε) * (Real.log (Real.log ((3 ^ m : ℕ) : ℝ))
          / Real.log (Real.log (Real.log ((3 ^ m : ℕ) : ℝ))))
        < ((Nat.digits 2 (3 ^ m)).sum : ℝ) :=
  BK.digitSum_three_pow_base_two_lower ε hε

end TH
