/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.RepetitionIdentity
import TH.BakerInterface
import Mathlib.Data.Nat.Prime.Basic

/-!
# Stage 2a: the extremal sliver, effectively, from Baker–Wüstholz (Theorem E1)

Milestone M-4 of the M4/A3 program ([M4A3] §6.1): near the elementary ceiling
`k ≈ 0.585·c` the integer multiplier `u := (m_c − m_a)/2^k` of a repetition
`(a, c, k)` is sub-exponential, and Lemma R turns the repetition into a small
linear form in **four** logarithms of rationals.  With `s := c − a`,
`λ'_s := (3^s − 2^s)/3^s` and `X := 3^c·λ'_s = 3^c − 3^a·2^s`, `Y := u·2^{c+k}`:

  `Λ := c·log 3 − (c+k)·log 2 − log u + log λ'_s = log X − log Y ≠ 0`,
  `|Λ| ≤ 6·(2/3)^{c+k}`   (since `X − Y = 2^c(ε_c − ε_a)`, an odd integer of
  modulus `≤ 2^c (2/3)^k`, while `X ≥ 3^{c-1}`),

and `BakerWustholz.linearForms_logs` bounds `log |Λ|` below.  The heights:
`h'(3) ≤ log 3`, `h'(2) ≤ 1`, `h'(u) ≤ max(log u, 1)` with
`log u ≤ c·log(3/2) − k·log 2` (the *slack* — small exactly in the sliver), and
`h'(λ'_s) ≤ s·log 3` (the gap-height).  Result:

* `repetition_extremal_bound` — **Theorem E1**: every repetition `(a, c, k)`
  with `2 ≤ a < c`, `2 ≤ k` satisfies
  `(c+k)·log(3/2) ≤ log 6 + C₄·max(log(c+k), 1)·s·(log 3)²·max(c·log(3/2) − k·log 2, 1)`
  with the fully explicit `C₄ := BakerWustholz.C 4 1`.  **Effective**: reading
  it backwards, no repetition can have both bounded slack and
  `s·log c ≲ c` — in particular, for *bounded* gaps `s ≤ S` the elementary
  ceiling is never approached within `c / O(log c)`, with computable constants.
* `extremal_sliver_bound` — the sliver form: if the slack is `≤ 1` (that is,
  `k ≥ c·log₂(3/2) − 1/log 2`, the extreme edge), then
  `(c+k)·log(3/2) ≤ log 6 + C₄·max(log(c+k), 1)·s·(log 3)²`.

**Honesty note** (deviation from the boxed E1 of [M4A3] §6.1): the plan's shape
"no repetition with `k ≥ 0.585c − κc/(s·log c)`" overshoots for gaps `s ≈ c` —
the modified height `h'(u) ≥ 1` contributes a `s·log c` term even at zero
slack, so the method needs `s·log c ≪ c` *as well*; the raw inequality above is
the honest effective content, and the plan's "in particular, for bounded gaps"
sentence is exactly what survives verbatim.  The large-`s` regime is the middle
band — Stage 2c territory, cf. `TH.CapstoneM4`.

First consumer of `CITED/BakerWustholz.lean` (the axiom starts extracting).
Axiom footprint: std3 + `BakerWustholz.linearForms_logs` ([BW93]).

## Contents

* `repetition_extremal_bound` — **Theorem E1**, the effective Baker–Wüstholz
  inequality for repetitions.
* `extremal_sliver_bound` — the extreme-sliver corollary (slack `≤ 1`).

## References

* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §6.1 (Stage 2a).
* [BW93] Baker, Wüstholz. *Logarithmic forms and group varieties.* J. reine
  angew. Math. **442** (1993), 19–62.  (Via `CITED/BakerWustholz.lean`.)
-/

namespace TH

/-! The numeric `log` facts (`one_le_log_three`, `log_two_le_one`,
`log_three_pos'`) and the constant-nonnegativity `C_one_nonneg` now live in
`TH/BakerInterface.lean` (§5.1 of `plan-A4+.html`). -/

/-! ## Elementary integer inequalities -/

private lemma six_mul_two_pow_le {n : ℕ} (hn : 5 ≤ n) : 6 * 2 ^ n ≤ 3 ^ n := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 5 + t := ⟨n - 5, by omega⟩
  have h : (2 : ℕ) ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by norm_num) t
  have e1 : 6 * 2 ^ (5 + t) = 192 * 2 ^ t := by
    rw [pow_add]
    ring
  have e2 : (3 : ℕ) ^ (5 + t) = 243 * 3 ^ t := by
    rw [pow_add]
    ring
  omega

private lemma two_pow_mod_three (s : ℕ) : 2 ^ s % 3 = 1 ∨ 2 ^ s % 3 = 2 := by
  induction s with
  | zero => left; rfl
  | succ t ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

/-- `3^s − 2^s` is coprime to `3^s` (`s ≥ 1`): the multiplier `λ'_s` is written
in lowest terms. -/
private lemma coprime_pow_sub (s : ℕ) (hs : 1 ≤ s) :
    Nat.Coprime (3 ^ s - 2 ^ s) (3 ^ s) := by
  have h23 : (2 : ℕ) ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by norm_num) s
  have h3 : ¬ (3 ∣ (3 ^ s - 2 ^ s)) := by
    intro hdvd
    have h33 : (3 : ℕ) ∣ 3 ^ s := dvd_pow_self 3 (by omega)
    have h32 : (3 : ℕ) ∣ 2 ^ s := by
      have h := Nat.dvd_sub h33 hdvd
      rwa [Nat.sub_sub_self h23] at h
    rcases two_pow_mod_three s with h | h <;> omega
  exact ((Nat.prime_three.coprime_iff_not_dvd.mpr h3).pow_left s).symm

/-! ## A log-Lipschitz bound -/

/-- If `Y` is within `X/2` of `X > 0`, then `|log X − log Y| ≤ 2|X − Y|/X`. -/
private lemma abs_log_sub_log_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h : |X - Y| ≤ X / 2) : |Real.log X - Real.log Y| ≤ 2 * |X - Y| / X := by
  have habs : 0 ≤ |X - Y| := abs_nonneg _
  have hY2 : X / 2 ≤ Y := by
    rcases abs_le.mp h with ⟨h1, h2⟩
    linarith
  have hdX : 0 ≤ |X - Y| / X := by positivity
  have hsplit : 2 * |X - Y| / X = 2 * (|X - Y| / X) := by ring
  rw [abs_le]
  constructor
  · -- `log Y − log X ≤ (Y−X)/X ≤ |X−Y|/X ≤ 2|X−Y|/X`
    have h1 : Real.log Y - Real.log X ≤ Y / X - 1 := by
      rw [← Real.log_div hY.ne' hX.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hY hX)
    have h2 : Y / X - 1 = (Y - X) / X := by
      field_simp
    have h3 : (Y - X) / X ≤ |X - Y| / X := by
      have habs' : Y - X ≤ |X - Y| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      gcongr
    linarith
  · -- `log X − log Y ≤ (X−Y)/Y ≤ |X−Y|/(X/2) = 2|X−Y|/X`
    have h1 : Real.log X - Real.log Y ≤ X / Y - 1 := by
      rw [← Real.log_div hX.ne' hY.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hX hY)
    have h2 : X / Y - 1 = (X - Y) / Y := by
      field_simp
    have h3 : (X - Y) / Y ≤ |X - Y| / Y := by
      have habs' : X - Y ≤ |X - Y| := le_abs_self _
      gcongr
    have h4 : |X - Y| / Y ≤ |X - Y| / (X / 2) := by
      gcongr
    have h5 : |X - Y| / (X / 2) = 2 * (|X - Y| / X) := by
      field_simp
    linarith

/-! ## The Baker–Wüstholz modified height over ℚ

`modifiedHeight_rat`, `norm_log_ratCast`, `mh_two`, `mh_three`, `mh_intCast`
now live in `TH/BakerInterface.lean` (§5.1 of `plan-A4+.html`); `mh_lambda`
below is the file-specific height of the moving multiplier `λ'_s`. -/

private lemma mh_lambda (s : ℕ) (hs : 1 ≤ s) :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ)
        (((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ))
      ≤ (s : ℝ) * Real.log 3 := by
  have h23 : (2 : ℕ) ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by norm_num) s
  have h23' : (2 : ℕ) ^ s < 3 ^ s := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hApos : 0 < 3 ^ s - 2 ^ s := by omega
  have h3spos : (0 : ℚ) < ((3 ^ s : ℕ) : ℚ) := by
    exact_mod_cast (by positivity : 0 < (3 : ℕ) ^ s)
  have hlampos : (0 : ℚ) < ((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ) :=
    div_pos (by exact_mod_cast hApos) h3spos
  have hslog : (1 : ℝ) ≤ (s : ℝ) * Real.log 3 := by
    have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    nlinarith [one_le_log_three]
  rw [modifiedHeight_rat, norm_log_ratCast hlampos]
  -- the Weil height: `h(λ'_s) = log 3^s = s·log 3`
  have h1 : Height.logHeight₁ (((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ))
      = (s : ℝ) * Real.log 3 := by
    rw [Rat.logHeight₁_div_natCast hApos (Nat.sub_le _ _) (coprime_pow_sub s hs),
      show (((3 ^ s : ℕ) : ℝ)) = (3 : ℝ) ^ s by push_cast; ring, Real.log_pow]
  -- the archimedean term: `|log λ'_s| = log (1/λ'_s) ≤ log 3 ≤ s·log 3`
  have h2 : |Real.log ((((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ) : ℚ) : ℝ)|
      ≤ (s : ℝ) * Real.log 3 := by
    set lamR : ℝ := ((((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ) : ℚ) : ℝ)
      with hlamR
    have hlamRpos : 0 < lamR := by
      rw [hlamR]
      exact_mod_cast hlampos
    have hlamRle : lamR ≤ 1 := by
      rw [hlamR]
      have : (((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ)) ≤ 1 := by
        rw [div_le_one h3spos]
        exact_mod_cast Nat.sub_le _ _
      exact_mod_cast this
    have hlamR3 : 1 / 3 ≤ lamR := by
      rw [hlamR]
      have key : 3 * (2 ^ s : ℕ) ≤ 2 * 3 ^ s := by
        obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
        have h : (2 : ℕ) ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by norm_num) t
        have e1 : 3 * 2 ^ (t + 1) = 6 * 2 ^ t := by rw [pow_add]; ring
        have e2 : 2 * 3 ^ (t + 1) = 6 * 3 ^ t := by rw [pow_add]; ring
        omega
      have hQ : (1 / 3 : ℚ) ≤ ((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ) := by
        rw [le_div_iff₀ h3spos]
        have hc : ((3 ^ s - 2 ^ s : ℕ) : ℚ)
            = ((3 ^ s : ℕ) : ℚ) - ((2 ^ s : ℕ) : ℚ) := by
          push_cast [Nat.cast_sub h23]
          ring
        have keyQ : 3 * ((2 ^ s : ℕ) : ℚ) ≤ 2 * ((3 ^ s : ℕ) : ℚ) := by
          exact_mod_cast key
        rw [hc]
        linarith
      have h := (Rat.cast_le (K := ℝ)).mpr hQ
      simpa using h
    have hlog0 : Real.log lamR ≤ 0 := Real.log_nonpos hlamRpos.le hlamRle
    rw [abs_of_nonpos hlog0, ← Real.log_inv]
    have hinv3 : lamR⁻¹ ≤ 3 := by
      rw [inv_le_comm₀ hlamRpos (by norm_num)]
      linarith
    calc Real.log lamR⁻¹ ≤ Real.log 3 :=
          Real.log_le_log (by positivity) hinv3
      _ ≤ (s : ℝ) * Real.log 3 := by
          have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
          nlinarith [log_three_pos']
  rw [h1]
  exact max_le le_rfl (max_le h2 hslog)

/-! ## Theorem E1 -/

set_option maxHeartbeats 800000 in
/-- **Theorem E1 (the extremal sliver, effective)** ([M4A3] §6.1): every
repetition `(a, c, k)` of the steering word with `2 ≤ a < c` and `2 ≤ k`
satisfies

  `(c+k)·log(3/2) ≤ log 6 + C₄ · max(log(c+k), 1) · (c−a) · (log 3)² ·
      max(c·log(3/2) − k·log 2, 1)`

with the fully explicit Baker–Wüstholz constant `C₄ = BakerWustholz.C 4 1`.
The last factor is the *slack* `≈ log u` of the integer multiplier
`u = (m_c − m_a)/2^k`; the inequality is effective and forbids, with computable
constants, any repetition whose slack and gap satisfy
`s · log(c+k) · max(slack, 1) ≲ c` — in particular bounded-gap repetitions
approaching the elementary ceiling `k ≈ 0.585·c` within `c/O(log c)`.
First consumer of the [BW93] axiom.  Footprint std3 + [BW93]. -/
@[category research solved, AMS 11, ref "BW93", group "three_halves_m4"]
theorem repetition_extremal_bound {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (hk : 2 ≤ k) (hrep : IsRepetition a c k) :
    ((c + k : ℕ) : ℝ) * Real.log (3 / 2)
      ≤ Real.log 6
        + BakerWustholz.C 4 1 * max (Real.log ((c + k : ℕ) : ℝ)) 1
          * ((c - a : ℕ) : ℝ) * Real.log 3 ^ 2
          * max ((c : ℝ) * Real.log (3 / 2) - (k : ℝ) * Real.log 2) 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, c = a + s := ⟨c - a, by omega⟩
  have hs1 : 1 ≤ s := by omega
  rw [Nat.add_sub_cancel_left]
  -- ## the integer multiplier u
  obtain ⟨u, hu⟩ := two_pow_dvd_of_repetition hrep
  have h2k : (0 : ℤ) < 2 ^ k := by positivity
  have hmlt : m a < m (a + s) := m_strictMono ha (by omega)
  have hu1 : 1 ≤ u := by
    by_contra hle
    have hu0 : u ≤ 0 := by omega
    have hnp := mul_nonpos_of_nonneg_of_nonpos h2k.le hu0
    linarith
  have huQ : ((m (a + s) : ℚ)) - ((m a : ℚ)) = 2 ^ k * (u : ℚ) := by
    exact_mod_cast hu
  -- ## the moving multiplier λ'_s
  have h23 : (2 : ℕ) ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by norm_num) s
  have h23' : (2 : ℕ) ^ s < 3 ^ s := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hApos : 0 < 3 ^ s - 2 ^ s := by omega
  set lam : ℚ := ((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ) with hlam
  have h3spos : (0 : ℚ) < ((3 ^ s : ℕ) : ℚ) := by
    exact_mod_cast (by positivity : 0 < (3 : ℕ) ^ s)
  have hlampos : 0 < lam := div_pos (by exact_mod_cast hApos) h3spos
  have hlam3 : 1 / 3 ≤ lam := by
    rw [hlam, le_div_iff₀ h3spos]
    have key : 3 * (2 ^ s : ℕ) ≤ 2 * 3 ^ s := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have h : (2 : ℕ) ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by norm_num) t
      have e1 : 3 * 2 ^ (t + 1) = 6 * 2 ^ t := by rw [pow_add]; ring
      have e2 : 2 * 3 ^ (t + 1) = 6 * 3 ^ t := by rw [pow_add]; ring
      omega
    have keyQ : 3 * ((2 ^ s : ℕ) : ℚ) ≤ 2 * ((3 ^ s : ℕ) : ℚ) := by
      exact_mod_cast key
    have hc : ((3 ^ s - 2 ^ s : ℕ) : ℚ)
        = ((3 ^ s : ℕ) : ℚ) - ((2 ^ s : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub h23]
      ring
    rw [hc]
    linarith
  -- ## X, Y and the Lemma-R contraction
  set N : ℕ := a + s + k with hN
  have hN5 : 5 ≤ N := by omega
  set Xq : ℚ := (3 : ℚ) ^ (a + s) - (3 : ℚ) ^ a * 2 ^ s with hXqdef
  set Yq : ℚ := (u : ℚ) * 2 ^ N with hYq
  have hXlam : Xq = (3 : ℚ) ^ (a + s) * lam := by
    rw [hXqdef, hlam]
    have h3ne : ((3 ^ s : ℕ) : ℚ) ≠ 0 := h3spos.ne'
    field_simp
    push_cast [Nat.cast_sub h23]
    ring
  have hXqpos : 0 < Xq := by
    rw [hXlam]
    exact mul_pos (by positivity) hlampos
  have hYqpos : 0 < Yq := by
    rw [hYq]
    exact mul_pos (by exact_mod_cast (by omega : (0 : ℤ) < u)) (by positivity)
  -- the ε-identity: `X − Y = 2^{a+s}(ε_{a+s} − ε_a)`
  have r1 : ((R (a + s) : ℤ) : ℚ) = 3 ^ (a + s) - 2 ^ (a + s) * (m (a + s) : ℚ) := by
    unfold R
    push_cast
    ring
  have r2 : ((R a : ℤ) : ℚ) = 3 ^ a - 2 ^ a * (m a : ℚ) := by
    unfold R
    push_cast
    ring
  have hsplit : (2 : ℚ) ^ (a + s) * eps a = 2 ^ s * ((R a : ℤ) : ℚ) := by
    rw [pow_add, mul_comm ((2 : ℚ) ^ a) ((2 : ℚ) ^ s), mul_assoc, two_pow_mul_eps]
  have hXY : Xq - Yq = 2 ^ (a + s) * (eps (a + s) - eps a) := by
    rw [mul_sub, two_pow_mul_eps, hsplit, hXqdef, hYq, hN, r1, r2]
    linear_combination (2 : ℚ) ^ (a + s) * huQ
  have hXYbound : |Xq - Yq| ≤ 2 ^ (a + s) * (2 / 3 : ℚ) ^ k := by
    rw [hXY, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (2 : ℚ) ^ (a + s))]
    exact mul_le_mul_of_nonneg_left (abs_eps_sub_le_of_repetition hrep)
      (by positivity)
  have hXYone : 1 ≤ |Xq - Yq| := by
    rw [hXY, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (2 : ℚ) ^ (a + s))]
    exact one_le_two_pow_mul_abs_eps_sub (by omega) (by omega)
  have hX3 : (3 : ℚ) ^ (a + s) ≤ 3 * Xq := by
    rw [hXlam]
    nlinarith [hlam3, pow_pos (show (0 : ℚ) < 3 by norm_num) (a + s)]
  have hhalf : |Xq - Yq| ≤ Xq / 2 := by
    have h6 : 6 * 2 ^ N ≤ 3 ^ N := six_mul_two_pow_le hN5
    have h6Q : (6 : ℚ) * 2 ^ N ≤ 3 ^ N := by exact_mod_cast h6
    have e2N : (2 : ℚ) ^ N = 2 ^ (a + s) * 2 ^ k := by rw [hN, pow_add]
    have e3N : (3 : ℚ) ^ N = 3 ^ (a + s) * 3 ^ k := by rw [hN, pow_add]
    rw [e2N, e3N] at h6Q
    have hstep : (2 : ℚ) ^ (a + s) * (2 / 3) ^ k ≤ (3 : ℚ) ^ (a + s) / 6 := by
      rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [h6Q]
    linarith [hXYbound, hstep, hX3]
  -- ## the linear form Λ, over ℝ
  have hXRpos : (0 : ℝ) < ((Xq : ℚ) : ℝ) := by exact_mod_cast hXqpos
  have hYRpos : (0 : ℝ) < ((Yq : ℚ) : ℝ) := by exact_mod_cast hYqpos
  have hlamRpos : (0 : ℝ) < ((lam : ℚ) : ℝ) := by exact_mod_cast hlampos
  have huRpos : (0 : ℝ) < ((u : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < u)
  set Λ : ℝ := ((a + s : ℕ) : ℝ) * Real.log 3 - ((N : ℕ) : ℝ) * Real.log 2
      - Real.log ((u : ℤ) : ℝ) + Real.log ((lam : ℚ) : ℝ) with hΛdef
  have hlogX : Real.log ((Xq : ℚ) : ℝ)
      = ((a + s : ℕ) : ℝ) * Real.log 3 + Real.log ((lam : ℚ) : ℝ) := by
    have hcast : ((Xq : ℚ) : ℝ) = (3 : ℝ) ^ (a + s) * ((lam : ℚ) : ℝ) := by
      rw [hXlam]
      push_cast
      ring
    rw [hcast, Real.log_mul (by positivity) hlamRpos.ne', Real.log_pow]
  have hlogY : Real.log ((Yq : ℚ) : ℝ)
      = Real.log ((u : ℤ) : ℝ) + ((N : ℕ) : ℝ) * Real.log 2 := by
    have hcast : ((Yq : ℚ) : ℝ) = ((u : ℤ) : ℝ) * (2 : ℝ) ^ N := by
      rw [hYq]
      push_cast
      ring
    rw [hcast, Real.log_mul huRpos.ne' (by positivity), Real.log_pow]
  have hΛeq : Λ = Real.log ((Xq : ℚ) : ℝ) - Real.log ((Yq : ℚ) : ℝ) := by
    rw [hΛdef, hlogX, hlogY]
    ring
  have hΛne : Λ ≠ 0 := by
    rw [hΛeq]
    intro h0
    have hXYeq : ((Xq : ℚ) : ℝ) = ((Yq : ℚ) : ℝ) := by
      have hexp := congrArg Real.exp (sub_eq_zero.mp h0)
      rwa [Real.exp_log hXRpos, Real.exp_log hYRpos] at hexp
    have : Xq = Yq := by exact_mod_cast hXYeq
    rw [this] at hXYone
    norm_num at hXYone
  -- upper bound |Λ| ≤ 6·(2/3)^N
  have hhalfR : |((Xq : ℚ) : ℝ) - ((Yq : ℚ) : ℝ)| ≤ ((Xq : ℚ) : ℝ) / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hhalf
    push_cast at h
    exact h
  have hΛle : |Λ| ≤ 6 * (2 / 3 : ℝ) ^ N := by
    rw [hΛeq]
    have hlip := abs_log_sub_log_le hXRpos hYRpos hhalfR
    have h1R : |((Xq : ℚ) : ℝ) - ((Yq : ℚ) : ℝ)| ≤ (2 : ℝ) ^ (a + s) * (2 / 3) ^ k := by
      have h := (Rat.cast_le (K := ℝ)).mpr hXYbound
      push_cast at h
      exact h
    have hX3R : (3 : ℝ) ^ (a + s) ≤ 3 * ((Xq : ℚ) : ℝ) := by exact_mod_cast hX3
    have hb1 : 2 * |((Xq : ℚ) : ℝ) - ((Yq : ℚ) : ℝ)| / ((Xq : ℚ) : ℝ)
        ≤ 2 * ((2 : ℝ) ^ (a + s) * (2 / 3) ^ k) / ((3 : ℝ) ^ (a + s) / 3) := by
      have hden : (3 : ℝ) ^ (a + s) / 3 ≤ ((Xq : ℚ) : ℝ) := by linarith
      gcongr
    have hb2 : 2 * ((2 : ℝ) ^ (a + s) * (2 / 3) ^ k) / ((3 : ℝ) ^ (a + s) / 3)
        = 6 * (2 / 3 : ℝ) ^ N := by
      rw [hN, div_pow, div_pow, pow_add]
      field_simp
      ring
    calc |Real.log ((Xq : ℚ) : ℝ) - Real.log ((Yq : ℚ) : ℝ)|
        ≤ 2 * |((Xq : ℚ) : ℝ) - ((Yq : ℚ) : ℝ)| / ((Xq : ℚ) : ℝ) := hlip
      _ ≤ 2 * ((2 : ℝ) ^ (a + s) * (2 / 3) ^ k) / ((3 : ℝ) ^ (a + s) / 3) := hb1
      _ = 6 * (2 / 3 : ℝ) ^ N := hb2
  have hlogΛle : Real.log Λ ≤ Real.log 6 - ((N : ℕ) : ℝ) * Real.log (3 / 2) := by
    rw [← Real.log_abs]
    calc Real.log |Λ| ≤ Real.log (6 * (2 / 3 : ℝ) ^ N) :=
          Real.log_le_log (abs_pos.mpr hΛne) hΛle
      _ = Real.log 6 + ((N : ℕ) : ℝ) * Real.log (2 / 3) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ = Real.log 6 - ((N : ℕ) : ℝ) * Real.log (3 / 2) := by
          rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
          ring
  -- ## the Baker–Wüstholz lower bound
  set α : Fin 4 → ℚ := ![3, 2, ((u : ℤ) : ℚ), lam] with hαdef
  set b : Fin 4 → ℤ := ![((a + s : ℕ) : ℤ), -((N : ℕ) : ℤ), -1, 1] with hbdef
  have e0 : α 0 = 3 := rfl
  have e1 : α 1 = 2 := rfl
  have e2 : α 2 = ((u : ℤ) : ℚ) := rfl
  have e3 : α 3 = lam := rfl
  have f0 : b 0 = ((a + s : ℕ) : ℤ) := rfl
  have f1 : b 1 = -((N : ℕ) : ℤ) := rfl
  have f2 : b 2 = -1 := rfl
  have f3 : b 3 = 1 := rfl
  have hα : ∀ i, α i ≠ 0 := by
    intro i
    fin_cases i
    · exact (by norm_num : (3 : ℚ) ≠ 0)
    · exact (by norm_num : (2 : ℚ) ≠ 0)
    · exact Int.cast_ne_zero.mpr (by omega)
    · exact hlampos.ne'
  have hbB : ∀ i, (b i).natAbs ≤ N := by
    intro i
    fin_cases i
    · show ((a + s : ℕ) : ℤ).natAbs ≤ N
      rw [Int.natAbs_natCast]
      omega
    · show (-((N : ℕ) : ℤ)).natAbs ≤ N
      rw [Int.natAbs_neg, Int.natAbs_natCast]
    · show ((-1 : ℤ)).natAbs ≤ N
      simp only [Int.natAbs_neg, Int.natAbs_one]
      omega
    · show ((1 : ℤ)).natAbs ≤ N
      simp only [Int.natAbs_one]
      omega
  -- the sum is (Λ : ℂ)
  have hlog3 : Complex.log (((3 : ℚ) : ℂ)) = ((Real.log 3 : ℝ) : ℂ) := by
    rw [show ((3 : ℚ) : ℂ) = (((3 : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_log (by norm_num)]
  have hlog2 : Complex.log (((2 : ℚ) : ℂ)) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show ((2 : ℚ) : ℂ) = (((2 : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_log (by norm_num)]
  have hlogu : Complex.log ((((u : ℤ) : ℚ)) : ℂ) = ((Real.log ((u : ℤ) : ℝ) : ℝ) : ℂ) := by
    rw [show ((((u : ℤ) : ℚ)) : ℂ) = ((((u : ℤ) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log huRpos.le]
  have hloglam : Complex.log (((lam : ℚ)) : ℂ) = ((Real.log ((lam : ℚ) : ℝ) : ℝ) : ℂ) := by
    rw [show (((lam : ℚ)) : ℂ) = ((((lam : ℚ) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log hlamRpos.le]
  have hsum : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) = ((Λ : ℝ) : ℂ) := by
    rw [Fin.sum_univ_four, e0, e1, e2, e3, f0, f1, f2, f3, eq_ratCast, eq_ratCast,
      eq_ratCast, eq_ratCast, hlog3, hlog2, hlogu, hloglam, hΛdef]
    push_cast
    ring
  have hΛneC : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) ≠ 0 := by
    rw [hsum]
    exact Complex.ofReal_ne_zero.mpr hΛne
  have hBW := BakerWustholz.linearForms_logs (n := 4) (by norm_num)
    (Rat.castHom ℂ) α hα b (B := N) (by omega) hbB hΛneC
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, Real.log_abs,
    Module.finrank_self, Nat.cast_one] at hBW
  rw [show (1 : ℝ) / (1 : ℝ) = 1 by norm_num] at hBW
  -- ## the height product
  set Δ : ℝ := ((a + s : ℕ) : ℝ) * Real.log (3 / 2) - (k : ℝ) * Real.log 2 with hΔdef
  have hΔu : Real.log ((u : ℤ) : ℝ) ≤ Δ := by
    have hmc : (m (a + s) : ℚ) ≤ (3 / 2) ^ (a + s) + 1 / 2 := by
      have h := neg_half_le_eps (a + s)
      unfold eps at h
      linarith
    have hma : (1 : ℚ) ≤ (m a : ℚ) := by exact_mod_cast m_pos a
    have hu2 : 2 ^ k * (u : ℚ) ≤ (3 / 2) ^ (a + s) := by linarith [huQ]
    have hu2R : (2 : ℝ) ^ k * ((u : ℤ) : ℝ) ≤ (3 / 2 : ℝ) ^ (a + s) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hu2
      push_cast at h
      exact h
    have hlog := Real.log_le_log (by positivity) hu2R
    rw [Real.log_mul (by positivity) huRpos.ne', Real.log_pow, Real.log_pow] at hlog
    rw [hΔdef]
    linarith
  have hmh2 : BakerWustholz.modifiedHeight (Rat.castHom ℂ) ((u : ℤ) : ℚ)
      ≤ max Δ 1 := by
    refine le_trans (mh_intCast hu1) ?_
    exact max_le (le_max_of_le_left hΔu) (le_max_right _ _)
  have hmhnn : ∀ q : ℚ, 0 ≤ BakerWustholz.modifiedHeight (Rat.castHom ℂ) q := by
    intro q
    rw [modifiedHeight_rat]
    positivity
  have hprod : (∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (α i))
      ≤ Real.log 3 * 1 * max Δ 1 * ((s : ℝ) * Real.log 3) := by
    rw [Fin.prod_univ_four, e0, e1, e2, e3]
    have hb0 := mh_three
    have hb1 := mh_two
    have hb2 := hmh2
    have hb3 : BakerWustholz.modifiedHeight (Rat.castHom ℂ) lam
        ≤ (s : ℝ) * Real.log 3 := by
      rw [hlam]
      exact mh_lambda s hs1
    have hmax1 : (0 : ℝ) ≤ max Δ 1 := le_trans zero_le_one (le_max_right _ _)
    have hlog3nn : (0 : ℝ) ≤ Real.log 3 := log_three_pos'.le
    have m01 : BakerWustholz.modifiedHeight (Rat.castHom ℂ) 3
        * BakerWustholz.modifiedHeight (Rat.castHom ℂ) 2 ≤ Real.log 3 * 1 :=
      mul_le_mul hb0 hb1 (hmhnn _) hlog3nn
    have m012 : BakerWustholz.modifiedHeight (Rat.castHom ℂ) 3
        * BakerWustholz.modifiedHeight (Rat.castHom ℂ) 2
        * BakerWustholz.modifiedHeight (Rat.castHom ℂ) ((u : ℤ) : ℚ)
        ≤ Real.log 3 * 1 * max Δ 1 :=
      mul_le_mul m01 hb2 (hmhnn _) (mul_nonneg hlog3nn zero_le_one)
    exact mul_le_mul m012 hb3 (hmhnn _)
      (mul_nonneg (mul_nonneg hlog3nn zero_le_one) hmax1)
  -- ## combine
  have hCmax : 0 ≤ BakerWustholz.C 4 1 * max (Real.log ((N : ℕ) : ℝ)) 1 :=
    mul_nonneg (C_one_nonneg 4) (le_trans zero_le_one (le_max_right _ _))
  have hlower : -(BakerWustholz.C 4 1 * max (Real.log ((N : ℕ) : ℝ)) 1
      * (Real.log 3 * 1 * max Δ 1 * ((s : ℝ) * Real.log 3))) ≤ Real.log Λ := by
    refine le_trans (neg_le_neg ?_) hBW
    exact mul_le_mul_of_nonneg_left hprod hCmax
  have harr : BakerWustholz.C 4 1 * max (Real.log ((N : ℕ) : ℝ)) 1
      * (Real.log 3 * 1 * max Δ 1 * ((s : ℝ) * Real.log 3))
      = BakerWustholz.C 4 1 * max (Real.log ((N : ℕ) : ℝ)) 1 * (s : ℝ)
        * Real.log 3 ^ 2 * max Δ 1 := by
    ring
  have hfinal : ((N : ℕ) : ℝ) * Real.log (3 / 2)
      ≤ Real.log 6 + BakerWustholz.C 4 1 * max (Real.log ((N : ℕ) : ℝ)) 1 * (s : ℝ)
        * Real.log 3 ^ 2 * max Δ 1 := by
    rw [← harr]
    linarith [hlower, hlogΛle]
  exact hfinal

/-- **The extreme sliver** ([M4A3] §6.1, "in particular"): a repetition whose
slack is at most 1 — i.e. `k ≥ (c·log(3/2) − 1)/log 2`, within `O(1)` of the
elementary ceiling — satisfies the slack-free effective bound
`(c+k)·log(3/2) ≤ log 6 + C₄·max(log(c+k), 1)·(c−a)·(log 3)²`.  For bounded
gaps `c − a ≤ S` this caps `c + k` at an explicit value: the ceiling is never
approached.  Footprint std3 + [BW93]. -/
@[category research solved, AMS 11, ref "BW93", group "three_halves_m4"]
theorem extremal_sliver_bound {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (hk : 2 ≤ k) (hrep : IsRepetition a c k)
    (hsliver : (c : ℝ) * Real.log (3 / 2) - (k : ℝ) * Real.log 2 ≤ 1) :
    ((c + k : ℕ) : ℝ) * Real.log (3 / 2)
      ≤ Real.log 6
        + BakerWustholz.C 4 1 * max (Real.log ((c + k : ℕ) : ℝ)) 1
          * ((c - a : ℕ) : ℝ) * Real.log 3 ^ 2 := by
  have h := repetition_extremal_bound ha hac hk hrep
  rw [max_eq_right hsliver, mul_one] at h
  exact h

/-! ## Theorem E1, Matveev engine (`plan-formalize-logforms.html` M-4, F-5a) -/

set_option maxHeartbeats 800000 in
/-- **Theorem E1, Matveev engine** (`plan-formalize-logforms.html` M-4, F-5a):
the effective repetition bound with Baker–Wüstholz replaced by Matveev's sharper
Corollary 2.3 (`CITED/Matveev.lean`).  Every repetition `(a, c, k)` with
`2 ≤ a < c`, `2 ≤ k` satisfies

  `(c+k)·log(3/2) ≤ log 6 + C₁(4,1) · log(e(c+k)) · (c−a) · (log 3)² · log 2 ·
      max(c·log(3/2) − k·log 2, 0.16)`

with `C₁(4,1) = Matveev.C₁ 4 1 ≈ 1.5×10¹³` in place of E1's
`C₄ = BakerWustholz.C 4 1 ≈ 4.9×10¹⁵`.  Three visible sharpenings over
`repetition_extremal_bound`: the constant (`≈325×`), the `log 2` height factor
(where BW rounds `h'(2)` up to `1`) and the `0.16` slack floor (where BW uses
`1`) — jointly the plan's `≈470×` effective shrink of the M4 program's only
quantitative constant.  The analytic core (the linear form `Λ`, its
`|Λ| ≤ 6(2/3)^{c+k}` contraction, the height of `λ'_s`) parallels
`repetition_extremal_bound`; only the engine call
(`log_linearForm_rat_ge_matveev`) and the modified-height evaluations
(`clampHeight_two`/`clampHeight_three`/`clampHeight_intCast`) differ.
Footprint std3 + [Mat00]. -/
@[category research solved, AMS 11, ref "Mat00", group "three_halves_m4"]
theorem repetition_extremal_bound_matveev {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (hk : 2 ≤ k) (hrep : IsRepetition a c k) :
    ((c + k : ℕ) : ℝ) * Real.log (3 / 2)
      ≤ Real.log 6
        + Matveev.C₁ 4 1 * Real.log (Real.exp 1 * ((c + k : ℕ) : ℝ))
          * ((c - a : ℕ) : ℝ) * Real.log 3 ^ 2 * Real.log 2
          * max ((c : ℝ) * Real.log (3 / 2) - (k : ℝ) * Real.log 2) 0.16 := by
  obtain ⟨s, rfl⟩ : ∃ s, c = a + s := ⟨c - a, by omega⟩
  have hs1 : 1 ≤ s := by omega
  rw [Nat.add_sub_cancel_left]
  -- ## the integer multiplier u
  obtain ⟨u, hu⟩ := two_pow_dvd_of_repetition hrep
  have h2k : (0 : ℤ) < 2 ^ k := by positivity
  have hmlt : m a < m (a + s) := m_strictMono ha (by omega)
  have hu1 : 1 ≤ u := by
    by_contra hle
    have hu0 : u ≤ 0 := by omega
    have hnp := mul_nonpos_of_nonneg_of_nonpos h2k.le hu0
    linarith
  have huQ : ((m (a + s) : ℚ)) - ((m a : ℚ)) = 2 ^ k * (u : ℚ) := by
    exact_mod_cast hu
  -- ## the moving multiplier λ'_s
  have h23 : (2 : ℕ) ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by norm_num) s
  have h23' : (2 : ℕ) ^ s < 3 ^ s := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hApos : 0 < 3 ^ s - 2 ^ s := by omega
  set lam : ℚ := ((3 ^ s - 2 ^ s : ℕ) : ℚ) / ((3 ^ s : ℕ) : ℚ) with hlam
  have h3spos : (0 : ℚ) < ((3 ^ s : ℕ) : ℚ) := by
    exact_mod_cast (by positivity : 0 < (3 : ℕ) ^ s)
  have hlampos : 0 < lam := div_pos (by exact_mod_cast hApos) h3spos
  have hlam3 : 1 / 3 ≤ lam := by
    rw [hlam, le_div_iff₀ h3spos]
    have key : 3 * (2 ^ s : ℕ) ≤ 2 * 3 ^ s := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have h : (2 : ℕ) ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by norm_num) t
      have e1 : 3 * 2 ^ (t + 1) = 6 * 2 ^ t := by rw [pow_add]; ring
      have e2 : 2 * 3 ^ (t + 1) = 6 * 3 ^ t := by rw [pow_add]; ring
      omega
    have keyQ : 3 * ((2 ^ s : ℕ) : ℚ) ≤ 2 * ((3 ^ s : ℕ) : ℚ) := by
      exact_mod_cast key
    have hc : ((3 ^ s - 2 ^ s : ℕ) : ℚ)
        = ((3 ^ s : ℕ) : ℚ) - ((2 ^ s : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub h23]
      ring
    rw [hc]
    linarith
  -- ## X, Y and the Lemma-R contraction
  set N : ℕ := a + s + k with hN
  have hN5 : 5 ≤ N := by omega
  set Xq : ℚ := (3 : ℚ) ^ (a + s) - (3 : ℚ) ^ a * 2 ^ s with hXqdef
  set Yq : ℚ := (u : ℚ) * 2 ^ N with hYq
  have hXlam : Xq = (3 : ℚ) ^ (a + s) * lam := by
    rw [hXqdef, hlam]
    have h3ne : ((3 ^ s : ℕ) : ℚ) ≠ 0 := h3spos.ne'
    field_simp
    push_cast [Nat.cast_sub h23]
    ring
  have hXqpos : 0 < Xq := by
    rw [hXlam]
    exact mul_pos (by positivity) hlampos
  have hYqpos : 0 < Yq := by
    rw [hYq]
    exact mul_pos (by exact_mod_cast (by omega : (0 : ℤ) < u)) (by positivity)
  -- the ε-identity: `X − Y = 2^{a+s}(ε_{a+s} − ε_a)`
  have r1 : ((R (a + s) : ℤ) : ℚ) = 3 ^ (a + s) - 2 ^ (a + s) * (m (a + s) : ℚ) := by
    unfold R
    push_cast
    ring
  have r2 : ((R a : ℤ) : ℚ) = 3 ^ a - 2 ^ a * (m a : ℚ) := by
    unfold R
    push_cast
    ring
  have hsplit : (2 : ℚ) ^ (a + s) * eps a = 2 ^ s * ((R a : ℤ) : ℚ) := by
    rw [pow_add, mul_comm ((2 : ℚ) ^ a) ((2 : ℚ) ^ s), mul_assoc, two_pow_mul_eps]
  have hXY : Xq - Yq = 2 ^ (a + s) * (eps (a + s) - eps a) := by
    rw [mul_sub, two_pow_mul_eps, hsplit, hXqdef, hYq, hN, r1, r2]
    linear_combination (2 : ℚ) ^ (a + s) * huQ
  have hXYbound : |Xq - Yq| ≤ 2 ^ (a + s) * (2 / 3 : ℚ) ^ k := by
    rw [hXY, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (2 : ℚ) ^ (a + s))]
    exact mul_le_mul_of_nonneg_left (abs_eps_sub_le_of_repetition hrep)
      (by positivity)
  have hXYone : 1 ≤ |Xq - Yq| := by
    rw [hXY, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (2 : ℚ) ^ (a + s))]
    exact one_le_two_pow_mul_abs_eps_sub (by omega) (by omega)
  have hX3 : (3 : ℚ) ^ (a + s) ≤ 3 * Xq := by
    rw [hXlam]
    nlinarith [hlam3, pow_pos (show (0 : ℚ) < 3 by norm_num) (a + s)]
  have hhalf : |Xq - Yq| ≤ Xq / 2 := by
    have h6 : 6 * 2 ^ N ≤ 3 ^ N := six_mul_two_pow_le hN5
    have h6Q : (6 : ℚ) * 2 ^ N ≤ 3 ^ N := by exact_mod_cast h6
    have e2N : (2 : ℚ) ^ N = 2 ^ (a + s) * 2 ^ k := by rw [hN, pow_add]
    have e3N : (3 : ℚ) ^ N = 3 ^ (a + s) * 3 ^ k := by rw [hN, pow_add]
    rw [e2N, e3N] at h6Q
    have hstep : (2 : ℚ) ^ (a + s) * (2 / 3) ^ k ≤ (3 : ℚ) ^ (a + s) / 6 := by
      rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [h6Q]
    linarith [hXYbound, hstep, hX3]
  -- ## the linear form Λ, over ℝ
  have hXRpos : (0 : ℝ) < ((Xq : ℚ) : ℝ) := by exact_mod_cast hXqpos
  have hYRpos : (0 : ℝ) < ((Yq : ℚ) : ℝ) := by exact_mod_cast hYqpos
  have hlamRpos : (0 : ℝ) < ((lam : ℚ) : ℝ) := by exact_mod_cast hlampos
  have huRpos : (0 : ℝ) < ((u : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < u)
  set Λ : ℝ := ((a + s : ℕ) : ℝ) * Real.log 3 - ((N : ℕ) : ℝ) * Real.log 2
      - Real.log ((u : ℤ) : ℝ) + Real.log ((lam : ℚ) : ℝ) with hΛdef
  have hlogX : Real.log ((Xq : ℚ) : ℝ)
      = ((a + s : ℕ) : ℝ) * Real.log 3 + Real.log ((lam : ℚ) : ℝ) := by
    have hcast : ((Xq : ℚ) : ℝ) = (3 : ℝ) ^ (a + s) * ((lam : ℚ) : ℝ) := by
      rw [hXlam]
      push_cast
      ring
    rw [hcast, Real.log_mul (by positivity) hlamRpos.ne', Real.log_pow]
  have hlogY : Real.log ((Yq : ℚ) : ℝ)
      = Real.log ((u : ℤ) : ℝ) + ((N : ℕ) : ℝ) * Real.log 2 := by
    have hcast : ((Yq : ℚ) : ℝ) = ((u : ℤ) : ℝ) * (2 : ℝ) ^ N := by
      rw [hYq]
      push_cast
      ring
    rw [hcast, Real.log_mul huRpos.ne' (by positivity), Real.log_pow]
  have hΛXY : Λ = Real.log ((Xq : ℚ) : ℝ) - Real.log ((Yq : ℚ) : ℝ) := by
    rw [hΛdef, hlogX, hlogY]
    ring
  have hΛne : Λ ≠ 0 := by
    rw [hΛXY]
    intro h0
    have hXYeq : ((Xq : ℚ) : ℝ) = ((Yq : ℚ) : ℝ) := by
      have hexp := congrArg Real.exp (sub_eq_zero.mp h0)
      rwa [Real.exp_log hXRpos, Real.exp_log hYRpos] at hexp
    have : Xq = Yq := by exact_mod_cast hXYeq
    rw [this] at hXYone
    norm_num at hXYone
  have hhalfR : |((Xq : ℚ) : ℝ) - ((Yq : ℚ) : ℝ)| ≤ ((Xq : ℚ) : ℝ) / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hhalf
    push_cast at h
    exact h
  have hΛle : |Λ| ≤ 6 * (2 / 3 : ℝ) ^ N := by
    rw [hΛXY]
    have hlip := abs_log_sub_log_le hXRpos hYRpos hhalfR
    have h1R : |((Xq : ℚ) : ℝ) - ((Yq : ℚ) : ℝ)| ≤ (2 : ℝ) ^ (a + s) * (2 / 3) ^ k := by
      have h := (Rat.cast_le (K := ℝ)).mpr hXYbound
      push_cast at h
      exact h
    have hX3R : (3 : ℝ) ^ (a + s) ≤ 3 * ((Xq : ℚ) : ℝ) := by exact_mod_cast hX3
    have hb1 : 2 * |((Xq : ℚ) : ℝ) - ((Yq : ℚ) : ℝ)| / ((Xq : ℚ) : ℝ)
        ≤ 2 * ((2 : ℝ) ^ (a + s) * (2 / 3) ^ k) / ((3 : ℝ) ^ (a + s) / 3) := by
      have hden : (3 : ℝ) ^ (a + s) / 3 ≤ ((Xq : ℚ) : ℝ) := by linarith
      gcongr
    have hb2 : 2 * ((2 : ℝ) ^ (a + s) * (2 / 3) ^ k) / ((3 : ℝ) ^ (a + s) / 3)
        = 6 * (2 / 3 : ℝ) ^ N := by
      rw [hN, div_pow, div_pow, pow_add]
      field_simp
      ring
    calc |Real.log ((Xq : ℚ) : ℝ) - Real.log ((Yq : ℚ) : ℝ)|
        ≤ 2 * |((Xq : ℚ) : ℝ) - ((Yq : ℚ) : ℝ)| / ((Xq : ℚ) : ℝ) := hlip
      _ ≤ 2 * ((2 : ℝ) ^ (a + s) * (2 / 3) ^ k) / ((3 : ℝ) ^ (a + s) / 3) := hb1
      _ = 6 * (2 / 3 : ℝ) ^ N := hb2
  have hlogΛle : Real.log Λ ≤ Real.log 6 - ((N : ℕ) : ℝ) * Real.log (3 / 2) := by
    rw [← Real.log_abs]
    calc Real.log |Λ| ≤ Real.log (6 * (2 / 3 : ℝ) ^ N) :=
          Real.log_le_log (abs_pos.mpr hΛne) hΛle
      _ = Real.log 6 + ((N : ℕ) : ℝ) * Real.log (2 / 3) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ = Real.log 6 - ((N : ℕ) : ℝ) * Real.log (3 / 2) := by
          rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
          ring
  -- ## the slack `Δ` and the height of `u`
  set Δ : ℝ := ((a + s : ℕ) : ℝ) * Real.log (3 / 2) - (k : ℝ) * Real.log 2 with hΔdef
  have hΔu : Real.log ((u : ℤ) : ℝ) ≤ Δ := by
    have hmc : (m (a + s) : ℚ) ≤ (3 / 2) ^ (a + s) + 1 / 2 := by
      have h := neg_half_le_eps (a + s)
      unfold eps at h
      linarith
    have hma : (1 : ℚ) ≤ (m a : ℚ) := by exact_mod_cast m_pos a
    have hu2 : 2 ^ k * (u : ℚ) ≤ (3 / 2) ^ (a + s) := by linarith [huQ]
    have hu2R : (2 : ℝ) ^ k * ((u : ℤ) : ℝ) ≤ (3 / 2 : ℝ) ^ (a + s) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hu2
      push_cast at h
      exact h
    have hlog := Real.log_le_log (by positivity) hu2R
    rw [Real.log_mul (by positivity) huRpos.ne', Real.log_pow, Real.log_pow] at hlog
    rw [hΔdef]
    linarith
  -- ## the linear form as a real sum, and the Matveev lower bound
  set α : Fin 4 → ℚ := ![3, 2, ((u : ℤ) : ℚ), lam] with hαdef
  set b : Fin 4 → ℤ := ![((a + s : ℕ) : ℤ), -((N : ℕ) : ℤ), -1, 1] with hbdef
  have e0 : α 0 = 3 := rfl
  have e1 : α 1 = 2 := rfl
  have e2 : α 2 = ((u : ℤ) : ℚ) := rfl
  have e3 : α 3 = lam := rfl
  have f0 : b 0 = ((a + s : ℕ) : ℤ) := rfl
  have f1 : b 1 = -((N : ℕ) : ℤ) := rfl
  have f2 : b 2 = -1 := rfl
  have f3 : b 3 = 1 := rfl
  have hα : ∀ i, 0 < α i := by
    intro i
    fin_cases i
    · exact (by norm_num : (0 : ℚ) < 3)
    · exact (by norm_num : (0 : ℚ) < 2)
    · show (0 : ℚ) < ((u : ℤ) : ℚ)
      exact_mod_cast (by omega : (0 : ℤ) < u)
    · exact hlampos
  have hbB : ∀ i, (b i).natAbs ≤ N := by
    intro i
    fin_cases i
    · show ((a + s : ℕ) : ℤ).natAbs ≤ N
      rw [Int.natAbs_natCast]; omega
    · show (-((N : ℕ) : ℤ)).natAbs ≤ N
      rw [Int.natAbs_neg, Int.natAbs_natCast]
    · show ((-1 : ℤ)).natAbs ≤ N
      simp only [Int.natAbs_neg, Int.natAbs_one]; omega
    · show ((1 : ℤ)).natAbs ≤ N
      simp only [Int.natAbs_one]; omega
  have hΛsum : Λ = ∑ i, (b i : ℝ) * Real.log ((α i : ℚ) : ℝ) := by
    rw [Fin.sum_univ_four, e0, e1, e2, e3, f0, f1, f2, f3, hΛdef]
    have c0 : ((3 : ℚ) : ℝ) = 3 := by norm_num
    have c1 : ((2 : ℚ) : ℝ) = 2 := by norm_num
    have c2 : (((u : ℤ) : ℚ) : ℝ) = ((u : ℤ) : ℝ) := by push_cast; ring
    rw [c0, c1, c2]
    push_cast
    ring
  have hmain := log_linearForm_rat_ge_matveev (n := 4) (by norm_num) α hα b
    (B := N) (by omega) hbB hΛsum hΛne
  -- ## the Matveev height product
  have hprod : (∏ i, Matveev.clampHeight (Rat.castHom ℂ) (α i))
      ≤ Real.log 3 * Real.log 2 * max Δ 0.16 * ((s : ℝ) * Real.log 3) := by
    rw [Fin.prod_univ_four, e0, e1, e2, e3]
    have hb0 : Matveev.clampHeight (Rat.castHom ℂ) (3 : ℚ) ≤ Real.log 3 := clampHeight_three.le
    have hb1 : Matveev.clampHeight (Rat.castHom ℂ) (2 : ℚ) ≤ Real.log 2 := clampHeight_two.le
    have hb2 : Matveev.clampHeight (Rat.castHom ℂ) ((u : ℤ) : ℚ) ≤ max Δ 0.16 :=
      le_trans (clampHeight_intCast hu1) (max_le_max hΔu le_rfl)
    have hb3 : Matveev.clampHeight (Rat.castHom ℂ) lam ≤ (s : ℝ) * Real.log 3 := by
      refine le_trans (clampHeight_le_modifiedHeight lam) ?_
      rw [hlam]; exact mh_lambda s hs1
    have hmax : (0 : ℝ) ≤ max Δ 0.16 := le_trans (by norm_num) (le_max_right _ _)
    have hlog3nn : (0 : ℝ) ≤ Real.log 3 := log_three_pos'.le
    have hlog2nn : (0 : ℝ) ≤ Real.log 2 := log_two_pos'.le
    have m01 : Matveev.clampHeight (Rat.castHom ℂ) 3 * Matveev.clampHeight (Rat.castHom ℂ) 2
        ≤ Real.log 3 * Real.log 2 :=
      mul_le_mul hb0 hb1 (clampHeight_nonneg _) hlog3nn
    have m012 : Matveev.clampHeight (Rat.castHom ℂ) 3 * Matveev.clampHeight (Rat.castHom ℂ) 2
        * Matveev.clampHeight (Rat.castHom ℂ) ((u : ℤ) : ℚ)
        ≤ Real.log 3 * Real.log 2 * max Δ 0.16 :=
      mul_le_mul m01 hb2 (clampHeight_nonneg _) (mul_nonneg hlog3nn hlog2nn)
    exact mul_le_mul m012 hb3 (clampHeight_nonneg _)
      (mul_nonneg (mul_nonneg hlog3nn hlog2nn) hmax)
  -- ## combine
  have hC1nn : 0 ≤ Matveev.C₁ 4 1 := by
    unfold Matveev.C₁; exact le_min (by positivity) (by positivity)
  have hLnn : 0 ≤ Real.log (Real.exp 1 * ((N : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hCLnn : 0 ≤ Matveev.C₁ 4 1 * Real.log (Real.exp 1 * ((N : ℕ) : ℝ)) :=
    mul_nonneg hC1nn hLnn
  have hchain : -(Matveev.C₁ 4 1 * Real.log (Real.exp 1 * ((N : ℕ) : ℝ))
        * (Real.log 3 * Real.log 2 * max Δ 0.16 * ((s : ℝ) * Real.log 3))) ≤ Real.log Λ :=
    le_trans (neg_le_neg (mul_le_mul_of_nonneg_left hprod hCLnn)) hmain
  have harr : Matveev.C₁ 4 1 * Real.log (Real.exp 1 * ((N : ℕ) : ℝ))
        * (Real.log 3 * Real.log 2 * max Δ 0.16 * ((s : ℝ) * Real.log 3))
      = Matveev.C₁ 4 1 * Real.log (Real.exp 1 * ((N : ℕ) : ℝ)) * ((s : ℕ) : ℝ)
        * Real.log 3 ^ 2 * Real.log 2 * max Δ 0.16 := by
    ring
  rw [← harr]
  linarith [hchain, hlogΛle]

/-- **The extreme sliver, Matveev engine**: the slack-free specialization of
`repetition_extremal_bound_matveev` (slack `≤ 0.16`, the extreme edge), with the
`max` collapsed to its `0.16` floor (which — unlike Baker–Wüstholz's floor `1` —
survives as a `0.16` factor rather than vanishing).  For bounded gaps `c − a ≤ S`
this caps `c + k` at an explicit value with the Matveev constant.  Footprint
std3 + [Mat00]. -/
@[category research solved, AMS 11, ref "Mat00", group "three_halves_m4"]
theorem extremal_sliver_bound_matveev {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (hk : 2 ≤ k) (hrep : IsRepetition a c k)
    (hsliver : (c : ℝ) * Real.log (3 / 2) - (k : ℝ) * Real.log 2 ≤ 0.16) :
    ((c + k : ℕ) : ℝ) * Real.log (3 / 2)
      ≤ Real.log 6
        + Matveev.C₁ 4 1 * Real.log (Real.exp 1 * ((c + k : ℕ) : ℝ))
          * ((c - a : ℕ) : ℝ) * Real.log 3 ^ 2 * Real.log 2 * 0.16 := by
  have h := repetition_extremal_bound_matveev ha hac hk hrep
  rw [max_eq_right hsliver] at h
  exact h

end TH
