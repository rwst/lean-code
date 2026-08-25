/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Digit streams and the parity of `⌊t mᵏ⌋` (Lemma D)

The arithmetic half of `plans/plan-dubD1O5.html`: the elementary observation that makes
the whole construction of `SZ/SqrtThree.lean` work.

> **Lemma D** (plan §1.1).  For `t > 0` and an integer `m ≥ 2`, `⌊m t⌋ = m ⌊t⌋ + d` with
> `d = ⌊m {t}⌋` the leading base-`m` digit of `{t}`.  Consequently `⌊t mᵏ⌋` is even for
> every `k ≥ 0` as soon as `⌊t⌋` is even and every *canonical* base-`m` digit of `{t}` is
> even.

Only that direction of Lemma D is needed downstream, and it is proved here in the sharper
quantitative form the construction actually uses: `floor_add_digitReal_mul_pow` computes
`⌊(N + digitReal m d) mˢ⌋` **on the nose** as an explicit integer, and
`even_floor_add_digitReal_mul_pow` reads off its parity.

## Canonical digits, and why a hypothesis is unavoidable

The word *canonical* in Lemma D is load-bearing: base `3`, the stream `2, 2, 2, …`
represents `1`, whose canonical expansion is `1, 0, 0, …` — an odd digit.  Formally the
tail `∑_{i ≥ s} dᵢ m^{-(i+1)}` is `≤ m^{-s}` with equality exactly for the constant
top-digit tail, and the floor identity needs the *strict* inequality.  So every statement
below carries a hypothesis of the shape "some digit at index `≥ s` is `≤ m - 2`".  Supplying
that hypothesis for the greedy of `SZ/CoverGame.lean` is lemma L1 of the plan, proved as
`SZ.exists_digitA_eq_zero` / `SZ.exists_digitB_eq_two`.

For **even** `m` the hypothesis is free (the largest even digit is `m - 2` already); it
bites only for odd `m`, and `m = 3` is the case that matters.

## Base-2 degeneracy

`digitReal_two_eq_zero`: for `m = 2` the only even digit is `0`, so the restricted-digit
set collapses to `{0}`.  This is the mechanism behind [Dub06EO] Thm 2(i)
(`2^{1/q} ∈ 𝒮`) — see plan §1.1 and note `note-dubD1O5-M1.html` §4(a) — and the exact
reason the method of this root has nothing to say at `m = 2`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
-/

namespace SZ

open Finset Filter Topology

/-- The `k`-th partial sum `∑_{i < k} dᵢ m^{-(i+1)}` of the base-`m` digit stream `d`. -/
noncomputable def digitSum (m : ℕ) (d : ℕ → ℤ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (d i : ℝ) / (m : ℝ) ^ (i + 1)

/-- The real number of `[0,1]` with base-`m` digit stream `d`, as the supremum of its
partial sums.  Defining it as a `⨆` rather than a `∑'` keeps every estimate below
order-theoretic; `digitSum_tendsto` recovers the limit description. -/
noncomputable def digitReal (m : ℕ) (d : ℕ → ℤ) : ℝ := ⨆ k, digitSum m d k

/-- `d` is a base-`m` digit stream: `m ≥ 2` and every `dᵢ` lies in `{0, …, m-1}`. -/
structure IsDigits (m : ℕ) (d : ℕ → ℤ) : Prop where
  two_le : 2 ≤ m
  nonneg : ∀ i, 0 ≤ d i
  le_sub_one : ∀ i, d i ≤ (m : ℤ) - 1

namespace IsDigits

variable {m : ℕ} {d : ℕ → ℤ}

theorem one_lt_cast (h : IsDigits m d) : (1 : ℝ) < (m : ℝ) := by
  exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) h.two_le

theorem cast_pos (h : IsDigits m d) : (0 : ℝ) < (m : ℝ) := lt_trans zero_lt_one h.one_lt_cast

theorem cast_ne_zero (h : IsDigits m d) : (m : ℝ) ≠ 0 := ne_of_gt h.cast_pos

theorem pow_pos' (h : IsDigits m d) (k : ℕ) : (0 : ℝ) < (m : ℝ) ^ k := pow_pos h.cast_pos k

end IsDigits

variable {m : ℕ} {d : ℕ → ℤ}

/-- `1/Mʲ - c/M^{j+1} = (M - c)/M^{j+1}` — the arithmetic behind every tail estimate. -/
private theorem tail_id {M : ℝ} (hM : M ≠ 0) (j : ℕ) (c : ℝ) :
    1 / M ^ j - c / M ^ (j + 1) = (M - c) / M ^ (j + 1) := by
  rw [pow_succ]
  field_simp

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_zero (m : ℕ) (d : ℕ → ℤ) : digitSum m d 0 = 0 := by
  simp [digitSum]

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_succ (m : ℕ) (d : ℕ → ℤ) (k : ℕ) :
    digitSum m d (k + 1) = digitSum m d k + (d k : ℝ) / (m : ℝ) ^ (k + 1) := by
  simp [digitSum, Finset.sum_range_succ]

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_monotone (h : IsDigits m d) : Monotone (digitSum m d) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [digitSum_succ]
  have : (0 : ℝ) ≤ (d k : ℝ) / (m : ℝ) ^ (k + 1) :=
    div_nonneg (by exact_mod_cast h.nonneg k) (h.pow_pos' _).le
  linarith

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_nonneg (h : IsDigits m d) (k : ℕ) : 0 ≤ digitSum m d k := by
  simpa [digitSum_zero] using digitSum_monotone h (Nat.zero_le k)

/-- The **tail estimate**: from index `k` on, a digit stream can add at most `m^{-k}`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_le_of_le (h : IsDigits m d) {k j : ℕ} (hkj : k ≤ j) :
    digitSum m d j ≤ digitSum m d k + 1 / (m : ℝ) ^ k - 1 / (m : ℝ) ^ j := by
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [digitSum_succ]
    have hp : (0 : ℝ) < (m : ℝ) ^ (j + 1) := h.pow_pos' _
    have hdj : (d j : ℝ) ≤ (m : ℝ) - 1 := by exact_mod_cast h.le_sub_one j
    have key : (d j : ℝ) / (m : ℝ) ^ (j + 1) ≤ 1 / (m : ℝ) ^ j - 1 / (m : ℝ) ^ (j + 1) := by
      rw [tail_id h.cast_ne_zero j 1]
      gcongr
    linarith

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_le_one (h : IsDigits m d) (k : ℕ) : digitSum m d k ≤ 1 := by
  have hb := digitSum_le_of_le h (Nat.zero_le k)
  have h1 : (0 : ℝ) < 1 / (m : ℝ) ^ k := one_div_pos.mpr (h.pow_pos' k)
  rw [digitSum_zero, pow_zero] at hb
  linarith

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem bddAbove_digitSum (h : IsDigits m d) : BddAbove (Set.range (digitSum m d)) :=
  ⟨1, by rintro _ ⟨k, rfl⟩; exact digitSum_le_one h k⟩

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_le_digitReal (h : IsDigits m d) (k : ℕ) :
    digitSum m d k ≤ digitReal m d :=
  le_ciSup (bddAbove_digitSum h) k

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitReal_nonneg (h : IsDigits m d) : 0 ≤ digitReal m d :=
  le_trans (digitSum_nonneg h 0) (digitSum_le_digitReal h 0)

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitReal_le_one (h : IsDigits m d) : digitReal m d ≤ 1 :=
  ciSup_le (digitSum_le_one h)

@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_tendsto (h : IsDigits m d) :
    Tendsto (digitSum m d) atTop (𝓝 (digitReal m d)) :=
  tendsto_atTop_ciSup (digitSum_monotone h) (bddAbove_digitSum h)

/-! ## The strict tail bound

The one place where *canonical* digits matter. -/

/-- **Strict tail bound.**  If some digit at an index `≥ k` is at most `m - 2`, the tail
beyond `k` is strictly less than `m^{-k}` — by a definite margin. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitReal_lt_digitSum_add (h : IsDigits m d) {k i₀ : ℕ} (hk : k ≤ i₀)
    (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    digitReal m d < digitSum m d k + 1 / (m : ℝ) ^ k := by
  have hp0 : (0 : ℝ) < (m : ℝ) ^ i₀ := h.pow_pos' _
  have hp1 : (0 : ℝ) < (m : ℝ) ^ (i₀ + 1) := h.pow_pos' _
  have hmar : (0 : ℝ) < 1 / (m : ℝ) ^ (i₀ + 1) := one_div_pos.mpr hp1
  have hdi : (d i₀ : ℝ) ≤ (m : ℝ) - 2 := by exact_mod_cast hsmall
  -- the step across the small digit gains a full `2 / m^{i₀+1}`
  have key : (d i₀ : ℝ) / (m : ℝ) ^ (i₀ + 1)
      ≤ 1 / (m : ℝ) ^ i₀ - 2 / (m : ℝ) ^ (i₀ + 1) := by
    rw [tail_id h.cast_ne_zero i₀ 2]
    gcongr
  rw [show (2 : ℝ) / (m : ℝ) ^ (i₀ + 1)
      = 1 / (m : ℝ) ^ (i₀ + 1) + 1 / (m : ℝ) ^ (i₀ + 1) from by ring] at key
  have h2 := digitSum_le_of_le h hk
  -- hence: the partial sum at `i₀ + 1` is already `1/m^{i₀+1}` below the naive bound
  have hstep : digitSum m d (i₀ + 1)
      ≤ digitSum m d k + 1 / (m : ℝ) ^ k
          - (1 / (m : ℝ) ^ (i₀ + 1) + 1 / (m : ℝ) ^ (i₀ + 1)) := by
    rw [digitSum_succ]
    linarith
  refine lt_of_le_of_lt (ciSup_le fun j => ?_) (by linarith : digitSum m d k + 1 / (m : ℝ) ^ k
      - 1 / (m : ℝ) ^ (i₀ + 1) < digitSum m d k + 1 / (m : ℝ) ^ k)
  rcases le_or_gt j (i₀ + 1) with hj | hj
  · have := digitSum_monotone h hj
    linarith
  · have h4 := digitSum_le_of_le h hj.le
    have h5 : (0 : ℝ) < 1 / (m : ℝ) ^ j := one_div_pos.mpr (h.pow_pos' j)
    linarith

/-! ## The floor identity -/

/-- Shifting a partial sum by `mˢ` produces an integer, explicitly. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitSum_mul_pow (h : IsDigits m d) (s : ℕ) :
    digitSum m d s * (m : ℝ) ^ s
      = ((∑ i ∈ Finset.range s, d i * (m : ℤ) ^ (s - (i + 1)) : ℤ) : ℝ) := by
  rw [digitSum, Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i + 1 ≤ s := Finset.mem_range.mp hi
  have hsplit : (m : ℝ) ^ s = (m : ℝ) ^ (i + 1) * (m : ℝ) ^ (s - (i + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  have hm0 : (m : ℝ) ≠ 0 := h.cast_ne_zero
  rw [hsplit]
  field_simp

/-- **The floor identity.**  With `N` an integer and `d` a base-`m` digit stream having
some digit `≤ m - 2` at an index `≥ s`, the integral part of `(N + digitReal m d) mˢ` is
the explicit integer `N mˢ + ∑_{i < s} dᵢ m^{s-1-i}`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem floor_add_digitReal_mul_pow (h : IsDigits m d) (N : ℤ) (s : ℕ) {i₀ : ℕ}
    (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋
      = N * (m : ℤ) ^ s + ∑ i ∈ Finset.range s, d i * (m : ℤ) ^ (s - (i + 1)) := by
  have hp : (0 : ℝ) < (m : ℝ) ^ s := h.pow_pos' _
  have hlo : digitSum m d s ≤ digitReal m d := digitSum_le_digitReal h s
  have hhi : digitReal m d < digitSum m d s + 1 / (m : ℝ) ^ s :=
    digitReal_lt_digitSum_add h hk hsmall
  have hmul := digitSum_mul_pow h s
  have hone : (1 / (m : ℝ) ^ s) * (m : ℝ) ^ s = 1 := by field_simp
  have hZ : ((N * (m : ℤ) ^ s + ∑ i ∈ Finset.range s, d i * (m : ℤ) ^ (s - (i + 1)) : ℤ) : ℝ)
      = ((N : ℝ) + digitSum m d s) * (m : ℝ) ^ s := by
    rw [add_mul, hmul]; push_cast; ring
  rw [Int.floor_eq_iff, hZ]
  refine ⟨by nlinarith, by nlinarith⟩

/-- **Lemma D at a general modulus** (paper Lemma 3.1, the *telescoping* lemma).  If
`p ∣ N` and `p` divides every digit of `d`, then `p ∣ ⌊(N + digitReal m d) mˢ⌋` for every
`s`.  The paper induces on `s` and needs `p ∣ m` or `p ∣ m - 1` to carry the induction;
the explicit floor formula above makes both hypotheses unnecessary, since each summand
`dᵢ m^{s-1-i}` is divisible by `p` on the nose. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem dvd_floor_add_digitReal_mul_pow (h : IsDigits m d) {p N : ℤ} (hN : p ∣ N)
    (hdvd : ∀ i, p ∣ d i) (s : ℕ) {i₀ : ℕ} (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    p ∣ ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋ := by
  rw [floor_add_digitReal_mul_pow h N s hk hsmall]
  exact dvd_add (hN.mul_right _) (Finset.dvd_sum fun i _ => (hdvd i).mul_right _)

/-- **Lemma D, the direction used.**  If `N` is even and every digit of `d` is even, then
every `⌊(N + digitReal m d) mˢ⌋` is even — the parity engine of `SZ/SqrtThree.lean`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem even_floor_add_digitReal_mul_pow (h : IsDigits m d) {N : ℤ} (hN : Even N)
    (hev : ∀ i, Even (d i)) (s : ℕ) {i₀ : ℕ} (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    Even ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋ := by
  rw [even_iff_two_dvd]
  exact dvd_floor_add_digitReal_mul_pow h (even_iff_two_dvd.mp hN)
    (fun i => even_iff_two_dvd.mp (hev i)) s hk hsmall

/-! ## The complement stream -/

/-- The digitwise complement `dᵢ ↦ (m-1) - dᵢ` realises `1 - digitReal m d`.  At `m = 3`
this is the involution `a ↦ 2 - a` of the even-digit Cantor set that turns the difference
equation `x - √m y = v` of plan §1.2 into the sum equation `x + √m y'' = σ`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitReal_compl (h : IsDigits m d) :
    digitReal m (fun i => (m : ℤ) - 1 - d i) = 1 - digitReal m d := by
  have hc : IsDigits m (fun i => (m : ℤ) - 1 - d i) :=
    { two_le := h.two_le
      nonneg := fun i => by have := h.le_sub_one i; omega
      le_sub_one := fun i => by have := h.nonneg i; omega }
  -- the partial sums of the complement
  have hpartial : ∀ k, digitSum m (fun i => (m : ℤ) - 1 - d i) k
      = (1 - 1 / (m : ℝ) ^ k) - digitSum m d k := by
    intro k
    induction k with
    | zero => simp [digitSum]
    | succ k ih =>
      rw [digitSum_succ, digitSum_succ, ih]
      have hp : (0 : ℝ) < (m : ℝ) ^ k := h.pow_pos' _
      have hp1 : (0 : ℝ) < (m : ℝ) ^ (k + 1) := h.pow_pos' _
      push_cast
      field_simp
      ring
  have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / (m : ℝ) ^ k) atTop (𝓝 0) := by
    have : ∀ k : ℕ, (1 : ℝ) / (m : ℝ) ^ k = (1 / (m : ℝ)) ^ k := fun k => by
      rw [div_pow, one_pow]
    simp only [this]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one h.cast_pos).mpr h.one_lt_cast)
  have hlim : Tendsto (digitSum m (fun i => (m : ℤ) - 1 - d i)) atTop
      (𝓝 (1 - digitReal m d)) := by
    have hfun : digitSum m (fun i => (m : ℤ) - 1 - d i)
        = fun k => (1 - 1 / (m : ℝ) ^ k) - digitSum m d k := funext hpartial
    rw [hfun]
    have hone : (1 : ℝ) - digitReal m d = (1 - 0) - digitReal m d := by ring
    rw [hone]
    exact ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub h0).sub
      (digitSum_tendsto h)
  exact tendsto_nhds_unique (digitSum_tendsto hc) hlim

/-! ## Base-2 degeneracy (plan §1.1, note M1 §4(a)) -/

/-- **`K₂ = {0}`.**  In base `2` the only even digit is `0`, so an even-digit stream
represents `0`.  This is the mechanism inside [Dub06EO] Thm 2(i) (`2^{1/q} ∈ 𝒮`), and the
reason the construction of this root starts at `m = 3`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_digit_parity"]
theorem digitReal_two_eq_zero {d : ℕ → ℤ} (h : IsDigits 2 d) (hev : ∀ i, Even (d i)) :
    digitReal 2 d = 0 := by
  have hz : ∀ i, d i = 0 := by
    intro i
    have h1 := h.nonneg i
    have h2 := h.le_sub_one i
    have h3 := hev i
    rw [Int.even_iff] at h3
    omega
  have : ∀ k, digitSum 2 d k = 0 := by
    intro k; simp [digitSum, hz]
  refine le_antisymm (ciSup_le fun k => by rw [this]) ?_
  simpa [this 0] using digitSum_le_digitReal h 0

end SZ
