/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.KernelReduction

/-!
# A14(iii): the parity word — the propagation criterion, and why multi-scale pairs do not fire

Angle A14 item (iii) of `plans/plan-A1+.html` §5 (work package W10″):

> *the parity word*: M4-for-`(bₙ)` is the report's open Table-E row; the dichotomy obstruction is
> that single `b`-repetitions do not force `t`-repetitions — test whether **multi-scale pairs** of
> `b`-repetitions do.

Executed here.  **Verdict: negative, and the reason is a resolution gap, not a Diophantine one.**
A pair of `b`-repetitions supplies an *upper* bound on `|ε_c − ε_a|` and, in the escape branch, only
the *order* of `ε_a` and `ε_c`; order relations never contradict each other, so no configuration of
pairs is refutable.  The one route that does convert many `b`-repetitions into a `t`-repetition is
the `ε`-pigeonhole, and its demand is exponential in `k` while the window in which the resulting
`t`-repetition is a contradiction is linear in `k`.  Both no-gos are machine-checked below.

## Part 1 — the mechanism T0.4 was missing: the parity word *drives* the dynamics

`t n` is the unique integer in the half-open window `(3ε_n − 1, 3ε_n + 1]` (`lt_t`, `t_le`)
congruent to `b n` mod 2 (`t_unique_of_parity`).  Since that window has length `2`, it contains
exactly one integer of each parity: **`(ε n, b n)` determines `t n`**.  So two positions carrying
the same parity letter carry the same steering letter as soon as their `ε`'s are closer than the
distance to the cell wall — and that distance has a closed form,

  `margin n = 1 − 2·|ε_{n+1}|`   (`t_eq_of_b_eq_of_close`),

with an unconditional floor `1 ≤ 2^n · margin n` (`one_le_two_pow_mul_margin`) from oddness of the
numerators `R`.  The margin is small exactly when `(3/2)^{n+1}` is close to a half-odd-integer, and
`distToNearestInt_le_margin` makes the consequence precise: `‖2·(3/2)^{n+1}‖ ≤ margin n`, so the
parity word is governed by a **Mahler-type quantity of the kernel's own class**, not a cheaper one.

## Part 2 — propagation, and its reach

* `isRepetition_of_isBRepetition_of_margin` — a `b`-repetition of length `k` **is** a
  `t`-repetition once `3·(3/2)^i·|ε_c − ε_a| < margin (a+i)` for every `i < k`: while synchronized
  the `ε`-difference expands by exactly `3/2` (`eps_sub_of_sync`), so one margin comparison per step
  suffices.
* `isRepetition_of_isBRepetition_of_close` — unconditionally, with the a-priori floor:
  `3^k·2^a·|ε_c − ε_a| < 1` forces the propagation.  This is the first propagation criterion for
  the parity word; T0.4 had only the dichotomy.
* `lt_two_pow_of_sync_criterion` — its reach: against the trivial repulsion floor `2^{-c}` the
  criterion can fire only when `3^k·2^a < 2^c`, i.e. only for pairs whose gap exceeds `1.58·k`.

## Part 3 — what a pair of `b`-repetitions actually supplies

* `eps_lt_eps_of_desync_pos` / `eps_lt_eps_of_desync_neg` — **the sign law**: the direction of the
  first desynchronization determines the *order* of `ε_a` and `ε_c`, nothing more.
* `bRepetition_information` — the exact trichotomy: a `t`-repetition; or a first desynchronization
  with `|Δt| = 4`, which separates (`(2/3)^{j+1} ≤ |ε_c − ε_a|`, T0.4's quantitative branch); or one
  with `|Δt| = 2`, which yields exactly one bit — the order.
* `exists_first_desync` — and the information is *finite*: every pair `2 ≤ a < c` has a first
  desynchronization index `j` with `|ε_c − ε_a| ≤ (2/3)^j`.  The hypothesis is only `2 ≤ a < c`, so
  a `b`-repetition of **every** length adds nothing to what an arbitrary pair already gives.  This
  is why T0.2's growth-ceiling proof of aperiodicity has no `b`-analogue: even the Morse–Hedlund
  floor `p_b(k) ≥ k+1` is out of reach here.

Multi-scale pairs therefore accumulate order relations and upper bounds on distances.  A system of
order relations on `s` points is always satisfiable, so no family of `b`-repetitions is refutable by
pair information alone — the plan's test comes out negative on its own terms.

## Part 4 — the only surviving route, and its two no-gos

The remaining route is the `ε`-pigeonhole: pack enough positions sharing a length-`k` parity factor
into a window, force two of them close (`exists_close_pair`), and propagate
(`exists_repetition_of_large_bClass`); the resulting `t`-repetition is a contradiction only inside
the T0.1 window `24·M + 24 < 41·k`.  Both budgets are computed:

* `bRoute_never_fires` — with the actual (a-priori) margin the demand is `3^k·2^M` positions inside
  `[2, M]`, and `M ≤ 3^k·2^M` for **every** `k` and `M`: the route has no window at all.
* `uniform_margin_route_vacuous` / `uniform_margin_route_never_fires` — and it is not the margin's
  fault.  Grant a *uniform* margin `μ > 0`; the demand is then exactly `2·(3/2)^k/μ` positions
  (`isRepetition_of_isBRepetition_of_uniform_margin`, `bClass_forces_window_of_uniform_margin`), and
  since `margin n ≤ 1` (`margin_le_one`) the best conceivable value `μ = 1` still demands
  `2·(3/2)^k`, while `window_lt_perfect_demand` shows the T0.1 window always satisfies
  `2^k·M < 2·3^k`.  Exponential demand, linear window, at every `k`.

## Part 5 — the input that would suffice

`bSuperlinear_of_ratio_bound`: M4-for-`b` follows from M4 plus a **uniform ratio bound**
`p_T(k) ≤ B·p_b(k)` — boundedly many steering factors per parity factor.  That is the exact missing
input, and Part 4 says what it costs: the parity factor determines the steering factor only at
`ε`-resolution `(2/3)^k`, so the honest count of steering factors per parity factor is exponential.

Everything in this file is `std3` — no cited axioms.

## Contents

* `lt_t`, `t_le`, `t_unique_of_parity` — the steering letter is the unique integer of parity `b n`
  in the window `(3ε_n − 1, 3ε_n + 1]`.
* `margin`, `margin_le_one`, `one_le_two_pow_mul_margin`, `distToNearestInt_le_margin` — the
  cell-wall distance, its floor, and its Mahler-type lower bound `‖2·(3/2)^{n+1}‖`.
* `t_eq_of_b_eq_of_close` — the one-step synchronization criterion.
* `isRepetition_of_isBRepetition_of_margin`, `isRepetition_of_isBRepetition_of_close`,
  `isRepetition_of_isBRepetition_of_uniform_margin`, `lt_two_pow_of_sync_criterion` — propagation,
  its uniform-margin form (demand constant `2·(3/2)^k`), and its reach.
* `eps_lt_eps_of_desync_pos`, `eps_lt_eps_of_desync_neg`, `bRepetition_information`,
  `exists_first_desync` — the pair information: order, separation, finiteness.
* `exists_close_pair`, `exists_repetition_of_large_bClass`, `bClass_forces_window`,
  `bClass_forces_window_of_uniform_margin` — the route, with and without a granted margin.
* `bRoute_never_fires`, `window_lt_perfect_demand`, `uniform_margin_route_vacuous`,
  `uniform_margin_route_never_fires` — the two no-gos.
* `bFactor`, `bComplexity`, `BSuperlinear`, `bComplexity_le_complexity`,
  `bSuperlinear_of_ratio_bound` — the parity-word complexity and the sufficient input.

## References

* [A1plus] `plans/plan-A1+.html` (this repository, 2026-08): §5 A14(iii), §7.3 (W10″).
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §3.3 (T0.1, T0.4 — the parity-word partials
  this file continues), §4 (the kernel and the reduction).
-/

namespace TH

/-! ## Part 1 — the parity word drives the dynamics -/

/-- Left end of the steering window: `3ε_n − 1 < t n` (from `ε_{n+1} < 1/2`). -/
@[category API, AMS 11 68, ref "M4A3", group "weyl_a14_parity"]
lemma lt_t (n : ℕ) : 3 * eps n - 1 < (t n : ℚ) := by
  have h := t_eq_eps n
  have h1 := eps_lt_half (n + 1)
  rw [h]
  linarith

/-- Right end of the steering window: `t n ≤ 3ε_n + 1` (from `−1/2 ≤ ε_{n+1}`). -/
@[category API, AMS 11 68, ref "M4A3", group "weyl_a14_parity"]
lemma t_le (n : ℕ) : (t n : ℚ) ≤ 3 * eps n + 1 := by
  have h := t_eq_eps n
  have h1 := neg_half_le_eps (n + 1)
  rw [h]
  linarith

/-- **The parity letter determines the steering letter.**  The window `(3ε_n − 1, 3ε_n + 1]` has
length `2`, so it contains exactly one integer of each parity: any integer in it congruent to
`b n` mod 2 *is* `t n`.  Hence the pair `(ε n, b n)` determines `t n`, and the parity word drives
the `×(3/2)` dynamics. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem t_unique_of_parity {n : ℕ} {u : ℤ} (hpar : u % 2 = b n)
    (h1 : 3 * eps n - 1 < (u : ℚ)) (h2 : (u : ℚ) ≤ 3 * eps n + 1) : u = t n := by
  have hb := b_eq_t_emod_two n
  have hlt : ((u - t n : ℤ) : ℚ) < 2 := by
    have := lt_t n
    push_cast
    linarith
  have hgt : (-2 : ℚ) < ((u - t n : ℤ) : ℚ) := by
    have := t_le n
    push_cast
    linarith
  have h3 : u - t n < 2 := by exact_mod_cast hlt
  have h4 : -2 < u - t n := by exact_mod_cast hgt
  omega

/-- The **margin** at position `n`: the distance from `ε_n` to the nearest cell wall of the map
`ε ↦ t`, in the normalization in which the walls are `2` apart.  Closed form
`margin n = 1 − 2·|ε_{n+1}|`: the margin collapses exactly when `(3/2)^{n+1}` approaches a
half-odd-integer. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
def margin (n : ℕ) : ℚ := 1 - 2 * |eps (n + 1)|

/-- The margin is at most `1`; `μ = 1` is the best conceivable uniform margin. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
lemma margin_le_one (n : ℕ) : margin n ≤ 1 := by
  have := abs_nonneg (eps (n + 1))
  unfold margin
  linarith

/-- **A-priori margin floor** `margin n ≥ 2^{-n}` (`n ≥ 1`), in integer-certificate form.  The
numerator `R (n+1)` is odd and `|R (n+1)| < 2^n`, hence `|R (n+1)| ≤ 2^n − 1` and
`2^n · margin n = 2^n − |R (n+1)| ≥ 1`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem one_le_two_pow_mul_margin {n : ℕ} (hn : 1 ≤ n) : 1 ≤ 2 ^ n * margin n := by
  have hsucc : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hlow := neg_two_pow_le_two_mul_R (n + 1)
  have hhigh := two_mul_R_lt_two_pow (n + 1)
  have hodd := R_emod_two (n + 1) (by omega)
  have heven : (2 : ℤ) ^ n % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [show (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j by ring]
    exact Int.mul_emod_right 2 _
  rw [hsucc] at hlow hhigh
  have hRle : |R (n + 1)| ≤ 2 ^ n - 1 := by
    rcases abs_cases (R (n + 1)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hRQ : |((R (n + 1) : ℤ) : ℚ)| ≤ (2 : ℚ) ^ n - 1 := by
    have : ((|R (n + 1)| : ℤ) : ℚ) ≤ (((2 ^ n - 1 : ℤ)) : ℚ) := by exact_mod_cast hRle
    rwa [Int.cast_abs, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_one] at this
  have habs : |((R (n + 1) : ℤ) : ℚ)| = 2 ^ (n + 1) * |eps (n + 1)| := by
    rw [← two_pow_mul_eps (n + 1), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ (n + 1))]
  have hexp : (2 : ℚ) ^ n * margin n = 2 ^ n - 2 ^ (n + 1) * |eps (n + 1)| := by
    unfold margin
    rw [pow_succ]
    ring
  rw [hexp, ← habs]
  linarith

/-- **The margin is governed by a Mahler-type quantity**: `‖2·(3/2)^{n+1}‖ ≤ margin n`, so any lower
bound on the distance from `2·(3/2)^{n+1}` to the integers is a lower bound on the margin.  The
parity word is therefore controlled by a Diophantine statement of the kernel's own class — not by a
cheaper one. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem distToNearestInt_le_margin (n : ℕ) :
    (2 * (3 / 2 : ℚ) ^ (n + 1)).distToNearestInt ≤ margin n := by
  have hx : 2 * (3 / 2 : ℚ) ^ (n + 1) = 2 * eps (n + 1) + ((2 * m (n + 1) : ℤ) : ℚ) := by
    unfold eps
    push_cast
    ring
  rw [hx, Rat.distToNearestInt_add_intCast, show margin n = 1 - 2 * |eps (n + 1)| from rfl]
  rcases le_or_gt (0 : ℚ) (eps (n + 1)) with h | h
  · rw [abs_of_nonneg h]
    have h1 := Rat.distToNearestInt_le_abs_sub_intCast (2 * eps (n + 1)) 1
    have h2 := eps_lt_half (n + 1)
    rw [abs_of_nonpos (by push_cast; linarith : 2 * eps (n + 1) - ((1 : ℤ) : ℚ) ≤ 0)] at h1
    push_cast at h1
    linarith
  · rw [abs_of_neg h]
    have h1 := Rat.distToNearestInt_le_abs_sub_intCast (2 * eps (n + 1)) (-1)
    have h2 := neg_half_le_eps (n + 1)
    rw [abs_of_nonneg (by push_cast; linarith : (0 : ℚ) ≤ 2 * eps (n + 1) - ((-1 : ℤ) : ℚ))] at h1
    push_cast at h1
    linarith

/-- **One-step synchronization**: two positions with the same parity letter carry the same steering
letter as soon as their `ε`'s are closer than the margin.  This is the step T0.4's dichotomy did not
have. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem t_eq_of_b_eq_of_close {p q : ℕ} (hb : b p = b q)
    (h : 3 * |eps q - eps p| < margin p) : t p = t q := by
  have hA1 : eps p - eps q ≤ |eps q - eps p| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have hA2 : -|eps q - eps p| ≤ eps p - eps q := by
    rw [abs_sub_comm]
    exact neg_abs_le _
  have hE1 : eps (p + 1) ≤ |eps (p + 1)| := le_abs_self _
  have hE2 : -|eps (p + 1)| ≤ eps (p + 1) := neg_abs_le _
  have ht := t_eq_eps p
  have hm : margin p = 1 - 2 * |eps (p + 1)| := rfl
  rw [hm] at h
  refine t_unique_of_parity (n := q) (u := t p) ?_ ?_ ?_
  · rw [← b_eq_t_emod_two p, hb]
  · rw [ht]
    linarith
  · rw [ht]
    linarith

/-! ## Part 2 — propagation of a parity repetition -/

/-- **Propagation criterion.**  A `b`-repetition of length `k` is a `t`-repetition once the
`ε`-difference stays inside the margin at every step.  While the windows are synchronized the
difference expands by exactly `3/2` per step (`eps_sub_of_sync`), so the hypothesis is one margin
comparison per step. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem isRepetition_of_isBRepetition_of_margin {a c k : ℕ} (hb : IsBRepetition a c k)
    (h : ∀ i < k, 3 * ((3 : ℚ) / 2) ^ i * |eps c - eps a| < margin (a + i)) :
    IsRepetition a c k := by
  have key : ∀ j, j ≤ k → ∀ i < j, t (a + i) = t (c + i) := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ n ih =>
      intro hnk i hi
      rcases Nat.lt_or_ge i n with hin | hin
      · exact ih (by omega) i hin
      · have hin' : i = n := by omega
        subst hin'
        have hsync := ih (by omega)
        have hd := eps_sub_of_sync (a := a) (c := c) i hsync
        have habs : |eps (c + i) - eps (a + i)| = ((3 : ℚ) / 2) ^ i * |eps c - eps a| := by
          rw [hd, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ ((3 : ℚ) / 2) ^ i)]
        refine t_eq_of_b_eq_of_close (hb i (by omega)) ?_
        rw [habs, ← mul_assoc]
        exact h i (by omega)
  exact key k le_rfl

/-- **Unconditional propagation.**  With only the a-priori margin floor `2^{-n}`, a `b`-repetition
of length `k` at `1 ≤ a` whose endpoints satisfy `3^k·2^a·|ε_c − ε_a| < 1` is a `t`-repetition. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem isRepetition_of_isBRepetition_of_close {a c k : ℕ} (ha : 1 ≤ a)
    (hb : IsBRepetition a c k) (h : (3 : ℚ) ^ k * 2 ^ a * |eps c - eps a| < 1) :
    IsRepetition a c k := by
  refine isRepetition_of_isBRepetition_of_margin hb fun i hi => ?_
  have hm : (1 : ℚ) ≤ 2 ^ (a + i) * margin (a + i) := one_le_two_pow_mul_margin (by omega)
  have hP : (0 : ℚ) < 2 ^ (a + i) := by positivity
  have hpow : ((3 : ℚ) / 2) ^ i * 2 ^ (a + i) = 3 ^ i * 2 ^ a := by
    rw [div_pow, pow_add]
    field_simp
  have hA : (0 : ℚ) ≤ |eps c - eps a| := abs_nonneg _
  have hmono : (3 : ℚ) ^ (i + 1) ≤ 3 ^ k := by
    refine pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (0 : ℚ) ≤ (2 : ℚ) ^ a := by positivity
  have hkey : 3 * ((3 : ℚ) / 2) ^ i * |eps c - eps a| * 2 ^ (a + i) < 1 := by
    calc 3 * ((3 : ℚ) / 2) ^ i * |eps c - eps a| * 2 ^ (a + i)
        = (((3 : ℚ) / 2) ^ i * 2 ^ (a + i)) * (3 * |eps c - eps a|) := by ring
      _ = ((3 : ℚ) ^ i * 2 ^ a) * (3 * |eps c - eps a|) := by rw [hpow]
      _ = (3 : ℚ) ^ (i + 1) * 2 ^ a * |eps c - eps a| := by rw [pow_succ]; ring
      _ ≤ (3 : ℚ) ^ k * 2 ^ a * |eps c - eps a| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono h2) hA
      _ < 1 := h
  refine lt_of_mul_lt_mul_right ?_ hP.le
  calc 3 * ((3 : ℚ) / 2) ^ i * |eps c - eps a| * 2 ^ (a + i) < 1 := hkey
    _ ≤ 2 ^ (a + i) * margin (a + i) := hm
    _ = margin (a + i) * 2 ^ (a + i) := by ring

/-- **Propagation under a uniform margin.**  Grant a lower bound `μ` on the margin along the whole
window; then a `b`-repetition propagates as soon as `2·(3/2)^k·|ε_c − ε_a| < μ`.  The constant
`2·(3/2)^k` is the exact price of the criterion: it is what the pigeonhole of Part 4 has to beat. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem isRepetition_of_isBRepetition_of_uniform_margin {a c k : ℕ} {μ : ℚ}
    (hb : IsBRepetition a c k) (hμ : ∀ i < k, μ ≤ margin (a + i))
    (h : 2 * ((3 : ℚ) / 2) ^ k * |eps c - eps a| < μ) : IsRepetition a c k := by
  refine isRepetition_of_isBRepetition_of_margin hb fun i hi => ?_
  have hA : (0 : ℚ) ≤ |eps c - eps a| := abs_nonneg _
  have hstep : 3 * ((3 : ℚ) / 2) ^ i = 2 * ((3 : ℚ) / 2) ^ (i + 1) := by
    rw [pow_succ]
    ring
  have hmono : ((3 : ℚ) / 2) ^ (i + 1) ≤ ((3 : ℚ) / 2) ^ k :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc 3 * ((3 : ℚ) / 2) ^ i * |eps c - eps a|
      = 2 * ((3 : ℚ) / 2) ^ (i + 1) * |eps c - eps a| := by rw [hstep]
    _ ≤ 2 * ((3 : ℚ) / 2) ^ k * |eps c - eps a| :=
        mul_le_mul_of_nonneg_right (by linarith) hA
    _ < μ := h
    _ ≤ margin (a + i) := hμ i hi

/-- **Reach of the criterion.**  Against the trivial repulsion floor `|ε_c − ε_a| ≥ 2^{-c}` the
propagation criterion can fire only for pairs whose gap exceeds `k·log₂ 3`: `3^k·2^a < 2^c`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem lt_two_pow_of_sync_criterion {a c k : ℕ} (ha : 1 ≤ a) (hac : a < c)
    (h : (3 : ℚ) ^ k * 2 ^ a * |eps c - eps a| < 1) : 3 ^ k * 2 ^ a < 2 ^ c := by
  have hfl := one_le_two_pow_mul_abs_eps_sub ha hac
  have hA : (0 : ℚ) < |eps c - eps a| := by
    rcases (abs_nonneg (eps c - eps a)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, mul_zero] at hfl
      norm_num at hfl
  have hQ : (3 : ℚ) ^ k * 2 ^ a < 2 ^ c := by
    have : (3 : ℚ) ^ k * 2 ^ a * |eps c - eps a| < 2 ^ c * |eps c - eps a| := by linarith
    exact lt_of_mul_lt_mul_right this hA.le
  exact_mod_cast hQ

/-! ## Part 3 — what a pair of `b`-repetitions supplies -/

/-- **Sign law, positive direction**: if the windows synchronize for `j` steps and then the steering
letters jump up (`Δt ≥ 2`), then `ε_a < ε_c`.  The first desynchronization determines the *order* of
the two orbit points — and, in the `|Δt| = 2` branch, nothing else. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem eps_lt_eps_of_desync_pos {a c j : ℕ} (hsync : ∀ i < j, t (a + i) = t (c + i))
    (hd : 2 ≤ t (c + j) - t (a + j)) : eps a < eps c := by
  have hX := eps_sub_of_sync (a := a) (c := c) j hsync
  have hY := abs_lt.mp (abs_eps_sub_lt_one (c + j + 1) (a + j + 1))
  have hΔ : ((t (c + j) : ℚ)) - t (a + j)
      = 3 * (eps (c + j) - eps (a + j)) - 2 * (eps (c + j + 1) - eps (a + j + 1)) := by
    rw [t_eq_eps (c + j), t_eq_eps (a + j)]
    ring
  have h2 : (2 : ℚ) ≤ (t (c + j) : ℚ) - t (a + j) := by exact_mod_cast hd
  have hpos : 0 < eps (c + j) - eps (a + j) := by linarith [hY.1, hY.2]
  rw [hX] at hpos
  have h32 : (0 : ℚ) < ((3 : ℚ) / 2) ^ j := by positivity
  have hcd : 0 < eps c - eps a := by
    by_contra hle
    push Not at hle
    nlinarith
  linarith

/-- **Sign law, negative direction**: a downward first desynchronization (`Δt ≤ −2`) forces
`ε_c < ε_a`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem eps_lt_eps_of_desync_neg {a c j : ℕ} (hsync : ∀ i < j, t (a + i) = t (c + i))
    (hd : t (c + j) - t (a + j) ≤ -2) : eps c < eps a := by
  have hX := eps_sub_of_sync (a := a) (c := c) j hsync
  have hY := abs_lt.mp (abs_eps_sub_lt_one (c + j + 1) (a + j + 1))
  have hΔ : ((t (c + j) : ℚ)) - t (a + j)
      = 3 * (eps (c + j) - eps (a + j)) - 2 * (eps (c + j + 1) - eps (a + j + 1)) := by
    rw [t_eq_eps (c + j), t_eq_eps (a + j)]
    ring
  have h2 : (t (c + j) : ℚ) - t (a + j) ≤ -2 := by exact_mod_cast hd
  have hneg : eps (c + j) - eps (a + j) < 0 := by linarith [hY.1, hY.2]
  rw [hX] at hneg
  have h32 : (0 : ℚ) < ((3 : ℚ) / 2) ^ j := by positivity
  have hcd : eps c - eps a < 0 := by
    by_contra hle
    push Not at hle
    nlinarith
  linarith

/-- **The exact content of a `b`-repetition** (A14(iii)'s test, answered).  Either it is a
`t`-repetition (T0.1 applies), or it desynchronizes first at some `j < k`, and then:
`|Δt| = 4` **separates** the endpoints (`(2/3)^{j+1} ≤ |ε_c − ε_a|`, T0.4's quantitative branch),
while `|Δt| = 2` yields exactly one bit — the **order** of `ε_a` and `ε_c`.  Order relations on a
family of positions are always jointly satisfiable, so multi-scale pairs of `b`-repetitions cannot
be refuted by pair information alone. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem bRepetition_information {a c k : ℕ} (hb : IsBRepetition a c k) :
    IsRepetition a c k ∨ ∃ j < k, (∀ i < j, t (a + i) = t (c + i)) ∧ t (a + j) ≠ t (c + j) ∧
      (|t (c + j) - t (a + j)| = 4 ∧ (2 / 3 : ℚ) ^ (j + 1) ≤ |eps c - eps a| ∨
        |t (c + j) - t (a + j)| = 2 ∧ (eps a < eps c ↔ 0 < t (c + j) - t (a + j))) := by
  rcases b_repetition_dichotomy hb with h | ⟨j, hjk, hsync, hne, hpar⟩
  · exact Or.inl h
  refine Or.inr ⟨j, hjk, hsync, hne, ?_⟩
  obtain ⟨h1a, h1b⟩ := abs_le.mp (t_abs_le (a + j))
  obtain ⟨h2a, h2b⟩ := abs_le.mp (t_abs_le (c + j))
  have hne' : t (c + j) - t (a + j) ≠ 0 := by omega
  have hcases : t (c + j) - t (a + j) = -4 ∨ t (c + j) - t (a + j) = -2 ∨
      t (c + j) - t (a + j) = 2 ∨ t (c + j) - t (a + j) = 4 := by omega
  rcases hcases with hd | hd | hd | hd
  · exact Or.inl ⟨by rw [hd]; norm_num, desync_eps_lower hsync (by rw [hd]; norm_num)⟩
  · refine Or.inr ⟨by rw [hd]; norm_num, ?_⟩
    have horder := eps_lt_eps_of_desync_neg hsync (by omega)
    exact ⟨fun hlt => absurd hlt (not_lt.mpr horder.le), fun h0 => absurd h0 (by omega)⟩
  · refine Or.inr ⟨by rw [hd]; norm_num, ?_⟩
    have horder := eps_lt_eps_of_desync_pos hsync (by omega)
    exact ⟨fun _ => by omega, fun _ => horder⟩
  · exact Or.inl ⟨by rw [hd]; norm_num, desync_eps_lower hsync (by rw [hd]; norm_num)⟩

/-- **The pair information is finite.**  Every pair `2 ≤ a < c` has a first desynchronization index
`j`, and the constraint it carries is the single inequality `|ε_c − ε_a| ≤ (2/3)^j`.  Note the
hypothesis: only `2 ≤ a < c`.  A `b`-repetition at `(a, c)` of *every* length therefore adds nothing
to what an arbitrary pair already gives — which is why T0.2's growth-ceiling proof of aperiodicity
has no parity-word analogue, and the Morse–Hedlund floor `p_b(k) ≥ k+1` stays out of reach. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem exists_first_desync {a c : ℕ} (ha : 2 ≤ a) (hac : a < c) :
    ∃ j, (∀ i < j, t (a + i) = t (c + i)) ∧ t (a + j) ≠ t (c + j) ∧
      |eps c - eps a| ≤ (2 / 3 : ℚ) ^ j := by
  have hex : ∃ i, t (a + i) ≠ t (c + i) := by
    by_contra hall
    push Not at hall
    have hrep : ∀ k, IsRepetition a c k := fun k i _ => hall i
    have hbound := repetition_pow_le_nat ha hac (hrep (3 ^ (c + 1)))
    have hlt : (3 : ℕ) ^ (c + 1) < 2 ^ (3 ^ (c + 1)) := Nat.lt_two_pow_self
    have hmono : (2 : ℕ) ^ (3 ^ (c + 1)) ≤ 2 ^ (3 ^ (c + 1) + c + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨Nat.find hex, fun i hi => not_not.mp (Nat.find_min hex hi), Nat.find_spec hex, ?_⟩
  exact abs_eps_sub_le_of_repetition (fun i hi => not_not.mp (Nat.find_min hex hi))

/-! ## Part 4 — the surviving route and its two no-gos -/

/-- **`ε`-pigeonhole**: more than `B` positions force two of them with `B·|ε_x − ε_y| < 1`, since
all `ε`'s live in the unit window `[-1/2, 1/2)`. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem exists_close_pair {B : ℕ} (hB : 0 < B) {S : Finset ℕ} (hcard : B < S.card) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ (B : ℚ) * |eps x - eps y| < 1 := by
  have hBQ : (0 : ℚ) < B := by exact_mod_cast hB
  have hnn : ∀ n : ℕ, (0 : ℚ) ≤ (eps n + 1 / 2) * B := fun n =>
    mul_nonneg (by linarith [neg_half_le_eps n]) hBQ.le
  have hmaps : ∀ n ∈ S, ⌊(eps n + 1 / 2) * B⌋₊ ∈ Finset.range B := by
    intro n _
    rw [Finset.mem_range, Nat.floor_lt (hnn n)]
    have h1 : eps n + 1 / 2 < 1 := by linarith [eps_lt_half n]
    calc (eps n + 1 / 2) * B < 1 * B := by exact mul_lt_mul_of_pos_right h1 hBQ
      _ = B := by ring
  have hlt : (Finset.range B).card < S.card := by rwa [Finset.card_range]
  obtain ⟨x, hx, y, hy, hxy, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨x, hx, y, hy, hxy, ?_⟩
  have h1 := Nat.floor_le (hnn x)
  have h2 := Nat.lt_floor_add_one ((eps x + 1 / 2) * B)
  have h3 := Nat.floor_le (hnn y)
  have h4 := Nat.lt_floor_add_one ((eps y + 1 / 2) * B)
  rw [hfeq] at h1 h2
  have hdiff : |(eps x - eps y) * B| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  calc (B : ℚ) * |eps x - eps y| = |(eps x - eps y) * B| := by
        rw [abs_mul, abs_of_nonneg hBQ.le]
        ring
    _ < 1 := hdiff

/-- **The route.**  A set of positions in `[2, M]` sharing a length-`k` parity factor, of size
exceeding `3^k·2^M`, contains a genuine `t`-repetition: two of them are `ε`-close by
`exists_close_pair`, and `isRepetition_of_isBRepetition_of_close` propagates. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem exists_repetition_of_large_bClass {k M : ℕ} {S : Finset ℕ}
    (hS2 : ∀ n ∈ S, 2 ≤ n) (hSM : ∀ n ∈ S, n ≤ M)
    (hSb : ∀ x ∈ S, ∀ y ∈ S, IsBRepetition x y k)
    (hcard : 3 ^ k * 2 ^ M < S.card) :
    ∃ a c, 2 ≤ a ∧ a < c ∧ c ≤ M ∧ IsRepetition a c k := by
  have hBpos : 0 < 3 ^ k * 2 ^ M := by positivity
  obtain ⟨x, hx, y, hy, hxy, hclose⟩ := exists_close_pair hBpos hcard
  have hBcast : ((3 ^ k * 2 ^ M : ℕ) : ℚ) = (3 : ℚ) ^ k * 2 ^ M := by push_cast; ring
  rw [hBcast] at hclose
  have main : ∀ p q : ℕ, p ∈ S → q ∈ S → p < q →
      (3 : ℚ) ^ k * 2 ^ M * |eps q - eps p| < 1 →
      ∃ a c, 2 ≤ a ∧ a < c ∧ c ≤ M ∧ IsRepetition a c k := by
    intro p q hp hq hpq hlt
    refine ⟨p, q, hS2 p hp, hpq, hSM q hq, ?_⟩
    refine isRepetition_of_isBRepetition_of_close (by have := hS2 p hp; omega)
      (hSb p hp q hq) ?_
    have h2p : (2 : ℚ) ^ p ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) (hSM p hp)
    have hA : (0 : ℚ) ≤ |eps q - eps p| := abs_nonneg _
    have h3 : (0 : ℚ) ≤ (3 : ℚ) ^ k := by positivity
    calc (3 : ℚ) ^ k * 2 ^ p * |eps q - eps p|
        ≤ (3 : ℚ) ^ k * 2 ^ M * |eps q - eps p| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2p h3) hA
      _ < 1 := hlt
  rcases Nat.lt_or_ge x y with h | h
  · exact main x y hx hy h (by rwa [abs_sub_comm] at hclose)
  · exact main y x hy hx (by omega) hclose

/-- The route's conclusion: a parity class large enough to fire forces the T0.1 growth ceiling
`41·k ≤ 24·M + 24`, so it can only produce a contradiction inside that window. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem bClass_forces_window {k M : ℕ} {S : Finset ℕ}
    (hS2 : ∀ n ∈ S, 2 ≤ n) (hSM : ∀ n ∈ S, n ≤ M)
    (hSb : ∀ x ∈ S, ∀ y ∈ S, IsBRepetition x y k)
    (hcard : 3 ^ k * 2 ^ M < S.card) : 41 * k ≤ 24 * M + 24 := by
  obtain ⟨a, c, ha, hac, hcM, hrep⟩ := exists_repetition_of_large_bClass hS2 hSM hSb hcard
  have := repetition_linear_bound ha hac hrep
  omega

/-- **The route under a uniform margin.**  With a global margin bound `μ > 0`, a parity class of
more than `B` positions in `[2, M]` fires as soon as `B ≥ 2·(3/2)^k/μ`, and again the conclusion is
the T0.1 growth ceiling.  This pins the demand constant: `2·(3/2)^k/μ` positions. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem bClass_forces_window_of_uniform_margin {k M B : ℕ} {μ : ℚ} (hμ0 : 0 < μ)
    (hμ : ∀ n, μ ≤ margin n) (hB : 0 < B) (hBμ : 2 * (3 : ℚ) ^ k ≤ μ * (2 ^ k * B))
    {S : Finset ℕ} (hS2 : ∀ n ∈ S, 2 ≤ n) (hSM : ∀ n ∈ S, n ≤ M)
    (hSb : ∀ x ∈ S, ∀ y ∈ S, IsBRepetition x y k) (hcard : B < S.card) :
    41 * k ≤ 24 * M + 24 := by
  obtain ⟨x, hx, y, hy, hxy, hclose⟩ := exists_close_pair hB hcard
  have hpow2 : (0 : ℚ) < 2 ^ k := by positivity
  have hkey : 2 * ((3 : ℚ) / 2) ^ k ≤ μ * B := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ hpow2]
    calc 2 * (3 : ℚ) ^ k ≤ μ * (2 ^ k * B) := hBμ
      _ = μ * B * 2 ^ k := by ring
  have main : ∀ p q : ℕ, p ∈ S → q ∈ S → p < q → (B : ℚ) * |eps q - eps p| < 1 →
      41 * k ≤ 24 * M + 24 := by
    intro p q hp hq hpq hlt
    have hA : (0 : ℚ) ≤ |eps q - eps p| := abs_nonneg _
    have hrep : IsRepetition p q k := by
      refine isRepetition_of_isBRepetition_of_uniform_margin (hSb p hp q hq)
        (fun i _ => hμ (p + i)) ?_
      calc 2 * ((3 : ℚ) / 2) ^ k * |eps q - eps p| ≤ μ * B * |eps q - eps p| :=
            mul_le_mul_of_nonneg_right hkey hA
        _ = μ * ((B : ℚ) * |eps q - eps p|) := by ring
        _ < μ * 1 := by exact mul_lt_mul_of_pos_left hlt hμ0
        _ = μ := mul_one _
    have hbd := repetition_linear_bound (hS2 p hp) hpq hrep
    have := hSM q hq
    omega
  rcases Nat.lt_or_ge x y with h | h
  · exact main x y hx hy h (by rwa [abs_sub_comm] at hclose)
  · exact main y x hy hx (by omega) hclose

/-! ### The no-gos -/

/-- `2·2^n ≤ 3^n` for `n ≥ 2`. -/
private lemma two_mul_two_pow_le : ∀ n : ℕ, 2 ≤ n → 2 * 2 ^ n ≤ 3 ^ n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by norm_num)
  | succ m ih =>
    intro hn
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hm1 : m = 1 := by omega
      subst hm1
      norm_num
    · have h := ih hm
      calc 2 * 2 ^ (m + 1) = 2 * (2 * 2 ^ m) := by ring
        _ ≤ 2 * 3 ^ m := by omega
        _ ≤ 3 ^ (m + 1) := by rw [pow_succ]; omega

/-- `k·2^k ≤ 3^k`: the linear window is always below the exponential cell budget. -/
private lemma mul_two_pow_le_three_pow (k : ℕ) : k * 2 ^ k ≤ 3 ^ k := by
  induction k with
  | zero => simp
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl <;> norm_num
    · have h2 := two_mul_two_pow_le m hm
      calc (m + 1) * 2 ^ (m + 1) = 2 * (m * 2 ^ m) + 2 * 2 ^ m := by ring
        _ ≤ 2 * 3 ^ m + 3 ^ m := by linarith
        _ = 3 ^ (m + 1) := by rw [pow_succ]; ring

/-- **No-go 1 — the route has no window at all.**  The positions available inside `[2, M]` never
reach the demand `3^k·2^M` of `exists_repetition_of_large_bClass`, for any `k` and any `M`: the
a-priori margin floor degrades along the window faster than the pigeonhole gains. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem bRoute_never_fires {k M : ℕ} {S : Finset ℕ} (hS2 : ∀ n ∈ S, 2 ≤ n)
    (hSM : ∀ n ∈ S, n ≤ M) : S.card ≤ 3 ^ k * 2 ^ M := by
  have hsub : S ⊆ Finset.Icc 2 M := fun n hn => Finset.mem_Icc.mpr ⟨hS2 n hn, hSM n hn⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  calc S.card ≤ M + 1 - 2 := hcard
    _ ≤ M := by omega
    _ ≤ 2 ^ M := (Nat.lt_two_pow_self).le
    _ ≤ 3 ^ k * 2 ^ M := Nat.le_mul_of_pos_left _ (by positivity)

/-- **No-go 2, arithmetic core.**  Inside the T0.1 window `24·M + 24 < 41·k` — the only range in
which a length-`k` `t`-repetition is a contradiction — the number of available positions always
satisfies `2^k·M < 2·3^k`, i.e. `M < 2·(3/2)^k`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem window_lt_perfect_demand {k M : ℕ} (h : 24 * M + 24 < 41 * k) : 2 ^ k * M < 2 * 3 ^ k := by
  have hM : M < 2 * k := by omega
  have hpos : (0 : ℕ) < 2 ^ k := by positivity
  have hk := mul_two_pow_le_three_pow k
  calc 2 ^ k * M < 2 ^ k * (2 * k) := mul_lt_mul_of_pos_left hM hpos
    _ = 2 * (k * 2 ^ k) := by ring
    _ ≤ 2 * 3 ^ k := Nat.mul_le_mul le_rfl hk

/-- **No-go 2 — and it is not the margin's fault.**  Grant a *uniform* margin `μ > 0`; by
`margin_le_one` the best conceivable value is `μ = 1`, and the pigeonhole then still demands
`B ≥ 2·(3/2)^k/μ ≥ 2·(3/2)^k` positions.  Inside the T0.1 window that demand exceeds the entire
window: `M < B`.  Exponential demand against a linear window, at every `k`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem uniform_margin_route_vacuous {k M B : ℕ} {μ : ℚ} (hμ1 : μ ≤ 1)
    (hBμ : 2 * (3 : ℚ) ^ k ≤ μ * (2 ^ k * B)) (hwin : 24 * M + 24 < 41 * k) : M < B := by
  have hpow : (0 : ℚ) ≤ 2 ^ k * (B : ℚ) := by positivity
  have hle := mul_le_of_le_one_left hpow hμ1
  have hQ : 2 * (3 : ℚ) ^ k ≤ 2 ^ k * (B : ℚ) := le_trans hBμ hle
  have hN : 2 * 3 ^ k ≤ 2 ^ k * B := by exact_mod_cast hQ
  have hw := window_lt_perfect_demand hwin
  exact lt_of_mul_lt_mul_left (lt_of_lt_of_le hw hN) (Nat.zero_le _)

/-- **No-go 2, in the form the route consumes.**  Inside the T0.1 window no parity class can reach
the demand of `bClass_forces_window_of_uniform_margin`, whatever uniform margin is granted.  With
`bRoute_never_fires` this closes A14(iii)'s multi-scale test: the pigeonhole never fires, and the
pair information (Part 3) is order data, which is never contradictory. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem uniform_margin_route_never_fires {k M B : ℕ} {μ : ℚ} (hμ1 : μ ≤ 1)
    (hBμ : 2 * (3 : ℚ) ^ k ≤ μ * (2 ^ k * B)) (hwin : 24 * M + 24 < 41 * k)
    {S : Finset ℕ} (hS2 : ∀ n ∈ S, 2 ≤ n) (hSM : ∀ n ∈ S, n ≤ M) : S.card ≤ B := by
  have hMB := uniform_margin_route_vacuous hμ1 hBμ hwin
  have hsub : S ⊆ Finset.Icc 2 M := fun n hn => Finset.mem_Icc.mpr ⟨hS2 n hn, hSM n hn⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  omega

/-! ## Part 5 — the parity-word complexity and the input that would suffice -/

/-- The length-`k` factor of the **parity** word at position `a`. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
def bFactor (a k : ℕ) : Fin k → ℤ := fun i => b (a + i)

/-- Two parity windows agree iff they are a `b`-repetition. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
lemma bFactor_eq_iff {a c k : ℕ} : bFactor a k = bFactor c k ↔ IsBRepetition a c k := by
  constructor
  · intro h i hik
    exact congrFun h ⟨i, hik⟩
  · intro h
    funext i
    exact h i i.isLt

/-- The set of parity factors is finite (letters in `{0, 1}`). -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
lemma bFactorSet_finite (k : ℕ) : (Set.range fun a : ℕ => bFactor a k).Finite := by
  refine Set.Finite.subset
    (Set.Finite.pi' (t := fun _ : Fin k => Set.Icc (0 : ℤ) 1)
      fun _ => Set.finite_Icc _ _) ?_
  rintro w ⟨a, rfl⟩
  intro i
  have h0 : (0 : ℤ) ≤ m (a + i) % 2 := Int.emod_nonneg _ (by norm_num)
  have h1 : m (a + i) % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  show bFactor a k i ∈ Set.Icc (0 : ℤ) 1
  rw [Set.mem_Icc]
  unfold bFactor b
  omega

/-- `p_b(k)`: the subword complexity of the parity word. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
noncomputable def bComplexity (k : ℕ) : ℕ :=
  (Set.range fun a : ℕ => bFactor a k).ncard

/-- **M4 for the parity word**, the open Table-E row: `p_b(k)/k → ∞`. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
def BSuperlinear : Prop := ∀ C : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → C * k < bComplexity k

/-- The parity word is a letter-to-letter image of the steering word, so `p_b ≤ p_T` — T0.1 says
nothing about `p_b`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem bComplexity_le_complexity (k : ℕ) : bComplexity k ≤ complexity k := by
  have himg : (Set.range fun a : ℕ => bFactor a k)
      = (fun w : Fin k → ℤ => fun i => w i % 2) '' (Set.range fun a : ℕ => factor a k) := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨factor a k, ⟨a, rfl⟩, by funext i; simp [bFactor, factor, b_eq_t_emod_two]⟩
    · rintro ⟨v, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by funext i; simp [bFactor, factor, b_eq_t_emod_two]⟩
  rw [bComplexity, himg, complexity]
  exact Set.ncard_image_le (factorSet_finite k)

/-- **The input that would suffice.**  M4 for the parity word follows from M4 for the steering word
together with a *uniform ratio bound* `p_T(k) ≤ B·p_b(k)` — boundedly many steering factors per
parity factor.  Part 4 prices that input: the parity factor pins the steering factor only at
`ε`-resolution `(2/3)^k`, so the honest count is exponential, not bounded. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_parity"]
theorem bSuperlinear_of_ratio_bound {B : ℕ}
    (hratio : ∀ k, complexity k ≤ B * bComplexity k) (hM4 : Superlinear) : BSuperlinear := by
  intro C
  obtain ⟨K, hK⟩ := hM4 (B * C)
  refine ⟨K, fun k hk => ?_⟩
  have h1 := hK k hk
  have h2 := hratio k
  have h3 : B * (C * k) < B * bComplexity k := by
    calc B * (C * k) = B * C * k := by ring
      _ < complexity k := h1
      _ ≤ B * bComplexity k := h2
  exact lt_of_mul_lt_mul_left h3 (Nat.zero_le _)

end TH
