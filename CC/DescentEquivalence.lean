/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Terras
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The descent reformulation of the Collatz conjecture (Ter76)

This file records the folklore **descent equivalence**: for the compact Collatz map `T` (`CC.T`),

> **every `n > 1` eventually drops strictly below itself**  ⟺  **every `n > 1` eventually reaches `1`.**

In symbols, `descent_iff_reaches_one`:

> `(∀ n > 1, ∃ k, T^[k] n < n)  ↔  (∀ n > 1, ∃ k, T^[k] n = 1)`.

The right-hand side is the Collatz conjecture (restricted to `n > 1`, which loses nothing). The
point is that the equivalence itself is a **theorem of arithmetic, independent of whether Collatz
holds** — it turns a *global* convergence statement into a purely *local* "everyone eventually
drops" statement, which is why the reformulation is useful.

## Proof

* `descent_of_reaches_one` (⟸) is immediate: if `T^[k] n = 1` and `n > 1` then `T^[k] n = 1 < n`.
* `reaches_one_of_descent` (⟹) is strong induction on `n`. Given `n > 1`, descent yields some
  `m = T^[k₀] n < n`; on the positive integers `T` never produces `0`, so `m ≥ 1`. If `m = 1` we are
  done; otherwise `1 < m < n` and the induction hypothesis carries `m` — hence `n` — to `1`, using
  additivity `T_iter_add`.

Two hypotheses are load-bearing and are exactly what a sloppy statement of this equivalence gets
wrong: the domain must be the positive integers so the descent target satisfies `m ≥ 1`
(`T_iter_pos` supplies this), and `∃ k` must denote a genuine step. The latter is automatic here —
`T^[0] n = n` is never `< n`, and never `= 1` when `n > 1` — as recorded by `exists_descent_iff`
and `exists_reaches_one_iff`.

## Contents

* `reaches_one_of_descent`, `descent_of_reaches_one` — the two directions.
* `descent_iff_reaches_one` — the equivalence.
* `exists_descent_iff`, `exists_reaches_one_iff` — the `∃ k` / `∃ k ≥ 1` bridges.
* `total_stopping_time_ne_top_iff` — a `⊤`-characterisation mirroring `CC.stopping_time_ne_top_iff`.
* `finite_stopping_iff_finite_total_stopping` — the equivalence restated: every `n > 1` has a finite
  **stopping time** iff every `n > 1` has a finite **total stopping time**.

## References

* [Ter76] R. Terras, *A stopping time problem on the positive integers*, Acta Arith. 30 (1976).
  The stopping-time framing; the descent equivalence is standard folklore around it.
-/

namespace CC

/-- **The substantive direction (⟹).** If every `n > 1` eventually drops below itself, then every
`n > 1` eventually reaches `1`. Strong induction on `n`: the descent target is `≥ 1` (positivity of
`T`), so it is either `1` or a strictly smaller value carried to `1` by the induction hypothesis. -/
@[category research solved, AMS 11, ref "Ter76", group "collatz_descent"]
theorem reaches_one_of_descent
    (H : ∀ n, 1 < n → ∃ k, T_iter k n < n) :
    ∀ n, 1 < n → ∃ k, T_iter k n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    obtain ⟨k₀, hk₀⟩ := H n hn
    have hm_pos : 1 ≤ T_iter k₀ n := T_iter_pos (by omega) k₀
    rcases eq_or_lt_of_le hm_pos with hm1 | hm1
    · -- the orbit already hit `1`
      exact ⟨k₀, hm1.symm⟩
    · -- `1 < T_iter k₀ n < n`: carry the smaller value to `1`, then prepend the `k₀` steps
      obtain ⟨k₁, hk₁⟩ := IH (T_iter k₀ n) hk₀ hm1
      exact ⟨k₁ + k₀, by rw [T_iter_add]; exact hk₁⟩

/-- **The easy direction (⟸).** Reaching `1` is in particular dropping below any `n > 1`. -/
@[category research solved, AMS 11, ref "Ter76", group "collatz_descent"]
theorem descent_of_reaches_one
    (H : ∀ n, 1 < n → ∃ k, T_iter k n = 1) :
    ∀ n, 1 < n → ∃ k, T_iter k n < n := by
  intro n hn
  obtain ⟨k, hk⟩ := H n hn
  exact ⟨k, by rw [hk]; omega⟩

/-- **The descent equivalence.** For the compact Collatz map `T`, "every `n > 1` eventually drops
below itself" is equivalent to "every `n > 1` reaches `1`" (the Collatz conjecture). The equivalence
holds unconditionally — it does not presuppose Collatz. -/
@[category research solved, AMS 11, ref "Ter76", group "collatz_descent"]
theorem descent_iff_reaches_one :
    (∀ n, 1 < n → ∃ k, T_iter k n < n) ↔ (∀ n, 1 < n → ∃ k, T_iter k n = 1) :=
  ⟨reaches_one_of_descent, descent_of_reaches_one⟩

/-! ### `∃ k` versus `∃ k ≥ 1`, and the stopping-time restatement -/

/-- A descent below `n` is automatically a *positive*-step descent: `T^[0] n = n` is never `< n`. -/
@[category API, AMS 11, group "collatz_descent"]
theorem exists_descent_iff (n : ℕ) :
    (∃ k, T_iter k n < n) ↔ (∃ k, k ≥ 1 ∧ T_iter k n < n) := by
  constructor
  · rintro ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [show T_iter 0 n = n from rfl] at hk; omega
    · exact ⟨k, hpos, hk⟩
  · rintro ⟨k, _, hk⟩; exact ⟨k, hk⟩

/-- Reaching `1` from `n > 1` is automatically a *positive*-step event: `T^[0] n = n ≠ 1`. -/
@[category API, AMS 11, group "collatz_descent"]
theorem exists_reaches_one_iff {n : ℕ} (hn : 1 < n) :
    (∃ k, T_iter k n = 1) ↔ (∃ k, k ≥ 1 ∧ T_iter k n = 1) := by
  constructor
  · rintro ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [show T_iter 0 n = n from rfl] at hk; omega
    · exact ⟨k, hpos, hk⟩
  · rintro ⟨k, _, hk⟩; exact ⟨k, hk⟩

/-- The total stopping time of `n` is finite iff some positive iterate of `n` equals `1`. Mirrors
`CC.stopping_time_ne_top_iff` for `CC.total_stopping_time`. -/
@[category API, AMS 11, ref "Ter76", group "collatz_descent"]
theorem total_stopping_time_ne_top_iff (n : ℕ) :
    total_stopping_time n ≠ ⊤ ↔ ∃ k : ℕ, k ≥ 1 ∧ T_iter k n = 1 := by
  simp only [total_stopping_time]; constructor
  · intro h; split at h
    · assumption
    · exact absurd rfl h
  · intro ⟨k, hk1, hk⟩; split
    · exact WithTop.natCast_ne_top _
    · rename_i h; exact absurd ⟨k, hk1, hk⟩ h

/-- **The descent equivalence, in stopping-time form.** Every `n > 1` has a finite stopping time
(`stopping_time n ≠ ⊤`) iff every `n > 1` has a finite total stopping time
(`total_stopping_time n ≠ ⊤`). This is `descent_iff_reaches_one` transported across the
`⊤`-characterisations of the two stopping times. -/
@[category research solved, AMS 11, ref "Ter76", group "collatz_descent"]
theorem finite_stopping_iff_finite_total_stopping :
    (∀ n, 1 < n → stopping_time n ≠ ⊤) ↔ (∀ n, 1 < n → total_stopping_time n ≠ ⊤) := by
  constructor
  · intro H n hn
    rw [total_stopping_time_ne_top_iff, ← exists_reaches_one_iff hn]
    exact descent_iff_reaches_one.mp
      (fun m hm => (exists_descent_iff m).mpr ((stopping_time_ne_top_iff m).mp (H m hm))) n hn
  · intro H n hn
    rw [stopping_time_ne_top_iff, ← exists_descent_iff n]
    exact descent_iff_reaches_one.mpr
      (fun m hm => (exists_reaches_one_iff hm).mpr ((total_stopping_time_ne_top_iff m).mp (H m hm)))
      n hn

end CC
