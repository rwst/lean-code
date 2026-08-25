/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# The Tijdeman engine: `[3, ∞) ⊆ 𝒵`

[Dub06EO] Theorem 1(i), after Tijdeman — and the reusable nested-interval engine that
`plans/report-dubickas.html` §D.6 asks for (also `plans/plan-A12.html` Route A
groundwork).

Dubickas runs the classical construction on the *fractional-part* form of the definition:
the interval `[α kⱼ, α(kⱼ+β) - β]` has length `αβ - β = 1` for `β = 1/(α-1)`, so it
contains an integer, and the nested intervals `Iⱼ = [kⱼ α^{-j}, (kⱼ+β) α^{-j}]` give a
`ξ` with `{ξ αⁿ} ≤ 1/(α-1) < 1/2`.

We run it directly on the *even integral part* form, which makes the construction
explicit rather than a nested intersection: round up to the next **even** integer,

> `x 0 = 2`,   `x (n+1) = 2 ⌈α · x n / 2⌉`.

Then `α x n ≤ x (n+1) < α x n + 2`, and `α ≥ 3` is exactly what is needed for the
intervals `[x n / αⁿ, (x n + 1)/αⁿ)` to nest: the upper ends need `x (n+1) + 1 < α x n + α`,
and `α x n + 3 ≤ α x n + α`.  The witness is the supremum of the lower ends.  Every `x n`
is even by construction, so no parity bookkeeping is needed at all.

## Main results

* `SZ.greedy` — the even greedy sequence, and its two-sided step bound.
* `SZ.floor_greedy` — `⌊ξ αⁿ⌋ = greedy α n` for the constructed `ξ`.
* `SZ.mem_MahlerZ_of_three_le` — **[Dub06EO] Theorem 1(i)**: `3 ≤ α ⟹ α ∈ 𝒵`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336, Theorem 1(i).
* [Tij72] R. Tijdeman, *Note on Mahler's 3/2-problem*, K. Norske Vidensk. Selsk. Skr. **16**
  (1972), 1–4.
-/

namespace SZ

variable {α : ℝ}

/-- The **even greedy**: round `α · x n` up to the next even integer. -/
noncomputable def greedy (α : ℝ) : ℕ → ℤ
  | 0 => 2
  | (n + 1) => 2 * ⌈α * (greedy α n : ℝ) / 2⌉

@[simp, category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem greedy_zero (α : ℝ) : greedy α 0 = 2 := rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem greedy_succ (α : ℝ) (n : ℕ) :
    greedy α (n + 1) = 2 * ⌈α * (greedy α n : ℝ) / 2⌉ := rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem greedy_even (α : ℝ) (n : ℕ) : Even (greedy α n) := by
  cases n with
  | zero => exact ⟨1, by norm_num⟩
  | succ n => exact ⟨⌈α * (greedy α n : ℝ) / 2⌉, by rw [greedy_succ]; ring⟩

/-- The greedy never falls below `α` times its predecessor. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem le_greedy_succ (α : ℝ) (n : ℕ) :
    α * (greedy α n : ℝ) ≤ (greedy α (n + 1) : ℝ) := by
  have h := Int.le_ceil (α * (greedy α n : ℝ) / 2)
  rw [greedy_succ]; push_cast; linarith

/-- …and it overshoots by less than `2`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem greedy_succ_lt (α : ℝ) (n : ℕ) :
    (greedy α (n + 1) : ℝ) < α * (greedy α n : ℝ) + 2 := by
  have h := Int.ceil_lt_add_one (α * (greedy α n : ℝ) / 2)
  rw [greedy_succ]; push_cast; linarith

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem greedy_pos (hα : 3 ≤ α) (n : ℕ) : 0 < (greedy α n : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have := le_greedy_succ α n
    nlinarith

/-! ## The nested intervals -/

/-- Lower ends of the nested intervals. -/
noncomputable def gLo (α : ℝ) (n : ℕ) : ℝ := (greedy α n : ℝ) / α ^ n

/-- Upper ends of the nested intervals. -/
noncomputable def gHi (α : ℝ) (n : ℕ) : ℝ := ((greedy α n : ℝ) + 1) / α ^ n

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem gLo_mono (hα : 3 ≤ α) : Monotone (gLo α) := by
  have hα0 : (0 : ℝ) < α := by linarith
  refine monotone_nat_of_le_succ fun n => ?_
  rw [gLo, gLo, div_le_div_iff₀ (pow_pos hα0 n) (pow_pos hα0 (n + 1))]
  have h := le_greedy_succ α n
  have hp : (0 : ℝ) < α ^ n := pow_pos hα0 n
  calc (greedy α n : ℝ) * α ^ (n + 1) = (α * (greedy α n : ℝ)) * α ^ n := by ring
    _ ≤ (greedy α (n + 1) : ℝ) * α ^ n := mul_le_mul_of_nonneg_right h hp.le

/-- The upper ends drop strictly — this is exactly where `α ≥ 3` is spent: the greedy
overshoots by less than `2`, and `2 + 1 ≤ α`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem gHi_succ_lt (hα : 3 ≤ α) (n : ℕ) : gHi α (n + 1) < gHi α n := by
  have hα0 : (0 : ℝ) < α := by linarith
  rw [gHi, gHi, div_lt_div_iff₀ (pow_pos hα0 (n + 1)) (pow_pos hα0 n)]
  have h := greedy_succ_lt α n
  have hp : (0 : ℝ) < α ^ n := pow_pos hα0 n
  calc ((greedy α (n + 1) : ℝ) + 1) * α ^ n
      < (α * (greedy α n : ℝ) + α) * α ^ n :=
        mul_lt_mul_of_pos_right (by linarith) hp
    _ = ((greedy α n : ℝ) + 1) * α ^ (n + 1) := by ring

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem gHi_anti (hα : 3 ≤ α) : Antitone (gHi α) :=
  antitone_nat_of_succ_le fun n => (gHi_succ_lt hα n).le

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem gLo_lt_gHi (hα : 3 ≤ α) (n : ℕ) : gLo α n < gHi α n := by
  have hα0 : (0 : ℝ) < α := by linarith
  rw [gLo, gHi, div_lt_div_iff₀ (pow_pos hα0 n) (pow_pos hα0 n)]
  have hp : (0 : ℝ) < α ^ n := pow_pos hα0 n
  nlinarith

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem gLo_lt_gHi' (hα : 3 ≤ α) (n m : ℕ) : gLo α n < gHi α m := by
  rcases le_total n m with h | h
  · exact lt_of_le_of_lt (gLo_mono hα h) (gLo_lt_gHi hα m)
  · exact lt_of_lt_of_le (gLo_lt_gHi hα n) (gHi_anti hα h)

/-- The witness: the supremum of the lower ends. -/
noncomputable def tijdemanWitness (α : ℝ) : ℝ := ⨆ n : ℕ, gLo α n

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem gLo_bddAbove (hα : 3 ≤ α) : BddAbove (Set.range (gLo α)) := by
  refine ⟨gHi α 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (gLo_lt_gHi' hα n 0).le

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem gLo_le_witness (hα : 3 ≤ α) (n : ℕ) : gLo α n ≤ tijdemanWitness α :=
  le_ciSup (gLo_bddAbove hα) n

@[category API, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem witness_lt_gHi (hα : 3 ≤ α) (n : ℕ) : tijdemanWitness α < gHi α n :=
  lt_of_le_of_lt (ciSup_le fun k => (gLo_lt_gHi' hα k (n + 1)).le) (gHi_succ_lt hα n)

/-- **The floors of the witness orbit are the greedy sequence.** -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem floor_greedy (hα : 3 ≤ α) (n : ℕ) :
    ⌊tijdemanWitness α * α ^ n⌋ = greedy α n := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hp : (0 : ℝ) < α ^ n := pow_pos hα0 n
  have h1 := gLo_le_witness hα n
  have h2 := witness_lt_gHi hα n
  rw [gLo, div_le_iff₀ hp] at h1
  rw [gHi, lt_div_iff₀ hp] at h2
  rw [Int.floor_eq_iff]
  exact ⟨by linarith, by linarith⟩

/-- **[Dub06EO] Theorem 1(i)** (Tijdeman).  Every real `α ≥ 3` lies in `𝒵`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d6_tijdeman"]
theorem mem_MahlerZ_of_three_le (hα : 3 ≤ α) : α ∈ MahlerZ := by
  have hpos : 0 < tijdemanWitness α := by
    refine lt_of_lt_of_le ?_ (gLo_le_witness hα 0)
    rw [gLo]; norm_num
  refine mem_MahlerZ_of_floor_eq (by linarith) (ne_of_gt hpos) 0 (greedy α)
    (fun n _ => greedy_even α n) (fun n _ => floor_greedy hα n)

end SZ
