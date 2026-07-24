/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.InfiniteComplexity
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Base-`b` digits along the orbit `{ξ bⁿ}`

The base-`b` expansion of a real number, read **dynamically**: `fractDigit b ξ k = ⌊b·{ξ bᵏ}⌋`
is the `(k+1)`-st digit of `ξ`, and the shift on digit sequences corresponds to the map
`x ↦ {b·x}` on `[0,1)`.  This is the orbit-indexed companion of `Real.digits`
(`Mathlib/Analysis/Real/OfDigits.lean`), which reads the digits of a *fixed* `x ∈ [0,1)` off a
series; here the digits of *every* orbit point are available at once, which is what dynamical
arguments (Bugeaud's Theorem 3.1, Mahler's `Z`-numbers, normality) actually consume.

## Main results

* `fractDigit_lt` — digits lie in `{0, …, b-1}`.
* `fract_eq_fractDigit_add` — the defining recursion `{ξ bᵏ} = (aₖ + {ξ bᵏ⁺¹}) / b`, i.e. the
  base-`b` expansion conjugates `x ↦ {b·x}` to the shift.
* `abs_fract_sub_fract_le` — **agreement of the first `m` digits pins the orbit points to
  within `b^{-m}`**.
* `not_isEventuallyPeriodic_fractDigit` — the digit sequence of an irrational number is not
  eventually periodic (the converse direction of "eventually periodic ⟺ rational").
* `exists_leftSpecial_fractDigit` — combining the previous item with the infinite Morse–Hedlund
  theorem: for every `m` there are two orbit positions whose digits differ but whose next `m`
  digits agree.  This is the engine of `Bugeaud.theorem_3_1`.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  193, 2012, §3.1.
-/

open ForMathlib.SubwordComplexity

namespace Real

/-- The `k`-th **base-`b` digit** of `ξ`, read off the orbit point `{ξ bᵏ}`:
`fractDigit b ξ k = ⌊b·{ξ bᵏ}⌋`.  For `ξ ∈ [0,1)` this is the digit `a_{k+1}` of the classical
expansion `ξ = 0.a₁a₂…`. -/
noncomputable def fractDigit (b : ℕ) (ξ : ℝ) (k : ℕ) : ℕ :=
  ⌊(b : ℝ) * Int.fract (ξ * (b : ℝ) ^ k)⌋₊

variable {b : ℕ} {ξ : ℝ}

/-- Digits lie in `{0, 1, …, b-1}`. -/
theorem fractDigit_lt (hb : 0 < b) (ξ : ℝ) (k : ℕ) : fractDigit b ξ k < b := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have h0 : (0 : ℝ) ≤ (b : ℝ) * Int.fract (ξ * (b : ℝ) ^ k) :=
    mul_nonneg hbpos.le (Int.fract_nonneg _)
  rw [fractDigit, Nat.floor_lt h0]
  have h1 := Int.fract_lt_one (ξ * (b : ℝ) ^ k)
  nlinarith

/-- The base-`b` expansion conjugates `x ↦ {b·x}` to the shift: the orbit point one step later
is the fractional part of `b` times the current one. -/
theorem fract_mul_pow_succ (b : ℕ) (ξ : ℝ) (k : ℕ) :
    Int.fract (ξ * (b : ℝ) ^ (k + 1)) = Int.fract ((b : ℝ) * Int.fract (ξ * (b : ℝ) ^ k)) := by
  have h : (b : ℝ) * Int.fract (ξ * (b : ℝ) ^ k)
      = ξ * (b : ℝ) ^ (k + 1) - ((b * ⌊ξ * (b : ℝ) ^ k⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h, Int.fract_sub_intCast]

/-- **The digit recursion** `{ξ bᵏ} = (aₖ + {ξ bᵏ⁺¹}) / b`. -/
theorem fract_eq_fractDigit_add (hb : 0 < b) (ξ : ℝ) (k : ℕ) :
    Int.fract (ξ * (b : ℝ) ^ k)
      = ((fractDigit b ξ k : ℝ) + Int.fract (ξ * (b : ℝ) ^ (k + 1))) / b := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have h0 : (0 : ℝ) ≤ (b : ℝ) * Int.fract (ξ * (b : ℝ) ^ k) :=
    mul_nonneg hbpos.le (Int.fract_nonneg _)
  have hcast : ((fractDigit b ξ k : ℕ) : ℝ) = (⌊(b : ℝ) * Int.fract (ξ * (b : ℝ) ^ k)⌋ : ℤ) := by
    rw [fractDigit]
    exact natCast_floor_eq_intCast_floor h0
  rw [fract_mul_pow_succ, hcast, Int.floor_add_fract]
  field_simp

/-- **Agreement of the first `m` digits pins the orbit points to within `b^{-m}`.** -/
theorem abs_fract_sub_fract_le (hb : 1 < b) (ξ : ℝ) :
    ∀ (m i j : ℕ), (∀ t, t < m → fractDigit b ξ (i + t) = fractDigit b ξ (j + t)) →
      |Int.fract (ξ * (b : ℝ) ^ i) - Int.fract (ξ * (b : ℝ) ^ j)| ≤ (1 / (b : ℝ)) ^ m := by
  have hb0 : 0 < b := by omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  intro m
  induction m with
  | zero =>
    intro i j _
    have hi0 := Int.fract_nonneg (ξ * (b : ℝ) ^ i)
    have hi1 := Int.fract_lt_one (ξ * (b : ℝ) ^ i)
    have hj0 := Int.fract_nonneg (ξ * (b : ℝ) ^ j)
    have hj1 := Int.fract_lt_one (ξ * (b : ℝ) ^ j)
    rw [pow_zero, abs_le]
    constructor <;> linarith
  | succ m ih =>
    intro i j h
    have hd : fractDigit b ξ i = fractDigit b ξ j := by
      have := h 0 (by omega); simpa using this
    have hnext : ∀ t, t < m → fractDigit b ξ (i + 1 + t) = fractDigit b ξ (j + 1 + t) := by
      intro t ht
      have := h (t + 1) (by omega)
      rw [show i + (t + 1) = i + 1 + t by omega, show j + (t + 1) = j + 1 + t by omega] at this
      exact this
    have hIH := ih (i + 1) (j + 1) hnext
    rw [fract_eq_fractDigit_add hb0 ξ i, fract_eq_fractDigit_add hb0 ξ j, hd]
    have hsplit : ((fractDigit b ξ j : ℝ) + Int.fract (ξ * (b : ℝ) ^ (i + 1))) / b
        - ((fractDigit b ξ j : ℝ) + Int.fract (ξ * (b : ℝ) ^ (j + 1))) / b
        = (Int.fract (ξ * (b : ℝ) ^ (i + 1)) - Int.fract (ξ * (b : ℝ) ^ (j + 1))) / b := by
      field_simp
      ring
    rw [hsplit, abs_div, abs_of_pos hbpos, div_le_iff₀ hbpos]
    calc |Int.fract (ξ * (b : ℝ) ^ (i + 1)) - Int.fract (ξ * (b : ℝ) ^ (j + 1))|
        ≤ (1 / (b : ℝ)) ^ m := hIH
      _ = (1 / (b : ℝ)) ^ (m + 1) * b := by
          rw [pow_succ (1 / (b : ℝ)) m]
          field_simp

/-- **The digit sequence of an irrational number is not eventually periodic.** -/
theorem not_isEventuallyPeriodic_fractDigit (hb : 1 < b) (hξ : Irrational ξ) :
    ¬ IsEventuallyPeriodic (fractDigit b ξ) := by
  have hb0 : 0 < b := by omega
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by positivity
  rintro ⟨N, p, hp, hper⟩
  -- the digits from `N` and from `N + p` agree forever
  have hagree : ∀ m t, t < m → fractDigit b ξ (N + t) = fractDigit b ξ (N + p + t) := by
    intro m t _
    have := hper (N + t) (by omega)
    rw [show N + t + p = N + p + t by omega] at this
    exact this.symm
  -- hence the two orbit points coincide
  have hzero : |Int.fract (ξ * (b : ℝ) ^ N) - Int.fract (ξ * (b : ℝ) ^ (N + p))| ≤ 0 := by
    have hlim : Filter.Tendsto (fun m : ℕ => (1 / (b : ℝ)) ^ m) Filter.atTop (nhds 0) := by
      refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
      rw [div_lt_one hbpos]
      exact hb1
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun m => ?_)
    exact abs_fract_sub_fract_le hb ξ m N (N + p) (hagree m)
  have heq : Int.fract (ξ * (b : ℝ) ^ N) = Int.fract (ξ * (b : ℝ) ^ (N + p)) := by
    have := abs_nonneg (Int.fract (ξ * (b : ℝ) ^ N) - Int.fract (ξ * (b : ℝ) ^ (N + p)))
    have h0 : |Int.fract (ξ * (b : ℝ) ^ N) - Int.fract (ξ * (b : ℝ) ^ (N + p))| = 0 := by linarith
    have := abs_eq_zero.mp h0
    linarith
  -- which makes `ξ` rational
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp heq
  have hc : ((b : ℤ) ^ N - (b : ℤ) ^ (N + p)) ≠ 0 := by
    have hlt : (b : ℤ) ^ N < (b : ℤ) ^ (N + p) := by
      apply pow_lt_pow_right₀ (by exact_mod_cast hb)
      omega
    omega
  have hmul : (((b : ℤ) ^ N - (b : ℤ) ^ (N + p) : ℤ) : ℝ) * ξ = (z : ℝ) := by
    push_cast
    linarith [hz]
  exact (Int.not_irrational z) (hmul ▸ Irrational.intCast_mul hξ hc)

/-- **Left-special digits.**  For an irrational `ξ` and every `m` there are two orbit positions
whose digits differ but whose next `m` digits agree: the common block has two distinct left
extensions.  (Infinite Morse–Hedlund applied to the digit sequence.) -/
theorem exists_leftSpecial_fractDigit (hb : 1 < b) (hξ : Irrational ξ) (m : ℕ) :
    ∃ i j : ℕ, fractDigit b ξ i ≠ fractDigit b ξ j ∧
      ∀ t, t < m → fractDigit b ξ (i + 1 + t) = fractDigit b ξ (j + 1 + t) := by
  have hb0 : 0 < b := by omega
  -- package the digits as a word over the finite alphabet `Fin b`
  set w : ℕ → Fin b := fun k => ⟨fractDigit b ξ k, fractDigit_lt hb0 ξ k⟩ with hw
  have hwval : ∀ k, (w k : ℕ) = fractDigit b ξ k := fun k => rfl
  have hnp : ¬ IsEventuallyPeriodic w := by
    rintro ⟨N, p, hp, hper⟩
    refine not_isEventuallyPeriodic_fractDigit hb hξ ⟨N, p, hp, fun k hk => ?_⟩
    have := hper k hk
    rw [← hwval, ← hwval, this]
  obtain ⟨i, j, hne, hagree⟩ := exists_leftSpecial_of_not_isEventuallyPeriodic hnp m
  refine ⟨i, j, ?_, fun t ht => ?_⟩
  · intro hcon
    exact hne (Fin.ext (by rw [hwval, hwval, hcon]))
  · have := hagree t ht
    rw [← hwval, ← hwval, this]

end Real
