/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.NumberTheory.Height.NumberField

@[expose] public section

/-!
# Heights of rational numbers: integer and coprime-fraction values

Mathlib computes the multiplicative/logarithmic Weil height of a rational number
as `max |num| den` (`Rat.mulHeight₁_eq_max`, `Rat.logHeight₁_eq_log_max`) and
evaluates it on positive natural casts (`Rat.logHeight₁_natCast`).  This file
adds the two evaluation lemmas missing for Baker–Wüstholz-style height
bookkeeping over `ℚ`:

* `Rat.mulHeight₁_intCast`, `Rat.logHeight₁_intCast` — the height of an integer:
  `H(n) = |n|`, `h(n) = log |n|` (the latter unconditionally, since
  `Real.log 0 = 0` matches `logHeight₁ 0 = 0`).
* `Rat.logHeight₁_div_natCast` — the height of a fraction in lowest terms with
  numerator at most the denominator: for `0 < A ≤ B` coprime,
  `h(A/B) = log B`.
-/

namespace Rat

/-- The multiplicative height of a nonzero integer, cast to `ℚ`, is its absolute
value. -/
theorem mulHeight₁_intCast {n : ℤ} (hn : n ≠ 0) :
    Height.mulHeight₁ (n : ℚ) = n.natAbs := by
  rw [Rat.mulHeight₁_eq_max, Rat.num_intCast, Rat.den_intCast]
  exact_mod_cast congrArg Nat.cast
    (Nat.max_eq_left (Int.one_le_abs (by exact_mod_cast hn) |>.trans_eq
      (Int.abs_eq_natAbs n) |> Int.ofNat_le.mp))

/-- The logarithmic height of an integer, cast to `ℚ`, is `log |n|`
(unconditionally: for `n = 0` both sides vanish since `Real.log 0 = 0`). -/
theorem logHeight₁_intCast (n : ℤ) :
    Height.logHeight₁ (n : ℚ) = Real.log |(n : ℝ)| := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Height.logHeight₁_zero]
  · rw [Rat.logHeight₁_eq_log_max, Rat.num_intCast, Rat.den_intCast]
    have h1 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
    rw [Nat.max_eq_left h1]
    congr 1
    rw [← Int.cast_natCast (R := ℝ), Int.natCast_natAbs, Int.cast_abs]

/-- The logarithmic height of a fraction `A/B` in lowest terms with
`0 < A ≤ B` is `log B`. -/
theorem logHeight₁_div_natCast {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (hcop : Nat.Coprime A B) :
    Height.logHeight₁ ((A : ℚ) / B) = Real.log B := by
  have hB : (0 : ℤ) < (B : ℤ) := by exact_mod_cast lt_of_lt_of_le hA hAB
  have hcop' : Nat.Coprime (A : ℤ).natAbs (B : ℤ).natAbs := by
    simpa [Int.natAbs_natCast] using hcop
  have hnum : ((A : ℚ) / B).num = (A : ℤ) := by
    have h := Rat.num_div_eq_of_coprime hB hcop'
    rwa [Int.cast_natCast, Int.cast_natCast] at h
  have hden : (((A : ℚ) / B).den : ℤ) = (B : ℤ) := by
    have h := Rat.den_div_eq_of_coprime hB hcop'
    rwa [Int.cast_natCast, Int.cast_natCast] at h
  have hden' : ((A : ℚ) / B).den = B := by exact_mod_cast hden
  rw [Rat.logHeight₁_eq_log_max, hnum, hden', Int.natAbs_natCast,
    Nat.max_eq_right hAB]

end Rat
