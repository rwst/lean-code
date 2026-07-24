/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Analysis.Real.FractDigits
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud, Chapter 3, §3.1 — the integer case

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), **Theorem 3.1**:

> Let `b ≥ 2` be an integer. For any irrational real number `ξ`, the numbers `{ξ bⁿ}`, `n ≥ 0`,
> cannot all lie in an interval of length strictly smaller than `1/b`.

Formalised here as `Bugeaud.theorem_3_1`: any `Set.Icc s (s + t)` containing the whole orbit has
`t ≥ 1/b`; `Bugeaud.theorem_3_1'` is the literal contrapositive.

## Proof (Bugeaud, pp. 49–50)

Write `aₖ = ⌊b·{ξ bᵏ}⌋` for the base-`b` digits (`Real.fractDigit`).  Since `ξ` is irrational the
digit sequence is not eventually periodic (`Real.not_isEventuallyPeriodic_fractDigit`), so by the
Morse–Hedlund complexity floor it has, for every `m`, a length-`m` factor with **two distinct
left extensions** (`Real.exists_leftSpecial_fractDigit`): positions `i, j` with `aᵢ ≠ a_j` but
`a_{i+1+t} = a_{j+1+t}` for `t < m`.  Agreeing digits pin the two orbit points to within `b^{-m}`
(`Real.abs_fract_sub_fract_le`), so the digit recursion `{ξ bᵏ} = (aₖ + {ξ bᵏ⁺¹})/b` gives

  `{ξ bⁱ} - {ξ bʲ} ≥ (1 - b^{-m}) / b`,

and letting `m → ∞` yields the bound `1/b`.

Two deviations from the book, both simplifications:

* Bugeaud first argues that a digit gap `a_{j+1} - a_{i+1} ≥ 2` settles the matter outright, and
  then assumes without loss of generality that the digits lie in `{ℓ, ℓ+1}` so that the word is
  binary and Theorem A.3 applies.  Working over the alphabet `Fin b` directly, that reduction is
  unnecessary: *any* pair of distinct digits gives the estimate above.
* The complexity floor is used in its left-special form
  (`ForMathlib.SubwordComplexity.exists_leftSpecial_of_not_isEventuallyPeriodic`) rather than as
  the inequality `p(m) ≥ m + 1`.

## Sharpness, and the necessity of irrationality

* Irrationality is necessary: `b/(b²-1) = 0·101010…` has its whole orbit inside an interval of
  length `1/(b+1) < 1/b` (`Bugeaud.fract_rat_orbit`, `Bugeaud.rat_orbit_mem_Icc`).
* The constant `1/b` is best possible: Sturmian digit sequences (Bugeaud's Theorem A.4) give
  irrational `ξ` whose orbit lies in a semi-open interval of length exactly `1/b`.  Recorded as
  the cited `axiom exists_irrational_orbit_subset_Ico`; a full treatment needs the Sturmian
  machinery of Appendix A, and the description of *all* such `ξ` is Theorem 2.1 of [AG10].

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  in Mathematics 193, Cambridge University Press, 2012, §3.1 (Theorem 3.1) and Appendix A
  (Theorems A.3, A.4).
* [AG10] J.-P. Allouche, A. Glen, *Distribution modulo 1 and the lexicographic world*, Ann. Sci.
  Math. Québec **33** (2009), 125–143 — reference [161] of [Bug12], Theorem 2.1.
-/

namespace Bugeaud

open Real ForMathlib.SubwordComplexity

variable {b : ℕ} {ξ : ℝ}

/-! ## The core estimate -/

/-- Two orbit points whose digits differ at the head and agree for the next `m` places are at
least `(1 - b^{-m})/b` apart — the quantitative heart of Theorem 3.1. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_1"]
theorem sub_ge_of_fractDigit_lt (hb : 2 ≤ b) (ξ : ℝ) {m i j : ℕ}
    (hd : fractDigit b ξ j < fractDigit b ξ i)
    (hagree : ∀ t, t < m → fractDigit b ξ (i + 1 + t) = fractDigit b ξ (j + 1 + t)) :
    (1 - (1 / (b : ℝ)) ^ m) / b
      ≤ Int.fract (ξ * (b : ℝ) ^ i) - Int.fract (ξ * (b : ℝ) ^ j) := by
  have hb0 : 0 < b := by omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  have htail := abs_fract_sub_fract_le (by omega : 1 < b) ξ m (i + 1) (j + 1) hagree
  have h2 : -((1 / (b : ℝ)) ^ m)
      ≤ Int.fract (ξ * (b : ℝ) ^ (i + 1)) - Int.fract (ξ * (b : ℝ) ^ (j + 1)) :=
    (abs_le.mp htail).1
  have h1 : (1 : ℝ) ≤ (fractDigit b ξ i : ℝ) - (fractDigit b ξ j : ℝ) := by
    have : ((fractDigit b ξ j : ℕ) : ℝ) + 1 ≤ ((fractDigit b ξ i : ℕ) : ℝ) := by
      exact_mod_cast hd
    linarith
  rw [fract_eq_fractDigit_add hb0 ξ i, fract_eq_fractDigit_add hb0 ξ j]
  rw [div_sub_div_same, div_le_div_iff_of_pos_right hbpos]
  linarith

/-- For every `m`, the orbit `({ξ bⁿ})` contains two points at distance `≥ (1 - b^{-m})/b`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_1"]
theorem exists_fract_sub_ge (hb : 2 ≤ b) (hξ : Irrational ξ) (m : ℕ) :
    ∃ i j : ℕ, (1 - (1 / (b : ℝ)) ^ m) / b
      ≤ Int.fract (ξ * (b : ℝ) ^ i) - Int.fract (ξ * (b : ℝ) ^ j) := by
  obtain ⟨i, j, hne, hagree⟩ := exists_leftSpecial_fractDigit (by omega : 1 < b) hξ m
  rcases Nat.lt_or_ge (fractDigit b ξ i) (fractDigit b ξ j) with hlt | hge
  · refine ⟨j, i, sub_ge_of_fractDigit_lt hb ξ hlt fun t ht => (hagree t ht).symm⟩
  · exact ⟨i, j, sub_ge_of_fractDigit_lt hb ξ (lt_of_le_of_ne hge (Ne.symm hne)) hagree⟩

/-! ## Theorem 3.1 -/

/-- **Theorem 3.1** (Bugeaud). Let `b ≥ 2` be an integer and `ξ` irrational. Then the numbers
`{ξ bⁿ}`, `n ≥ 0`, cannot all lie in an interval of length strictly smaller than `1/b`: any
interval `[s, s+t]` containing the whole orbit has `t ≥ 1/b`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_1",
  formal_uses exists_fract_sub_ge]
theorem theorem_3_1 (hb : 2 ≤ b) (hξ : Irrational ξ) {s t : ℝ}
    (h : ∀ n : ℕ, Int.fract (ξ * (b : ℝ) ^ n) ∈ Set.Icc s (s + t)) : 1 / (b : ℝ) ≤ t := by
  have hb0 : 0 < b := by omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hstep : ∀ m : ℕ, (1 - (1 / (b : ℝ)) ^ m) / b ≤ t := by
    intro m
    obtain ⟨i, j, hij⟩ := exists_fract_sub_ge hb hξ m
    have hi := (Set.mem_Icc.mp (h i)).2
    have hj := (Set.mem_Icc.mp (h j)).1
    linarith
  have hlim : Filter.Tendsto (fun m : ℕ => (1 - (1 / (b : ℝ)) ^ m) / b) Filter.atTop
      (nhds ((1 - 0) / b)) := by
    refine Filter.Tendsto.div_const ?_ (b : ℝ)
    refine Filter.Tendsto.const_sub 1 ?_
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [div_lt_one hbpos]
    exact hb1
  have := le_of_tendsto hlim (Filter.Eventually.of_forall hstep)
  simpa using this

/-- **Theorem 3.1**, literal form: no interval of length `< 1/b` contains the whole orbit. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_1",
  formal_uses theorem_3_1]
theorem theorem_3_1' (hb : 2 ≤ b) (hξ : Irrational ξ) {s t : ℝ} (ht : t < 1 / (b : ℝ)) :
    ∃ n : ℕ, Int.fract (ξ * (b : ℝ) ^ n) ∉ Set.Icc s (s + t) := by
  by_contra hcon
  push Not at hcon
  exact absurd (theorem_3_1 hb hξ hcon) (not_le.mpr ht)

/-! ## Irrationality is necessary -/

/-- The orbit of the rational number `b/(b²-1) = 0·101010…` alternates between `b/(b²-1)` and
`1/(b²-1)`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_1"]
theorem fract_rat_orbit (hb : 2 ≤ b) (n : ℕ) :
    Int.fract ((b : ℝ) / ((b : ℝ) ^ 2 - 1) * (b : ℝ) ^ n)
      = if Even n then (b : ℝ) / ((b : ℝ) ^ 2 - 1) else 1 / ((b : ℝ) ^ 2 - 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hc : (0 : ℝ) < (b : ℝ) ^ 2 - 1 := by nlinarith
  have hnn : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) ^ 2 - 1) := by positivity
  have hlt1 : (b : ℝ) / ((b : ℝ) ^ 2 - 1) < 1 := by
    rw [div_lt_one hc]; nlinarith
  have h1c : 1 / ((b : ℝ) ^ 2 - 1) < 1 := by
    rw [div_lt_one hc]; nlinarith
  induction n with
  | zero => simpa using Int.fract_eq_self.mpr ⟨hnn, hlt1⟩
  | succ n ih =>
    rw [Real.fract_mul_pow_succ, ih]
    by_cases hev : Even n
    · rw [if_pos hev, if_neg (by simp [Nat.even_add_one, hev])]
      have hb1 : (b : ℝ) * ((b : ℝ) / ((b : ℝ) ^ 2 - 1)) = 1 + 1 / ((b : ℝ) ^ 2 - 1) := by
        field_simp
        ring
      rw [hb1, Int.fract_one_add]
      exact Int.fract_eq_self.mpr ⟨div_nonneg zero_le_one hc.le, h1c⟩
    · rw [if_neg hev, if_pos (by simp [Nat.even_add_one, hev])]
      have hb1 : (b : ℝ) * (1 / ((b : ℝ) ^ 2 - 1)) = (b : ℝ) / ((b : ℝ) ^ 2 - 1) := by ring
      rw [hb1]
      exact Int.fract_eq_self.mpr ⟨hnn, hlt1⟩

/-- **Irrationality is necessary in Theorem 3.1.**  The whole orbit of the rational number
`b/(b²-1)` lies in an interval of length `1/(b+1)`, which is strictly smaller than `1/b`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_1",
  formal_uses fract_rat_orbit]
theorem rat_orbit_mem_Icc (hb : 2 ≤ b) (n : ℕ) :
    Int.fract ((b : ℝ) / ((b : ℝ) ^ 2 - 1) * (b : ℝ) ^ n)
      ∈ Set.Icc (1 / ((b : ℝ) ^ 2 - 1)) (1 / ((b : ℝ) ^ 2 - 1) + 1 / ((b : ℝ) + 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hc : (0 : ℝ) < (b : ℝ) ^ 2 - 1 := by nlinarith
  have hb1 : (0 : ℝ) < (b : ℝ) + 1 := by linarith
  have hsum : 1 / ((b : ℝ) ^ 2 - 1) + 1 / ((b : ℝ) + 1) = (b : ℝ) / ((b : ℝ) ^ 2 - 1) := by
    field_simp
    ring
  have hle : 1 / ((b : ℝ) ^ 2 - 1) ≤ (b : ℝ) / ((b : ℝ) ^ 2 - 1) := by
    gcongr
    linarith
  rw [fract_rat_orbit hb n, Set.mem_Icc, hsum]
  split_ifs with hev
  · exact ⟨hle, le_refl _⟩
  · exact ⟨le_refl _, hle⟩

/-- The interval trapping the orbit of `b/(b²-1)` is shorter than `1/b`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_1"]
theorem rat_interval_shorter (hb : 2 ≤ b) : 1 / ((b : ℝ) + 1) < 1 / (b : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  apply one_div_lt_one_div_of_lt <;> linarith

/-! ## Sharpness -/

/-- **Theorem 3.1 is best possible** (cited, [Bug12] p. 50).  For every integer `b ≥ 2` there are
irrational numbers `ξ` all of whose orbit points `{ξ bⁿ}` lie in a *semi-open* interval of length
exactly `1/b`: take for the digit sequence of `ξ` a Sturmian sequence `s_{θ,ρ}` as in Bugeaud's
Theorem A.4.  Theorem 2.1 of [AG10] describes all such `ξ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_1"]
axiom exists_irrational_orbit_subset_Ico (b : ℕ) (hb : 2 ≤ b) :
    ∃ ξ s : ℝ, Irrational ξ ∧
      ∀ n : ℕ, Int.fract (ξ * (b : ℝ) ^ n) ∈ Set.Ico s (s + 1 / (b : ℝ))

end Bugeaud
