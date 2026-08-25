/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.SliceHygiene
import SZ.SqrtTwo
import SZ.SqrtThree
import SZ.Tijdeman
import Mathlib.Tactic.IntervalCases

/-!
# The four cells `m ∈ {5,6,7,8}`, and Theorem B

The range `2 < √m < 3` of `paper-dubD1O5.tex` Theorem B — the part that no engine of
[Dub06EO] reaches — instantiated from the generic cover game of `SZ/Slice.lean`.

| `m` | `e` | `M` | `U` | `j` | hygiene |
|---|---|---|---|---|---|
| `5` | `4` | `1` | `1+√5` | `2` | Proposition 5.4 (`m ≥ 5`, `e = m-1`) |
| `6` | `4` | `4/5` | `(4/5)(1+√6)` | `3` | free (`e = m-2`) |
| `7` | `6` | `1` | `1+√7` | `3` | Proposition 5.4 |
| `8` | `6` | `6/7` | `(6/7)(1+√8)` | `3` | free (`e = m-2`) |

Each cell is a `Slice` — the two gap conditions are rational inequalities in `√m` — plus
the check that the translate `σ = (2 + M)√m - 2j` lands in the window `(0, U)`.  The
translate is **not** uniform in `m`: `j = 2` serves `m = 5` but not `m ≥ 6`.

Assembling these with the cells already in this directory — `m = 2`
(`SZ.sqrtTwo_mem_S`), the perfect squares (`SZ.natCast_mem_MahlerZ`), `m = 3`
(`SZ.sqrtThree_mem_MahlerZ`) and `m ≥ 9` (`SZ.mem_MahlerZ_of_three_le`) — gives
**Theorem B**: `√m ∈ 𝒮` if and only if `m = 2`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
-/

namespace SZ

/-! ## Rational bounds on the four square roots -/

private theorem s5_lb : (2.236 : ℝ) < Real.sqrt 5 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private theorem s5_ub : Real.sqrt 5 < 2.2361 := by
  have h : Real.sqrt 5 < Real.sqrt (2.2361 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.2361)] at h

private theorem s6_lb : (2.449 : ℝ) < Real.sqrt 6 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private theorem s6_ub : Real.sqrt 6 < 2.4495 := by
  have h : Real.sqrt 6 < Real.sqrt (2.4495 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.4495)] at h

private theorem s7_lb : (2.645 : ℝ) < Real.sqrt 7 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private theorem s7_ub : Real.sqrt 7 < 2.6458 := by
  have h : Real.sqrt 7 < Real.sqrt (2.6458 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.6458)] at h

private theorem s8_lb : (2.828 : ℝ) < Real.sqrt 8 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private theorem s8_ub : Real.sqrt 8 < 2.8285 := by
  have h : Real.sqrt 8 < Real.sqrt (2.8285 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.8285)] at h

/-! ## The four slices -/

/-- The cell `m = 5`: `e = 4`, `M = 1`, `U = 1 + √5`. -/
noncomputable def slice5 : Slice where
  m := 5
  p := 2
  e := 4
  U := 1 + Real.sqrt 5
  three_le := by norm_num
  not_square := not_isSquare_of_bounded (by norm_num) (by decide)
  two_le_p := by norm_num
  p_le_e := by norm_num
  p_dvd_e := by norm_num
  e_le := by norm_num
  U_def := by push_cast; ring
  p_le_U := by have := s5_lb; push_cast; linarith
  gap := by have := s5_ub; push_cast; linarith

/-- The cell `m = 6`: `e = 4`, `M = 4/5`, `U = (4/5)(1 + √6)`. -/
noncomputable def slice6 : Slice where
  m := 6
  p := 2
  e := 4
  U := 4 * (1 + Real.sqrt 6) / 5
  three_le := by norm_num
  not_square := not_isSquare_of_bounded (by norm_num) (by decide)
  two_le_p := by norm_num
  p_le_e := by norm_num
  p_dvd_e := by norm_num
  e_le := by norm_num
  U_def := by push_cast; ring
  p_le_U := by have := s6_lb; push_cast; linarith
  gap := by have := s6_ub; push_cast; linarith

/-- The cell `m = 7`: `e = 6`, `M = 1`, `U = 1 + √7`. -/
noncomputable def slice7 : Slice where
  m := 7
  p := 2
  e := 6
  U := 1 + Real.sqrt 7
  three_le := by norm_num
  not_square := not_isSquare_of_bounded (by norm_num) (by decide)
  two_le_p := by norm_num
  p_le_e := by norm_num
  p_dvd_e := by norm_num
  e_le := by norm_num
  U_def := by push_cast; ring
  p_le_U := by have := s7_lb; push_cast; linarith
  gap := by have := s7_ub; push_cast; linarith

/-- The cell `m = 8`: `e = 6`, `M = 6/7`, `U = (6/7)(1 + √8)`. -/
noncomputable def slice8 : Slice where
  m := 8
  p := 2
  e := 6
  U := 6 * (1 + Real.sqrt 8) / 7
  three_le := by norm_num
  not_square := not_isSquare_of_bounded (by norm_num) (by decide)
  two_le_p := by norm_num
  p_le_e := by norm_num
  p_dvd_e := by norm_num
  e_le := by norm_num
  U_def := by push_cast; ring
  p_le_U := by have := s8_lb; push_cast; linarith
  gap := by have := s8_ub; push_cast; linarith

/-! ## The four cells -/

/-- `√5 ∈ 𝒵`, with the translate `j = 2`, `k₀ = 1`: `σ = 3√5 - 4 = 2.708…` -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem sqrtFive_mem_MahlerZ : Real.sqrt 5 ∈ MahlerZ := by
  have hM : slice5.M = 1 := by norm_num [Slice.M, slice5]
  have hsq : slice5.sq = Real.sqrt 5 := by norm_num [Slice.sq, slice5]
  have hp : (slice5.p : ℝ) = 2 := by norm_num [slice5]
  have hU : slice5.U = 1 + Real.sqrt 5 := rfl
  have hσ : slice5.sigma 2 1 = 3 * Real.sqrt 5 - 4 := by
    rw [Slice.sigma, hM, hsq, hp]; push_cast; ring
  have h := Slice.mem_MahlerZ_of_uniform slice5 rfl (by norm_num [slice5])
    (by rw [hsq, hp]; have := s5_lb; linarith)
    (j := 2) (k₀ := 1) (by norm_num) (by norm_num)
    (by rw [hσ]; have := s5_lb; linarith)
    (by rw [hσ, hU]; have := s5_ub; linarith)
  norm_num [slice5] at h
  exact h

/-- `√6 ∈ 𝒵`, with the translate `j = 3`, `k₀ = 1`: `σ = 2.8√6 - 6 = 0.858…`  Here
`e = m - 2`, so tail hygiene is not needed. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem sqrtSix_mem_MahlerZ : Real.sqrt 6 ∈ MahlerZ := by
  have hM : slice6.M = 4 / 5 := by norm_num [Slice.M, slice6]
  have hsq : slice6.sq = Real.sqrt 6 := by norm_num [Slice.sq, slice6]
  have hp : (slice6.p : ℝ) = 2 := by norm_num [slice6]
  have hU : slice6.U = 4 * (1 + Real.sqrt 6) / 5 := rfl
  have hσ : slice6.sigma 3 1 = 14 / 5 * Real.sqrt 6 - 6 := by
    rw [Slice.sigma, hM, hsq, hp]; push_cast; ring
  have h := Slice.mem_MahlerZ_of_e_le slice6 rfl (by norm_num [slice6])
    (j := 3) (k₀ := 1) (by norm_num)
    (by rw [hσ]; have := s6_lb; linarith)
    (by rw [hσ, hU]; have := s6_ub; linarith)
  norm_num [slice6] at h
  exact h

/-- `√7 ∈ 𝒵`, with the translate `j = 3`, `k₀ = 1`: `σ = 3√7 - 6 = 1.937…` -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem sqrtSeven_mem_MahlerZ : Real.sqrt 7 ∈ MahlerZ := by
  have hM : slice7.M = 1 := by norm_num [Slice.M, slice7]
  have hsq : slice7.sq = Real.sqrt 7 := by norm_num [Slice.sq, slice7]
  have hp : (slice7.p : ℝ) = 2 := by norm_num [slice7]
  have hU : slice7.U = 1 + Real.sqrt 7 := rfl
  have hσ : slice7.sigma 3 1 = 3 * Real.sqrt 7 - 6 := by
    rw [Slice.sigma, hM, hsq, hp]; push_cast; ring
  have h := Slice.mem_MahlerZ_of_uniform slice7 rfl (by norm_num [slice7])
    (by rw [hsq, hp]; have := s7_lb; linarith)
    (j := 3) (k₀ := 1) (by norm_num) (by norm_num)
    (by rw [hσ]; have := s7_lb; linarith)
    (by rw [hσ, hU]; have := s7_ub; linarith)
  norm_num [slice7] at h
  exact h

/-- `√8 ∈ 𝒵`, with the translate `j = 3`, `k₀ = 1`: `σ = (20/7)√8 - 6 = 2.081…`  Here
`e = m - 2`, so tail hygiene is not needed. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem sqrtEight_mem_MahlerZ : Real.sqrt 8 ∈ MahlerZ := by
  have hM : slice8.M = 6 / 7 := by norm_num [Slice.M, slice8]
  have hsq : slice8.sq = Real.sqrt 8 := by norm_num [Slice.sq, slice8]
  have hp : (slice8.p : ℝ) = 2 := by norm_num [slice8]
  have hU : slice8.U = 6 * (1 + Real.sqrt 8) / 7 := rfl
  have hσ : slice8.sigma 3 1 = 20 / 7 * Real.sqrt 8 - 6 := by
    rw [Slice.sigma, hM, hsq, hp]; push_cast; ring
  have h := Slice.mem_MahlerZ_of_e_le slice8 rfl (by norm_num [slice8])
    (j := 3) (k₀ := 1) (by norm_num)
    (by rw [hσ]; have := s8_lb; linarith)
    (by rw [hσ, hU]; have := s8_ub; linarith)
  norm_num [slice8] at h
  exact h

/-- `𝒵` meets `(2,3)`: the paper's Corollary 6.1.  Since `[3,∞) ⊆ 𝒵`, any element of `𝒮`
above `2` would have to lie in this interval. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem exists_mem_MahlerZ_Ioo_two_three : ∃ α ∈ MahlerZ, 2 < α ∧ α < 3 :=
  ⟨Real.sqrt 5, sqrtFive_mem_MahlerZ, by have := s5_lb; linarith, by have := s5_ub; linarith⟩

/-! ## Theorem B -/

/-- Every `√m` with `m ≥ 2` an integer other than `2` lies in `𝒵`: the perfect squares
trivially, `m = 3` by `SZ.sqrtThree_mem_MahlerZ`, the four cells `{5,6,7,8}` by the cover
game above, and `m ≥ 9` because then `√m ≥ 3`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem sqrt_natCast_mem_MahlerZ {m : ℕ} (hm : 2 ≤ m) (hne : m ≠ 2) :
    Real.sqrt m ∈ MahlerZ := by
  rcases le_or_gt 9 m with h9 | h9
  · refine mem_MahlerZ_of_three_le ?_
    have h : Real.sqrt 9 ≤ Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast h9)
    rwa [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)] at h
  · interval_cases m
    · exact absurd rfl hne
    · simpa using sqrtThree_mem_MahlerZ
    · have h4 : Real.sqrt ((4 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by
        rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [h4]
      exact natCast_mem_MahlerZ (le_refl 2)
    · simpa using sqrtFive_mem_MahlerZ
    · simpa using sqrtSix_mem_MahlerZ
    · simpa using sqrtSeven_mem_MahlerZ
    · simpa using sqrtEight_mem_MahlerZ

/-- **Theorem B.**  For an integer `m ≥ 2`, `√m ∈ 𝒮` if and only if `m = 2`.  Both
directions are proved from scratch in this directory, so the statement carries no
citation. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem sqrt_natCast_mem_S_iff {m : ℕ} (hm : 2 ≤ m) : Real.sqrt m ∈ S ↔ m = 2 := by
  constructor
  · intro hS
    by_contra hne
    exact hS.2 (sqrt_natCast_mem_MahlerZ hm hne)
  · rintro rfl
    simpa using sqrtTwo_mem_S

end SZ
