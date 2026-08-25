/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases

/-!
# Divisibility by `p`: Theorem C

Section 7 of `paper-dubD1O5.tex`.  Parity is not special: replacing the even digits
throughout by the digits divisible by `p` turns the cover game of `SZ/Slice.lean` into a
machine that designs a multiplier `ξ` with `p ∣ ⌊ξ √mⁿ⌋` for **every** `n ≥ 1`.

> **Theorem C.**  Let `p ≥ 2` and let `m ≥ 3` be an integer that is not a perfect square.
> Suppose that either
> * (i) `m ≡ 1 (mod p)` and `m ≥ p²`, or
> * (ii) `p ∣ m` and `(m - p)(1 + √m) > p(m - 1)`.
>
> Then there is a real `ξ ≠ 0` with `p ∣ ⌊ξ √mⁿ⌋` for every `n ≥ 1`.  Consequently
> `⌊ξ √mⁿ⌋` is composite for every sufficiently large `n`.

Both branches are built here as a `Slice`, and the two gap conditions of the covering
induction are checked from the hypotheses:

* branch (i): `p ∣ m - 1` forces `e = m - 1`, `M = 1`, `U = 1 + √m`, and `m ≥ p²` gives
  `√m ≥ p`, hence `p ≤ U` and `p√m - e ≤ U`.  Tail hygiene is
  `Slice.dvd_floor_of_uniform`, whose hypothesis is exactly `√m ≥ p`.
* branch (ii): `p ∣ m` forces `e = m - p`, and the displayed inequality *is* `U > p`.  For
  the second gap condition one first shows that `U > p` already forces `m > p²`
  (`sq_lt_of_window`), whence `p√m < m` and `p√m - e < p ≤ U`.  Here `e = m - p ≤ m - 2`,
  so hygiene is free (`Slice.dvd_floor_of_e_le`).

The translate — the paper's Lemma 3.3 — is `Slice.exists_translate`; it needs no
hypothesis beyond the `p ≤ U` already carried by the `Slice`.

At `p = 2` branch (i) covers every odd `m ≥ 5` and branch (ii) every even non-square
`m ≥ 6`, so Theorem C contains all of Theorem B except the two cells `m = 3`
(`SZ.sqrtThree_mem_MahlerZ`) and `m = 2` (`SZ.sqrtTwo_mem_S`).

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
-/

namespace SZ

/-! ## `p` against `√m` -/

theorem p_le_sqrt {p : ℤ} {m : ℕ} (hp : 0 ≤ p) (h : p ^ 2 ≤ (m : ℤ)) :
    (p : ℝ) ≤ Real.sqrt m := by
  have hpr : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hc : ((p : ℝ)) ^ 2 ≤ (m : ℝ) := by exact_mod_cast h
  have h2 := Real.sqrt_le_sqrt hc
  rwa [Real.sqrt_sq hpr] at h2

theorem p_lt_sqrt {p : ℤ} {m : ℕ} (hp : 0 ≤ p) (h : p ^ 2 < (m : ℤ)) :
    (p : ℝ) < Real.sqrt m := by
  have hpr : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hc : ((p : ℝ)) ^ 2 < (m : ℝ) := by exact_mod_cast h
  have h2 : Real.sqrt (((p : ℝ)) ^ 2) < Real.sqrt m :=
    Real.sqrt_lt_sqrt (by positivity) hc
  rwa [Real.sqrt_sq hpr] at h2

/-- **The threshold on branch (ii)** (paper Section 7).  For `p ∣ m`, the window condition
`(m-p)(1+√m) > p(m-1)` already forces `m > p²`.  Writing `m = kp` with `k ≤ p` and
`√m ≤ p`, one gets `(m-p)(1+√m) ≤ p(k-1)(1+p) = p(kp+k-p-1) ≤ p(kp-1) = p(m-1)`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_thmc"]
theorem sq_lt_of_window {p : ℤ} {m : ℕ} (hp : 2 ≤ p) (hm : 3 ≤ m) (hd : p ∣ (m : ℤ))
    (hU : (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m)) :
    p ^ 2 < (m : ℤ) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hm3 : (3 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hk1 : 1 ≤ k := by nlinarith
  have hkp : k ≤ p := by nlinarith
  -- the real-valued shadow of the integer data
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkpr : (k : ℝ) ≤ (p : ℝ) := by exact_mod_cast hkp
  have hmr : (m : ℝ) = (p : ℝ) * (k : ℝ) := by exact_mod_cast hk
  have hs : Real.sqrt m ≤ (p : ℝ) := by
    have h2 : Real.sqrt m ≤ Real.sqrt (((p : ℝ)) ^ 2) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hcon)
    rwa [Real.sqrt_sq (by linarith)] at h2
  have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (p : ℝ))
      (by linarith : (0:ℝ) ≤ (k : ℝ) - 1)) (by linarith : (0:ℝ) ≤ (p : ℝ) - Real.sqrt m),
    mul_nonneg (by linarith : (0:ℝ) ≤ (p : ℝ)) (by linarith : (0:ℝ) ≤ (p : ℝ) - (k : ℝ))]

/-! ## Branch (i): `p ∣ m - 1` and `m ≥ p²` -/

/-- The slice of branch (i): the full alphabet `e = m - 1`, `M = 1`, `U = 1 + √m`. -/
noncomputable def sliceOne (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m) (hns : ¬ IsSquare m)
    (hd : p ∣ (m : ℤ) - 1) (hpm : p ^ 2 ≤ (m : ℤ)) : Slice where
  m := m
  p := p
  e := (m : ℤ) - 1
  U := 1 + Real.sqrt m
  three_le := hm
  not_square := hns
  two_le_p := hp
  p_le_e := by
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ p - 2) (by omega : (0:ℤ) ≤ p)]
  p_dvd_e := hd
  e_le := le_refl _
  U_def := by push_cast; ring
  p_le_U := by
    have := p_le_sqrt (show (0:ℤ) ≤ p by omega) hpm
    linarith
  gap := by
    have hs := p_le_sqrt (show (0:ℤ) ≤ p by omega) hpm
    have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
    push_cast
    nlinarith

/-! ## Branch (ii): `p ∣ m` and `(m-p)(1+√m) > p(m-1)` -/

/-- The slice of branch (ii): the alphabet stops at `e = m - p`, so `M = (m-p)/(m-1) < 1`
and the tail hygiene of Section 5 is not needed. -/
noncomputable def sliceTwo (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m) (hns : ¬ IsSquare m)
    (hd : p ∣ (m : ℤ))
    (hU : (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m)) : Slice where
  m := m
  p := p
  e := (m : ℤ) - p
  U := ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m) / ((m : ℝ) - 1)
  three_le := hm
  not_square := hns
  two_le_p := hp
  p_le_e := by
    have h := sq_lt_of_window hp hm hd hU
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ p - 2) (by omega : (0:ℤ) ≤ p)]
  p_dvd_e := dvd_sub hd dvd_rfl
  e_le := by omega
  U_def := by
    have hm1 : ((m : ℝ) - 1) ≠ 0 := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      intro h; linarith
    field_simp
    push_cast
    ring
  p_le_U := by
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    rw [le_div_iff₀ hm1]
    linarith
  gap := by
    have h := sq_lt_of_window hp hm hd hU
    have hs := p_lt_sqrt (show (0:ℤ) ≤ p by omega) h
    have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hpU : (p : ℝ) ≤ ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m) / ((m : ℝ) - 1) := by
      rw [le_div_iff₀ hm1]; linarith
    push_cast
    nlinarith

/-! ## Theorem C -/

/-- **Theorem C** ([Dub06EO]-style designed multiplier at a general modulus).  For `p ≥ 2`
and a non-square `m ≥ 3` satisfying (i) `p ∣ m - 1` and `p² ≤ m`, or (ii) `p ∣ m` and
`p(m-1) < (m-p)(1+√m)`, there is a real `ξ > 0` with `p ∣ ⌊ξ √mⁿ⌋` for every `n ≥ 1`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_thmc"]
theorem exists_dvd_floor_sqrt (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m) (hns : ¬ IsSquare m)
    (hcase : (p ∣ (m : ℤ) - 1 ∧ p ^ 2 ≤ (m : ℤ)) ∨
      (p ∣ (m : ℤ) ∧ (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m))) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → p ∣ ⌊ξ * Real.sqrt m ^ n⌋ := by
  rcases hcase with ⟨hd, hpm⟩ | ⟨hd, hU⟩
  · -- branch (i): the uniform alphabet, hygiene from `√m ≥ p`
    set S : Slice := sliceOne p m hp hm hns hd hpm with hS
    obtain ⟨j, hj, h0, h1⟩ := S.exists_translate (k₀ := 1) le_rfl
    have hpsq : (S.p : ℝ) ≤ S.sq := by
      simp only [Slice.sq, hS, sliceOne]
      exact p_le_sqrt (show (0:ℤ) ≤ p by omega) hpm
    exact Slice.dvd_floor_of_uniform S rfl hpsq hj le_rfl h0.le h1.le
  · -- branch (ii): `e = m - p ≤ m - 2`, hygiene free
    set S : Slice := sliceTwo p m hp hm hns hd hU with hS
    obtain ⟨j, hj, h0, h1⟩ := S.exists_translate (k₀ := 1) le_rfl
    have he : S.e ≤ (S.m : ℤ) - 2 := by
      simp only [hS, sliceTwo]
      omega
    exact Slice.dvd_floor_of_e_le S he hj h0.le h1.le

/-- **Theorem C, the corollary.**  The designed integral parts `⌊ξ √mⁿ⌋` are composite for
every sufficiently large `n`: they are divisible by `p` and eventually exceed `p`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_thmc"]
theorem exists_eventually_composite_sqrt (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m)
    (hns : ¬ IsSquare m)
    (hcase : (p ∣ (m : ℤ) - 1 ∧ p ^ 2 ≤ (m : ℤ)) ∨
      (p ∣ (m : ℤ) ∧ (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m))) :
    ∃ ξ : ℝ, 0 < ξ ∧ (∀ n : ℕ, 1 ≤ n → p ∣ ⌊ξ * Real.sqrt m ^ n⌋) ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        ∃ a b : ℤ, 1 < a ∧ 1 < b ∧ ⌊ξ * Real.sqrt m ^ n⌋ = a * b := by
  obtain ⟨ξ, hξ, hdvd⟩ := exists_dvd_floor_sqrt p m hp hm hns hcase
  have hmr : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hs1 : 1 < Real.sqrt m := by
    have h : Real.sqrt 1 < Real.sqrt m := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    rwa [Real.sqrt_one] at h
  obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt (((p : ℝ) + 1) / ξ) hs1
  have hbig : (p : ℝ) + 1 < ξ * Real.sqrt m ^ N0 := by
    have := (div_lt_iff₀ hξ).mp hN0
    linarith
  refine ⟨ξ, hξ, hdvd, max N0 1, le_max_right _ _, fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hmono : Real.sqrt m ^ N0 ≤ Real.sqrt m ^ n :=
    pow_le_pow_right₀ hs1.le hn0
  have hval : (p : ℝ) + 1 < ξ * Real.sqrt m ^ n := by
    have := mul_le_mul_of_nonneg_left hmono hξ.le
    linarith
  have hfl : p + 1 ≤ ⌊ξ * Real.sqrt m ^ n⌋ := Int.le_floor.mpr (by push_cast; linarith)
  obtain ⟨b, hb⟩ := hdvd n hn1
  have hb1 : 1 < b := by
    by_contra hcon
    push Not at hcon
    have h1 : p * b ≤ p * 1 := mul_le_mul_of_nonneg_left hcon (by omega)
    rw [← hb] at h1
    omega
  exact ⟨p, b, by omega, hb1, hb⟩

/-! ## Theorem B's non-square cells, by the printed proof -/

/-- **The uniform greedy of the paper's proof of Theorem B**, as a corollary of Theorem C
at `p = 2`: branch (i) serves the odd bases (`2 ∣ m - 1` and `4 ≤ m`), branch (ii) the even
ones, where `(m-2)(1+√m) - 2(m-1) = √m(√m-2)(√m+1) > 0`.  `SZ/Cells.lean` reaches `m ≥ 9`
by the shorter route through `[3,∞) ⊆ 𝒵` (`SZ.mem_MahlerZ_of_three_le`); this is the same
statement proved the way the paper prints it. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_thmc"]
theorem sqrt_mem_MahlerZ_of_four_le {m : ℕ} (hm : 4 ≤ m) (hns : ¬ IsSquare m) :
    Real.sqrt m ∈ MahlerZ := by
  have hm5 : 5 ≤ m := by
    rcases Nat.lt_or_ge m 5 with h | h
    · interval_cases m
      exact absurd ⟨2, by norm_num⟩ hns
    · exact h
  have hcase : ((2 : ℤ) ∣ (m : ℤ) - 1 ∧ (2 : ℤ) ^ 2 ≤ (m : ℤ)) ∨
      ((2 : ℤ) ∣ (m : ℤ) ∧
        ((2 : ℤ) : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - ((2 : ℤ) : ℝ)) * (1 + Real.sqrt m)) := by
    rcases Nat.even_or_odd m with he | ho
    · refine Or.inr ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := he
        exact ⟨(k : ℤ), by push_cast [hk]; ring⟩
      · have hs := p_lt_sqrt (p := 2) (m := m) (by norm_num)
          (by exact_mod_cast (by omega : 4 < m))
        have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
        have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
        push_cast at hs ⊢
        nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < Real.sqrt m)
          (by linarith : (0:ℝ) < Real.sqrt m - 2)) (by linarith : (0:ℝ) < Real.sqrt m + 1)]
    · refine Or.inl ⟨?_, by exact_mod_cast (by omega : 4 ≤ m)⟩
      obtain ⟨k, hk⟩ := ho
      exact ⟨(k : ℤ), by push_cast [hk]; ring⟩
  obtain ⟨ξ, hξ, hdvd⟩ := exists_dvd_floor_sqrt 2 m (by norm_num) (by omega) hns hcase
  refine ⟨?_, ξ, ne_of_gt hξ, fun n hn => even_iff_two_dvd.mpr (hdvd n hn)⟩
  have h : Real.sqrt 1 < Real.sqrt m :=
    Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast (by omega : 1 < m))
  rwa [Real.sqrt_one] at h

/-! ## The table of Section 7

The four `(p, m)` pairs displayed in the paper, with the hypotheses of Theorem C checked.
The smallest admissible base on branch (i) is `m = p² + 1`; on branch (ii) it is the
smallest multiple of `p` clearing the window inequality. -/

private theorem s12_lb : (2.7 : ℝ) < Real.sqrt 12 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- `p = 3`, `m = 10 = 3² + 1`: branch (i), the smallest base of its branch. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_thmc"]
theorem exists_three_dvd_floor_sqrt_ten :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (3 : ℤ) ∣ ⌊ξ * Real.sqrt 10 ^ n⌋ := by
  have h := exists_dvd_floor_sqrt 3 10 (by norm_num) (by norm_num)
    (not_isSquare_of_bounded (by norm_num) (by decide))
    (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num at h
  exact h

/-- `p = 3`, `m = 12`: branch (ii), where `e = m - p = 9` and hygiene is free. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_thmc"]
theorem exists_three_dvd_floor_sqrt_twelve :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (3 : ℤ) ∣ ⌊ξ * Real.sqrt 12 ^ n⌋ := by
  have h := exists_dvd_floor_sqrt 3 12 (by norm_num) (by norm_num)
    (not_isSquare_of_bounded (by norm_num) (by decide))
    (Or.inr ⟨by norm_num, by have := s12_lb; norm_num; linarith⟩)
  norm_num at h
  exact h

/-- `p = 4`, `m = 17 = 4² + 1`: branch (i). -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_thmc"]
theorem exists_four_dvd_floor_sqrt_seventeen :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (4 : ℤ) ∣ ⌊ξ * Real.sqrt 17 ^ n⌋ := by
  have h := exists_dvd_floor_sqrt 4 17 (by norm_num) (by norm_num)
    (not_isSquare_of_bounded (by norm_num) (by decide))
    (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num at h
  exact h

/-- `p = 5`, `m = 26 = 5² + 1`: branch (i). -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_thmc"]
theorem exists_five_dvd_floor_sqrt_twentySix :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (5 : ℤ) ∣ ⌊ξ * Real.sqrt 26 ^ n⌋ := by
  have h := exists_dvd_floor_sqrt 5 26 (by norm_num) (by norm_num)
    (not_isSquare_of_bounded (by norm_num) (by decide))
    (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num at h
  exact h

end SZ
