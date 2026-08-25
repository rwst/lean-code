/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# `√2 ∈ 𝒮`: the base-2 degeneracy

Proposition 2.3 of `paper-dubD1O5.tex`, and the whole of the `𝒮` side of its Theorem B.
It is the mechanism inside [Dub06EO] Thm 2(i) (`2^{1/q} ∈ 𝒮`), isolated.

## The statement

Three assertions, of which the first is `SZ.digitReal_two_eq_zero` in
`SZ/DigitParity.lean`:

* `Ev₂ = {0}`, hence `K₂ = {0}` — in base `2` the only even digit is `0`;
* **rigidity**: if `⌊t 2ᵏ⌋` is even for every `k ≥ 0`, then `t ∈ 2ℤ`
  (`SZ.eq_intCast_of_even_floors`);
* consequently `√2 ∈ 𝒮` (`SZ.sqrtTwo_mem_S`).

## The mechanism

Rigidity is a two-line dynamical argument on the fractional part.  From
`⌊2u⌋ = 2⌊u⌋ + ⌊2{u}⌋` with `⌊2{u}⌋ ∈ {0,1}`, parity of the two floors forces
`⌊2{u}⌋ = 0`, i.e. `{u} < 1/2`, and *then* the doubling map is linear on the fractional
part: `{2u} = 2{u}`.  Applying this along the orbit gives `{t 2ᵏ} = 2ᵏ {t} < 1/2` for
every `k`, which is Archimedean nonsense unless `{t} = 0`.

The passage to `√2` is the even/odd split of the exponent that runs through this whole
root: with `t₁ = 2ξ` and `t₂ = √2 ξ`,

`ξ (√2)^{2k+2} = t₁ 2ᵏ`,   `ξ (√2)^{2k+1} = t₂ 2ᵏ`,

so a witness for `√2` makes both `t₁` and `t₂` even integers, and `√2 = t₁/t₂` is
rational.

## Why this is the end of the road at `m = 2`, not an accident

The construction of `SZ/CoverGame.lean` solves `x + √m y = σ` with `x, y` in the
restricted-digit Cantor set `K_m`.  At `m = 2` that set is a single point, so there is
nothing to intersect: the dichotomy `dim K₂ = 0` against `dim K₃ = log 2 / log 3 > 0` is
the entire difference between `√2 ∈ 𝒮` and `√3 ∈ 𝒵` (`SZ.sqrtThree_mem_MahlerZ`).

Nothing here is special to the exponent `2`: the same argument applied to
`t_r = ξ (2^{1/q})^r`, `r = 0, …, q-1`, gives [Dub06EO] Thm 2(i) in full.  We formalize
the case the paper states.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336, Theorem 2(i).
-/

namespace SZ

/-! ## The doubling map on the fractional part -/

/-- `⌊2u⌋ = 2⌊u⌋ + ⌊2{u}⌋`: the integral part of a doubled real, split off its
fractional part. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem floor_two_mul (u : ℝ) : ⌊2 * u⌋ = 2 * ⌊u⌋ + ⌊2 * Int.fract u⌋ := by
  have e : (2 : ℝ) * u = 2 * Int.fract u + ((2 * ⌊u⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [e, Int.floor_add_intCast]
  ring

/-- `⌊2{u}⌋` is `0` or `1`, since `0 ≤ 2{u} < 2`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem floor_two_fract_cases (u : ℝ) : ⌊2 * Int.fract u⌋ = 0 ∨ ⌊2 * Int.fract u⌋ = 1 := by
  have h0 : (0 : ℝ) ≤ 2 * Int.fract u := by
    have := Int.fract_nonneg u; linarith
  have h1 : 2 * Int.fract u < 2 := by
    have := Int.fract_lt_one u; linarith
  have hlo : (0 : ℤ) ≤ ⌊2 * Int.fract u⌋ := Int.floor_nonneg.mpr h0
  have hhi : ⌊2 * Int.fract u⌋ < 2 := by
    have : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
    exact Int.floor_lt.mpr (by rw [this]; exact h1)
  omega

/-- **The parity step.**  If both `⌊u⌋` and `⌊2u⌋` are even, then `{u} < 1/2`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem fract_lt_half {u : ℝ} (h : Even ⌊u⌋) (h2 : Even ⌊2 * u⌋) : Int.fract u < 1 / 2 := by
  have key : ⌊2 * Int.fract u⌋ = 0 := by
    have hsplit := floor_two_mul u
    have hev : Even ⌊2 * Int.fract u⌋ := by
      have : ⌊2 * Int.fract u⌋ = ⌊2 * u⌋ - 2 * ⌊u⌋ := by omega
      rw [this]
      exact h2.sub (h.mul_left 2)
    rcases floor_two_fract_cases u with h0 | h1
    · exact h0
    · rw [h1] at hev; exact absurd hev (by decide)
  have := Int.lt_floor_add_one (2 * Int.fract u)
  rw [key] at this
  push_cast at this
  linarith

/-- Where the fractional part is below `1/2`, doubling is **linear** on it. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem fract_two_mul {u : ℝ} (h : Int.fract u < 1 / 2) :
    Int.fract (2 * u) = 2 * Int.fract u := by
  have e : (2 : ℝ) * u = ((2 * ⌊u⌋ : ℤ) : ℝ) + 2 * Int.fract u := by
    rw [Int.fract]; push_cast; ring
  rw [e, Int.fract_intCast_add]
  refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
  · have := Int.fract_nonneg u; linarith
  · linarith

/-! ## Rigidity of the even-floor orbit -/

/-- **Rigidity, the fractional half.**  If `⌊t 2ᵏ⌋` is even for every `k ≥ 0` then
`{t} = 0`: the orbit satisfies `{t 2ᵏ} = 2ᵏ {t} < 1/2`, and `2ᵏ` is unbounded. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem fract_eq_zero_of_even_floors {t : ℝ} (h : ∀ k : ℕ, Even ⌊t * 2 ^ k⌋) :
    Int.fract t = 0 := by
  have hhalf : ∀ k : ℕ, Int.fract (t * 2 ^ k) < 1 / 2 := by
    intro k
    refine fract_lt_half (h k) ?_
    have e : (2 : ℝ) * (t * 2 ^ k) = t * 2 ^ (k + 1) := by ring
    rw [e]; exact h (k + 1)
  have hpow : ∀ k : ℕ, Int.fract (t * 2 ^ k) = 2 ^ k * Int.fract t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : t * 2 ^ (k + 1) = 2 * (t * 2 ^ k) := by ring
      rw [e, fract_two_mul (hhalf k), ih]
      ring
  by_contra hne
  have hpos : 0 < Int.fract t := lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm hne)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (1 / 2 : ℝ) ^ j < Int.fract t :=
    exists_pow_lt_of_lt_one hpos (by norm_num)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hone : (1 : ℝ) < 2 ^ j * Int.fract t := by
    have e : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [div_pow]; norm_num
    rw [e] at hj
    have := mul_lt_mul_of_pos_left hj h2j
    rwa [mul_one_div, div_self (ne_of_gt h2j)] at this
  have := hhalf j
  rw [hpow j] at this
  linarith

/-- **Rigidity.**  If `⌊t 2ᵏ⌋` is even for every `k ≥ 0`, then `t` is an even integer.
This is the whole obstruction at base `2`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem eq_intCast_of_even_floors {t : ℝ} (h : ∀ k : ℕ, Even ⌊t * 2 ^ k⌋) :
    ∃ z : ℤ, Even z ∧ t = (z : ℝ) := by
  refine ⟨⌊t⌋, by simpa using h 0, ?_⟩
  have hf := fract_eq_zero_of_even_floors h
  rw [Int.fract] at hf
  linarith

/-! ## The capstone -/

@[category API, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h

/-- **`√2 ∉ 𝒵`.**  A witness would make both `2ξ` and `√2 ξ` even integers, hence
`√2` rational. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem sqrtTwo_notMem_MahlerZ : Real.sqrt 2 ∉ MahlerZ := by
  rintro ⟨-, ξ, hξ, hev⟩
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- the even exponents: `ξ (√2)^{2(k+1)} = (2ξ) 2ᵏ`
  have h1 : ∀ k : ℕ, Even ⌊2 * ξ * 2 ^ k⌋ := by
    intro k
    have e : 2 * ξ * 2 ^ k = ξ * Real.sqrt 2 ^ (2 * (k + 1)) := by
      rw [pow_mul, hsq, pow_succ]; ring
    rw [e]; exact hev _ (by omega)
  -- the odd exponents: `ξ (√2)^{2k+1} = (√2 ξ) 2ᵏ`
  have h2 : ∀ k : ℕ, Even ⌊Real.sqrt 2 * ξ * 2 ^ k⌋ := by
    intro k
    have e : Real.sqrt 2 * ξ * 2 ^ k = ξ * Real.sqrt 2 ^ (2 * k + 1) := by
      rw [pow_succ, pow_mul, hsq]; ring
    rw [e]; exact hev _ (by omega)
  obtain ⟨z₁, -, hz₁⟩ := eq_intCast_of_even_floors h1
  obtain ⟨z₂, -, hz₂⟩ := eq_intCast_of_even_floors h2
  have hz₁ne : ((z₁ : ℝ)) ≠ 0 := by rw [← hz₁]; exact mul_ne_zero two_ne_zero hξ
  refine irrational_sqrt_two ⟨(z₁ : ℚ) / (z₂ : ℚ), ?_⟩
  have hz₂ne : ((z₂ : ℝ)) ≠ 0 := by
    rw [← hz₂]
    exact mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) hξ
  have hcancel : Real.sqrt 2 * (Real.sqrt 2 * ξ) = 2 * ξ := by
    rw [← mul_assoc, ← sq, hsq]
  push_cast
  rw [← hz₁, ← hz₂, div_eq_iff (by rw [hz₂]; exact hz₂ne)]
  exact hcancel.symm

/-- **Proposition 2.3: `√2 ∈ 𝒮`.**  The `𝒮` side of Theorem B, and the cell where the
method of this root has nothing to work with. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_sqrt_two"]
theorem sqrtTwo_mem_S : Real.sqrt 2 ∈ S := ⟨one_lt_sqrt_two, sqrtTwo_notMem_MahlerZ⟩

end SZ
