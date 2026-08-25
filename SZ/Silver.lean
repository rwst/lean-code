/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Theorem A: `1 + √2 ∈ 𝒵`, and its orbit is the Pell sequence

The headline of `plans/plan-dubD1.html`, answering `plans/report-dubickas.html` §D.1 —
"decide `1 + √2 ∈ 𝒮` or `𝒵`", the report's *best single open case* — on the `𝒵` side.

`1 + √2` is the Pisot number that evades every engine of [Dub06EO]:

* Tijdeman's nested intervals (Thm 1(i)) need `α ≥ 3`; here `α = 2.414…`;
* strong-Pisot trace decay (Thm 1(iii)) needs a *positive* second conjugate; here
  `ᾱ = 1 - √2 ∈ (-1,0)`, so `{αⁿ}` accumulates at both `0` and `1`;
* Dubickas–Zaimi confinement (Thm 1(iv)) needs `P_α(1) ≤ -3`; here `P_α(1) = -2`, which
  puts the confinement target at exactly `1/2` — the even/odd threshold itself.  Concretely
  `{αⁿ/4} = 1/2 - ᾱⁿ/4` alternates sides of `1/2` forever.

The third mechanism — *sign-compensated trace parity* (`SZ/PellDesign.lean`) — turns that
last obstruction into the fuel.  With `ξ = (2-√2)/4` the trace `ξαⁿ + ξ̄ᾱⁿ` is the integer
`P_{n-1}` (Pell), whose parity is `n+1 mod 2` because `P_{m+2} ≡ P_m (mod 2)`; and the
conjugate term `ξ̄ᾱⁿ` lies in `(0,1)` for even `n` and `(-1,0)` for odd `n`.  The two
2-periodic effects cancel:

> `⌊ξ (1+√2)ⁿ⌋ = P_{n-1} - 1` (`n` even),  `= P_{n-1}` (`n` odd) — **even in both cases**.

First terms: `0, 0, 0, 2, 4, 12, 28, 70, 168, …`.

The mod-2 recurrence is `T_{n+2} ≡ T_n` precisely because `2 ∣ a`; for the golden mean
(`a = 1`) it is Fibonacci, of period `3`, the alternating pattern is not a solution, and
indeed `φ ∈ 𝒮` (`SZ/GoldenS.lean`).  **The method knows where it must fail.**

## Main results

* `SZ.silver_pair` — `(1+√2, 1-√2)` is a real quadratic pair for `x² = 2x + 1`.
* `SZ.floor_silver` — the exact orbit, `⌊ξ αⁿ⌋ = rec2 2 1 1 0 n - [n even]`.
* `SZ.floor_silver_pell` — the same in Pell form.
* `SZ.silver_mem_MahlerZ` — **Theorem A**: `1 + √2 ∈ 𝒵`.
* `SZ.fract_silver` — report §E.3's corner: the fractional parts sit within
  `ξ̄ |ᾱ|ⁿ` of `1` (even `n`) and of `0` (odd `n`), so the limit set is `{0,1}` — the
  two-point minimum for a non-strong Pisot number — while every integral part is even.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
-/

namespace SZ

open Real

/-! ## The Pell sequence -/

/-- The Pell numbers `0, 1, 2, 5, 12, 29, …`. -/
def pell : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 2 * pell (n + 1) + pell n

@[simp, category API, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem pell_zero : pell 0 = 0 := rfl

@[simp, category API, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem pell_one : pell 1 = 1 := rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem pell_add_two (n : ℕ) : pell (n + 2) = 2 * pell (n + 1) + pell n := rfl

/-- The design's trace sequence at `(a,b) = (2,1)` is the Pell sequence shifted by one,
with the convention `P₋₁ = 1` supplied by the seed. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem rec2_two_one_succ (n : ℕ) : rec2 2 1 1 0 (n + 1) = pell n := by
  induction n using SZ.twoStep with
  | h0 => rfl
  | h1 => rfl
  | hs n ih1 ih2 =>
    rw [show n + 2 + 1 = (n + 1) + 2 from rfl, rec2_add_two, pell_add_two, ih1, ih2]
    ring

/-! ## The pair -/

private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by nlinarith [sqrt_two_sq, sqrt_two_pos]

private theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by nlinarith [sqrt_two_sq, sqrt_two_pos]

/-- `1 + √2` and `1 - √2` are the two roots of `x² = 2x + 1`, and the second lies in the
open unit disc. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem silver_pair : Pair (1 + Real.sqrt 2) (1 - Real.sqrt 2) 2 1 where
  one_lt := by linarith [sqrt_two_pos]
  absLt := by
    rw [abs_lt]; constructor <;> [linarith [sqrt_two_lt_two]; linarith [one_lt_sqrt_two]]
  sum := by push_cast; ring
  prod := by push_cast; nlinarith [sqrt_two_sq]

@[category API, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem silver_conj_neg : (1 : ℝ) - Real.sqrt 2 < 0 := by linarith [one_lt_sqrt_two]

/-- The designed multiplier at `1 + √2` is `ξ = (2 - √2)/4`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem xiDesign_silver :
    xiDesign (1 + Real.sqrt 2) (1 - Real.sqrt 2) = (2 - Real.sqrt 2) / 4 := by
  have h : (1 + Real.sqrt 2) - (1 - Real.sqrt 2) = 2 * Real.sqrt 2 := by ring
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos
  show (-(1 - Real.sqrt 2)) / ((1 + Real.sqrt 2) - (1 - Real.sqrt 2)) = _
  rw [h]
  field_simp
  nlinarith [sqrt_two_sq]

/-! ## Theorem A -/

/-- **The exact orbit.**  `⌊((2-√2)/4)·(1+√2)ⁿ⌋ = rec2 2 1 1 0 n - [2 ∣ n]` for every
`n ≥ 0`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem floor_silver (n : ℕ) :
    ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n⌋
      = rec2 2 1 1 0 n - (if n % 2 = 0 then 1 else 0) := by
  rw [← xiDesign_silver]
  exact floorNeg silver_pair silver_conj_neg n

/-- **The exact orbit, in Pell form.**  `⌊ξ (1+√2)^{n+1}⌋ = P_n - [2 ∤ n]`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem floor_silver_pell (n : ℕ) :
    ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ (n + 1)⌋
      = pell n - (if n % 2 = 0 then 0 else 1) := by
  rw [floor_silver, rec2_two_one_succ]
  congr 1
  rcases Nat.even_or_odd n with he | ho
  · have : n % 2 = 0 := Nat.even_iff.mp he
    rw [ite_eq_right (by omega), ite_eq_left this]
  · have : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [ite_eq_left (by omega), ite_eq_right (by omega)]

/-- **Theorem A.**  `1 + √2 ∈ 𝒵`: the explicit `ξ = (2-√2)/4` makes every integral part
`⌊ξ (1+√2)ⁿ⌋` even.  This settles `plans/report-dubickas.html` §D.1. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem silver_mem_MahlerZ : (1 + Real.sqrt 2) ∈ MahlerZ := by
  refine mem_MahlerZ_of_neg silver_pair silver_conj_neg ⟨1, by ring⟩ ?_
  rintro ⟨k, hk⟩
  omega

/-- Every integral part is even, spelled out at the explicit witness. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem even_floor_silver (n : ℕ) :
    Even ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n⌋ := by
  rw [floor_silver]
  have := rec2_dvd_sub (m := 2) (A := 2) (B := 1) (t₀ := (1 : ℤ)) (t₁ := (0 : ℤ))
    ⟨1, by ring⟩ ⟨0, by ring⟩ n
  obtain ⟨k, hk⟩ := this
  exact ⟨k, by omega⟩

/-! ## The limit set (report §E.3) -/

/-- **Report §E.3's corner.**  The fractional parts of the witness orbit sit within
`ξ̄ |ᾱ|ⁿ` of `1` at even `n` and of `0` at odd `n`; since `|ᾱ| = √2 - 1 < 1`, the limit
set is the two-point set `{0,1}` — the minimum possible for a Pisot number that is not
strong ([DubA06] Thm 2) — while every integral part stays even. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem fract_silver (n : ℕ) :
    |Int.fract ((2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n)
      - (if n % 2 = 0 then 1 else 0)|
      ≤ |(1 : ℝ) - Real.sqrt 2| ^ n := by
  set α : ℝ := 1 + Real.sqrt 2
  set β : ℝ := 1 - Real.sqrt 2
  have hp := xiDesign'_pos silver_pair
  have hlt := xiDesign'_lt_one silver_pair silver_conj_neg
  have hid : xiDesign α β * α ^ n + xiDesign' α β * β ^ n = (rec2 2 1 1 0 n : ℝ) :=
    rec2_real silver_pair.sq_alpha silver_pair.sq_beta (xiDesign_seed₀ silver_pair)
      (xiDesign_seed₁ silver_pair) n
  rw [← xiDesign_silver, Int.fract, floorNeg silver_pair silver_conj_neg n]
  have hval : xiDesign α β * α ^ n
      = (rec2 2 1 1 0 n : ℝ) - xiDesign' α β * β ^ n := by linarith
  rw [hval]
  push_cast
  have hb : |xiDesign' α β * β ^ n| ≤ |β| ^ n := by
    rw [abs_mul, abs_of_pos hp, ← abs_pow]
    exact mul_le_of_le_one_left (abs_nonneg _) hlt.le
  rcases Nat.even_or_odd n with he | ho
  · rw [ite_eq_left (Nat.even_iff.mp he)]
    calc |(rec2 2 1 1 0 n : ℝ) - xiDesign' α β * β ^ n - ((rec2 2 1 1 0 n : ℝ) - 1) - 1|
        = |xiDesign' α β * β ^ n| := by rw [show (rec2 2 1 1 0 n : ℝ)
            - xiDesign' α β * β ^ n - ((rec2 2 1 1 0 n : ℝ) - 1) - 1
            = -(xiDesign' α β * β ^ n) by ring, abs_neg]
      _ ≤ |β| ^ n := hb
  · have hn2 : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [ite_eq_right (by omega : ¬ n % 2 = 0)]
    calc |(rec2 2 1 1 0 n : ℝ) - xiDesign' α β * β ^ n - ((rec2 2 1 1 0 n : ℝ) - 0) - 0|
        = |xiDesign' α β * β ^ n| := by rw [show (rec2 2 1 1 0 n : ℝ)
            - xiDesign' α β * β ^ n - ((rec2 2 1 1 0 n : ℝ) - 0) - 0
            = -(xiDesign' α β * β ^ n) by ring, abs_neg]
      _ ≤ |β| ^ n := hb

end SZ
