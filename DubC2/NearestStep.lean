/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.DubickasWord
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The nearest-integer orbit of `ξ(3/2)ⁿ`: model, alphabet and branch table

Milestone M3 of `plans/plan-dubC2.html`, first layer.  Fix a real `ξ ≠ 0` and put

`xₙ = [ξ(3/2)ⁿ + ½] = round (ξ(3/2)ⁿ)`,  `yₙ = {ξ(3/2)ⁿ + ½}`,  `sₙ = 2x_{n+1} − 3xₙ`.

This is the `ν = 1/2` instance of the carry formalism of `Z32/DubickasWord.lean`, so nothing
here is re-proved: `DubC2.xN`, `DubC2.yN`, `DubC2.sN` are *definitionally* `Z32.xInt`,
`Z32.yFract`, `Z32.carry` at `(p, q, ν) = (3, 2, 1/2)`, and every identity below is an
instantiation plus `norm_num`.  The bridge to Mathlib's `round` is `round_eq`.

## Main results

* `DubC2.xN_eq_round` — the model is the nearest integer, `xₙ = round (ξ(3/2)ⁿ)`.
* `DubC2.sN_eq` — `sₙ = 3yₙ − 2y_{n+1} − ½` ([Dub09AA] (3) at `ν = 1/2`).
* `DubC2.sN_eq_neg_one_or_one` — **the alphabet collapses to two letters as soon as `xₙ` is
  odd**: `|sₙ| ≤ 2` for interval reasons and `sₙ ≡ xₙ (mod 2)` for arithmetic ones.
* `DubC2.stepA`, `DubC2.stepB` — **the branch table**.  With `xₙ` odd the letter is a function
  of `yₙ` alone, and the two half-lines `[0,½)`, `[½,1)` are an exact partition:

  | letter | window for `yₙ` | `sₙ` | `y_{n+1}` | `x_{n+1}` |
  |---|---|---|---|---|
  | `A` | `[0, ½)` | `−1` | `(6yₙ+1)/4` | `(3xₙ−1)/2` |
  | `B` | `[½, 1)` | `+1` | `(6yₙ−3)/4` | `(3xₙ+1)/2` |

  This exactness is the G-4(c) observation of the plan: at the top level there is no gap for a
  window or arc rule to exploit, which is why the odd-residue coordinates must do all the work.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
-/

namespace DubC2

variable {ξ : ℝ} {n : ℕ}

/-! ## The model -/

/-- The nearest integer `xₙ = [ξ(3/2)ⁿ + ½]`, as the `ν = 1/2` instance of `Z32.xInt`. -/
noncomputable def xN (ξ : ℝ) (n : ℕ) : ℤ := Z32.xInt 3 2 ξ (1 / 2) n

/-- The residual `yₙ = {ξ(3/2)ⁿ + ½} ∈ [0,1)`, as the `ν = 1/2` instance of `Z32.yFract`. -/
noncomputable def yN (ξ : ℝ) (n : ℕ) : ℝ := Z32.yFract 3 2 ξ (1 / 2) n

/-- The carry `sₙ = 2x_{n+1} − 3xₙ`, as the `ν = 1/2` instance of `Z32.carry`. -/
noncomputable def sN (ξ : ℝ) (n : ℕ) : ℤ := Z32.carry 3 2 ξ (1 / 2) n

/-- **The model is the nearest integer.**  Mathlib's `round_eq : round x = ⌊x + 1/2⌋` is exactly
[DN05]'s `[z + ½]`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem xN_eq_round (ξ : ℝ) (n : ℕ) : xN ξ n = round (ξ * ((3 : ℝ) / 2) ^ n) := by
  rw [xN, Z32.xInt, Z32.orb, round_eq]
  norm_num

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_32"]
theorem yN_nonneg (ξ : ℝ) (n : ℕ) : 0 ≤ yN ξ n := Z32.yFract_nonneg n

@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_32"]
theorem yN_lt_one (ξ : ℝ) (n : ℕ) : yN ξ n < 1 := Z32.yFract_lt_one n

/-- **[Dub09AA] (3) at `ν = 1/2`**: `sₙ = 3yₙ − 2y_{n+1} − ½`. -/
@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_32"]
theorem sN_eq (ξ : ℝ) (n : ℕ) :
    (sN ξ n : ℝ) = 3 * yN ξ n - 2 * yN ξ (n + 1) - 1 / 2 := by
  have h := Z32.carry_eq (p := 3) (q := 2) (ξ := ξ) (ν := 1 / 2) (by norm_num) n
  simp only [sN, yN]
  push_cast at h ⊢
  linarith

/-- The defining recurrence `2x_{n+1} = 3xₙ + sₙ` — an identity, not a hypothesis. -/
@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_32"]
theorem two_mul_xN_succ (ξ : ℝ) (n : ℕ) : 2 * xN ξ (n + 1) = 3 * xN ξ n + sN ξ n := by
  simp only [sN, xN, Z32.carry]
  push_cast
  ring

/-! ## The alphabet -/

/-- The carry is confined to `{−2,…,2}` by the interval `0 ≤ yₙ < 1` alone. -/
@[category API, AMS 11 37, ref "Dub09AA", group "dn05_nearest_32"]
theorem abs_sN_le_two (ξ : ℝ) (n : ℕ) : -2 ≤ sN ξ n ∧ sN ξ n ≤ 2 := by
  have h := sN_eq ξ n
  have h0 := yN_nonneg ξ n
  have h1 := yN_lt_one ξ n
  have h2 := yN_nonneg ξ (n + 1)
  have h3 := yN_lt_one ξ (n + 1)
  have hup : sN ξ n < 3 := by
    by_contra hc
    push Not at hc
    have : (3 : ℝ) ≤ (sN ξ n : ℝ) := by exact_mod_cast hc
    linarith
  have hlo : -3 < sN ξ n := by
    by_contra hc
    push Not at hc
    have : (sN ξ n : ℝ) ≤ -3 := by exact_mod_cast hc
    linarith
  omega

/-- **Two letters.**  If `xₙ` is odd then `sₙ ≡ xₙ ≡ 1 (mod 2)`, and with `|sₙ| ≤ 2` only
`sₙ = ±1` survives. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem sN_eq_neg_one_or_one (h2 : ¬ (2 : ℤ) ∣ xN ξ n) : sN ξ n = -1 ∨ sN ξ n = 1 := by
  have hrec := two_mul_xN_succ ξ n
  have hb := abs_sN_le_two ξ n
  omega

/-! ## The branch table -/

/-- Letter `A`: `yₙ < ½` forces `sₙ = −1`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem sN_eq_neg_one (h2 : ¬ (2 : ℤ) ∣ xN ξ n) (hy : yN ξ n < 1 / 2) : sN ξ n = -1 := by
  rcases sN_eq_neg_one_or_one h2 with h | h
  · exact h
  · exfalso
    have he := sN_eq ξ n
    rw [h] at he
    have h2' := yN_nonneg ξ (n + 1)
    push_cast at he
    linarith

/-- Letter `B`: `yₙ ≥ ½` forces `sₙ = +1`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem sN_eq_one (h2 : ¬ (2 : ℤ) ∣ xN ξ n) (hy : 1 / 2 ≤ yN ξ n) : sN ξ n = 1 := by
  rcases sN_eq_neg_one_or_one h2 with h | h
  · exfalso
    have he := sN_eq ξ n
    rw [h] at he
    have h3' := yN_lt_one ξ (n + 1)
    push_cast at he
    linarith
  · exact h

/-- **Branch `A`** (`yₙ ∈ [0,½)`): the carry, the residual map `4y_{n+1} = 6yₙ + 1`, and the
integer step `2x_{n+1} = 3xₙ − 1`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem stepA (h2 : ¬ (2 : ℤ) ∣ xN ξ n) (hy : yN ξ n < 1 / 2) :
    sN ξ n = -1 ∧ 4 * yN ξ (n + 1) = 6 * yN ξ n + 1 ∧
      2 * xN ξ (n + 1) = 3 * xN ξ n - 1 := by
  have hs := sN_eq_neg_one h2 hy
  refine ⟨hs, ?_, ?_⟩
  · have he := sN_eq ξ n
    rw [hs] at he
    push_cast at he
    linarith
  · have hrec := two_mul_xN_succ ξ n
    omega

/-- **Branch `B`** (`yₙ ∈ [½,1)`): the carry, the residual map `4y_{n+1} = 6yₙ − 3`, and the
integer step `2x_{n+1} = 3xₙ + 1`. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem stepB (h2 : ¬ (2 : ℤ) ∣ xN ξ n) (hy : 1 / 2 ≤ yN ξ n) :
    sN ξ n = 1 ∧ 4 * yN ξ (n + 1) = 6 * yN ξ n - 3 ∧
      2 * xN ξ (n + 1) = 3 * xN ξ n + 1 := by
  have hs := sN_eq_one h2 hy
  refine ⟨hs, ?_, ?_⟩
  · have he := sN_eq ξ n
    rw [hs] at he
    push_cast at he
    linarith
  · have hrec := two_mul_xN_succ ξ n
    omega

end DubC2
