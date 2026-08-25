/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Silver
import SZ.Tijdeman
import SZ.QuadThm6
import SZ.GoldenS
import Mathlib.Tactic.LinearCombination

/-!
# Theorem B: the golden mean is the only quadratic Pisot number in `𝒮`

Milestone M3 of `plans/plan-dubD1.html`, the classification capstone: the first complete
`𝒮`/`𝒵` verdict for a natural class of algebraic numbers.

A quadratic Pisot number `α` has a conjugate `β` with `|β| < 1`, `β ≠ 0`, and
`α + β = a ∈ ℤ`, `α β = -b ∈ ℤ`.  Five cells exhaust the class, and four of them land in
`𝒵`:

| cell | verdict | engine |
|---|---|---|
| `β ∈ (0,1)` (strong Pisot) | `𝒵` | `SZ.mem_MahlerZ_of_pos` — [Dub06EO] Thm 1(iii) |
| `β ∈ (-1,0)`, `a ≥ 3` (so `α > 3`) | `𝒵` | `SZ.mem_MahlerZ_of_three_le` — Thm 1(i), Tijdeman |
| `(a,b) = (2,1)`: `α = 1 + √2` | `𝒵` | `SZ.mem_MahlerZ_of_neg` — **the new cell** |
| `(a,b) = (2,2)`: `α = 1 + √3` | `𝒵` | `SZ.oneAddSqrtThree_mem_MahlerZ` — Thm 1(iv) |
| `(a,b) = (1,1)`: `α = φ` | `𝒮` | `SZ.golden_mem_S` — Thm 2(ii) |

The bookkeeping that makes the list finite is elementary: `β < 0` forces `b ≥ 1`, `a ≥ 1`,
and `b ≤ a` — the last because `(1+α)(1+β) = 1 + a - b` is a *positive integer*.

Only the `(2,1)` cell is new; the other four are [Dub06EO]'s, reproved here so that the
classification carries no citation.  Salem numbers have degree `≥ 4`, so "quadratic Pisot"
is the whole of degree `2` among the algebraic integers `> 1` with all other conjugates
inside the unit disc.

## Consequence for [Dub06EO] Problem 5

*Is there an element of `𝒮` greater than `2`?*  `SZ.quadPisot_notMem_S_of_two_lt`: no
quadratic Pisot number can be one — the entire class is eliminated, and the problem's
most natural candidate, `1 + √2`, turns out to lie in `𝒵`.  The problem itself stays open.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
-/

namespace SZ

open Real

/-- **A quadratic Pisot number**: `α > 1` is an algebraic integer of degree `2` whose
conjugate `β` is a nonzero real in the open unit disc.  Presented by the symmetric
functions `α + β = a` and `α β = -b`. -/
def IsQuadPisot (α : ℝ) : Prop :=
  1 < α ∧ ∃ (β : ℝ) (a b : ℤ), β ≠ 0 ∧ |β| < 1 ∧ α + β = (a : ℝ) ∧ α * β = -(b : ℝ)

@[category API, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem isQuadPisot_silver : IsQuadPisot (1 + Real.sqrt 2) :=
  ⟨silver_pair.one_lt, 1 - Real.sqrt 2, 2, 1, ne_of_lt silver_conj_neg,
    silver_pair.absLt, silver_pair.sum, silver_pair.prod⟩

@[category API, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem isQuadPisot_golden : IsQuadPisot golden := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : 2 < Real.sqrt 5 := by nlinarith
  have h2 : Real.sqrt 5 < 3 := by nlinarith
  refine ⟨one_lt_golden, (1 - Real.sqrt 5) / 2, 1, 1, ?_, ?_, ?_, ?_⟩
  · intro he
    rw [div_eq_zero_iff] at he
    rcases he with h | h <;> linarith
  · rw [abs_lt]
    constructor <;> [linarith; linarith]
  · rw [golden]; push_cast; ring
  · rw [golden]; push_cast; linear_combination (-1/4 : ℝ) * hsq

/-! ## The classification -/

/-- **Theorem B (the `𝒵` half).**  Every quadratic Pisot number other than the golden mean
lies in `𝒵`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem quadPisot_mem_MahlerZ {α : ℝ} (h : IsQuadPisot α) (hne : α ≠ golden) :
    α ∈ MahlerZ := by
  obtain ⟨hα1, β, a, b, hβ0, hβabs, hsum, hprod⟩ := h
  have hp : Pair α β a b := ⟨hα1, hβabs, hsum, hprod⟩
  have hα0 : (0 : ℝ) < α := lt_trans zero_lt_one hα1
  rcases lt_trichotomy β 0 with hneg | hzero | hpos
  · -- the negative-conjugate family: `1 ≤ b ≤ a`
    have hβgt : -1 < β := hp.neg_one_lt_beta
    have hbpos : 0 < b := by
      have h1 : -(b : ℝ) < 0 := by rw [← hprod]; exact mul_neg_of_pos_of_neg hα0 hneg
      have h2 : (0 : ℝ) < (b : ℝ) := by linarith
      exact_mod_cast h2
    have hapos : 0 < a := by
      have h2 : (0 : ℝ) < (a : ℝ) := by rw [← hsum]; linarith
      exact_mod_cast h2
    have hba : b ≤ a := by
      have hmul : (0 : ℝ) < (1 + α) * (1 + β) :=
        mul_pos (by linarith) (by linarith)
      have hkey : (0 : ℝ) < 1 + (a : ℝ) - (b : ℝ) := by nlinarith [hsum, hprod]
      have h2 : (0 : ℤ) < 1 + a - b := by exact_mod_cast hkey
      omega
    rcases (by omega : a = 1 ∨ a = 2 ∨ 3 ≤ a) with ha | ha | ha
    · -- `a = 1`, hence `b = 1` and `α` is the golden mean
      exfalso
      have hb1 : b = 1 := by omega
      subst ha; subst hb1
      have hsq : α ^ 2 = α + 1 := by have := hp.sq_alpha; push_cast at this; linarith
      have h5 : (2 * α - 1) ^ 2 = 5 := by nlinarith
      have hroot : 2 * α - 1 = Real.sqrt 5 := by
        rw [← h5, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 2 * α - 1)]
      exact hne (by rw [golden, ← hroot]; ring)
    · -- `a = 2`, so `b = 1` (Theorem A) or `b = 2` (`1 + √3`)
      subst ha
      rcases (by omega : b = 1 ∨ b = 2) with hb | hb
      · subst hb
        exact mem_MahlerZ_of_neg hp hneg ⟨1, by ring⟩ (by rintro ⟨k, hk⟩; omega)
      · subst hb
        have hsq : α ^ 2 = 2 * α + 2 := by have := hp.sq_alpha; push_cast at this; linarith
        have h3 : (α - 1) ^ 2 = 3 := by nlinarith
        have hroot : α - 1 = Real.sqrt 3 := by
          rw [← h3, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ α - 1)]
        have : α = 1 + Real.sqrt 3 := by linarith
        rw [this]; exact oneAddSqrtThree_mem_MahlerZ
    · -- `a ≥ 3`, so `α > 3`: Tijdeman
      have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      exact mem_MahlerZ_of_three_le (by linarith [hsum])
  · exact absurd hzero hβ0
  · exact mem_MahlerZ_of_pos hp hpos

/-- **Theorem B.**  Among the quadratic Pisot numbers, membership in `𝒮` characterises the
golden mean. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem quadPisot_mem_S_iff {α : ℝ} (h : IsQuadPisot α) : α ∈ S ↔ α = golden := by
  constructor
  · intro hS
    by_contra hne
    exact hS.2 (quadPisot_mem_MahlerZ h hne)
  · rintro rfl; exact golden_mem_S

/-- **[Dub06EO] Problem 5 loses its whole natural class.**  No quadratic Pisot number
greater than `2` lies in `𝒮`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem quadPisot_notMem_S_of_two_lt {α : ℝ} (h : IsQuadPisot α) (hα : 2 < α) :
    α ∉ S := by
  intro hS
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h5 : Real.sqrt 5 < 3 := by nlinarith
  have he := (quadPisot_mem_S_iff h).mp hS
  rw [he, golden] at hα
  linarith

end SZ
