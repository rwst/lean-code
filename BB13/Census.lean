/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.FailureCount

/-!
# The relation-tower census of the certified range (W6 of plan2-BB13)

Everything known about the failures of Problem 10.13 lives in `E ∩ [1, 256] = {1, 2, 3, 4, 7}`
(`BB13.failuresUpTo_256_eq`).  This file determines their **line structure** in the kernel, and
the answer corrects a claim of the first version of this development.

## The census

Through `BB13.Mnum_eq_mNat` the slope test becomes a decidable identity of naturals
(`sameTower_iff_nat`), and the five certified failures carry the frame points

| `n` | `mₙ` | `(x, y) = (mₙ2ⁿ, 3ⁿ)` | slope |
|---|---|---|---|
| 1 | 2 | `(4, 3)` | `4/3` |
| 2 | 2 | `(8, 9)` | `8/9` |
| 3 | 3 | `(24, 27)` | `8/9` |
| 4 | 5 | `(80, 81)` | `80/81` |
| 7 | 17 | `(2176, 2187)` | `2176/2187` |

so the relation-tower partition is `{1}, {2, 3}, {4}, {7}` (`census_sameTower`): **four** lines
carrying five failures.  Against that, the five are pairwise *un*-`Linkable`
(`census_not_linkable`): **five** threshold-towers.  The pair `n = 2`, `n = 3` is the witness
that the two notions differ — `(24, 27) = 3·(8, 9)` is a genuine scaling relation while
`2·(3/4)²·3 = 27/8 > 1` puts the pair outside the reach of the §3 gap principle
(`sameTower_two_three`, `not_linkable_two_three`).  The observed relation-tower height in the
certified range is therefore `2`, not `1`.

## The towers are complete

The confinement of `BB13/LineTower.lean` bounds a companion of `b` by `2b`, so a companion of a
certified failure would itself lie in `[1, 14) ⊆ [1, 256]` and hence be certified.  Combining with
the census determines every known line-fibre outright (`lineFibre_two_eq`,
`lineFibre_eq_singleton`):

`lineFibre (linePoint 2) = {2, 3}`,  `lineFibre (linePoint b) = {b}` for `b ∈ {1, 4, 7}`.

No known relation-tower can grow, and the hypothesis of
`BB13.failures_card_le_of_heightBound` — a bound on the fibres above `n = 256` — concerns a range
in which the `10⁶` scan of `BB13/m0_failures.py` finds no failure at all.

Footprint: `std3` throughout (kernel `decide` only; no `native_decide`).

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* [DD90] Delmer–Deshouillers, Math. Comp. **54** (1990) — the exact-integer scan.
* `plans/plan2-BB13.html` (W6); `plans/report-BB13.md` item F2.
-/

namespace BB13

open scoped Real

/-! ### The decidable slope test -/

/-- **The line test, decidably**: two indices share a line exactly when
`3ᵃ·(m_b 2ᵇ) = mₐ2ᵃ·3ᵇ`, an identity of naturals. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_iff_nat (a b : ℕ) :
    SameTower a b ↔ 3 ^ a * (mNat b * 2 ^ b) = mNat a * 2 ^ a * 3 ^ b := by
  rw [SameTower, linePoint_eq_iff_collinear, CollinearPts, failPoint, failPoint, Mnum_eq_mNat,
    Mnum_eq_mNat]
  push_cast
  constructor <;> intro h <;> exact_mod_cast h

/-! ### The census of `E ∩ [1, 256] = {1, 2, 3, 4, 7}` -/

/-- **The `{2, 3}` collision**: the frame points `(8, 9)` and `(24, 27) = 3·(8, 9)` are collinear,
so `n = 2` and `n = 3` form a relation-tower of height `2`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_two_three : SameTower 2 3 := by rw [sameTower_iff_nat]; decide

/-- **…but they are not `Linkable`**: `2·(3/4)²·3 = 27/8 > 1`, so the §3 gap principle does not
reach the pair.  Collinearity is strictly weaker than threshold-linkage — the concrete form of
the referee's objection F2. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem not_linkable_two_three : ¬ Linkable 3 (3 / 4) 2 3 := by
  rw [Linkable]; norm_num

/-- **The relation-tower census**: on the certified failures, sharing a line means being equal or
being the pair `{2, 3}`.  The partition is `{1}, {2, 3}, {4}, {7}` — four lines. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem census_sameTower {a b : ℕ} (ha : a ∈ ({1, 2, 3, 4, 7} : Finset ℕ))
    (hb : b ∈ ({1, 2, 3, 4, 7} : Finset ℕ)) :
    SameTower a b ↔ (a = b ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rw [sameTower_iff_nat]
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- **The threshold-tower census**: the five certified failures are pairwise un-`Linkable`, i.e.
each is a tower base — five threshold-towers against four relation-towers. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem census_not_linkable {a b : ℕ} (ha : a ∈ ({1, 2, 3, 4, 7} : Finset ℕ))
    (hb : b ∈ ({1, 2, 3, 4, 7} : Finset ℕ)) (hab : a < b) : ¬ Linkable 3 (3 / 4) a b := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rw [Linkable]
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    first
      | omega
      | norm_num

/-! ### The known towers are complete -/

/-- A certified failure's line carries only certified failures: a companion of `b ≤ 7` lies below
`2b ≤ 14`, hence inside the kernel-verified range. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem lineFibre_subset_census {b : ℕ} (hb : b ∈ ({1, 2, 3, 4, 7} : Finset ℕ)) :
    lineFibre (linePoint b) ⊆ ({1, 2, 3, 4, 7} : Set ℕ) := by
  have hb7 : 1 ≤ b ∧ b ≤ 7 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb; omega
  rintro n ⟨hn1, hnf, hr⟩
  have hn256 : n ≤ 256 := by
    rcases le_or_gt n b with h | h
    · omega
    · have hb0 : 1 ≤ b := hb7.1
      have hfb : IsFailure 3 2 (3 / 4) b := by
        rw [failures_up_to_256 b hb7.1 (by omega)]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb; omega
      have := sameTower_lt_two_mul hb0 h hnf hr.symm
      omega
  have := (failures_up_to_256 n hn1 hn256).mp hnf
  simpa using this

/-- **The `{2, 3}` tower, determined**: the line of slope `8/9` carries exactly the failures
`2` and `3`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem lineFibre_two_eq : lineFibre (linePoint 2) = {2, 3} := by
  apply Set.Subset.antisymm
  · intro n hn
    have hmem := lineFibre_subset_census (b := 2) (by decide) hn
    have hsame : SameTower 2 n := hn.2.2.symm
    have hn' : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 7 := by simpa using hmem
    have := (census_sameTower (a := 2) (b := n) (by decide)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)).mp hsame
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rintro n (rfl | rfl)
    · exact ⟨by norm_num, (isFailure_iff_failNat 2).mpr (by decide), rfl⟩
    · exact ⟨by norm_num, (isFailure_iff_failNat 3).mpr (by decide), sameTower_two_three.symm⟩

/-- **The singleton towers, determined**: the lines of `n = 1`, `4`, `7` carry that failure
alone. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem lineFibre_eq_singleton {b : ℕ} (hb : b = 1 ∨ b = 4 ∨ b = 7) :
    lineFibre (linePoint b) = {b} := by
  have hbmem : b ∈ ({1, 2, 3, 4, 7} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  apply Set.Subset.antisymm
  · intro n hn
    have hmem := lineFibre_subset_census hbmem hn
    have hn' : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 7 := by simpa using hmem
    have hnmem : n ∈ ({1, 2, 3, 4, 7} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have := (census_sameTower hbmem hnmem).mp hn.2.2.symm
    simp only [Set.mem_singleton_iff]
    omega
  · rintro n rfl
    refine ⟨by omega, ?_, rfl⟩
    rw [isFailure_iff_failNat]
    rcases hb with rfl | rfl | rfl <;> decide

end BB13
