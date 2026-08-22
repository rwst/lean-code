/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.PracticalBound
import ForMathlib.Data.Real.NearestIntNatDiv

/-!
# M0 in the kernel: verifying the failure set `F = {1,2,3,4,7}` (D4 empirical anchor)

Milestone **M0** of `plans/plan-1013.html` is the exact-integer scan (`BB13/m0_failures.py`) certifying
`F = {1, 2, 3, 4, 7}` up to `n = 10⁶`.  This file asks: **how much of M0 can Lean derive natively?**

The obstacle is that `IsFailure 3 2 (3/4) n` is a *real* inequality (`‖(3/2)ⁿ‖ < (3/4)ⁿ`), not
decidable as stated.  The bridge below removes it:

* `isFailure_iff_failNat` — **`IsFailure 3 2 (3/4) n ↔ 2ⁿ·|kₙ| < 3ⁿ`**, the real predicate equals
  the exact-integer test `2ⁿ·residNat n < 3ⁿ`.  Its heart is `distToNearestInt_natCast_div`
  (ForMathlib): `‖(3/2)ⁿ‖ = min(3ⁿ mod 2ⁿ, 2ⁿ − 3ⁿ mod 2ⁿ)/2ⁿ = residNat n / 2ⁿ`.

Through it the failure set becomes a **decidable** statement about naturals, which the kernel
verifies for a bounded range:

* `failures_up_to_256` / `failuresUpTo_256_eq` — **`{n : 1 ≤ n ≤ 256, IsFailure 3 2 (3/4) n} =
  {1,2,3,4,7}`**, a genuine statement about the real `IsFailure`, proved by kernel `decide`,
  **axiom-free** (`std3` only — no `native_decide`, no `Lean.ofReduceBool`).
* `failuresUpTo_256_ncard` — hence `F(256) = 5`.  This is also the additive constant of the
  repaired count `BB13.failures_card_le_of_heightBound` (`#E ≤ 5 + H·K(ε*)`): the certified
  segment is spliced in rather than absorbed into a Diophantine constant.

## What Lean can and cannot do here

Kernel `decide` reaches `n ≤ 256` comfortably (the residues `3ⁿ mod 2ⁿ` are GMP bignums, but the
`List.range`/`∀ m < N` reduction is linear in `N`); `n` in the low thousands is feasible but slow.
The full `n = 10⁶` is out of the kernel's reach — the naive `3ⁿ mod 2ⁿ` is `Θ(n²)`-digit work per
`n` and the scan is a million-fold — and `native_decide` (which would clear `10⁴`–`10⁵`) is
disallowed as it trusts the compiler via `Lean.ofReduceBool`.  So the honest split stands: the
kernel certifies the initial segment against the *real* definition; the full `10⁶` record remains
`BB13/m0_failures.py`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 — Prob. 10.13.
* [DD90] F. Delmer, J.-M. Deshouillers, Math. Comp. **54** (1990) — the exact-integer recursion.
-/

namespace BB13

open scoped Real

/-- `‖(3/2)ⁿ‖ = residNat n / 2ⁿ`: the real nearest-integer distance is the exact-integer residue
`min(3ⁿ mod 2ⁿ, 2ⁿ − 3ⁿ mod 2ⁿ)` over `2ⁿ` (`distToNearestInt_natCast_div`). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem distToNearestInt_three_halves (n : ℕ) :
    distToNearestInt (((3 : ℝ) / 2) ^ n) = (residNat n : ℝ) / (2 : ℝ) ^ n := by
  have h32 : ((3 : ℝ) / 2) ^ n = ((3 ^ n : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) := by push_cast; rw [div_pow]
  rw [h32, distToNearestInt_natCast_div _ _ (show 0 < 2 ^ n by positivity)]
  simp only [residNat]; push_cast; ring

/-- **The bridge:** the real failure predicate `‖(3/2)ⁿ‖ < (3/4)ⁿ` equals the decidable
exact-integer test `2ⁿ · residNat n < 3ⁿ` (`= failNat n`).  Turns M0 into a kernel computation. -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem isFailure_iff_failNat (n : ℕ) : IsFailure 3 2 (3 / 4) n ↔ 2 ^ n * residNat n < 3 ^ n := by
  rw [isFailure_iff 3 2 (3 / 4) n (by norm_num)]
  simp only [Nat.cast_ofNat]
  rw [distToNearestInt_three_halves, div_lt_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ n by positivity)]
  have hrw : (3 / 4 : ℝ) ^ n * (2 : ℝ) ^ n = ((3 ^ n : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) := by
    rw [← mul_pow, show (3 / 4 : ℝ) * 2 = 3 / 2 by norm_num, div_pow]; norm_cast
  rw [hrw, lt_div_iff₀ (show (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) by positivity),
    show (residNat n : ℝ) * ((2 ^ n : ℕ) : ℝ) = ((residNat n * 2 ^ n : ℕ) : ℝ) by push_cast; ring,
    Nat.cast_lt, mul_comm]

set_option maxRecDepth 100000 in
/-- **M0 in the kernel:** for `1 ≤ n ≤ 256`, `‖(3/2)ⁿ‖ < (3/4)ⁿ` holds iff `n ∈ {1,2,3,4,7}` —
a statement about the real `IsFailure`, `decide`-verified, **axiom-free**. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem failures_up_to_256 (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 256) :
    IsFailure 3 2 (3 / 4) n ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 7 := by
  have H : ∀ m, m < 257 → 1 ≤ m →
      (2 ^ m * residNat m < 3 ^ m ↔ (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 7)) := by decide
  rw [isFailure_iff_failNat]
  exact H n (by omega) hn1

/-- **`F(256) = {1,2,3,4,7}`:** the D4 set `BB13.failuresUpTo 256` of failures up to `256` is
exactly `{1, 2, 3, 4, 7}`, kernel-verified against the real definition, axiom-free. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem failuresUpTo_256_eq : failuresUpTo 256 = {1, 2, 3, 4, 7} := by
  ext n
  simp only [failuresUpTo, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, hN, hf⟩; exact (failures_up_to_256 n h1 hN).mp hf
  · rintro (rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨by norm_num, by norm_num, (isFailure_iff_failNat _).mpr (by decide)⟩

/-- **`F(256) = 5`:** the five certified failures `{1, 2, 3, 4, 7}`, and the additive constant of
`BB13.failures_card_le_of_heightBound`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem failuresUpTo_256_ncard : (failuresUpTo 256).ncard = 5 := by
  rw [failuresUpTo_256_eq,
    show ({1, 2, 3, 4, 7} : Set ℕ) = ↑({1, 2, 3, 4, 7} : Finset ℕ) by simp, Set.ncard_coe_finset]
  decide

/-! ## The nearest-integer numerator, computably

`Mnum` is `round` of a real and hence noncomputable.  The exact-integer form
`mₙ = ⌊(2·3ⁿ + 2ⁿ)/2ⁿ⁺¹⌋` (rounding half up, as `round` does) makes the frame points — and with
them the line structure of `BB13/LineTower.lean` — decidable, which is what the relation-tower
census of `BB13/Census.lean` runs on. -/

/-- `mₙ = round((3/2)ⁿ)` as a natural-number computation: `(2·3ⁿ + 2ⁿ) / 2ⁿ⁺¹`. -/
def mNat (n : ℕ) : ℕ := (2 * 3 ^ n + 2 ^ n) / 2 ^ (n + 1)

/-- **The `Mnum` bridge:** `round((3/2)ⁿ) = (2·3ⁿ + 2ⁿ)/2ⁿ⁺¹`, the second half of M0's
"decidability" work (the first being `isFailure_iff_failNat`). -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem Mnum_eq_mNat (n : ℕ) : Mnum 3 2 n = (mNat n : ℤ) := by
  have h1 : (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ n + 1 / 2
      = ((2 * 3 ^ n + 2 ^ n : ℕ) : ℝ) / ((2 ^ (n + 1) : ℕ) : ℝ) := by
    push_cast
    rw [div_pow, pow_succ]
    field_simp
  rw [Mnum, round_eq, h1, Int.floor_div_natCast, Int.floor_natCast, mNat, Int.natCast_div]

end BB13
