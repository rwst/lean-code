/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith

@[expose] public section
/-!
# Two gap-fillers for `padicVal` arithmetic

Both statements below are standard and both are missing from Mathlib, which has the
`ℚ`-valued versions of the first and only the *even*-exponent half of the second.

## Main statements

* `padicValInt_neg` — `v_p(-z) = v_p(z)`.

* `padicValInt_add_eq_min` — the ultrametric equality on `ℤ`: if `x` and `y` have
  distinct `p`-adic valuations then `v_p(x + y) = min (v_p x) (v_p y)`.  Mathlib has
  `padicValRat.add_eq_min` (and the inequality `padicValRat.min_le_padicValRat_add`);
  this is the `ℤ`-valued transport, which avoids the `ℤ`-valued `padicValRat` and the
  casts at every use site.  Destination: `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`.

* `padicValNat.pow_two_sub_one_of_odd` — the odd-exponent companion of Mathlib's
  lifting-the-exponent lemma `padicValNat.pow_two_sub_one`.  The latter computes
  `v_2(x^n - 1)` for odd `x` and *even* `n`; for odd `n` no lifting happens at all and
  `v_2(x^n - 1) = v_2(x - 1)`, because `x^n - 1 = (x-1)(x^{n-1} + ⋯ + 1)` and the
  second factor is a sum of an odd number of odd terms.  Together the two lemmas give
  the complete closed form.  Destination: `Mathlib/NumberTheory/Multiplicity.lean`.
-/

/-- The `p`-adic valuation on `ℤ` is invariant under negation (it factors through
`Int.natAbs`). -/
theorem padicValInt_neg (p : ℕ) (z : ℤ) : padicValInt p (-z) = padicValInt p z := by
  simp [padicValInt]

/-- **Ultrametric equality on `ℤ`**: if `x` and `y` have distinct `p`-adic valuations,
then `v_p(x + y) = min (v_p x) (v_p y)`.  The `ℤ`-valued transport of
`padicValRat.add_eq_min`. -/
theorem padicValInt_add_eq_min {p : ℕ} [hp : Fact (Nat.Prime p)] {x y : ℤ}
    (hxy : x + y ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : padicValInt p x ≠ padicValInt p y) :
    padicValInt p (x + y) = min (padicValInt p x) (padicValInt p y) := by
  have hq : ((x : ℚ) + (y : ℚ)) ≠ 0 := by exact_mod_cast hxy
  have key := padicValRat.add_eq_min (p := p) hq (by exact_mod_cast hx) (by exact_mod_cast hy)
    (by simpa [padicValRat.of_int] using fun hh => h (by exact_mod_cast hh))
  rw [show ((x : ℚ) + y) = ((x + y : ℤ) : ℚ) by push_cast; ring] at key
  simp only [padicValRat.of_int] at key
  exact_mod_cast key

/-- **Odd-exponent companion of lifting-the-exponent at `p = 2`**: for odd `x > 1` and
*odd* `n`, no lifting occurs and `v_2(x^n - 1) = v_2(x - 1)`.

Mathlib's `padicValNat.pow_two_sub_one` covers the even-exponent half; this is the other
half, so that between them `v_2(x^n - 1)` is determined for every `n ≠ 0`.

The proof is the factorization `x^n - 1 = (x - 1) · ∑_{i<n} x^i`, whose second factor is
a sum of `n` odd terms and hence odd for odd `n`. -/
theorem padicValNat.pow_two_sub_one_of_odd {x n : ℕ} (h1x : 1 < x) (hx : ¬2 ∣ x)
    (hn : Odd n) : padicValNat 2 (x ^ n - 1) = padicValNat 2 (x - 1) := by
  have hx1 : 1 ≤ x := le_of_lt h1x
  have hxn1 : 1 ≤ x ^ n := Nat.one_le_pow _ _ (by omega)
  have hfac : x ^ n - 1 = (x - 1) * ∑ i ∈ Finset.range n, x ^ i := by
    have h : ((x : ℤ) ^ n - 1) = ((x : ℤ) - 1) * ∑ i ∈ Finset.range n, (x : ℤ) ^ i := by
      rw [mul_comm]; exact (geom_sum_mul _ _).symm
    zify [hx1, hxn1]
    linarith [h]
  have hsum_odd : ¬2 ∣ ∑ i ∈ Finset.range n, x ^ i := by
    have hmod : (∑ i ∈ Finset.range n, x ^ i) % 2 = 1 := by
      rw [Finset.sum_nat_mod]
      have hterm : ∀ i ∈ Finset.range n, x ^ i % 2 = 1 := by
        intro i _
        rw [Nat.pow_mod, Nat.two_dvd_ne_zero.mp hx]
        simp
      rw [Finset.sum_congr rfl hterm]
      simp [Nat.odd_iff.mp hn]
    omega
  have hne1 : x - 1 ≠ 0 := by omega
  have hne2 : (∑ i ∈ Finset.range n, x ^ i) ≠ 0 := by
    intro h; rw [h] at hsum_odd; simp at hsum_odd
  rw [hfac, padicValNat.mul hne1 hne2, padicValNat.eq_zero_of_not_dvd hsum_odd, add_zero]
