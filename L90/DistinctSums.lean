/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Algebra.BigOperators.Intervals
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Lagarias — Distinctness of the integers `∑ 2^{aᵢ} 3ⁱ` (Lag90, §2, Corollary 2.1a)

Jeffrey C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arithmetica **56**
(1990), 33–53, **Corollary 2.1a**.

**Corollary 2.1a.** *For fixed `k`, the integers*
```
  ∑_{i=0}^{k} 2^{aᵢ} 3ⁱ,      a₀ > a₁ > ⋯ > a_k ≥ 0,                                       (2.3)
```
*are all distinct* — equivalently, the map from a strictly decreasing exponent vector
`(a₀ > a₁ > ⋯ > a_k)` to the integer `∑ 2^{aᵢ} 3ⁱ` is **injective** (`corollary_2_1a`: equal sums
force `aᵢ = bᵢ` for all `i ≤ k`).

These integers are (a reindexing of) the numerators of the rational `3x+1` cycles: distinctness is the
arithmetic underpinning of the uniqueness in Theorem 2.1 ([[l90-rational-cycles-corpus-root]],
`L90.theorem_2_1`) — the injectivity of the parity-sequence ↦ cycle correspondence.

## Coppersmith's direct proof

Lagarias gives a direct proof due to Don Coppersmith. Since `a_k` is the **smallest** exponent, every
term of `B = ∑_{i=0}^{k} 2^{aᵢ} 3ⁱ` is divisible by `2^{a_k}`, and
```
  B = 2^{a_k} · (3^k + ∑_{i<k} 2^{aᵢ - a_k} 3ⁱ) = 2^{a_k} · (odd),
```
because `3^k` is odd while each `i < k` term is even (`aᵢ - a_k ≥ 1`). Hence `2^{a_k}` is the **highest
power of `2` dividing `B`** (`val_eq`: `padicValNat 2 B = a_k`). This recovers `a_k` from `B`; subtract
`2^{a_k} 3^k` and recurse on `B' = ∑_{i<k} 2^{aᵢ} 3ⁱ` to recover all the `aᵢ`, proving uniqueness of
the representation `(2.3)`.

## Contents
* `val_eq` — Coppersmith's key fact: `padicValNat 2 (∑_{i≤k} 2^{aᵢ} 3ⁱ) = a_k` when `a_k` is the
  strict minimum exponent.
* `corollary_2_1a` — Corollary 2.1a: the representation `(2.3)` is unique (the sums are distinct).

## References
* [Lag90] Lagarias, Jeffrey C. *The set of rational cycles for the `3x+1` problem.* Acta Arithmetica
  56 (1990), 33–53 (§2, Corollary 2.1a; the direct proof is credited to Don Coppersmith).
-/

namespace L90

open Finset

/-- **Coppersmith's key fact.** If `a_k` is the strict minimum among the exponents `a₀, …, a_k`
(`a_k < aᵢ` for `i < k`), then `2^{a_k}` is the highest power of `2` dividing `∑_{i≤k} 2^{aᵢ} 3ⁱ`:
`padicValNat 2 (∑_{i≤k} 2^{aᵢ} 3ⁱ) = a_k`. *Proof:* factor out `2^{a_k}`; the cofactor
`3^k + ∑_{i<k} 2^{aᵢ - a_k} 3ⁱ` is odd (`3^k` odd, the rest even since `aᵢ - a_k ≥ 1`). -/
@[category API, AMS 11, ref "Lag90"]
theorem val_eq (k : ℕ) (a : ℕ → ℕ) (ha : ∀ i, i < k → a k < a i) :
    padicValNat 2 (∑ i ∈ range (k + 1), 2 ^ (a i) * 3 ^ i) = a k := by
  -- factor `2^{a_k}` out of every term (`a_k ≤ aᵢ` for `i ≤ k`)
  have hfact : (∑ i ∈ range (k + 1), 2 ^ (a i) * 3 ^ i)
      = 2 ^ (a k) * ∑ i ∈ range (k + 1), 2 ^ (a i - a k) * 3 ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hge : a k ≤ a i := by
      rcases Nat.eq_or_lt_of_le (show i ≤ k by omega) with h | h
      · exact le_of_eq (congrArg a h).symm
      · exact (ha i h).le
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hge]
  -- the cofactor is odd: the `i = k` term is `3^k` (odd), every `i < k` term is even
  have hodd : Odd (∑ i ∈ range (k + 1), 2 ^ (a i - a k) * 3 ^ i) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
    refine Even.add_odd ?_ (Odd.pow ⟨1, rfl⟩)
    obtain ⟨c, hc⟩ : 2 ∣ ∑ i ∈ range k, 2 ^ (a i - a k) * 3 ^ i :=
      Finset.dvd_sum (fun i hi => Dvd.dvd.mul_right
        (dvd_pow_self 2 (by rw [Finset.mem_range] at hi; have := ha i hi; omega)) _)
    exact ⟨c, by omega⟩
  have hm_ne : (∑ i ∈ range (k + 1), 2 ^ (a i - a k) * 3 ^ i) ≠ 0 := by
    have := Nat.odd_iff.mp hodd; omega
  have hm2 : ¬ (2 ∣ ∑ i ∈ range (k + 1), 2 ^ (a i - a k) * 3 ^ i) := by
    have := Nat.odd_iff.mp hodd; omega
  rw [hfact, padicValNat_base_pow_mul (by norm_num) hm_ne,
    padicValNat.eq_zero_of_not_dvd hm2, zero_add]

/-- **Corollary 2.1a (Lagarias 1990, §2; direct proof due to Coppersmith).** *For fixed `k`, the
integers `∑_{i=0}^{k} 2^{aᵢ} 3ⁱ` with `a₀ > a₁ > ⋯ > a_k ≥ 0` are all distinct.* Stated as injectivity:
if two strictly decreasing exponent vectors `a, b` (on `{0, …, k}`) give the same sum, then `aᵢ = bᵢ`
for every `i ≤ k`.

*Proof:* induction on `k`. The smallest exponent `a_k = padicValNat 2 B = b_k` is recovered from the
common value `B` by `val_eq`; subtract the `i = k` term and apply the inductive hypothesis to the
remaining length-`k` sum. -/
@[category research solved, AMS 11, ref "Lag90", group "lag90_rational_cycles"]
theorem corollary_2_1a (k : ℕ) (a b : ℕ → ℕ)
    (ha : StrictAntiOn a (Set.Iic k)) (hb : StrictAntiOn b (Set.Iic k))
    (h : ∑ i ∈ range (k + 1), 2 ^ (a i) * 3 ^ i = ∑ i ∈ range (k + 1), 2 ^ (b i) * 3 ^ i) :
    ∀ i ≤ k, a i = b i := by
  induction k generalizing a b with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    have h0 : 2 ^ a 0 = 2 ^ b 0 := by simpa using h
    exact Nat.pow_right_injective (by norm_num) h0
  | succ k ih =>
    -- `a (k+1) = padicValNat 2 B = b (k+1)` is the smallest exponent
    have hva : ∀ i, i < k + 1 → a (k + 1) < a i := fun i hik =>
      ha (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr le_rfl) hik
    have hvb : ∀ i, i < k + 1 → b (k + 1) < b i := fun i hik =>
      hb (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr le_rfl) hik
    have hak : a (k + 1) = b (k + 1) := by
      have e1 := val_eq (k + 1) a hva
      have e2 := val_eq (k + 1) b hvb
      rw [h, e2] at e1
      exact e1.symm
    -- subtract the top term, recurse
    have hpeel : ∑ i ∈ range (k + 1), 2 ^ (a i) * 3 ^ i
        = ∑ i ∈ range (k + 1), 2 ^ (b i) * 3 ^ i := by
      have e := h
      rw [Finset.sum_range_succ (fun i => 2 ^ (a i) * 3 ^ i),
        Finset.sum_range_succ (fun i => 2 ^ (b i) * 3 ^ i), hak] at e
      omega
    have ihres := ih a b (ha.mono (Set.Iic_subset_Iic.mpr (by omega)))
      (hb.mono (Set.Iic_subset_Iic.mpr (by omega))) hpeel
    intro i hi
    rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · rw [heq]; exact hak
    · exact ihres i (by omega)

end L90
