/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.Basic
import ForMathlib.Data.Rat.NearestInt
import CITED.CorvajaZannier

/-!
# The Nair–Kumar–Rout S-unit tuple theorem (arXiv 2506.02898): vocabulary and refutation

**⚠ THE CITED AXIOM FORMERLY RECORDED HERE WAS FALSE — retired 2026-07-14.**
This file carried `NKR.sUnit_pair_integrality`, a faithful ℚ-specialized
transcription of **Theorem 1.3(i)** of the unrefereed preprint [NKR25] (statement
verified against the paper 2026-07-06).  That theorem is **false as printed**:
inequality (1) of [NKR25] reads `‖∑ αᵢuᵢ‖ < (∏ H(uᵢ))^{-ε₁}` with no strict
positivity on the left (their Theorem 1.1(iv) *does* carry `0 <`), so families whose
linear combination is an *exact* integer slip through.  The family
`(u₁, u₂) = (3^m/2, 3^{2m}/2)` satisfies every hypothesis — `(3^m + 3^{2m})/2 ∈ ℤ`
by parity, ratios `3^{-m}` pairwise distinct — while no entry is ever an algebraic
integer, contradicting conclusion (i).  The machine-checked refutation is
`NKR.thm13i_unrepaired_false` below (std3-clean).  The gap in the paper's §4.1 proof
is the uniform-`ε` step: their `κ` (hence `ε`) depends on the tuple, while their
Lemma 2.2 requires one fixed `ε`.

**The repair and the derivation.**  Adding the per-member strict positivity
`0 < ‖α₁u₁ + α₂u₂‖` repairs the statement, and over `ℚ` (`m = 2`, `Γ = ⟨2,3⟩`) the
repaired theorem is **provable** from the `S`-arithmetic Subspace Theorem at `n = 3`
— no axiom needed.  See `CITED/NairKumarRoutProof.lean`
(`NKR.pair_finite`, `NKR.sUnit_pair_integrality_of_subspace`; machinery in
`CITED/NairKumarRoutLemmas.lean`); the consumer `TH/GapDichotomy.lean` discharges
positivity by parity.  [NKR25] remains cited as the statement template and for
attribution — not as authority.

## Statement conventions (the ℚ-specialization)

* **Group**: `Γ = ⟨2, 3⟩ ≤ ℚ*`, exponent-encoded — `NKR.uval x y = 2^x·3^y`
  (a bijection onto `Γ`, so an infinite encoded set is an infinite tuple set).
* **Tuple length**: `m = 2` (all our uses), coefficients `α₁, α₂ ∈ ℚ*`.
* **(P1)** is vacuous over `ℚ`; **(P2)** over `ℚ` reduces to `u₁ ≠ -u₂`.
* **Height**: `H(2^x·3^y)` is the explicit `CZ.height23`;
  `‖·‖ = Rat.distToNearestInt`; thresholds live in `ℝ` via `rpow`.

## Contents

* `NKR.uval` — the value `2^x·3^y` under the exponent encoding of `Γ = ⟨2,3⟩`.
* `NKR.uval_neg_natCast` — the consumer's instance `uval (-n) n = (3/2)^n`.
* `NKR.thm13i_unrepaired_false` — **the refutation** of the unrepaired
  Theorem 1.3(i) transcription (the retired axiom's exact statement).

## References

* [NKR25] Nair, Parvathi S., Veekesh Kumar, and S. S. Rout. "Algebraic
  approximations to linear combinations of S-units." arXiv:2506.02898
  (v3, 18 Nov 2025). **Unrefereed preprint; Theorem 1.3(i) refuted below.**
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §6.3 (Stage 2c), §10.1.
* `report-formalize-subspace.html` §4, §6 (the refactor this file's repair
  completes).
-/

namespace NKR

/-- The value `u = 2^x·3^y` of the Main-Theorem tuples under the exponent
encoding of `Γ = ⟨2, 3⟩`. -/
@[category API, AMS 11, ref "NKR25", group "three_halves_m4"]
def uval (x y : ℤ) : ℚ := (2 : ℚ) ^ x * (3 : ℚ) ^ y

/-- The consumer's instance of the encoding: `uval (-n) n = (3/2)^n`. -/
@[category API, AMS 11, ref "NKR25", group "three_halves_m4"]
lemma uval_neg_natCast (n : ℕ) : uval (-(n : ℤ)) n = (3 / 2 : ℚ) ^ n := by
  unfold uval
  rw [zpow_neg, zpow_natCast, zpow_natCast, div_pow, inv_mul_eq_div]

private lemma uval_neg_one_pow (m : ℤ) : uval (-1) m = 2⁻¹ * (3 : ℚ) ^ m := by
  unfold NKR.uval
  rw [zpow_neg_one]

private lemma cast_pow_eq_zpow (n : ℕ) : (((3 : ℤ) ^ n : ℤ) : ℚ) = (3 : ℚ) ^ ((n : ℕ) : ℤ) := by
  push_cast
  rw [zpow_natCast]

/-- **The unrepaired [NKR25] Theorem 1.3(i) is false** (⚠ machine-checked
refutation): the ∀-closure of the statement previously recorded here as the cited
axiom `sUnit_pair_integrality` — i.e. Theorem 1.3(i) of the preprint, ℚ-specialized
exactly as documented above — is **disprovable** in plain Lean + Mathlib.  The
witness family is `(u₁, u₂) = (3^m/2, 3^{2m}/2)`, `m ≥ 1`: the sum
`(3^m + 3^{2m})/2` is an *exact* integer by parity, so the distance to `ℤ` is `0`,
which inequality (1) of [NKR25] does not exclude; the ratios `3^{-m}` are pairwise
distinct and all other hypotheses hold — yet no entry is ever an integer.  The
repaired (strict-positivity) statement is *proved* in
`CITED/NairKumarRoutProof.lean`. -/
@[category research solved, AMS 11, ref "NKR25", group "three_halves_m4"]
theorem thm13i_unrepaired_false :
    ¬ (∀ (α₁ α₂ : ℚ), α₁ ≠ 0 → α₂ ≠ 0 → ∀ (ε₁ : ℝ), 0 < ε₁ →
      ∀ (𝒩 : Set ((ℤ × ℤ) × (ℤ × ℤ))), 𝒩.Infinite →
      (∀ q ∈ 𝒩, 1 ≤ |uval q.1.1 q.1.2| ∧ 1 ≤ |uval q.2.1 q.2.2|) →
      (∀ q ∈ 𝒩, uval q.1.1 q.1.2 ≠ -uval q.2.1 q.2.2) →
      (∀ q ∈ 𝒩, ∀ q' ∈ 𝒩, q ≠ q' →
        uval q.1.1 q.1.2 / uval q.2.1 q.2.2 ≠ uval q'.1.1 q'.1.2 / uval q'.2.1 q'.2.2 ∧
        uval q.2.1 q.2.2 / uval q.1.1 q.1.2 ≠ uval q'.2.1 q'.2.2 / uval q'.1.1 q'.1.2) →
      (∀ q ∈ 𝒩,
        ((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℝ)
          < ((CZ.height23 q.1.1 q.1.2 * CZ.height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)) →
      ∃ q ∈ 𝒩, (∃ n : ℤ, uval q.1.1 q.1.2 = n) ∧ (∃ n : ℤ, uval q.2.1 q.2.2 = n)) := by
  intro H
  -- the family: F m = ((-1, m+1), (-1, 2(m+1)))
  set F : ℕ → ((ℤ × ℤ) × (ℤ × ℤ)) :=
    fun m => ((-1, (m : ℤ) + 1), (-1, 2 * ((m : ℤ) + 1))) with hF
  have hFinj : Function.Injective F := by
    intro a b hab
    have := congrArg (fun q => q.1.2) hab
    simpa [hF] using this
  have hmem : ∀ q ∈ Set.range F, ∃ m : ℤ, 1 ≤ m ∧ q = ((-1, m), (-1, 2 * m)) := by
    rintro q ⟨m, rfl⟩
    exact ⟨(m : ℤ) + 1, by omega, rfl⟩
  -- entries are ≥ 1 in absolute value
  have habs : ∀ q ∈ Set.range F, 1 ≤ |uval q.1.1 q.1.2| ∧ 1 ≤ |uval q.2.1 q.2.2| := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := hmem q hq
    have h1 : (1 : ℚ) ≤ 2⁻¹ * (3 : ℚ) ^ m := by
      have h3 : (3 : ℚ) ^ (1 : ℤ) ≤ (3 : ℚ) ^ m := zpow_le_zpow_right₀ (by norm_num) hm
      rw [zpow_one] at h3
      linarith
    have h2 : (1 : ℚ) ≤ 2⁻¹ * (3 : ℚ) ^ (2 * m) := by
      have h3 : (3 : ℚ) ^ (1 : ℤ) ≤ (3 : ℚ) ^ (2 * m) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_one] at h3
      linarith
    constructor
    · rw [uval_neg_one_pow, abs_of_pos (by positivity)]; exact h1
    · rw [uval_neg_one_pow, abs_of_pos (by positivity)]; exact h2
  -- (P2)
  have hP2 : ∀ q ∈ Set.range F, uval q.1.1 q.1.2 ≠ -uval q.2.1 q.2.2 := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := hmem q hq
    have h1 : (0 : ℚ) < uval (-1) m := by rw [uval_neg_one_pow]; positivity
    have h2 : (0 : ℚ) < uval (-1) (2 * m) := by rw [uval_neg_one_pow]; positivity
    intro h
    rw [h] at h1
    linarith
  -- distinct ratios (both orders)
  have hratio : ∀ q ∈ Set.range F, ∀ q' ∈ Set.range F, q ≠ q' →
      uval q.1.1 q.1.2 / uval q.2.1 q.2.2 ≠ uval q'.1.1 q'.1.2 / uval q'.2.1 q'.2.2 ∧
      uval q.2.1 q.2.2 / uval q.1.1 q.1.2 ≠ uval q'.2.1 q'.2.2 / uval q'.1.1 q'.1.2 := by
    intro q hq q' hq' hne
    obtain ⟨m, hm, rfl⟩ := hmem q hq
    obtain ⟨m', hm', rfl⟩ := hmem q' hq'
    have hmm' : m ≠ m' := by
      intro h
      exact hne (by rw [h])
    have hdiv : ∀ k l : ℤ, uval (-1) k / uval (-1) l = (3 : ℚ) ^ (k - l) := by
      intro k l
      rw [uval_neg_one_pow, uval_neg_one_pow, zpow_sub₀ (by norm_num : (3:ℚ) ≠ 0)]
      have h3l : (3 : ℚ) ^ l ≠ 0 := zpow_ne_zero _ (by norm_num)
      field_simp
    have hinj : ∀ a b : ℤ, (3 : ℚ) ^ a = (3 : ℚ) ^ b → a = b := by
      intro a b hab
      exact zpow_right_injective₀ (by norm_num) (by norm_num) hab
    constructor
    · rw [hdiv, hdiv]
      intro h
      have h2 : m - 2 * m = m' - 2 * m' := hinj _ _ h
      omega
    · rw [hdiv, hdiv]
      intro h
      have h2 : 2 * m - m = 2 * m' - m' := hinj _ _ h
      omega
  -- the sum is an exact integer: distance 0
  have happrox : ∀ q ∈ Set.range F,
      (((1 : ℚ) * uval q.1.1 q.1.2 + (1 : ℚ) * uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((CZ.height23 q.1.1 q.1.2 * CZ.height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-(1:ℝ)) := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := hmem q hq
    obtain ⟨n, rfl, hn⟩ : ∃ n : ℕ, m = (n : ℤ) ∧ 1 ≤ n := ⟨m.toNat, by omega, by omega⟩
    have h3odd : (3 : ℤ) ^ n % 2 = 1 := Int.odd_iff.mp (Odd.pow (by decide))
    obtain ⟨j, hj⟩ : ∃ j : ℤ, (3 : ℤ) ^ n = 2 * j + 1 := ⟨(3 : ℤ) ^ n / 2, by omega⟩
    have heven : (3 : ℤ) ^ n + (3 : ℤ) ^ (2 * n) = 2 * (2 * j ^ 2 + 3 * j + 1) := by
      rw [two_mul n, pow_add, hj]; ring
    set k : ℤ := 2 * j ^ 2 + 3 * j + 1 with hk
    have hz2 : (3 : ℚ) ^ (2 * ((n : ℕ) : ℤ)) = (((3 : ℤ) ^ (2 * n) : ℤ) : ℚ) := by
      rw [show (2 * ((n : ℕ) : ℤ)) = (((2 * n : ℕ) : ℕ) : ℤ) by push_cast; ring,
        ← cast_pow_eq_zpow]
    have hsum : (1 : ℚ) * uval (-1) (n : ℤ) + (1 : ℚ) * uval (-1) (2 * (n : ℤ)) = (k : ℚ) := by
      rw [uval_neg_one_pow, uval_neg_one_pow, ← cast_pow_eq_zpow, hz2]
      have h2 : (((3 : ℤ) ^ n : ℤ) : ℚ) + (((3 : ℤ) ^ (2 * n) : ℤ) : ℚ) = 2 * (k : ℚ) := by
        have hc := congrArg (fun z : ℤ => (z : ℚ)) heven
        push_cast at hc ⊢
        linarith
      linarith
    have hb : (0 : ℝ)
        < ((CZ.height23 (-1) (n : ℤ) : ℕ) : ℝ) * ((CZ.height23 (-1) (2 * (n : ℤ)) : ℕ) : ℝ) := by
      have h1 : 1 ≤ CZ.height23 (-1) (n : ℤ) := by
        rw [CZ.height23]
        exact le_max_of_le_left (Nat.one_le_iff_ne_zero.mpr (by positivity))
      have h2 : 1 ≤ CZ.height23 (-1) (2 * (n : ℤ)) := by
        rw [CZ.height23]
        exact le_max_of_le_left (Nat.one_le_iff_ne_zero.mpr (by positivity))
      exact_mod_cast Nat.mul_pos h1 h2
    rw [hsum, Rat.distToNearestInt_intCast]
    push_cast
    exact Real.rpow_pos_of_pos hb _
  -- apply the (false) statement
  obtain ⟨q, hq, ⟨n₁, hn₁⟩, -⟩ := H 1 1 one_ne_zero one_ne_zero 1 one_pos (Set.range F)
    (Set.infinite_range_of_injective hFinj) habs hP2 hratio happrox
  obtain ⟨m, hm, rfl⟩ := hmem q hq
  -- 3^m/2 = n₁ is impossible by parity
  obtain ⟨n, rfl, hn⟩ : ∃ n : ℕ, m = (n : ℤ) ∧ 1 ≤ n := ⟨m.toNat, by omega, by omega⟩
  rw [uval_neg_one_pow, ← cast_pow_eq_zpow] at hn₁
  have hkey : ((3 : ℤ) ^ n : ℚ) = ((2 * n₁ : ℤ) : ℚ) := by
    push_cast at hn₁ ⊢
    linarith
  have hkeyZ : (3 : ℤ) ^ n = 2 * n₁ := by exact_mod_cast hkey
  have h3odd : (3 : ℤ) ^ n % 2 = 1 := Int.odd_iff.mp (Odd.pow (by decide))
  omega


end NKR
