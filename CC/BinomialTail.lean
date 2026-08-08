/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik

Ported into this corpus from `shaikidris/CET` v2.0.1, file
`lean/CollatzEndpointTransport/Common/TerrasBinomialTail.lean` (Lean 4.15.0).
Adaptation to Lean 4.32.0-rc1 by Ralf Stephan in collaboration with Claude Code.
Namespace `CollatzEndpointTransport.Terras` → `CC.ParityTail` (the plain name
`CC.oddCount` is already taken by `CC/ResidueGraphDrift.lean`).

The substantive change: the upstream file sits on its own parity-vector
bijection, which this corpus already has as `CC.terras_bijection`.  That layer
was therefore **not** ported.  `oddCount` is redefined on `ZMod (2 ^ k)` through
`CC.parityVec`, word weight is taken over `ZMod 2` rather than `Bool`, and the
exact binomial count is transported across `CC.terras_bijection` in place of the
upstream `terrasMap`.  The generating-function layer is unchanged.

Upstream Apache-2.0 header retained.
-/
import CC.TerrasBijection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Binomial tails for Terras parity words

Elementary tail bounds for the number of odd steps in the first `k` Terras
steps, i.e. for the weight of a parity word under the Terras–Everett bijection
`CC.parityVec k : ZMod (2 ^ k) ≃ (Fin k → ZMod 2)` ([Ter76], `CC.terras_bijection`).

The core estimate is the generating-function inequality

  `x ^ K * ∑_{j ≤ K} choose k j ≤ (1 + x) ^ k`   for `0 ≤ x ≤ 1`, `K ≤ k`,

which is finite combinatorics: no probability space, no independence
assumption, no asymptotics.  Choosing `x = exp (-4t)` and feeding
`Real.cosh_le_exp_half_sq` turns it into the explicit Hoeffding-type bound

  `#{r : ZMod (2 ^ k) | oddCount k r ≤ K} ≤ 2 ^ k * exp (-2 t ^ 2 k)`
      whenever `K ≤ (1/2 - t) * k`,

together with the mirror statement for the upper tail `k - K ≤ oddCount k r`.

The exact count `#{r | oddCount k r = j} = choose k j` is the precise sense in
which the odd-step count is `Binomial (k, 1/2)` under uniform residues: it is a
counting identity obtained by transporting word weights across the
Terras–Everett bijection, with no probabilistic hypothesis anywhere.
-/

namespace CC

namespace ParityTail

open Nat Finset

scoped instance neZeroTwoPow (k : ℕ) : NeZero ((2 : ℕ) ^ k) :=
  ⟨pow_ne_zero k two_ne_zero⟩

/-! ### The generating-function layer

Pure binomial combinatorics; nothing here mentions the Collatz map. -/

/-- The lower binomial tail through weight `K`. -/
@[category API, AMS 05, group "parity_tail"]
def lowerBinomialSum (k K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (K + 1), k.choose j

/-- The weighted binomial generating function is exactly `(1 + x) ^ k`. -/
@[category API, AMS 05, group "parity_tail"]
theorem weightedBinomialSum_eq (k : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * x ^ j) = (1 + x) ^ k := by
  simpa [add_comm, mul_comm] using (add_pow x 1 k).symm

/-- The elementary lower-tail generating-function bound. -/
@[category API, AMS 05, group "parity_tail"]
theorem pow_mul_lowerBinomialSum_le
    {k K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKk : K ≤ k) :
    x ^ K * (lowerBinomialSum k K : ℝ) ≤ (1 + x) ^ k := by
  calc
    x ^ K * (lowerBinomialSum k K : ℝ) =
        ∑ j ∈ Finset.range (K + 1), x ^ K * (k.choose j : ℝ) := by
          simp [lowerBinomialSum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (K + 1), (k.choose j : ℝ) * x ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hpow : x ^ K ≤ x ^ j := pow_le_pow_of_le_one hx0 hx1 hjK
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (k.choose j))
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * x ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ hKk))
      intro j _ _
      positivity
    _ = (1 + x) ^ k := weightedBinomialSum_eq k x

/-- Division form of `pow_mul_lowerBinomialSum_le`, valid for `x > 0`. -/
@[category API, AMS 05, group "parity_tail"]
theorem lowerBinomialSum_le_div
    {k K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKk : K ≤ k) :
    (lowerBinomialSum k K : ℝ) ≤ (1 + x) ^ k / x ^ K := by
  apply (le_div_iff₀ (pow_pos hx0 K)).2
  simpa [mul_comm] using
    pow_mul_lowerBinomialSum_le (k := k) (K := K) (x := x) hx0.le hx1 hKk

/-- The scalar inequality behind the explicit Hoeffding optimization:
`cosh (2t) ≤ exp ((2t)² / 2)` in exponential coordinates. -/
@[category API, AMS 26, group "parity_tail"]
theorem one_add_exp_neg_four_mul_le (t : ℝ) :
    1 + Real.exp (-4 * t) ≤ 2 * Real.exp (-2 * t + 2 * t ^ 2) := by
  have hcosh := Real.cosh_le_exp_half_sq (2 * t)
  have hmul :
      2 * Real.exp (-2 * t) * Real.cosh (2 * t) ≤
        2 * Real.exp (-2 * t) * Real.exp ((2 * t) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hcosh (by positivity)
  calc
    1 + Real.exp (-4 * t) = 2 * Real.exp (-2 * t) * Real.cosh (2 * t) := by
      rw [Real.cosh_eq]
      have hcancel : Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by
        rw [← Real.exp_add, show -2 * t + 2 * t = 0 by ring, Real.exp_zero]
      have hdouble :
          Real.exp (-2 * t) * Real.exp (-(2 * t)) = Real.exp (-4 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show 2 * Real.exp (-2 * t) *
            ((Real.exp (2 * t) + Real.exp (-(2 * t))) / 2) =
          Real.exp (-2 * t) * Real.exp (2 * t) +
            Real.exp (-2 * t) * Real.exp (-(2 * t)) by ring]
      rw [hcancel, hdouble]
    _ ≤ 2 * Real.exp (-2 * t) * Real.exp ((2 * t) ^ 2 / 2) := hmul
    _ = 2 * Real.exp (-2 * t + 2 * t ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Explicit lower binomial-tail estimate with Hoeffding exponent `2t²k`. -/
@[category API, AMS 05 60, group "parity_tail"]
theorem lowerBinomialSum_le_hoeffding
    {k K : ℕ} {t : ℝ} (ht : 0 ≤ t) (hcut : (K : ℝ) ≤ (1 / 2 - t) * k) :
    (lowerBinomialSum k K : ℝ) ≤ (2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k) := by
  have hKkreal : (K : ℝ) ≤ k := by
    calc
      (K : ℝ) ≤ (1 / 2 - t) * k := hcut
      _ ≤ k := by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
  have hKk : K ≤ k := by exact_mod_cast hKkreal
  set x : ℝ := Real.exp (-4 * t) with hx_def
  have hx0 : 0 < x := by rw [hx_def]; positivity
  have hx1 : x ≤ 1 := by
    rw [hx_def, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have htail : x ^ K * (lowerBinomialSum k K : ℝ) ≤ (1 + x) ^ k :=
    pow_mul_lowerBinomialSum_le hx0.le hx1 hKk
  set z : ℝ := -2 * t + 2 * t ^ 2 with hz_def
  have hbase : 1 + x ≤ 2 * Real.exp z := by
    rw [hx_def, hz_def]; exact one_add_exp_neg_four_mul_le t
  have hpow : (1 + x) ^ k ≤ (2 * Real.exp z) ^ k :=
    pow_le_pow_left₀ (by positivity) hbase k
  have hnonpos : -4 * t ≤ 0 := by nlinarith
  have hcutScaled : (-4 * t) * ((1 / 2 - t) * k) ≤ (-4 * t) * K :=
    mul_le_mul_of_nonpos_left hcut hnonpos
  have harg : (k : ℝ) * z ≤ -2 * t ^ 2 * k + (K : ℝ) * (-4 * t) := by
    rw [hz_def]; nlinarith
  have hexp :
      Real.exp ((k : ℝ) * z) ≤ Real.exp (-2 * t ^ 2 * k + (K : ℝ) * (-4 * t)) :=
    Real.exp_le_exp.mpr harg
  have htarget :
      (1 + x) ^ k ≤ ((2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k)) * x ^ K := by
    calc
      (1 + x) ^ k ≤ (2 * Real.exp z) ^ k := hpow
      _ = (2 : ℝ) ^ k * Real.exp ((k : ℝ) * z) := by
        rw [mul_pow, ← Real.exp_nat_mul]
      _ ≤ (2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k + (K : ℝ) * (-4 * t)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k)) * x ^ K := by
        rw [hx_def, ← Real.exp_nat_mul, Real.exp_add]
        ring
  have hfin :
      (lowerBinomialSum k K : ℝ) * x ^ K ≤
        ((2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k)) * x ^ K := by
    simpa [mul_comm] using htail.trans htarget
  exact le_of_mul_le_mul_right hfin (pow_pos hx0 K)

/-! ### Word weight and the exact binomial count -/

/-- The number of `1` entries of a length-`k` parity word. -/
@[category API, AMS 05, group "parity_tail"]
def wordWeight {k : ℕ} (v : Fin k → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i : Fin k => v i = 1).card

/-- **Exact word count.** Length-`k` parity words of weight `j` number
`choose k j`. -/
@[category API, AMS 05, group "parity_tail"]
theorem card_wordWeight_eq_choose (k j : ℕ) :
    (Finset.univ.filter fun v : Fin k → ZMod 2 => wordWeight v = j).card
      = k.choose j := by
  classical
  have hone : (1 : ZMod 2) ≠ 0 := by decide
  have hbit : ∀ x y : ZMod 2, (x = 1 ↔ y = 1) → x = y := by decide
  have hbij :
      (Finset.univ.filter fun v : Fin k → ZMod 2 => wordWeight v = j).card
        = (Finset.powersetCard j (Finset.univ : Finset (Fin k))).card := by
    apply Finset.card_bij (fun v _ => Finset.univ.filter fun i : Fin k => v i = 1)
    · intro v hv
      have hw : wordWeight v = j := (Finset.mem_filter.mp hv).2
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact hw
    · intro v _ w _ hvw
      funext i
      have hi := Finset.ext_iff.mp hvw i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hbit _ _ hi
    · intro s hs
      have hcard : s.card = j := (Finset.mem_powersetCard.mp hs).2
      have hfil :
          (Finset.univ.filter
            fun i : Fin k => (if i ∈ s then (1 : ZMod 2) else 0) = 1) = s := by
        ext i
        by_cases h : i ∈ s <;> simp [h]
      refine ⟨fun i => if i ∈ s then (1 : ZMod 2) else 0, ?_, hfil⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, wordWeight, hfil]
      exact hcard
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-! ### Transport to Collatz residues via the Terras–Everett bijection -/

/-- The number of odd steps among the first `k` Terras steps of a residue class
mod `2 ^ k`, read off its parity word. -/
@[category API, AMS 11 37, ref "Ter76", group "parity_tail"]
def oddCount (k : ℕ) (r : ZMod (2 ^ k)) : ℕ :=
  wordWeight (CC.parityVec k r)

/-- The odd-step count cannot exceed the length of the parity word. -/
@[category API, AMS 11 37, ref "Ter76", group "parity_tail"]
theorem oddCount_le_length (k : ℕ) (r : ZMod (2 ^ k)) : oddCount k r ≤ k := by
  classical
  show (Finset.univ.filter fun i : Fin k => CC.parityVec k r i = 1).card ≤ k
  calc
    (Finset.univ.filter fun i : Fin k => CC.parityVec k r i = 1).card
        ≤ (Finset.univ : Finset (Fin k)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = k := by simp

/-- **Exact binomial count.** The residues mod `2 ^ k` whose first `k` Terras
steps contain exactly `j` odd steps number exactly `choose k j`.

This is the precise sense in which the odd count is `Binomial (k, 1/2)` under
uniform residues: a counting identity across `CC.terras_bijection` [Ter76], with
no probabilistic hypothesis and no independence assumption. -/
@[category research solved, AMS 11 37 05, ref "Ter76", group "parity_tail"]
theorem card_residues_with_oddCount (k j : ℕ) :
    (Finset.univ.filter fun r : ZMod (2 ^ k) => oddCount k r = j).card
      = k.choose j := by
  classical
  have hcard :
      (Finset.univ.filter fun r : ZMod (2 ^ k) => oddCount k r = j).card =
      (Finset.univ.filter fun v : Fin k → ZMod 2 => wordWeight v = j).card := by
    apply Finset.card_bij (fun r _ => CC.parityVec k r)
    · intro r hr
      simpa [oddCount] using (Finset.mem_filter.mp hr).2
    · intro r _ s _ hrs
      exact (CC.terras_bijection k).1 hrs
    · intro v hv
      obtain ⟨r, hr⟩ := (CC.terras_bijection k).2 v
      refine ⟨r, ?_, hr⟩
      have hw : wordWeight v = j := (Finset.mem_filter.mp hv).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, oddCount, hr]
      exact hw
  rw [hcard, card_wordWeight_eq_choose]

/-- Exact count of residues whose first `k` Terras parity bits contain at most
`K` odd steps. -/
@[category API, AMS 11 37 05, ref "Ter76", group "parity_tail"]
theorem card_residues_with_oddCount_le (k K : ℕ) :
    (Finset.univ.filter fun r : ZMod (2 ^ k) => oddCount k r ≤ K).card
      = lowerBinomialSum k K := by
  classical
  set s : Finset (ZMod (2 ^ k)) :=
    Finset.univ.filter (fun r => oddCount k r ≤ K) with hs_def
  have hmap : ∀ r ∈ s, oddCount k r ∈ Finset.range (K + 1) := by
    intro r hr
    have hrK : oddCount k r ≤ K := by simpa [hs_def] using hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hrK)
  calc
    (Finset.univ.filter fun r : ZMod (2 ^ k) => oddCount k r ≤ K).card
        = s.card := by rw [hs_def]
    _ = ∑ j ∈ Finset.range (K + 1),
        (s.filter fun r : ZMod (2 ^ k) => oddCount k r = j).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ j ∈ Finset.range (K + 1), k.choose j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hfilter :
          (s.filter fun r : ZMod (2 ^ k) => oddCount k r = j) =
            Finset.univ.filter fun r : ZMod (2 ^ k) => oddCount k r = j := by
        ext r
        simp only [hs_def, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun hw => ⟨hw.le.trans hjK, hw⟩⟩
      rw [hfilter, card_residues_with_oddCount]
    _ = lowerBinomialSum k K := rfl

/-- Exact count of the symmetric upper tail: at least `k - K` odd steps. -/
@[category API, AMS 11 37 05, ref "Ter76", group "parity_tail"]
theorem card_residues_with_oddCount_ge_sub (k K : ℕ) (hKk : K ≤ k) :
    (Finset.univ.filter fun r : ZMod (2 ^ k) => k - K ≤ oddCount k r).card
      = lowerBinomialSum k K := by
  classical
  set s : Finset (ZMod (2 ^ k)) :=
    Finset.univ.filter (fun r => k - K ≤ oddCount k r) with hs_def
  have hmap : ∀ r ∈ s, k - oddCount k r ∈ Finset.range (K + 1) := by
    intro r hr
    have hge : k - K ≤ oddCount k r := by simpa [hs_def] using hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
  calc
    (Finset.univ.filter fun r : ZMod (2 ^ k) => k - K ≤ oddCount k r).card
        = s.card := by rw [hs_def]
    _ = ∑ j ∈ Finset.range (K + 1),
        (s.filter fun r : ZMod (2 ^ k) => k - oddCount k r = j).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ j ∈ Finset.range (K + 1), k.choose j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hjk : j ≤ k := hjK.trans hKk
      have hfilter :
          (s.filter fun r : ZMod (2 ^ k) => k - oddCount k r = j) =
            Finset.univ.filter fun r : ZMod (2 ^ k) => oddCount k r = k - j := by
        ext r
        have hodd : oddCount k r ≤ k := oddCount_le_length k r
        simp only [hs_def, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hge, hdefect⟩
          omega
        · intro hw
          exact ⟨by omega, by omega⟩
      rw [hfilter, card_residues_with_oddCount, Nat.choose_symm hjk]
    _ = lowerBinomialSum k K := rfl

/-! ### The transported tail bounds -/

/-- Explicit Hoeffding bound for the lower Terras parity tail. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "parity_tail"]
theorem card_residues_with_oddCount_le_hoeffding
    {k K : ℕ} {t : ℝ} (ht : 0 ≤ t) (hcut : (K : ℝ) ≤ (1 / 2 - t) * k) :
    ((Finset.univ.filter fun r : ZMod (2 ^ k) => oddCount k r ≤ K).card : ℝ)
      ≤ (2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k) := by
  rw [card_residues_with_oddCount_le]
  exact lowerBinomialSum_le_hoeffding ht hcut

/-- Normalized lower-tail proportion among all `2 ^ k` residues. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "parity_tail"]
theorem card_residues_with_oddCount_le_div_pow_le_exp
    {k K : ℕ} {t : ℝ} (ht : 0 ≤ t) (hcut : (K : ℝ) ≤ (1 / 2 - t) * k) :
    ((Finset.univ.filter fun r : ZMod (2 ^ k) => oddCount k r ≤ K).card : ℝ)
        / (2 : ℝ) ^ k ≤ Real.exp (-2 * t ^ 2 * k) := by
  apply (div_le_iff₀ (pow_pos (by norm_num) k)).2
  simpa [mul_comm] using card_residues_with_oddCount_le_hoeffding ht hcut

/-- Explicit Hoeffding bound for the symmetric upper Terras parity tail. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "parity_tail"]
theorem card_residues_with_oddCount_ge_sub_le_hoeffding
    {k K : ℕ} {t : ℝ} (ht : 0 ≤ t) (hcut : (K : ℝ) ≤ (1 / 2 - t) * k) :
    ((Finset.univ.filter fun r : ZMod (2 ^ k) => k - K ≤ oddCount k r).card : ℝ)
      ≤ (2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k) := by
  have hKkreal : (K : ℝ) ≤ k := by
    calc
      (K : ℝ) ≤ (1 / 2 - t) * k := hcut
      _ ≤ k := by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
  have hKk : K ≤ k := by exact_mod_cast hKkreal
  rw [card_residues_with_oddCount_ge_sub k K hKk]
  exact lowerBinomialSum_le_hoeffding ht hcut

/-- Normalized symmetric upper-tail proportion among all `2 ^ k` residues. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "parity_tail"]
theorem card_residues_with_oddCount_ge_sub_div_pow_le_exp
    {k K : ℕ} {t : ℝ} (ht : 0 ≤ t) (hcut : (K : ℝ) ≤ (1 / 2 - t) * k) :
    ((Finset.univ.filter fun r : ZMod (2 ^ k) => k - K ≤ oddCount k r).card : ℝ)
        / (2 : ℝ) ^ k ≤ Real.exp (-2 * t ^ 2 * k) := by
  apply (div_le_iff₀ (pow_pos (by norm_num) k)).2
  simpa [mul_comm] using card_residues_with_oddCount_ge_sub_le_hoeffding ht hcut

end ParityTail

end CC
