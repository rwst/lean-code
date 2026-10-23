/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.TwoLogCap
import BB13.LineTower
import BB13.TheoremsST

/-!
# Published rates cap the span of a line (item P4 of plan-beyond-BB13)

If `a < b` are exceptions on one line, the span `d = b − a` satisfies the tower arm
`2ᵈ|kₐ|2ᵃ ≤ 3ᵃ` (`BB13.tower_arms`). A lower bound `‖(3/2)ᵃ‖ ≥ cᵃ` turns it into
`d ≤ a·log₂(3/(4c))` (`BB13.rate_fibre_cap`). This file states that conversion for exceptions on
a line, with the rate as a hypothesis, and instantiates it at the two published rates:

* [Ben03, Prop. 2.2] and [Hab03, Thm. 2], independently: `‖(3/2)ᵏ‖ > 2^{−0.8k}` for `k ≥ 5`.
  We use it through the rational `0.574349 < 2^{−0.8}`, and get `213 d ≤ 82 a`, so
  `d < 0.385 a` (`span_lt_of_habsieger`; exact slope `log₂ 3 − 1.2 = 0.38496…`).
* [Zud07, Thm. 1]: `‖(3/2)ᵏ‖ > 0.5803ᵏ` for `k ≥ K`, `K` effective but not computed; this gives
  `35 d ≤ 13 a` (`span_cap_zudilin`; exact slope `0.37009…`).

So the strata of tall relation-towers (span `≥ γa`) are empty for `γ ≥ 0.385` once the rate of
[Ben03, Hab03] is granted, against the elementary ceiling `γ < log₂(3/2) = 0.58496`.

The residue scales along a line, `k_b = 3^{b−a} kₐ` (`BB13.sameTower_resid`), so the sign of `kₙ`
is constant on a line (`resid_pos_iff_of_sameTower`). Every Dickson failure `n ≥ 3` has
`kₙ = rₙ − 2ⁿ < 0` (`resid_neg_of_notDickson`), so the Waring count of Theorem C lives on the
negative lines; in the census only the line of `n = 1` is negative (`census_resid`).

No axiom: both rates enter as hypotheses.

## References

* [Ben03] M. A. Bennett, *Pillai's conjecture revisited*, J. Number Theory **98** (2003), Prop. 2.2.
* [Hab03] L. Habsieger, *Explicit lower bounds for ‖(3/2)ᵏ‖*, Acta Arith. **106** (2003), Thm. 2.
* [Zud07] W. Zudilin, J. Théor. Nombres Bordeaux **19** (2007), Thm. 1.
* `plans/plan-beyond-BB13.html`, §4.3, item P4.
-/

namespace BB13

/-- The linkage relation of two indices on one line. -/
theorem link_of_sameTower {a d : ℕ} (h : SameTower a (a + d)) :
    (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d) := by
  have := collinear_imp_link 3 2 a (a + d) (by norm_num) (by norm_num) (by omega)
    ((linePoint_eq_iff_collinear a (a + d)).mp h)
  simpa using this

/-- A rate `(P/Q)ᵃ ≤ ‖(3/2)ᵃ‖` in the integer form of `BB13.rate_fibre_cap`. -/
theorem rate_int_of_real {a P Q : ℕ} (hQ : 0 < Q)
    (hrate : ((P : ℝ) / Q) ^ a ≤ distToNearestInt (((3 : ℝ) / 2) ^ a)) :
    (2 * P) ^ a ≤ Q ^ a * (resid 3 2 a).natAbs := by
  have hd := distToNearestInt_eq_resid 3 2 a (by norm_num)
  push_cast at hd
  rw [hd, div_pow, div_le_div_iff₀ (by positivity) (by positivity)] at hrate
  have : (((2 * P) ^ a : ℕ) : ℝ) ≤ ((Q ^ a * (resid 3 2 a).natAbs : ℕ) : ℝ) := by
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs, mul_pow]
    linarith
  exact_mod_cast this

/-- **A rate caps the span of a line**: if `a < b` are on one line, `b` is an exception, and
`‖(3/2)ᵃ‖ ≥ (P/Q)ᵃ`, then `2^{b−a}(4P)ᵃ ≤ (3Q)ᵃ`, i.e. `b − a ≤ a·log₂(3Q/(4P))`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem span_cap_of_rate {a b P Q : ℕ} (hab : a < b) (hfb : IsFailure 3 2 (3 / 4) b)
    (hst : SameTower a b) (hQ : 0 < Q)
    (hrate : ((P : ℝ) / Q) ^ a ≤ distToNearestInt (((3 : ℝ) / 2) ^ a)) :
    2 ^ (b - a) * (4 * P) ^ a ≤ (3 * Q) ^ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab.le
  rw [show a + d - a = d by omega]
  exact rate_fibre_cap (rate_int_of_real hQ hrate)
    (tower_arms hfb (link_of_sameTower hst)).2

/-- **The span under the rate of [Ben03, Hab03]**: `‖(3/2)ᵃ‖ ≥ 0.574349ᵃ` (implied by
`‖(3/2)ᵃ‖ > 2^{−0.8a}`, `a ≥ 5`) gives `213 (b − a) ≤ 82 a`. Certificate:
`750000²¹³ ≤ 2⁸²·574349²¹³`. -/
@[category research solved, AMS 11, ref "Bug12" "Hab03" "Ben03", group "bugeaud_10_13"]
theorem span_cap_habsieger {a b : ℕ} (hab : a < b) (hfb : IsFailure 3 2 (3 / 4) b)
    (hst : SameTower a b)
    (hrate : ((574349 : ℕ) / (1000000 : ℕ) : ℝ) ^ a ≤ distToNearestInt (((3 : ℝ) / 2) ^ a)) :
    213 * (b - a) ≤ 82 * a := by
  have h := span_cap_of_rate hab hfb hst (by norm_num) hrate
  have h2 : 2 ^ (b - a) * (4 * 574349) ^ a ≤ (4 * 750000) ^ a := by
    calc 2 ^ (b - a) * (4 * 574349 : ℕ) ^ a ≤ (3 * 1000000) ^ a := h
      _ = (4 * 750000) ^ a := by norm_num
  exact exponent_transfer (by norm_num)
    (by norm_num : (750000 : ℕ) ^ 213 ≤ 2 ^ 82 * 574349 ^ 213)
    (cancel_pow_factor (by norm_num) h2)

/-- **Under the rate of [Ben03, Hab03] the span is below `0.385 a`**, so the stratum of spans
`≥ γa` is empty for every `γ ≥ 0.385`. -/
@[category research solved, AMS 11, ref "Bug12" "Hab03" "Ben03", group "bugeaud_10_13"]
theorem span_lt_of_habsieger {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hfb : IsFailure 3 2 (3 / 4) b) (hst : SameTower a b)
    (hrate : ((574349 : ℕ) / (1000000 : ℕ) : ℝ) ^ a ≤ distToNearestInt (((3 : ℝ) / 2) ^ a)) :
    ((b - a : ℕ) : ℝ) < 0.385 * a := by
  have h := span_cap_habsieger hab hfb hst hrate
  have h' : (213 : ℝ) * ((b - a : ℕ) : ℝ) ≤ 82 * a := by exact_mod_cast h
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  linarith

/-- **The span under the rate of [Zud07]**: `‖(3/2)ᵃ‖ ≥ 0.5803ᵃ` gives `35 (b − a) ≤ 13 a`. -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem span_cap_zudilin {a b : ℕ} (hab : a < b) (hfb : IsFailure 3 2 (3 / 4) b)
    (hst : SameTower a b)
    (hrate : ((5803 : ℕ) / (10000 : ℕ) : ℝ) ^ a ≤ distToNearestInt (((3 : ℝ) / 2) ^ a)) :
    35 * (b - a) ≤ 13 * a := by
  have h := span_cap_of_rate hab hfb hst (by norm_num) hrate
  have h2 : 2 ^ (b - a) * (4 * 5803) ^ a ≤ (4 * 7500) ^ a := by
    calc 2 ^ (b - a) * (4 * 5803 : ℕ) ^ a ≤ (3 * 10000) ^ a := h
      _ = (4 * 7500) ^ a := by norm_num
  exact exponent_transfer (by norm_num)
    (by norm_num : (7500 : ℕ) ^ 35 ≤ 2 ^ 13 * 5803 ^ 35)
    (cancel_pow_factor (by norm_num) h2)

/-- **The sign of the residue is a line invariant**: `k_b = 3^{b−a} kₐ` on a line. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem resid_pos_iff_of_sameTower {a b : ℕ} (hab : a ≤ b) (h : SameTower a b) :
    0 < resid 3 2 b ↔ 0 < resid 3 2 a := by
  rw [sameTower_resid hab h]
  exact ⟨fun h' ↦ pos_of_mul_pos_right h' (by positivity), fun h' ↦ by positivity⟩

/-- **Dickson failures have negative residue**: for `n ≥ 3`, `¬(Dₙ)` forces `mₙ = qₙ + 1` and
`kₙ = rₙ − 2ⁿ < 0`. As in `BB13.isFailure_of_notDickson`, `2ⁿ − rₙ ≤ qₙ`; with
`2·3ⁿ ≤ 4ⁿ` this gives `2ⁿ ≤ 2rₙ`, the rounding bit of `BB13.mNat_eq_quot_add`. -/
@[category research solved, AMS 11, ref "Bug12" "Dic36", group "bugeaud_10_13"]
theorem resid_neg_of_notDickson {n : ℕ} (hn : 3 ≤ n) (hnd : ¬ DicksonCond n) :
    resid 3 2 n < 0 := by
  have hdiv := Nat.div_add_mod (3 ^ n) (2 ^ n)
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hrlt : 3 ^ n % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  simp only [DicksonCond, waringQuot] at hnd
  have hne : 3 ^ n % 2 ^ n + 3 ^ n / 2 ^ n + 1 ≠ 2 ^ n := by
    intro heq
    have hfac : (2 ^ n - 1) * (3 ^ n / 2 ^ n + 1) = 3 ^ n := by
      zify [hone] at heq hdiv ⊢
      linear_combination hdiv - heq
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (Dvd.intro _ hfac)
    have := three_pow_mod_eight k
    have h8 : 8 ∣ 2 ^ n := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact Nat.pow_dvd_pow 2 hn
    omega
  have hq : 2 ^ n - 3 ^ n % 2 ^ n ≤ 3 ^ n / 2 ^ n := by omega
  have h4 : 2 * 3 ^ n ≤ 2 ^ n * 2 ^ n := by
    have := two_mul_three_pow_le_four_pow hn
    rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow] at this
    exact_mod_cast this
  have hbit : 2 ^ n ≤ 2 * (3 ^ n % 2 ^ n) := by
    have h1 : (2 ^ n - 3 ^ n % 2 ^ n) * 2 ^ n ≤ 3 ^ n := by
      calc (2 ^ n - 3 ^ n % 2 ^ n) * 2 ^ n ≤ 3 ^ n / 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ hq
        _ ≤ 3 ^ n := Nat.div_mul_le_self _ _
    have h2 : 2 * (2 ^ n - 3 ^ n % 2 ^ n) * 2 ^ n ≤ 2 ^ n * 2 ^ n := by
      calc 2 * (2 ^ n - 3 ^ n % 2 ^ n) * 2 ^ n = 2 * ((2 ^ n - 3 ^ n % 2 ^ n) * 2 ^ n) := by ring
        _ ≤ 2 * 3 ^ n := Nat.mul_le_mul_left _ h1
        _ ≤ 2 ^ n * 2 ^ n := h4
    have := Nat.le_of_mul_le_mul_right h2 (by positivity)
    omega
  rw [resid, Mnum_eq_mNat, mNat_eq_quot_add, ite_eq_left hbit]
  push_cast
  have hdivZ : ((2 ^ n * (3 ^ n / 2 ^ n) + 3 ^ n % 2 ^ n : ℕ) : ℤ) = ((3 ^ n : ℕ) : ℤ) := by
    rw [hdiv]
  have hrltZ : ((3 ^ n % 2 ^ n : ℕ) : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast hrlt
  push_cast at hdivZ hrltZ
  nlinarith

/-- **The census signs**: `k₁ = −1`, `k₂ = 1`, `k₃ = 3`, `k₄ = 1`, `k₇ = 11`. Only the line of
`n = 1` is negative. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem census_resid : resid 3 2 1 = -1 ∧ resid 3 2 2 = 1 ∧ resid 3 2 3 = 3 ∧
    resid 3 2 4 = 1 ∧ resid 3 2 7 = 11 := by
  simp only [resid, Mnum_eq_mNat, mNat]
  norm_num

end BB13
