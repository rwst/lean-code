/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.StewartDigits
import TH.DigitBlocks.GapPrinciples
import TH.DigitBlocks.Defs
import Mathlib.Data.Nat.Log

/-!
# Theorem B1: the binary digit changes of `3^m` grow

Milestone **M-3 = Theorem B1** of the digit-block plan ([A4+] §3.1), the
digit-*change* strengthening of Stewart's digit-*sum* theorem
(`TH/StewartDigits.lean`, rung M3½).  The number of binary digit changes
(`transitionCount`, `TH/DigitBlocks/Defs.lean`) of `3^m` obeys the same
effective lower bound as its digit sum:

  `∃ C > 0, ∀ m ≥ 2 :   log m / (log log m + C) − 1  ≤  transitionCount (3^m)`

(`transitionCount_three_pow_lower`), and in particular
`transitionCount (3^m) → ∞` (`transitionCount_three_pow_tendsto_atTop`): no power
of `3` eventually has a bounded number of maximal binary blocks.  This is the
`3^m` instance of **Bugeaud–Kaneko [BK17] Rem. 4.4** (block count `≫ log m/log
log m`, the `S`-unit `S = {3}`), whose qualitative precursor is
**Blecksmith–Filaseta–Nicol [BFN93]** (block count `→ ∞`); it is genuinely
stronger than Stewart's theorem, whose `k` guaranteed ones could all sit in a
single run.

## Proof

The engine is the same window pigeonhole as `StewartDigits`, run against a
*second* gap principle.  Each depth window `[M − θ^{j+1}, M − θ^j)`
(`M := ⌊log₂ 3^m⌋`) is shown **non-constant**:

* it is not all-zeros — Stewart's `window_hit` (contradicting the zero-run
  `gap_bound`, or oddness at bit `0`);
* it is not all-ones — `window_clear` (contradicting the all-ones
  `gap_bound_ones` of `TH/DigitBlocks/GapPrinciples.lean`).

A window holding both a set bit and a clear bit contains an adjacent
digit-change (`exists_transition`, a discrete intermediate-value step).  The `k`
disjoint windows then inject into the transition set
(`log_le_transitionCount`), and `windowCount_lower_bound` (the shared endgame,
also `GapPrinciples`) converts `⌊log_θ M⌋ ≤ transitionCount` into the headline
bound with the *same* constant `C` as Stewart's theorem.

Axiom footprint: std3 + `BakerWustholz.linearForms_logs` ([BW93]) — the
combinatorial pigeonhole is axiom-free; the only cited input is the same
Baker–Wüstholz bound behind both gap principles.

## Contents

* `transitionCount_three_pow_lower` — **Theorem B1**: the effective digit-change
  lower bound.
* `transitionCount_three_pow_tendsto_atTop` — corollary: `transitionCount (3^m)
  → ∞`.

## References

* [Ste80] Stewart, *On the representation of an integer in two different bases*,
  J. reine angew. Math. **319** (1980).  (The digit-sum template.)
* [BK17] Bugeaud, Kaneko, *On the digital representation of smooth numbers*,
  arXiv:1704.00432 (2017).  (Rem. 4.4: the `≫ log m/log log m` block count of
  `3^m` — the effective form of B1.)
* [BFN93] Blecksmith, Filaseta, Nicol, *A result on the digits of `aⁿ`*, Acta
  Arith. **64** (1993).  (Qualitative precursor: block count `→ ∞`.)
* [BW93] Baker, Wüstholz, *Logarithmic forms and group varieties*, J. reine
  angew. Math. **442** (1993).  (Via `CITED/BakerWustholz.lean`.)
* [A4+] `plan-A4+.html` (this repository, 2026-07): §2 (the engine), §3.1 (B1),
  §5.2 (this file).
-/

namespace TH

/-! ## Non-constant windows contain a digit change -/

/-- Discrete intermediate value: if a Boolean sequence differs at `a < b` then
some adjacent pair in `[a, b)` differs. -/
private theorem exists_transition (f : ℕ → Bool) {a b : ℕ} (hab : a < b)
    (hne : f a ≠ f b) : ∃ i, a ≤ i ∧ i < b ∧ f i ≠ f (i + 1) := by
  by_contra hc
  push Not at hc
  have key : ∀ k, a + k ≤ b → f a = f (a + k) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have h1 : f a = f (a + k) := ih (by omega)
      have h2 : f (a + k) = f (a + k + 1) := hc (a + k) (by omega) (by omega)
      rw [h1, h2]; congr 1
  have hbeq : f a = f b := by
    have hk := key (b - a) (by omega)
    rwa [Nat.add_sub_cancel' hab.le] at hk
  exact hne hbeq

/-- No depth window `[M − θ^{j+1}, M − θ^j)` of `3^m` is all ones, once `θ`
exceeds the gap-principle threshold (the all-ones companion of
`TH.window_hit`): the window contains a clear bit.  Via `gap_bound_ones`, which
needs no oddness input, so — unlike `window_hit` — there is no `x = 0` edge
case. -/
private theorem window_clear {m θ : ℕ} (hm : 1 ≤ m) (hθ2 : 2 ≤ θ)
    (hθbig : 2 * (BakerWustholz.C 3 1 * Real.log 3 * max (Real.log ((2 * m : ℕ) : ℝ)) 1)
      < (θ : ℝ) * Real.log 2)
    {j : ℕ} (hj : θ ^ (j + 1) ≤ Nat.log 2 (3 ^ m)) :
    ∃ i, Nat.log 2 (3 ^ m) - θ ^ (j + 1) ≤ i ∧ i < Nat.log 2 (3 ^ m) - θ ^ j
      ∧ (3 ^ m).testBit i = false := by
  set M : ℕ := Nat.log 2 (3 ^ m) with hMdef
  have hpowlt : θ ^ j < θ ^ (j + 1) := by
    have h1 : θ ^ (j + 1) = θ ^ j * θ := pow_succ θ j
    have h2 : 1 ≤ θ ^ j := Nat.one_le_pow _ _ (by omega)
    nlinarith
  by_contra hc
  push Not at hc
  simp only [Bool.not_eq_false] at hc
  have hxy : M - θ ^ (j + 1) < M - θ ^ j := by omega
  have hgb := gap_bound_ones hm hxy (Nat.sub_le _ _) hc
  rw [← hMdef] at hgb
  have hjM : θ ^ j ≤ M := by omega
  have hXcast : ((M : ℝ) - ((M - θ ^ (j + 1) : ℕ) : ℝ)) = ((θ : ℕ) : ℝ) ^ (j + 1) := by
    rw [Nat.cast_sub hj]; push_cast; ring
  have hYcast : ((M : ℝ) + 1 - ((M - θ ^ j : ℕ) : ℝ)) = ((θ : ℕ) : ℝ) ^ j + 1 := by
    rw [Nat.cast_sub hjM]; push_cast; ring
  rw [hXcast, hYcast] at hgb
  have hθj1 : (1 : ℝ) ≤ ((θ : ℕ) : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ θ))
  have hCnn : (0 : ℝ) ≤ BakerWustholz.C 3 1 * Real.log 3
      * max (Real.log ((2 * m : ℕ) : ℝ)) 1 :=
    mul_nonneg (mul_nonneg (C_one_nonneg 3) log_three_pos'.le)
      (le_trans zero_le_one (le_max_right _ _))
  have hkey : ((θ : ℕ) : ℝ) * Real.log 2 * ((θ : ℕ) : ℝ) ^ j
      ≤ (2 * (BakerWustholz.C 3 1 * Real.log 3 * max (Real.log ((2 * m : ℕ) : ℝ)) 1))
        * ((θ : ℕ) : ℝ) ^ j := by
    have hlhs : ((θ : ℕ) : ℝ) * Real.log 2 * ((θ : ℕ) : ℝ) ^ j
        = ((θ : ℕ) : ℝ) ^ (j + 1) * Real.log 2 := by ring
    rw [hlhs]; nlinarith [hgb, hθj1, hCnn]
  have hθpos : (0 : ℝ) < ((θ : ℕ) : ℝ) ^ j := by positivity
  have hfin := le_of_mul_le_mul_right hkey hθpos
  linarith

/-- Every depth window `[M − θ^{j+1}, M − θ^j)` of `3^m` (above the threshold)
is non-constant: it contains a digit change.  Combines `TH.window_hit` (a set
bit) with `window_clear` (a clear bit) through `exists_transition`. -/
private theorem window_has_transition {m θ : ℕ} (hm : 1 ≤ m) (hθ2 : 2 ≤ θ)
    (hθbig : 2 * (BakerWustholz.C 3 1 * Real.log 3 * max (Real.log ((2 * m : ℕ) : ℝ)) 1)
      < (θ : ℝ) * Real.log 2)
    {j : ℕ} (hj : θ ^ (j + 1) ≤ Nat.log 2 (3 ^ m)) :
    ∃ i, Nat.log 2 (3 ^ m) - θ ^ (j + 1) ≤ i ∧ i < Nat.log 2 (3 ^ m) - θ ^ j
      ∧ (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + 1) := by
  obtain ⟨a, ha1, ha2, ha3⟩ := window_hit hm hθ2 hθbig hj
  obtain ⟨c, hc1, hc2, hc3⟩ := window_clear hm hθ2 hθbig hj
  have hac : a ≠ c := by intro h; rw [h, hc3] at ha3; exact absurd ha3 (by decide)
  have hfne : (3 ^ m).testBit a ≠ (3 ^ m).testBit c := by rw [ha3, hc3]; decide
  rcases lt_or_gt_of_ne hac with hlt | hgt
  · obtain ⟨i, hi1, hi2, hi3⟩ := exists_transition (fun i => (3 ^ m).testBit i) hlt hfne
    exact ⟨i, by omega, by omega, hi3⟩
  · obtain ⟨i, hi1, hi2, hi3⟩ :=
      exists_transition (fun i => (3 ^ m).testBit i) hgt hfne.symm
    exact ⟨i, by omega, by omega, hi3⟩

/-! ## The pigeonhole -/

/-- The interval pigeonhole for digit changes (the `log_le_sum_digits` analogue):
with `θ` above the gap-principle threshold, the `k = ⌊log_θ M⌋` windows are
disjoint and each contains a digit change, so `⌊log_θ ⌊log₂ 3^m⌋⌋ ≤
transitionCount (3^m)`. -/
private theorem log_le_transitionCount {m θ : ℕ} (hm : 1 ≤ m) (hθ2 : 2 ≤ θ)
    (hθbig : 2 * (BakerWustholz.C 3 1 * Real.log 3 * max (Real.log ((2 * m : ℕ) : ℝ)) 1)
      < (θ : ℝ) * Real.log 2) :
    Nat.log θ (Nat.log 2 (3 ^ m)) ≤ transitionCount (3 ^ m) := by
  set M : ℕ := Nat.log 2 (3 ^ m) with hMdef
  set k : ℕ := Nat.log θ M with hkdef
  have hMpos : 1 ≤ M := by
    rw [hMdef]
    have h2 : (2 : ℕ) ^ 1 ≤ 3 ^ m := by
      calc (2 : ℕ) ^ 1 ≤ 3 ^ 1 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    calc 1 = Nat.log 2 (2 ^ 1) := (Nat.log_pow (by norm_num) 1).symm
      _ ≤ Nat.log 2 (3 ^ m) := Nat.log_mono_right h2
  have hwin : ∀ j : ℕ, ∃ i : ℕ, j < k →
      (M - θ ^ (j + 1) ≤ i ∧ i < M - θ ^ j
        ∧ (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + 1)) := by
    intro j
    by_cases hj : j < k
    · have hpow : θ ^ (j + 1) ≤ M := by
        calc θ ^ (j + 1) ≤ θ ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ M := by rw [hkdef]; exact Nat.pow_log_le_self θ (by omega)
      obtain ⟨i, h1, h2, h3⟩ := window_has_transition hm hθ2 hθbig (by rw [← hMdef]; exact hpow)
      rw [← hMdef] at h1 h2
      exact ⟨i, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose f hf using hwin
  have hfmem : ∀ j ∈ Finset.range k, f j ∈ (Finset.range M).filter
      (fun i => (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + 1)) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hf j (Finset.mem_range.mp hj)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h3⟩
  have hmono : ∀ a b : ℕ, a < b → b < k → f b < f a := by
    intro a b hab hbk
    obtain ⟨ha1, _, _⟩ := hf a (by omega)
    obtain ⟨_, hb2, _⟩ := hf b hbk
    have hpow : θ ^ (a + 1) ≤ θ ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hinj : Set.InjOn f (Finset.range k) := by
    intro a ha b hb heq
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · have := hmono a b h hb; omega
    · exact h
    · have := hmono b a h ha; omega
  have hcard : k ≤ ((Finset.range M).filter
      (fun i => (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + 1))).card := by
    calc k = (Finset.range k).card := (Finset.card_range k).symm
      _ ≤ _ := Finset.card_le_card_of_injOn f hfmem hinj
  have hTC : transitionCount (3 ^ m) = ((Finset.range M).filter
      (fun i => (3 ^ m).testBit i ≠ (3 ^ m).testBit (i + 1))).card := rfl
  rw [hTC]; exact hcard

/-! ## Theorem B1 -/

/-- **Theorem B1** ([A4+] §3.1; [BK17] Rem. 4.4 for the integer `3^m`): the
number of binary digit changes of `3^m` obeys the same effective lower bound as
its digit sum,

  `log m / (log log m + C) − 1 ≤ transitionCount (3^m)`   for every `m ≥ 2`,

with `C > 0` the *same* constant as `stewart_digitSum_three_pow` (both come from
`windowCount_lower_bound`).  Strictly stronger than the digit-sum theorem: the
guaranteed ones are now spread over `≫ log m/log log m` separated blocks.
Footprint std3 + [BW93]. -/
@[category research solved, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
theorem transitionCount_three_pow_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      Real.log m / (Real.log (Real.log m) + C) - 1 ≤ (transitionCount (3 ^ m) : ℝ) :=
  windowCount_lower_bound (fun m => transitionCount (3 ^ m))
    (fun _ _ hm hθ2 hθbig => log_le_transitionCount (by omega) hθ2 hθbig)

/-- **Corollary**: the number of binary digit changes (equivalently, of maximal
equal-digit blocks) of `3^m` tends to infinity — no power of `3` eventually has
a bounded number of binary blocks ([BFN93] qualitatively, [BK17] with rate).
Footprint std3 + [BW93]. -/
@[category research solved, AMS 11, ref "BK17", group "three_pow_digit_blocks"]
theorem transitionCount_three_pow_tendsto_atTop :
    Filter.Tendsto (fun m : ℕ => transitionCount (3 ^ m)) Filter.atTop Filter.atTop :=
  tendsto_atTop_of_lower_bound (fun m => transitionCount (3 ^ m))
    transitionCount_three_pow_lower

end TH
