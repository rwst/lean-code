/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Tactic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud, Chapter 3, §3.9 — Exercise 3.1 (Mahler's parity identity)

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), **Exercise 3.1** (cf. Mahler [Mah68]):

> Establish that, for any non-negative integer `m`, the real interval `(m, m+1)` contains at most
> one **Z-number**.  [Hint. Assume that `ξ` is a Z-number. For an integer `n ≥ 0`, write
> `xₙ = ⌊ξ (3/2)ⁿ⌋` and put `εₙ = 0` if `xₙ` is even and `εₙ = 1` otherwise. Prove that
> `3{ξ} = ε₀ + (2/3) ε₁ + (2/3)² ε₂ + ⋯`. Conclude.]

Here a **Z-number** (Definition 3.2, Mahler 1968) is a positive real `ξ` with
`{ξ (3/2)ⁿ} ∈ [0, 1/2)` for every `n ≥ 0`.

## What is formalised

* `Bugeaud.parity_identity` — **the parity identity itself**:
  `3 {ξ} = ∑' n, (2/3)ⁿ · εₙ`, where `εₙ = ⌊ξ (3/2)ⁿ⌋ mod 2` (`Bugeaud.zParity`).  This is the
  hint's series, and it is the headline deliverable: the fractional part of a Z-number is an
  explicit convergent series in the *parity word* of its `(3/2)`-orbit.  (`Bugeaud.parity_hasSum`
  is the same statement as a `HasSum`.)

* `Bugeaud.zNumber_subsingleton_Ioo` — **the exercise's conclusion**: for every integer `m` the
  set of Z-numbers in the open interval `(m, m+1)` is a subsingleton.  Consequently there are at
  most countably many Z-numbers.  The engine is `Bugeaud.eq_of_floor_eq`: two Z-numbers with the
  same integer part are equal.

## Proof

The whole argument rests on one deterministic step (`Bugeaud.floor_step`): for a Z-number `ξ`,

  `2 ⌊ξ (3/2)ⁿ⁺¹⌋ = 3 ⌊ξ (3/2)ⁿ⌋ + (⌊ξ (3/2)ⁿ⌋ mod 2)`.

Writing `xₙ = ⌊ξ (3/2)ⁿ⌋`, `yₙ = {ξ (3/2)ⁿ}`, this says `xₙ₊₁ = ⌊3 xₙ / 2⌋ + (xₙ mod 2)`: the next
integer part is a function of the current one *because* `ξ` is a Z-number.  The proof is a bounded
integer squeeze — `2 xₙ₊₁ - 3 xₙ = 3 yₙ - 2 yₙ₊₁` is a real number in `(-1, 3/2)`, hence the
integer `0` or `1`, and its parity is that of `xₙ` — so `omega` finishes.

From `floor_step` two things follow:

* **The identity.**  `floor_step` gives the one-step recursion `3 yₙ = εₙ + 2 yₙ₊₁`
  (`Bugeaud.three_zFrac`).  Setting `Rₙ = (2/3)ⁿ · 3 yₙ`, this telescopes to
  `Rₙ - Rₙ₊₁ = (2/3)ⁿ εₙ` (`Bugeaud.rem_sub_succ`), so the partial sums are `3 y₀ - Rₙ`
  (`Bugeaud.sum_range_eq`).  Since `0 ≤ yₙ < 1/2`, `Rₙ → 0` (a squeeze against `(2/3)ⁿ · 3/2`),
  and the series — dominated by the geometric `∑ (2/3)ⁿ` — sums to `3 y₀ = 3 {ξ}`.

* **The conclusion.**  Two Z-numbers with `⌊ξ⌋ = ⌊ξ'⌋` have equal integer parts along the whole
  orbit (`Bugeaud.floor_eq`, an induction on `floor_step`), hence equal parity words, hence the
  same series, hence `{ξ} = {ξ'}` by the identity, hence `ξ = ξ'`.

## Remarks

* The identity needs only the fractional-part bound, not positivity of `ξ`; `0 < ξ` (part of
  Definition 3.2) is carried for faithfulness but never used, and `εₙ ∈ {0, 1}` holds
  unconditionally because integer `emod 2` is `0` or `1`.
* This is the same `ℚ₂`-flavoured functional identity as the local plan-B1E2 program
  (`∑ wⱼ (2/3)ʲ = -3 x₀`) and as report-bbook3's target **T15** (Mahler's parity identity as a
  `2`-adic functional equation); the intended reuse is that structured parity words `(εₙ)`
  (automatic/morphic) make `3{ξ}` a Mahler-type value, excluding classes of `ξ` from being
  Z-numbers.
* The Z-number predicate is also defined, independently, in the Antihydra/SRS program as
  `StringRewriting.AntihydraSRS.IsZNumber`; the two live in different corpus roots and are kept
  separate (importing the SRS rewriting machinery into a Bugeaud chapter would be inappropriate).
-/

open Filter Topology

namespace Bugeaud

variable {ξ ξ' : ℝ}

/-- A **Z-number** (Mahler 1968; Bugeaud, Definition 3.2): a positive real `ξ` all of whose
`(3/2)`-power multiples have fractional part below `1/2`, i.e. `{ξ (3/2)ⁿ} ∈ [0, 1/2)` for every
`n : ℕ`. -/
def IsZNumber (ξ : ℝ) : Prop :=
  0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * (3 / 2) ^ n) < 1 / 2

/-- The parity `εₙ = ⌊ξ (3/2)ⁿ⌋ mod 2 ∈ {0, 1}` of the `n`-th integer part of the orbit. -/
noncomputable def zParity (ξ : ℝ) (n : ℕ) : ℤ := ⌊ξ * (3 / 2) ^ n⌋ % 2

/-- The remainder `Rₙ = (2/3)ⁿ · 3 {ξ (3/2)ⁿ}` after `n` terms of the parity series. -/
noncomputable def zRem (ξ : ℝ) (n : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ n * (3 * Int.fract (ξ * (3 / 2) ^ n))

/-- The parity `εₙ` is `0` or `1`. -/
@[category API, AMS 11, ref "Bug12", group "bug_ex_3_1"]
theorem zParity_eq_zero_or_one (ξ : ℝ) (n : ℕ) : zParity ξ n = 0 ∨ zParity ξ n = 1 :=
  Int.emod_two_eq _

/-- **The deterministic floor step.**  For a Z-number `ξ`, the next integer part
`⌊ξ (3/2)ⁿ⁺¹⌋` is fixed by the current one: `2 ⌊ξ (3/2)ⁿ⁺¹⌋ = 3 ⌊ξ (3/2)ⁿ⌋ + ⌊ξ (3/2)ⁿ⌋ mod 2`,
equivalently `xₙ₊₁ = ⌊3 xₙ / 2⌋ + (xₙ mod 2)`.  This is the whole content of Exercise 3.1; the
proof is a bounded integer squeeze on `2 xₙ₊₁ - 3 xₙ = 3 yₙ - 2 yₙ₊₁ ∈ (-1, 3/2)`. -/
@[category API, AMS 11, ref "Bug12", group "bug_ex_3_1"]
theorem floor_step (hξ : IsZNumber ξ) (n : ℕ) :
    2 * ⌊ξ * (3 / 2) ^ (n + 1)⌋ = 3 * ⌊ξ * (3 / 2) ^ n⌋ + ⌊ξ * (3 / 2) ^ n⌋ % 2 := by
  obtain ⟨_, hz⟩ := hξ
  set u := ξ * (3 / 2) ^ n with hu
  set x := ⌊u⌋ with hx
  have huc : ξ * (3 / 2) ^ (n + 1) = (3 / 2) * u := by rw [hu, pow_succ]; ring
  rw [huc]
  set x' := ⌊(3 / 2) * u⌋ with hx'
  have e1 : Int.fract u = u - (x : ℝ) := rfl
  have e2 : Int.fract ((3 / 2) * u) = (3 / 2) * u - (x' : ℝ) := rfl
  have hy0 : (0 : ℝ) ≤ u - (x : ℝ) := by rw [← e1]; exact Int.fract_nonneg u
  have hy1 : u - (x : ℝ) < 1 / 2 := by rw [← e1]; exact hz n
  have hy0' : (0 : ℝ) ≤ (3 / 2) * u - (x' : ℝ) := by rw [← e2]; exact Int.fract_nonneg _
  have hy1' : (3 / 2) * u - (x' : ℝ) < 1 / 2 := by rw [← e2, ← huc]; exact hz (n + 1)
  have hR : (2 * (x' : ℝ) - 3 * (x : ℝ)) = 3 * (u - (x : ℝ)) - 2 * ((3 / 2) * u - (x' : ℝ)) := by
    ring
  have hlow : (-1 : ℝ) < 2 * (x' : ℝ) - 3 * (x : ℝ) := by rw [hR]; linarith
  have hupp : 2 * (x' : ℝ) - 3 * (x : ℝ) < 3 / 2 := by rw [hR]; linarith
  have h1 : (-1 : ℤ) < 2 * x' - 3 * x := by
    have : (-1 : ℝ) < ((2 * x' - 3 * x : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h2 : 2 * x' - 3 * x < 2 := by
    have : ((2 * x' - 3 * x : ℤ) : ℝ) < 2 := by push_cast; linarith
    exact_mod_cast this
  omega

/-- **The one-step recursion for the fractional parts**: `3 yₙ = εₙ + 2 yₙ₊₁`, the analytic form
of `floor_step`. -/
@[category API, AMS 11, ref "Bug12", group "bug_ex_3_1", formal_uses floor_step]
theorem three_zFrac (hξ : IsZNumber ξ) (n : ℕ) :
    3 * Int.fract (ξ * (3 / 2) ^ n)
      = ((⌊ξ * (3 / 2) ^ n⌋ % 2 : ℤ) : ℝ) + 2 * Int.fract (ξ * (3 / 2) ^ (n + 1)) := by
  have hstep := floor_step hξ n
  have e1 : Int.fract (ξ * (3 / 2) ^ n) = ξ * (3 / 2) ^ n - (⌊ξ * (3 / 2) ^ n⌋ : ℝ) := rfl
  have e2 : Int.fract (ξ * (3 / 2) ^ (n + 1))
      = ξ * (3 / 2) ^ (n + 1) - (⌊ξ * (3 / 2) ^ (n + 1)⌋ : ℝ) := rfl
  have hstepR : (2 * (⌊ξ * (3 / 2) ^ (n + 1)⌋ : ℝ))
      = 3 * (⌊ξ * (3 / 2) ^ n⌋ : ℝ) + ((⌊ξ * (3 / 2) ^ n⌋ % 2 : ℤ) : ℝ) := by exact_mod_cast hstep
  have hBR : ξ * (3 / 2) ^ (n + 1) = (3 / 2) * (ξ * (3 / 2) ^ n) := by rw [pow_succ]; ring
  rw [e1, e2]
  linarith [hstepR, hBR]

/-- Telescoping identity for the remainder: `Rₙ - Rₙ₊₁ = (2/3)ⁿ εₙ`. -/
@[category API, AMS 11, ref "Bug12", group "bug_ex_3_1", formal_uses three_zFrac]
theorem zRem_sub_succ (hξ : IsZNumber ξ) (n : ℕ) :
    zRem ξ n - zRem ξ (n + 1) = (2 / 3 : ℝ) ^ n * (zParity ξ n : ℝ) := by
  have h : 3 * Int.fract (ξ * (3 / 2) ^ n) - 2 * Int.fract (ξ * (3 / 2) ^ (n + 1))
      = (zParity ξ n : ℝ) := by
    have := three_zFrac hξ n; simp only [zParity]; linarith
  simp only [zRem]
  linear_combination ((2 / 3 : ℝ) ^ n) * h

/-- The `N`-th partial sum of the parity series equals `3 {ξ} - R_N`. -/
@[category API, AMS 11, ref "Bug12", group "bug_ex_3_1", formal_uses zRem_sub_succ]
theorem sum_range_eq (hξ : IsZNumber ξ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (2 / 3 : ℝ) ^ k * (zParity ξ k : ℝ) = 3 * Int.fract ξ - zRem ξ N := by
  induction N with
  | zero => simp [zRem]
  | succ N ih => rw [Finset.sum_range_succ, ih, ← zRem_sub_succ hξ N]; ring

/-- **Mahler's parity identity, `HasSum` form**: the parity series `∑ (2/3)ⁿ εₙ` sums to `3 {ξ}`. -/
@[category API, AMS 11, ref "Bug12", group "bug_ex_3_1", formal_uses sum_range_eq]
theorem parity_hasSum (hξ : IsZNumber ξ) :
    HasSum (fun n : ℕ => (2 / 3 : ℝ) ^ n * (zParity ξ n : ℝ)) (3 * Int.fract ξ) := by
  have hnonneg : ∀ n, 0 ≤ (2 / 3 : ℝ) ^ n * (zParity ξ n : ℝ) := by
    intro n
    apply mul_nonneg (by positivity)
    exact_mod_cast Int.emod_nonneg ⌊ξ * (3 / 2) ^ n⌋ (by norm_num)
  have hle : ∀ n, (2 / 3 : ℝ) ^ n * (zParity ξ n : ℝ) ≤ (2 / 3 : ℝ) ^ n := by
    intro n
    apply mul_le_of_le_one_right (by positivity)
    rcases zParity_eq_zero_or_one ξ n with h | h <;> rw [h] <;> norm_num
  have hsummable : Summable (fun n : ℕ => (2 / 3 : ℝ) ^ n * (zParity ξ n : ℝ)) :=
    Summable.of_nonneg_of_le hnonneg hle (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hrem : Tendsto (zRem ξ) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
      (h := fun N => (2 / 3 : ℝ) ^ N * (3 / 2)) tendsto_const_nhds ?_ ?_ ?_
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (2 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_const (3 / 2)
    · intro N
      simp only [zRem]
      exact mul_nonneg (by positivity) (by linarith [Int.fract_nonneg (ξ * (3 / 2) ^ N)])
    · intro N
      simp only [zRem]
      have hf : Int.fract (ξ * (3 / 2) ^ N) < 1 / 2 := hξ.2 N
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
  have htend : Tendsto (fun N => ∑ k ∈ Finset.range N, (2 / 3 : ℝ) ^ k * (zParity ξ k : ℝ))
      atTop (nhds (3 * Int.fract ξ)) := by
    have h1 : Tendsto (fun N => 3 * Int.fract ξ - zRem ξ N) atTop (nhds (3 * Int.fract ξ - 0)) :=
      tendsto_const_nhds.sub hrem
    rw [sub_zero] at h1
    simpa only [sum_range_eq hξ] using h1
  have hsum : (∑' n, (2 / 3 : ℝ) ^ n * (zParity ξ n : ℝ)) = 3 * Int.fract ξ :=
    tendsto_nhds_unique hsummable.hasSum.tendsto_sum_nat htend
  rw [← hsum]; exact hsummable.hasSum

/-- **Mahler's parity identity** (Exercise 3.1): for a Z-number `ξ`,
`3 {ξ} = ∑' n, (2/3)ⁿ εₙ`, where `εₙ = ⌊ξ (3/2)ⁿ⌋ mod 2` is the parity of the `n`-th integer part
of the `(3/2)`-orbit. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_ex_3_1", formal_uses parity_hasSum]
theorem parity_identity (hξ : IsZNumber ξ) :
    3 * Int.fract ξ = ∑' n : ℕ, (2 / 3 : ℝ) ^ n * (zParity ξ n : ℝ) :=
  (parity_hasSum hξ).tsum_eq.symm

/-- Two Z-numbers whose integer parts agree at step `n` also agree at step `n + 1`
(immediate from `floor_step`). -/
@[category API, AMS 11, ref "Bug12", group "bug_ex_3_1", formal_uses floor_step]
theorem floor_step_determined (hξ : IsZNumber ξ) (hξ' : IsZNumber ξ') (n : ℕ)
    (h : ⌊ξ * (3 / 2) ^ n⌋ = ⌊ξ' * (3 / 2) ^ n⌋) :
    ⌊ξ * (3 / 2) ^ (n + 1)⌋ = ⌊ξ' * (3 / 2) ^ (n + 1)⌋ := by
  have e := floor_step hξ n
  have e' := floor_step hξ' n
  rw [h] at e
  omega

/-- Two Z-numbers with the same integer part have the same integer part along the whole orbit. -/
@[category API, AMS 11, ref "Bug12", group "bug_ex_3_1", formal_uses floor_step_determined]
theorem floor_eq (hξ : IsZNumber ξ) (hξ' : IsZNumber ξ') (h0 : ⌊ξ⌋ = ⌊ξ'⌋) (n : ℕ) :
    ⌊ξ * (3 / 2) ^ n⌋ = ⌊ξ' * (3 / 2) ^ n⌋ := by
  induction n with
  | zero => simpa using h0
  | succ n ih => exact floor_step_determined hξ hξ' n ih

/-- **The exercise's engine**: two Z-numbers with the same integer part are equal.  Their orbits'
integer parts agree (`floor_eq`), hence their parity words agree, hence — by the parity identity —
their fractional parts agree, hence `ξ = ⌊ξ⌋ + {ξ} = ⌊ξ'⌋ + {ξ'} = ξ'`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_ex_3_1",
  formal_uses parity_identity, formal_uses floor_eq]
theorem eq_of_floor_eq (hξ : IsZNumber ξ) (hξ' : IsZNumber ξ') (h0 : ⌊ξ⌋ = ⌊ξ'⌋) : ξ = ξ' := by
  have hpar : ∀ n, zParity ξ n = zParity ξ' n := by
    intro n; simp only [zParity]; rw [floor_eq hξ hξ' h0 n]
  have hfract : Int.fract ξ = Int.fract ξ' := by
    have h1 := parity_identity hξ
    have h2 := parity_identity hξ'
    have hseries : (∑' n, (2 / 3 : ℝ) ^ n * (zParity ξ n : ℝ))
        = ∑' n, (2 / 3 : ℝ) ^ n * (zParity ξ' n : ℝ) := by
      apply tsum_congr; intro n; rw [hpar n]
    have : 3 * Int.fract ξ = 3 * Int.fract ξ' := by rw [h1, h2, hseries]
    linarith
  have hξe : (⌊ξ⌋ : ℝ) + Int.fract ξ = ξ := Int.floor_add_fract ξ
  have hξ'e : (⌊ξ'⌋ : ℝ) + Int.fract ξ' = ξ' := Int.floor_add_fract ξ'
  rw [← hξe, ← hξ'e, h0, hfract]

/-- **Exercise 3.1** (Mahler): for every integer `m`, the open interval `(m, m+1)` contains at most
one Z-number.  Hence the Z-numbers form an (at most) countable set. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_ex_3_1", formal_uses eq_of_floor_eq]
theorem zNumber_subsingleton_Ioo (m : ℤ) :
    Set.Subsingleton {ξ : ℝ | IsZNumber ξ ∧ ξ ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1)} := by
  rintro ξ ⟨hξ, hξm⟩ ξ' ⟨hξ', hξ'm⟩
  apply eq_of_floor_eq hξ hξ'
  have hm : ⌊ξ⌋ = m := by rw [Int.floor_eq_iff]; exact ⟨le_of_lt hξm.1, hξm.2⟩
  have hm' : ⌊ξ'⌋ = m := by rw [Int.floor_eq_iff]; exact ⟨le_of_lt hξ'm.1, hξ'm.2⟩
  rw [hm, hm']

end Bugeaud
