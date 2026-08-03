/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Quotient
import ForMathlib.NumberTheory.PadicMeasurableSpace
import ForMathlib.NumberTheory.PadicFracPart
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Strong approximation at `S = {∞, 2, 3}`: the fundamental domain of the diagonal

This is the arithmetic half of the construction of the solenoid
`Σ₆ = (ℝ × ℚ₂ × ℚ₃) / ℤ[1/6]` (plan-A1+, §2.1, work package W1).  Everything downstream —
compactness of `Σ₆`, Haar measure, the character group, the Weyl dictionary — rests on the single
elementary fact proved here:

> **Every element of `G₆ = ℝ × ℚ₂ × ℚ₃` is congruent modulo the diagonal copy of `ℤ[1/6]` to
> exactly one point of `D = [0,1) × ℤ₂ × ℤ₃`.**

(`exists_unique_fundamental`.)  The two halves are genuinely different arguments:

* **Existence** is *strong approximation*: subtract from `y ∈ ℚ₂` a `2`-adic principal part
  `m/2ᵏ ∈ ℤ[1/2]` (`exists_principal_part`, obtained from the density of `ℤ` in `ℤ_[2]`), subtract
  from `z ∈ ℚ₃` a `3`-adic principal part `m'/3ᵏ' ∈ ℤ[1/3]`, and then subtract an ordinary integer
  to move the real coordinate into `[0,1)`.  The point of the ring `ℤ[1/6]` is that it is large
  enough to contain all three corrections, while each correction is invisible at the *other* finite
  place: `m/2ᵏ` is a `3`-adic integer and `m'/3ᵏ'` is a `2`-adic integer
  (`padicNorm_intCast_div_natPow_le_one`).
* **Uniqueness** is the product formula in disguise: a rational in `ℤ[1/6]` which is both a `2`-adic
  and a `3`-adic integer is a rational integer (`exists_intCast_of_mem_Z16`), and an integer of
  absolute value `< 1` is `0`.

The consequences are packaged for the next file: `Δ₆` is discrete (`instDiscreteTopologyΔ₆`) and
therefore closed (`instIsClosedΔ₆`), and `D` sits inside the compact `Dcl = [0,1] × ℤ₂ × ℤ₃`
(`isCompact_Dcl`), which is what makes the quotient compact even though `G₆` is not.

## Main statements

* `exists_unique_fundamental` — the fundamental domain: `∃! d ∈ D, g - d ∈ Δ₆`.
* `exists_principal_part` — `p`-adic principal parts: every `y ∈ ℚ_[p]` is within `1` of some
  `m/pᵏ`.
* `exists_intCast_of_mem_Z16` — an element of `ℤ[1/6]` integral at both `2` and `3` is an integer.
* `eq_zero_of_mem_Δ₆_of_small` — `Δ₆` meets the unit box only at `0`; hence
  `instDiscreteTopologyΔ₆` and `instIsClosedΔ₆`.
* `isCompact_Dcl`, `D_subset_Dcl` — the compact box containing the fundamental domain.

## References

Plan A1+ §2.1 (the box "Strong approximation at `S = {∞,2,3}` — the fundamental domain").
The object is the `S`-adic solenoid of Furstenberg's `×2, ×3` system; see [EW11, Ch. 8] for the
general algebraic frame.  Nothing here is deeper than the Chinese remainder theorem.
-/

namespace TH.S6

open Metric Set

/-- The ambient group `G₆ = ℝ × ℚ₂ × ℚ₃` of the `{∞, 2, 3}`-adic solenoid. -/
abbrev G6 : Type := ℝ × ℚ_[2] × ℚ_[3]

/-! ### The ring `ℤ[1/6]` -/

/-- The ring `ℤ[1/6] = {m/6ᵏ}` of `{2,3}`-integers, as a subring of `ℚ`.  Its diagonal image in
`G₆` is the lattice `Δ₆` whose quotient is the solenoid. -/
def Z16 : Subring ℚ where
  carrier := {q : ℚ | ∃ (m : ℤ) (k : ℕ), q = (m : ℚ) / 6 ^ k}
  zero_mem' := ⟨0, 0, by norm_num⟩
  one_mem' := ⟨1, 0, by norm_num⟩
  add_mem' := by
    rintro a b ⟨m, k, rfl⟩ ⟨m', k', rfl⟩
    exact ⟨m * 6 ^ k' + m' * 6 ^ k, k + k', by push_cast; rw [pow_add]; field_simp⟩
  mul_mem' := by
    rintro a b ⟨m, k, rfl⟩ ⟨m', k', rfl⟩
    exact ⟨m * m', k + k', by push_cast; rw [pow_add]; ring⟩
  neg_mem' := by
    rintro a ⟨m, k, rfl⟩
    exact ⟨-m, k, by push_cast; ring⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem mem_Z16 {q : ℚ} : q ∈ Z16 ↔ ∃ (m : ℤ) (k : ℕ), q = (m : ℚ) / 6 ^ k := Iff.rfl

/-- `m/pᵏ ∈ ℤ[1/6]` whenever `p ∈ {2, 3}`: the two principal-part corrections both live in the
ring. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem div_two_pow_mem_Z16 (m : ℤ) (k : ℕ) : ((m : ℚ) / 2 ^ k) ∈ Z16 :=
  ⟨m * 3 ^ k, k, by rw [show (6 : ℚ) = 2 * 3 by norm_num, mul_pow]; push_cast; field_simp⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem div_three_pow_mem_Z16 (m : ℤ) (k : ℕ) : ((m : ℚ) / 3 ^ k) ∈ Z16 :=
  ⟨m * 2 ^ k, k, by rw [show (6 : ℚ) = 3 * 2 by norm_num, mul_pow]; push_cast; field_simp⟩

/-! ### Integrality at `2` and at `3` -/

/-- If `p` does not divide `q` then `m/qᵏ` is a `p`-adic integer.  With `(p, q) = (3, 2)` this says
the `2`-adic principal part is invisible at `3`, and with `(p, q) = (2, 3)` the other way round. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem padicNorm_intCast_div_natPow_le_one {p q : ℕ} [Fact p.Prime] (hq : ¬ p ∣ q) (m : ℤ)
    (k : ℕ) : padicNorm p ((m : ℚ) / (q : ℚ) ^ k) ≤ 1 := by
  have h1 : padicNorm p ((q : ℚ) ^ k) = 1 := by
    rw [IsAbsoluteValue.abv_pow (padicNorm p), (padicNorm.nat_eq_one_iff q).mpr hq, one_pow]
  rw [padicNorm.div, h1, div_one]
  exact padicNorm.of_int m

private theorem padicNorm_six_two : padicNorm 2 (6 : ℚ) = 2⁻¹ := by
  have h6 : (6 : ℚ) = ((2 : ℕ) : ℚ) * ((3 : ℕ) : ℚ) := by norm_num
  rw [h6, padicNorm.mul, padicNorm.padicNorm_p_of_prime,
    (padicNorm.nat_eq_one_iff 3).mpr (by decide)]
  norm_num

private theorem padicNorm_six_three : padicNorm 3 (6 : ℚ) = 3⁻¹ := by
  have h6 : (6 : ℚ) = ((3 : ℕ) : ℚ) * ((2 : ℕ) : ℚ) := by norm_num
  rw [h6, padicNorm.mul, padicNorm.padicNorm_p_of_prime,
    (padicNorm.nat_eq_one_iff 2).mpr (by decide)]
  norm_num

/-- If `m/6ᵏ` is a `p`-adic integer for `p ∈ {2,3}`, then `pᵏ` divides `m`. -/
private theorem pow_dvd_of_padicNorm_le_one {p : ℕ} [Fact p.Prime] (hp6 : padicNorm p (6 : ℚ)
    = (p : ℚ)⁻¹) {m : ℤ} {k : ℕ} (h : padicNorm p ((m : ℚ) / 6 ^ k) ≤ 1) :
    ((p ^ k : ℕ) : ℤ) ∣ m := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℚ) < p := lt_trans zero_lt_one hp1
  rw [padicNorm.dvd_iff_norm_le]
  rw [padicNorm.div, IsAbsoluteValue.abv_pow (padicNorm p), hp6, div_le_one (by positivity)] at h
  calc padicNorm p (m : ℚ) ≤ ((p : ℚ)⁻¹) ^ k := h
    _ = (p : ℚ) ^ (-k : ℤ) := by rw [zpow_neg, zpow_natCast, inv_pow]

/-- **Uniqueness input.**  An element of `ℤ[1/6]` which is integral at both finite places is a
rational integer.  This is the only place where the two primes interact, and it is what makes the
fundamental domain a *fundamental* domain rather than merely a covering set. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem exists_intCast_of_mem_Z16 {r : ℚ} (hr : r ∈ Z16) (h2 : padicNorm 2 r ≤ 1)
    (h3 : padicNorm 3 r ≤ 1) : ∃ n : ℤ, r = (n : ℚ) := by
  obtain ⟨m, k, rfl⟩ := hr
  have hd2 : ((2 ^ k : ℕ) : ℤ) ∣ m := pow_dvd_of_padicNorm_le_one padicNorm_six_two h2
  have hd3 : ((3 ^ k : ℕ) : ℤ) ∣ m := pow_dvd_of_padicNorm_le_one padicNorm_six_three h3
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) ((3 ^ k : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow k k (by decide : Nat.Coprime 2 3))
  obtain ⟨n, hn⟩ := hcop.mul_dvd hd2 hd3
  refine ⟨n, ?_⟩
  have h6 : ((6 : ℚ)) ^ k = ((2 ^ k : ℕ) : ℚ) * ((3 ^ k : ℕ) : ℚ) := by
    push_cast; rw [← mul_pow]; norm_num
  rw [hn, h6]
  push_cast
  field_simp

/-! ### `p`-adic principal parts -/

/-- **Strong approximation at one finite place.**  Every `y ∈ ℚ_[p]` differs from an element
`m/pᵏ` of `ℤ[1/p]` by a `p`-adic integer.  Proof: scale `y` into `ℤ_[p]` by a power of `p`, then
use that `ℤ` is dense in `ℤ_[p]`.

The proof lives in `ForMathlib/NumberTheory/PadicFracPart.lean`, where the same statement is the
well-definedness input for the canonical character `Padic.fracPart` used by W3. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem exists_principal_part (p : ℕ) [Fact p.Prime] (y : ℚ_[p]) :
    ∃ (m : ℤ) (k : ℕ), ‖y - (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p])‖ ≤ 1 :=
  Padic.exists_principal_part p y

/-! ### The diagonal `Δ₆` and the fundamental domain `D` -/

/-- The diagonal embedding `ℚ → G₆`, `q ↦ (q, q, q)`. -/
noncomputable def diag : ℚ →+ G6 where
  toFun q := ((q : ℝ), (q : ℚ_[2]), (q : ℚ_[3]))
  map_zero' := by simp
  map_add' q r := by simp [Prod.mk_add_mk]

@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem diag_apply (q : ℚ) : diag q = ((q : ℝ), (q : ℚ_[2]), (q : ℚ_[3])) := rfl

/-- The lattice `Δ₆ = {(r, r, r) : r ∈ ℤ[1/6]} ⊆ G₆`. -/
noncomputable def Δ₆ : AddSubgroup G6 := AddSubgroup.map diag Z16.toAddSubgroup

@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem mem_Δ₆ {g : G6} : g ∈ Δ₆ ↔ ∃ q ∈ Z16, diag q = g := by
  simp [Δ₆, AddSubgroup.mem_map]

@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem diag_mem_Δ₆ {q : ℚ} (hq : q ∈ Z16) : diag q ∈ Δ₆ := mem_Δ₆.mpr ⟨q, hq, rfl⟩

/-- The fundamental domain `D = [0,1) × ℤ₂ × ℤ₃`. -/
def D : Set G6 := Ico (0 : ℝ) 1 ×ˢ (closedBall (0 : ℚ_[2]) 1 ×ˢ closedBall (0 : ℚ_[3]) 1)

/-- The compact box `[0,1] × ℤ₂ × ℤ₃` containing the fundamental domain. -/
def Dcl : Set G6 := Icc (0 : ℝ) 1 ×ˢ (closedBall (0 : ℚ_[2]) 1 ×ˢ closedBall (0 : ℚ_[3]) 1)

@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem mem_D {d : G6} : d ∈ D ↔ (0 ≤ d.1 ∧ d.1 < 1) ∧ ‖d.2.1‖ ≤ 1 ∧ ‖d.2.2‖ ≤ 1 := by
  simp [D, Set.mem_prod, Set.mem_Ico]

@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem D_subset_Dcl : D ⊆ Dcl := by
  rintro d hd
  rw [mem_D] at hd
  exact ⟨⟨hd.1.1, hd.1.2.le⟩, mem_closedBall_zero_iff.mpr hd.2.1,
    mem_closedBall_zero_iff.mpr hd.2.2⟩

/-- `[0,1] × ℤ₂ × ℤ₃` is compact: the real factor is a closed interval and the two `p`-adic factors
are closed unit balls in proper spaces. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem isCompact_Dcl : IsCompact Dcl :=
  isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

/-! ### The fundamental domain theorem -/

private theorem norm_sub_le_max' {p : ℕ} [Fact p.Prime] (a b : ℚ_[p]) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa using Padic.nonarchimedean a (-b)

/-- **Existence half of strong approximation.**  Every `g ∈ G₆` is congruent mod `Δ₆` to a point of
the fundamental domain. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem exists_mem_D_sub_mem_Δ₆ (g : G6) : ∃ d ∈ D, g - d ∈ Δ₆ := by
  obtain ⟨m, k, hm⟩ := exists_principal_part 2 g.2.1
  obtain ⟨m', k', hm'⟩ := exists_principal_part 3 g.2.2
  set a : ℚ := (m : ℚ) / (2 : ℚ) ^ k with ha
  set b : ℚ := (m' : ℚ) / (3 : ℚ) ^ k' with hb
  set n : ℤ := ⌊g.1 - (a : ℝ) - (b : ℝ)⌋ with hn
  set r : ℚ := a + b + (n : ℚ) with hr
  have hrZ : r ∈ Z16 := by
    refine Subring.add_mem _ (Subring.add_mem _ ?_ ?_) (intCast_mem _ n)
    · simpa [ha] using div_two_pow_mem_Z16 m k
    · simpa [hb] using div_three_pow_mem_Z16 m' k'
  -- the two "invisible at the other place" bounds
  have hb2 : padicNorm 2 b ≤ 1 := by
    simpa [hb] using padicNorm_intCast_div_natPow_le_one (p := 2) (q := 3) (by decide) m' k'
  have ha3 : padicNorm 3 a ≤ 1 := by
    simpa [ha] using padicNorm_intCast_div_natPow_le_one (p := 3) (q := 2) (by decide) m k
  refine ⟨g - diag r, ?_, ?_⟩
  · rw [mem_D]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := Int.floor_le (g.1 - (a : ℝ) - (b : ℝ))
      simp only [diag_apply, Prod.fst_sub, hr]
      push_cast
      linarith
    · have := Int.lt_floor_add_one (g.1 - (a : ℝ) - (b : ℝ))
      simp only [diag_apply, Prod.fst_sub, hr]
      push_cast
      linarith
    · have hsplit : (g - diag r).2.1 = (g.2.1 - (a : ℚ_[2])) - ((b + (n : ℚ) : ℚ) : ℚ_[2]) := by
        simp only [diag_apply, Prod.snd_sub, Prod.fst_sub, hr]
        push_cast
        ring
      rw [hsplit]
      refine le_trans (norm_sub_le_max' _ _) (max_le hm ?_)
      rw [Padic.eq_padicNorm]
      have : padicNorm 2 (b + (n : ℚ)) ≤ 1 :=
        le_trans padicNorm.nonarchimedean (max_le hb2 (padicNorm.of_int n))
      exact_mod_cast this
    · have hsplit : (g - diag r).2.2 = (g.2.2 - (b : ℚ_[3])) - ((a + (n : ℚ) : ℚ) : ℚ_[3]) := by
        simp only [diag_apply, Prod.snd_sub, hr]
        push_cast
        ring
      rw [hsplit]
      refine le_trans (norm_sub_le_max' _ _) (max_le hm' ?_)
      rw [Padic.eq_padicNorm]
      have : padicNorm 3 (a + (n : ℚ)) ≤ 1 :=
        le_trans padicNorm.nonarchimedean (max_le ha3 (padicNorm.of_int n))
      exact_mod_cast this
  · simpa using diag_mem_Δ₆ hrZ

/-- **The lattice meets the unit box only at the origin.**  This is the uniqueness half of strong
approximation, and simultaneously the discreteness of `Δ₆`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem eq_zero_of_mem_Δ₆_of_small {g : G6} (hg : g ∈ Δ₆) (h1 : |g.1| < 1) (h2 : ‖g.2.1‖ ≤ 1)
    (h3 : ‖g.2.2‖ ≤ 1) : g = 0 := by
  obtain ⟨q, hq, rfl⟩ := mem_Δ₆.mp hg
  have hq2 : padicNorm 2 q ≤ 1 := by
    have h := h2
    simp only [diag_apply, Padic.eq_padicNorm] at h
    exact_mod_cast h
  have hq3 : padicNorm 3 q ≤ 1 := by
    have h := h3
    simp only [diag_apply, Padic.eq_padicNorm] at h
    exact_mod_cast h
  obtain ⟨n, rfl⟩ := exists_intCast_of_mem_Z16 hq hq2 hq3
  have hn : |(n : ℝ)| < 1 := by
    simp only [diag_apply] at h1
    exact_mod_cast h1
  have : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
      exact_mod_cast this
    linarith
  subst this
  simp [diag_apply]

/-- **Strong approximation at `S = {∞, 2, 3}`.**  Every element of `G₆ = ℝ × ℚ₂ × ℚ₃` is congruent
modulo the diagonal `ℤ[1/6]` to exactly one point of `D = [0,1) × ℤ₂ × ℤ₃`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem exists_unique_fundamental (g : G6) : ∃! d, d ∈ D ∧ g - d ∈ Δ₆ := by
  obtain ⟨d, hdD, hd⟩ := exists_mem_D_sub_mem_Δ₆ g
  refine ⟨d, ⟨hdD, hd⟩, ?_⟩
  rintro d' ⟨hd'D, hd'⟩
  have hmem : d' - d ∈ Δ₆ := by
    have : (g - d) - (g - d') ∈ Δ₆ := AddSubgroup.sub_mem _ hd hd'
    simpa [sub_sub_sub_cancel_left] using this
  rw [mem_D] at hdD hd'D
  have h1 : |(d' - d).1| < 1 := by
    rw [Prod.fst_sub, abs_lt]
    constructor <;> linarith [hdD.1.1, hdD.1.2, hd'D.1.1, hd'D.1.2]
  have h2 : ‖(d' - d).2.1‖ ≤ 1 := by
    rw [Prod.snd_sub, Prod.fst_sub]
    exact le_trans (norm_sub_le_max' _ _) (max_le hd'D.2.1 hdD.2.1)
  have h3 : ‖(d' - d).2.2‖ ≤ 1 := by
    rw [Prod.snd_sub, Prod.snd_sub]
    exact le_trans (norm_sub_le_max' _ _) (max_le hd'D.2.2 hdD.2.2)
  have := eq_zero_of_mem_Δ₆_of_small hmem h1 h2 h3
  linear_combination (norm := abel) this

/-- Every point of `G₆` has a representative in the compact box `Dcl`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_strong_approx"]
theorem exists_mem_Dcl_sub_mem_Δ₆ (g : G6) : ∃ d ∈ Dcl, g - d ∈ Δ₆ := by
  obtain ⟨d, hdD, hd⟩ := exists_mem_D_sub_mem_Δ₆ g
  exact ⟨d, D_subset_Dcl hdD, hd⟩

/-! ### Discreteness and closedness of the lattice -/

/-- `Δ₆` is a *discrete* subgroup of `G₆`: the open box `(-1,1) × {‖·‖<1} × {‖·‖<1}` isolates the
origin. -/
instance instDiscreteTopologyΔ₆ : DiscreteTopology Δ₆ := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  rw [isOpen_induced_iff]
  refine ⟨Ioo (-1 : ℝ) 1 ×ˢ (ball (0 : ℚ_[2]) 1 ×ˢ ball (0 : ℚ_[3]) 1),
    isOpen_Ioo.prod (Metric.isOpen_ball.prod Metric.isOpen_ball), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, mem_ball_zero_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, h1'⟩, h2, h3⟩
    have : (x : G6) = 0 :=
      eq_zero_of_mem_Δ₆_of_small x.2 (abs_lt.mpr ⟨h1, h1'⟩) h2.le h3.le
    exact Subtype.ext this
  · rintro rfl
    norm_num

/-- A discrete subgroup of a Hausdorff topological group is closed. -/
instance instIsClosedΔ₆ : IsClosed (Δ₆ : Set G6) := AddSubgroup.isClosed_of_discrete

end TH.S6
