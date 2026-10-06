/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import ForMathlib.NumberTheory.Solenoid.SIntegers

@[expose] public section

/-!
# The ambient group `ℝ × ∏_{p ∈ S} ℚ_p` and the fundamental domain of `ℤ[1/N_S]`

For a finite set `S` of primes the `S`-adic solenoid is `Σ_S = G_S / Δ_S`, where
`G_S = ℝ × ∏_{p ∈ S} ℚ_p` and `Δ_S` is the diagonal copy of the ring `ℤ[1/N_S]` of `S`-integers.
This file proves the one arithmetic fact on which compactness, Haar measure and the character
theory of `Σ_S` rest:

> **Every `g ∈ G_S` is congruent modulo `Δ_S` to exactly one point of
> `D_S = [0,1) × ∏_{p ∈ S} ℤ_p`.**

* **Existence** is strong approximation: subtract from each `p`-adic coordinate its principal
  part `Padic.principalPart p (g p) = m/pᵏ ∈ ℤ[1/N_S]`, which is invisible at every other prime of
  `S`, then subtract an integer to move the real coordinate into `[0,1)`.
* **Uniqueness** is the uniqueness engine `Rat.exists_intCast_of_mem_sIntegers`: an element of
  `Δ_S` in the unit box is integral at every prime, hence an integer, hence `0`.

Consequently `Δ_S` is discrete, hence closed, and `D_S` lies in the compact box
`[0,1] × ∏_{p ∈ S} ℤ_p`.

## Main declarations

* `Solenoid.ambient S`, `Solenoid.diag S`, `Solenoid.lattice S`.
* `Solenoid.D S`, `Solenoid.Dcl S`, `Solenoid.isCompact_Dcl`.
* `Solenoid.exists_mem_D_sub_mem_lattice`, `Solenoid.eq_zero_of_mem_lattice_of_small`,
  `Solenoid.exists_unique_fundamental`.
* `Solenoid.instDiscreteTopologyLattice` (closedness then comes from
  `AddSubgroup.isClosed_of_discrete`).

## Implementation notes

The real coordinate of `g : ambient S` is `g.1`, the `p`-adic coordinate `g.2 p` with `p : S`.
For `S = {2, 3}` this file specialises to `TH/Solenoid/StrongApprox.lean`, which is kept as it is.

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer (2011),
  Chapter 8 (the `S`-adic solenoid).
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Section 1.4.
* A. Weil, *Basic Number Theory*, Springer (1967) (strong approximation).
-/

namespace Solenoid

open Metric Set Rat

variable (S : Finset Nat.Primes)

/-- The ambient group `G_S = ℝ × ∏_{p ∈ S} ℚ_p` of the `S`-adic solenoid. -/
abbrev ambient : Type := ℝ × ((p : S) → ℚ_[((p : Nat.Primes) : ℕ)])

/-- The diagonal embedding `ℚ → G_S`, `q ↦ (q, (q)_p)`. -/
noncomputable def diag : ℚ →+ ambient S where
  toFun q := ((q : ℝ), fun p : S ↦ (q : ℚ_[((p : Nat.Primes) : ℕ)]))
  map_zero' := by ext <;> simp
  map_add' q r := by ext <;> simp

/-- The lattice `Δ_S = diag ℤ[1/N_S] ⊆ G_S`. -/
noncomputable def lattice : AddSubgroup (ambient S) :=
  (sIntegers S).toAddSubgroup.map (diag S)

/-- The fundamental domain `D_S = [0,1) × ∏_{p ∈ S} ℤ_p`. -/
def D : Set (ambient S) := Ico (0 : ℝ) 1 ×ˢ univ.pi fun _ ↦ closedBall 0 1

/-- The compact box `[0,1] × ∏_{p ∈ S} ℤ_p` containing the fundamental domain. -/
def Dcl : Set (ambient S) := Icc (0 : ℝ) 1 ×ˢ univ.pi fun _ ↦ closedBall 0 1

variable {S}

theorem diag_apply (q : ℚ) :
    diag S q = ((q : ℝ), fun p : S ↦ (q : ℚ_[((p : Nat.Primes) : ℕ)])) := rfl

@[simp] theorem diag_fst (q : ℚ) : (diag S q).1 = q := rfl

@[simp] theorem diag_snd (q : ℚ) (p : S) : (diag S q).2 p = (q : ℚ_[((p : Nat.Primes) : ℕ)]) :=
  rfl

theorem mem_lattice {g : ambient S} : g ∈ lattice S ↔ ∃ q ∈ sIntegers S, diag S q = g := by
  simp [lattice, AddSubgroup.mem_map]

theorem diag_mem_lattice {q : ℚ} (hq : q ∈ sIntegers S) : diag S q ∈ lattice S :=
  mem_lattice.mpr ⟨q, hq, rfl⟩

theorem mem_D {d : ambient S} : d ∈ D S ↔ (0 ≤ d.1 ∧ d.1 < 1) ∧ ∀ p, ‖d.2 p‖ ≤ 1 := by
  simp [D, Set.mem_prod, Set.mem_Ico]

theorem mem_Dcl {d : ambient S} : d ∈ Dcl S ↔ (0 ≤ d.1 ∧ d.1 ≤ 1) ∧ ∀ p, ‖d.2 p‖ ≤ 1 := by
  simp [Dcl, Set.mem_prod, Set.mem_Icc]

theorem D_subset_Dcl : D S ⊆ Dcl S := fun d hd ↦ by
  rw [mem_D] at hd
  exact mem_Dcl.mpr ⟨⟨hd.1.1, hd.1.2.le⟩, hd.2⟩

/-- `[0,1] × ∏_{p ∈ S} ℤ_p` is compact: a closed interval times finitely many closed unit balls of
proper spaces. -/
theorem isCompact_Dcl : IsCompact (Dcl S) :=
  isCompact_Icc.prod (isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _)

/-! ### The fundamental domain theorem -/

private theorem norm_sub_le_max {p : ℕ} [Fact p.Prime] (a b : ℚ_[p]) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa using Padic.nonarchimedean a (-b)

/-- A `p`-adic principal part is invisible at every other prime. -/
theorem padicNorm_principalPart_le_one {p ℓ : Nat.Primes} (h : p ≠ ℓ) (y : ℚ_[(p : ℕ)]) :
    padicNorm ℓ (Padic.principalPart (p : ℕ) y) ≤ 1 := by
  obtain ⟨m, k, hmk⟩ := Padic.exists_principalPart_eq (p := (p : ℕ)) y
  rw [hmk]
  exact padicNorm.intCast_div_pow_le_one_of_not_dvd (fun hd ↦ h
    (Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 p.2).mp hd).symm)) m k

theorem principalPart_mem_sIntegers {p : S} (y : ℚ_[((p : Nat.Primes) : ℕ)]) :
    Padic.principalPart _ y ∈ sIntegers S := by
  obtain ⟨m, k, hmk⟩ := Padic.exists_principalPart_eq (p := ((p : Nat.Primes) : ℕ)) y
  rw [hmk]
  exact div_pow_mem_sIntegers p.2 m k

/-- **Existence half of strong approximation.**  Every `g ∈ G_S` is congruent modulo `Δ_S` to a
point of the fundamental domain. -/
theorem exists_mem_D_sub_mem_lattice (g : ambient S) : ∃ d ∈ D S, g - d ∈ lattice S := by
  set a : S → ℚ := fun p ↦ Padic.principalPart _ (g.2 p) with ha
  set x : ℝ := g.1 - ((∑ p, a p : ℚ) : ℝ) with hx
  set n : ℤ := ⌊x⌋ with hn
  set r : ℚ := ∑ p, a p + n with hr
  have hrS : r ∈ sIntegers S :=
    add_mem (Subring.sum_mem _ fun p _ ↦ principalPart_mem_sIntegers _) (intCast_mem _ n)
  have hreal : (g - diag S r).1 = x - n := by
    simp only [Prod.fst_sub, diag_fst, hr, hx]
    push_cast
    ring
  refine ⟨g - diag S r, ?_, by simpa using diag_mem_lattice hrS⟩
  rw [mem_D, hreal]
  refine ⟨⟨sub_nonneg.mpr (Int.floor_le x), ?_⟩, fun p ↦ ?_⟩
  · linarith [Int.lt_floor_add_one x]
  · -- split off the `p`-th principal part; the rest is integral at `p`
    have hsplit : (g - diag S r).2 p =
        (g.2 p - (a p : ℚ_[((p : Nat.Primes) : ℕ)])) -
          ((∑ q ∈ Finset.univ.erase p, a q + n : ℚ) : ℚ_[((p : Nat.Primes) : ℕ)]) := by
      simp only [Prod.snd_sub, Pi.sub_apply, diag_snd, hr, ← Finset.add_sum_erase _ _
        (Finset.mem_univ p)]
      push_cast
      ring
    rw [hsplit]
    refine (norm_sub_le_max _ _).trans (max_le (Padic.principalPart_spec _) ?_)
    rw [Padic.eq_padicNorm]
    have hrest : padicNorm ((p : Nat.Primes) : ℕ) (∑ q ∈ Finset.univ.erase p, a q + n) ≤ 1 :=
      padicNorm.nonarchimedean.trans (max_le
        (padicNorm.sum_le' (fun q hq ↦ padicNorm_principalPart_le_one
          (fun h ↦ Finset.ne_of_mem_erase hq (Subtype.ext h)) _) zero_le_one)
        (padicNorm.of_int n))
    exact_mod_cast hrest

/-- **The lattice meets the unit box only at the origin.**  This is the uniqueness half of strong
approximation, and at the same time the discreteness of `Δ_S`. -/
theorem eq_zero_of_mem_lattice_of_small {g : ambient S} (hg : g ∈ lattice S) (h1 : |g.1| < 1)
    (h2 : ∀ p, ‖g.2 p‖ ≤ 1) : g = 0 := by
  obtain ⟨q, hq, rfl⟩ := mem_lattice.mp hg
  obtain ⟨n, rfl⟩ := exists_intCast_of_mem_sIntegers hq fun p hp ↦ by
    have h := h2 ⟨p, hp⟩
    rw [diag_snd, Padic.eq_padicNorm] at h
    exact_mod_cast h
  have hn : |(n : ℝ)| < 1 := by simpa using h1
  have : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    linarith
  subst this
  simp

/-- **Strong approximation for `S`.**  Every element of `G_S = ℝ × ∏_{p ∈ S} ℚ_p` is congruent
modulo the diagonal `ℤ[1/N_S]` to exactly one point of `D_S = [0,1) × ∏_{p ∈ S} ℤ_p`. -/
theorem exists_unique_fundamental (g : ambient S) : ∃! d, d ∈ D S ∧ g - d ∈ lattice S := by
  obtain ⟨d, hdD, hd⟩ := exists_mem_D_sub_mem_lattice g
  refine ⟨d, ⟨hdD, hd⟩, ?_⟩
  rintro d' ⟨hd'D, hd'⟩
  have hmem : d' - d ∈ lattice S := by
    simpa [sub_sub_sub_cancel_left] using sub_mem hd hd'
  rw [mem_D] at hdD hd'D
  have h1 : |(d' - d).1| < 1 := by
    rw [Prod.fst_sub, abs_lt]
    constructor <;> linarith [hdD.1.1, hdD.1.2, hd'D.1.1, hd'D.1.2]
  have h2 : ∀ p, ‖(d' - d).2 p‖ ≤ 1 := fun p ↦ by
    rw [Prod.snd_sub, Pi.sub_apply]
    exact (norm_sub_le_max _ _).trans (max_le (hd'D.2 p) (hdD.2 p))
  exact (sub_eq_zero.mp (eq_zero_of_mem_lattice_of_small hmem h1 h2))

/-- Every point of `G_S` has a representative in the compact box `Dcl S`. -/
theorem exists_mem_Dcl_sub_mem_lattice (g : ambient S) : ∃ d ∈ Dcl S, g - d ∈ lattice S := by
  obtain ⟨d, hdD, hd⟩ := exists_mem_D_sub_mem_lattice g
  exact ⟨d, D_subset_Dcl hdD, hd⟩

/-! ### Discreteness and closedness of the lattice -/

/-- `Δ_S` is a *discrete* subgroup of `G_S`: the open box `(-1,1) × ∏ {‖·‖ < 1}` isolates the
origin.  Closedness then follows from `AddSubgroup.isClosed_of_discrete`. -/
instance instDiscreteTopologyLattice : DiscreteTopology (lattice S) := by
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨Ioo (-1 : ℝ) 1 ×ˢ univ.pi fun _ ↦ ball 0 1,
    isOpen_Ioo.prod (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_ball), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, Set.mem_univ_pi, mem_ball_zero_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, h1'⟩, h2⟩
    exact Subtype.ext (eq_zero_of_mem_lattice_of_small x.2 (abs_lt.mpr ⟨h1, h1'⟩)
      fun p ↦ (h2 p).le)
  · rintro rfl
    norm_num

theorem isClosed_lattice : IsClosed (lattice S : Set (ambient S)) :=
  AddSubgroup.isClosed_of_discrete

end Solenoid
