/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import ForMathlib.NumberTheory.PadicMeasurableSpace

@[expose] public section

/-!
# Haar measure on `ℚ_[p]`, normalized on the unit ball

`ℚ_[p]` is a locally compact (indeed proper) second-countable topological group, so it carries a
Haar measure; with the Borel σ-algebra of `ForMathlib/NumberTheory/PadicMeasurableSpace.lean` in
place, Mathlib's `MeasureTheory.Measure.addHaarMeasure` applies verbatim.  The only choice is the
normalization, and there is a canonical one: the compact open subgroup
`ℤ_[p] = {x | ‖x‖ ≤ 1}` is given mass `1`.

The point of the file is the mass of a ball:

`haarMeasure p (closedBall c (p ^ (-k)))` `=` `(p ^ k)⁻¹`,

i.e. the residue classes mod `pᵏ` all have the same mass and there are `pᵏ` of them.  The proof is
the finite partition of the unit ball into the `pᵏ` balls around `0, 1, …, pᵏ - 1`, which is
Mathlib's `PadicInt.appr` (existence) together with `PadicInt.ker_toZModPow` (separation),
transported across `PadicInt.norm_def`.

This is the `ℚ_[p]`-analogue of `ForMathlib/NumberTheory/PadicIntHaar.lean`
(`PadicInt.measure_toZModPow_fiber`, the same masses for the fibers of `toZModPow` on `ℤ_[p]`).
The two are genuinely different statements: a measure on `ℤ_[p]` cannot be translated by a general
element of `ℚ_[p]`, so a construction that needs an ambient invariant measure on `ℚ_[p]` —
for instance a Haar measure on `ℝ × ℚ_[2] × ℚ_[3]` and its solenoid quotient — has to work here.

## Main declarations

* `Padic.unitBall` — `ℤ_[p] ⊆ ℚ_[p]` as a `PositiveCompacts`.
* `Padic.haarMeasure` — Haar measure on `ℚ_[p]`, normalized by `haarMeasure p (ℤ_[p]) = 1`.
* `Padic.exists_natCast_approx`, `Padic.natCast_eq_of_norm_sub_le` — the residues mod `pᵏ`
  represented by `0, 1, …, pᵏ - 1`.
* `Padic.haarMeasure_closedBall`, `Padic.haarMeasure_residueBall` — a ball of radius `p⁻ᵏ`, i.e.
  a residue class mod `pᵏ`, has mass `p⁻ᵏ`.
-/

namespace Padic

open Metric MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ### The measure -/

/-- The unit ball of `ℚ_[p]` — the image of `ℤ_[p]` — as a positive compact set.  It is compact
because `ℚ_[p]` is proper, and open (hence of nonempty interior) because the metric is
ultrametric. -/
noncomputable def unitBall (p : ℕ) [Fact p.Prime] : PositiveCompacts ℚ_[p] :=
  ⟨⟨closedBall 0 1, isCompact_closedBall _ _⟩, by
    rw [(IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).interior_eq]
    exact ⟨0, by simp⟩⟩

/-- **Haar measure on `ℚ_[p]`**, normalized so that the unit ball `ℤ_[p]` has mass `1`. -/
noncomputable def haarMeasure (p : ℕ) [Fact p.Prime] : Measure ℚ_[p] :=
  Measure.addHaarMeasure (unitBall p)

noncomputable instance instIsAddHaarMeasureHaarMeasure : (haarMeasure p).IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure (unitBall p)).IsAddHaarMeasure)

instance instSigmaFiniteHaarMeasure : SigmaFinite (haarMeasure p) :=
  inferInstanceAs (SigmaFinite (Measure.addHaarMeasure (unitBall p)))

instance instSFiniteHaarMeasure : SFinite (haarMeasure p) :=
  inferInstanceAs (SFinite (Measure.addHaarMeasure (unitBall p)))

instance instIsAddRightInvariantHaarMeasure : (haarMeasure p).IsAddRightInvariant :=
  inferInstanceAs ((Measure.addHaarMeasure (unitBall p)).IsAddRightInvariant)

/-- The normalization: the `p`-adic integers have mass `1`. -/
theorem haarMeasure_closedBall_one : haarMeasure p (closedBall 0 1) = 1 :=
  Measure.addHaarMeasure_self

/-! ### Residues mod `pᵏ` -/

/-- Every `p`-adic integer is within `p⁻ᵏ` of a natural number `< pᵏ`: the truncation of its
`p`-adic expansion, `PadicInt.appr`. -/
theorem exists_natCast_approx (k : ℕ) {y : ℚ_[p]} (hy : ‖y‖ ≤ 1) :
    ∃ j : ℕ, j < p ^ k ∧ ‖y - (j : ℚ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
  set x : ℤ_[p] := ⟨y, hy⟩ with hx
  refine ⟨x.appr k, PadicInt.appr_lt x k, ?_⟩
  have h : ‖x - (x.appr k : ℤ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow]
    exact PadicInt.appr_spec k x
  rw [PadicInt.norm_def] at h
  push_cast [hx] at h
  exact h

/-- Two natural numbers `< pᵏ` that are `p`-adically `pᵏ`-close are equal: the residues mod `pᵏ`
are separated by exactly the radius `p⁻ᵏ`. -/
theorem natCast_eq_of_norm_sub_le {k i j : ℕ} (hi : i < p ^ k) (hj : j < p ^ k)
    (h : ‖(i : ℚ_[p]) - (j : ℚ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ)) : i = j := by
  have hmem : ((i : ℤ_[p]) - (j : ℤ_[p])) ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def]
    push_cast
    exact h
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  simp only [map_natCast] at hmem
  have : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩
  have := congrArg ZMod.val hmem
  rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this

/-! ### The mass of a ball -/

/-- Haar measure does not see the center of a ball. -/
theorem haarMeasure_closedBall_center (c : ℚ_[p]) (r : ℝ) :
    haarMeasure p (closedBall c r) = haarMeasure p (closedBall 0 r) := by
  have h : (fun x => c + x) ⁻¹' (closedBall c r) = closedBall 0 r := by
    ext x
    simp [mem_closedBall, dist_eq_norm]
  rw [← h, measure_preimage_add]

private theorem zpow_neg_le_one (k : ℕ) : (p : ℝ) ^ (-k : ℤ) ≤ 1 := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hp)

theorem haarMeasure_closedBall_zero (k : ℕ) :
    haarMeasure p (closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-k : ℤ))) = ((p : ℝ≥0∞) ^ k)⁻¹ := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩
  set r : ℝ := (p : ℝ) ^ (-k : ℤ) with hr
  set f : Fin (p ^ k) → Set ℚ_[p] := fun j => closedBall ((j : ℕ) : ℚ_[p]) r with hf
  have hcover : closedBall (0 : ℚ_[p]) 1 = ⋃ j, f j := by
    ext y
    simp only [Set.mem_iUnion, hf, mem_closedBall, dist_eq_norm, sub_zero]
    constructor
    · intro hy
      obtain ⟨j, hj, hjy⟩ := exists_natCast_approx k hy
      exact ⟨⟨j, hj⟩, hjy⟩
    · rintro ⟨j, hj⟩
      calc ‖y‖ = ‖(y - ((j : ℕ) : ℚ_[p])) + ((j : ℕ) : ℚ_[p])‖ := by ring_nf
        _ ≤ max ‖y - ((j : ℕ) : ℚ_[p])‖ ‖((j : ℕ) : ℚ_[p])‖ := nonarchimedean _ _
        _ ≤ 1 := max_le (hj.trans (zpow_neg_le_one k))
              (by exact_mod_cast norm_int_le_one (p := p) (j : ℕ))
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro a b hab
    refine Set.disjoint_left.2 fun y hya hyb => hab ?_
    simp only [hf, mem_closedBall] at hya hyb
    have hab' : ‖((a : ℕ) : ℚ_[p]) - ((b : ℕ) : ℚ_[p])‖ ≤ r := by
      rw [← dist_eq_norm]
      exact (IsUltrametricDist.dist_triangle_max _ y _).trans
        (max_le (by rwa [dist_comm]) hyb)
    exact Fin.ext (natCast_eq_of_norm_sub_le a.2 b.2 hab')
  have hsum : (1 : ℝ≥0∞) = (p : ℝ≥0∞) ^ k * haarMeasure p (closedBall (0 : ℚ_[p]) r) := by
    calc (1 : ℝ≥0∞) = haarMeasure p (closedBall (0 : ℚ_[p]) 1) := haarMeasure_closedBall_one.symm
      _ = ∑' j : Fin (p ^ k), haarMeasure p (f j) := by
          rw [hcover]; exact measure_iUnion hdisj fun _ => measurableSet_closedBall
      _ = ∑ _j : Fin (p ^ k), haarMeasure p (closedBall (0 : ℚ_[p]) r) := by
          rw [tsum_fintype]
          exact Finset.sum_congr rfl fun j _ => haarMeasure_closedBall_center _ _
      _ = (p : ℝ≥0∞) ^ k * haarMeasure p (closedBall (0 : ℚ_[p]) r) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum.symm)

/-- **The mass of a `p`-adic ball.**  With the normalization `haarMeasure p (ℤ_[p]) = 1`, the ball
of radius `p⁻ᵏ` — a residue class mod `pᵏ` — has mass `p⁻ᵏ`. -/
theorem haarMeasure_closedBall (c : ℚ_[p]) (k : ℕ) :
    haarMeasure p (closedBall c ((p : ℝ) ^ (-k : ℤ))) = ((p : ℝ≥0∞) ^ k)⁻¹ := by
  rw [haarMeasure_closedBall_center, haarMeasure_closedBall_zero]

/-! ### Residue classes -/

/-- The residue class of `c` mod `pᵏ` inside `ℚ_[p]`: the ball of radius `p⁻ᵏ` around `c`.  It is
clopen, and (for `‖c‖ ≤ 1`) one of the `pᵏ` classes partitioning `ℤ_[p]`. -/
def residueBall (p : ℕ) [Fact p.Prime] (k : ℕ) (c : ℚ_[p]) : Set ℚ_[p] :=
  closedBall c ((p : ℝ) ^ (-k : ℤ))

theorem mem_residueBall {k : ℕ} {c y : ℚ_[p]} :
    y ∈ residueBall p k c ↔ ‖y - c‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
  rw [residueBall, mem_closedBall, dist_eq_norm]

theorem isOpen_residueBall (k : ℕ) (c : ℚ_[p]) : IsOpen (residueBall p k c) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact IsUltrametricDist.isOpen_closedBall c (zpow_pos hp _).ne'

theorem measurableSet_residueBall (k : ℕ) (c : ℚ_[p]) : MeasurableSet (residueBall p k c) :=
  measurableSet_closedBall

/-- The residue class mod `p⁰ = 1` around the origin is all of `ℤ_[p]`. -/
theorem residueBall_zero : residueBall p 0 (0 : ℚ_[p]) = closedBall 0 1 := by
  rw [residueBall]
  norm_num

/-- A residue class of a `p`-adic integer consists of `p`-adic integers. -/
theorem residueBall_subset_unitBall {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) (k : ℕ) :
    residueBall p k c ⊆ closedBall (0 : ℚ_[p]) 1 := by
  intro y hy
  rw [mem_residueBall] at hy
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  calc ‖y‖ = ‖(y - c) + c‖ := by ring_nf
    _ ≤ max ‖y - c‖ ‖c‖ := nonarchimedean _ _
    _ ≤ 1 := max_le (hy.trans (zpow_neg_le_one k)) hc

/-- **Every residue class mod `pᵏ` has mass `p⁻ᵏ`.** -/
theorem haarMeasure_residueBall (k : ℕ) (c : ℚ_[p]) :
    haarMeasure p (residueBall p k c) = ((p : ℝ≥0∞) ^ k)⁻¹ :=
  haarMeasure_closedBall c k

end Padic
