/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The cyclic construction via transfer matrices

The *sequence* construction `SEQ` (`GeneratingFunction/Seq.lean`) enumerates open words —
finite lists of atoms, with no constraint across the two ends. This file adds its *cyclic*
sibling: fixed-position **cyclic words** under an allowed-adjacency relation, counted by a
**transfer matrix**.

Fix a finite set of letters and a transfer matrix `M : Matrix n n R`, where `M i j` is the
weight of the directed step `i → j` (e.g. `1`, or a monomial) and is `0` when that step is
forbidden. When the data is just *which* steps are allowed, `transferMatrix` assembles `M`
from that adjacency relation — so a combinatorial rule, not a hand-picked matrix, is the
input. A *cyclic word of length `k`* is a closed walk `i₀ → i₁ → ⋯ → i_{k-1} → i₀`,
and its weight is the product of its step weights; the total weight of all length-`k`
cyclic words is the trace `tr(Mᵏ)` (the sum over all closed walks — for a `0/1` adjacency
matrix, simply their number). Collecting these gives the cyclic generating function

    cycGF M  =  ∑ₖ tr(Mᵏ) Xᵏ.

Classically this is the trace of the resolvent, `cycGF M = tr((1 - X·M)⁻¹)`
(`cycGF_eq_trace_inv`): the matrix `1 - X·M` (`oneSubXSmul`) is invertible over `R⟦X⟧`, with
inverse the **resolvent** `∑ₖ Mᵏ Xᵏ` (`resolvent`, `inv_oneSubXSmul`) — the entrywise
walk-counting generating functions — and summing its diagonal recovers `cycGF M`. Cramer's rule
then makes `cycGF M` a rational series with denominator `det(1 - X·M)`:
`det(1 - X·M) · cycGF M = tr(adj(1 - X·M))` (`det_oneSubXSmul_mul_cycGF`). What is still left
to the prose here (see the `TODO`) is the bijection "closed walks of length `k` ↔ cyclic words
of length `k`" turning `tr(Mᵏ)` into an honest `Nat.card`.

## Main definitions

* `transferMatrix`: the `0/1` transfer matrix of an allowed-adjacency relation.
* `cycGF`: the cyclic generating function `∑ₖ tr(Mᵏ) Xᵏ` of a transfer matrix `M`.
* `oneSubXSmul`: the matrix `1 - X·M` over `R⟦X⟧`.
* `resolvent`: the resolvent matrix `(1 - X·M)⁻¹`, with `(i, j)` entry `∑ₖ (Mᵏ)ᵢⱼ Xᵏ`.

## Main results

* `coeff_cycGF`: the `k`-th coefficient of `cycGF M` is `tr(Mᵏ)`.
* `inv_oneSubXSmul`: the resolvent is the inverse of `1 - X·M`.
* `cycGF_eq_trace_inv`: the resolvent closed form `cycGF M = tr((1 - X·M)⁻¹)`.
* `det_oneSubXSmul_mul_cycGF`: rationality, `det(1 - X·M) · cycGF M = tr(adj(1 - X·M))`.
* `cycGF_fibMatrix_funEq`: the Lucas functional equation `C = (2 - X) + (X + X²)·C`.
* `cycGF_fibMatrix_inv`: the closed form `C = (2 - X)·(1 - (X + X²))⁻¹` over a field.

## TODO

* The combinatorial bridge `tr(Mᵏ) = Nat.card {cyclic words of length k}` for a `0/1`
  adjacency matrix, tying `cycGF` to an enumerated class as elsewhere in the framework.

## References

* [P. Flajolet and R. Sedgewick, *Analytic Combinatorics*][flajolet2009] (the
  transfer-matrix method).
-/

@[expose] public section

open PowerSeries Matrix

namespace Combinatorics

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

section Semiring

variable {R : Type*} [Semiring R]

/-- The cyclic generating function of a transfer matrix `M`: the ordinary GF whose
`n`-th coefficient is `tr(Mⁿ)`, the (weighted) number of cyclic words of length `n`. -/
noncomputable def cycGF (M : Matrix n n R) : PowerSeries R :=
  PowerSeries.mk fun k => Matrix.trace (M ^ k)

@[simp]
theorem coeff_cycGF (M : Matrix n n R) (k : ℕ) :
    PowerSeries.coeff k (cycGF M) = Matrix.trace (M ^ k) := by
  rw [cycGF, coeff_mk]

/-- The **transfer matrix** of an allowed-adjacency relation `Adj` on the letter set `n`:
its `(i, j)` entry is `1` when the step `i → j` is allowed and `0` when forbidden. This is
how a local "which letter may follow which" rule becomes a matrix; feeding it to `cycGF`
enumerates the cyclic words obeying `Adj` at every step (the seam included). -/
def transferMatrix (Adj : n → n → Prop) [DecidableRel Adj] : Matrix n n R :=
  .of fun i j => if Adj i j then 1 else 0

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem transferMatrix_apply (Adj : n → n → Prop) [DecidableRel Adj] (i j : n) :
    transferMatrix Adj i j = if Adj i j then (1 : R) else 0 := rfl

end Semiring

section Resolvent

variable {R : Type*} [CommRing R]

/-- The **resolvent matrix** of `M`: the matrix of power series whose `(i, j)` entry is the
ordinary generating function `∑ₖ (Mᵏ)ᵢⱼ Xᵏ`, counting (weighted) walks `i → j` by their length.
It is the inverse of `1 - X·M` (`inv_oneSubXSmul`), so its trace recovers the cyclic
generating function `cycGF M` (`trace_resolvent`) — the resolvent form of the transfer-matrix
method. -/
noncomputable def resolvent (M : Matrix n n R) : Matrix n n (PowerSeries R) :=
  .of fun i j => mk fun k => (M ^ k) i j

@[simp]
theorem coeff_resolvent (M : Matrix n n R) (i j : n) (k : ℕ) :
    coeff k (resolvent M i j) = (M ^ k) i j := by
  simp [resolvent, coeff_mk]

/-- The matrix `1 - X·M` over `R⟦X⟧`, with `M` embedded entrywise as constant power series. Its
inverse is the resolvent `resolvent M` (`inv_oneSubXSmul`), and its determinant
`det(1 - X·M)` is the denominator of the rational series `cycGF M`
(`det_oneSubXSmul_mul_cycGF`). -/
noncomputable def oneSubXSmul (M : Matrix n n R) : Matrix n n (PowerSeries R) :=
  1 - (X : PowerSeries R) • M.map (C : R →+* PowerSeries R)

/-- The `(i, j)` coefficient of `M · resolvent M` shifts the walk count by one step:
`[Xᵐ] (M · resolvent M)ᵢⱼ = (Mᵐ⁺¹)ᵢⱼ`. -/
private theorem coeff_map_C_mul_resolvent (M : Matrix n n R) (i j : n) (m : ℕ) :
    coeff m ((M.map (C : R →+* PowerSeries R) * resolvent M) i j) = (M ^ (m + 1)) i j := by
  rw [mul_apply, map_sum]
  simp_rw [map_apply, coeff_C_mul, coeff_resolvent]
  rw [← mul_apply, ← pow_succ']

omit [Fintype n] in
/-- The `(i, j)` coefficient of the identity matrix over `R⟦X⟧`: the entry `(1 : Matrix n n R) i j`
in degree `0`, and `0` in every positive degree. -/
private theorem coeff_one_apply (i j : n) (m : ℕ) :
    coeff m ((1 : Matrix n n (PowerSeries R)) i j)
      = if m = 0 then (1 : Matrix n n R) i j else 0 := by
  have h1 : (1 : Matrix n n (PowerSeries R)) = (1 : Matrix n n R).map (C : R →+* PowerSeries R) :=
    (Matrix.map_one (C : R →+* PowerSeries R) (map_zero _) (map_one _)).symm
  rw [h1, map_apply, coeff_C]

/-- The geometric-series identity `(1 - X·M) · ∑ₖ Mᵏ Xᵏ = 1`: multiplying `1 - X·M` by the
resolvent gives the identity matrix, proved coefficient by coefficient. -/
theorem oneSubXSmul_mul_resolvent (M : Matrix n n R) :
    oneSubXSmul M * resolvent M = 1 := by
  rw [oneSubXSmul, sub_mul, one_mul, Matrix.smul_mul]
  ext i j m
  rw [sub_apply, smul_apply, smul_eq_mul, map_sub, coeff_resolvent, coeff_one_apply]
  obtain _ | m := m
  · simp [coeff_zero_eq_constantCoeff_apply]
  · rw [coeff_succ_X_mul, coeff_map_C_mul_resolvent, sub_self]
    simp

/-- **The resolvent is the inverse of `1 - X·M`** in `Matrix n n R⟦X⟧`. -/
theorem inv_oneSubXSmul (M : Matrix n n R) :
    (oneSubXSmul M)⁻¹ = resolvent M :=
  inv_eq_right_inv (oneSubXSmul_mul_resolvent M)

/-- The trace of the resolvent is the cyclic generating function: summing the diagonal
walk-counting series `∑ₖ (Mᵏ)ᵢᵢ Xᵏ` over `i` yields `∑ₖ tr(Mᵏ) Xᵏ = cycGF M`. -/
theorem trace_resolvent (M : Matrix n n R) : trace (resolvent M) = cycGF M := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_cycGF]
  simp only [Matrix.trace, diag_apply, map_sum, coeff_resolvent]

/-- **The resolvent closed form of the cyclic OGF**: `cycGF M = tr((1 - X·M)⁻¹)`, the trace of
the resolvent `(1 - X·M)⁻¹` of the transfer matrix `M`. This is the transfer-matrix method in
its general (resolvent) form. -/
theorem cycGF_eq_trace_inv (M : Matrix n n R) :
    cycGF M = trace ((oneSubXSmul M)⁻¹) := by
  rw [inv_oneSubXSmul, trace_resolvent]

/-- The denominator `det(1 - X·M)` is a unit in `R⟦X⟧`: its constant term is `det 1 = 1`. -/
private theorem isUnit_det_oneSubXSmul (M : Matrix n n R) :
    IsUnit (det (oneSubXSmul M)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hmap :
      (constantCoeff (R := R)).mapMatrix (oneSubXSmul M) = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, map_apply, oneSubXSmul, ← coeff_zero_eq_constantCoeff_apply,
      sub_apply, map_sub, coeff_one_apply, if_pos rfl, smul_apply, smul_eq_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul, sub_zero]
  rw [RingHom.map_det, hmap, det_one]
  exact isUnit_one

/-- **Rationality of the cyclic OGF**: `det(1 - X·M) · cycGF M = tr(adj(1 - X·M))`. Equivalently
`cycGF M = tr(adj(1 - X·M)) / det(1 - X·M)`, exhibiting `cycGF M` as a rational series with
denominator `det(1 - X·M)` — the classical transfer-matrix rationality statement. -/
theorem det_oneSubXSmul_mul_cycGF (M : Matrix n n R) :
    det (oneSubXSmul M) * cycGF M
      = trace (oneSubXSmul M).adjugate := by
  rw [cycGF_eq_trace_inv, Matrix.inv_def, trace_smul, smul_eq_mul, ← mul_assoc,
    Ring.mul_inverse_cancel _ (isUnit_det_oneSubXSmul M), one_mul]

end Resolvent

end Combinatorics
