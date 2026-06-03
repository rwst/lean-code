/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant of an anti-triangular matrix with constant anti-diagonal

A square matrix that vanishes strictly above its anti-diagonal and is constant (`= c`) on the
anti-diagonal has determinant `± c ^ (size)`. Reversing the rows (or columns) turns it into a
triangular matrix with constant diagonal `c`, and the reversal permutation contributes the sign.

This determinant identity is the linear-algebra core of Kronecker's rationality criterion for
formal power series; see Bertin's Theorem 1.1.1 [Ber92].

## References

* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

namespace Matrix

/-- A square matrix that vanishes strictly above its anti-diagonal (`T i j = 0` when `i + j < K`)
and is constantly `c` on the anti-diagonal (`T i i.rev = c`) has determinant `± c ^ (K+1)`: reverse
the columns to make it lower-triangular with diagonal `c`, then `det_permute'` supplies the sign. -/
theorem det_eq_unit_mul_pow_of_antidiag_const {R : Type*} [CommRing R] {K : ℕ}
    (T : Matrix (Fin (K + 1)) (Fin (K + 1)) R) (c : R)
    (hbelow : ∀ i j : Fin (K + 1), (i : ℕ) + (j : ℕ) < K → T i j = 0)
    (hdiag : ∀ i : Fin (K + 1), T i i.rev = c) :
    ∃ u : R, IsUnit u ∧ T.det = u * c ^ (K + 1) := by
  set rev : Equiv.Perm (Fin (K + 1)) := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ with hrev
  have hcoe : ⇑rev = Fin.rev := rfl
  -- Reversing the rows makes the matrix upper-triangular with diagonal `c`.
  have hut : Matrix.BlockTriangular (T.submatrix rev id) id := by
    intro i j hij
    simp only [id_eq] at hij
    rw [Matrix.submatrix_apply, id_eq]
    apply hbelow
    have hr : (rev i).val = K - i.val := by rw [hcoe, Fin.val_rev]; omega
    have hji : (j : ℕ) < (i : ℕ) := hij
    have hi : (i : ℕ) < K + 1 := i.isLt
    omega
  have hdet' : (T.submatrix rev id).det = c ^ (K + 1) := by
    rw [Matrix.det_of_upperTriangular hut]
    have hd : ∀ i : Fin (K + 1), (T.submatrix rev id) i i = c := fun i => by
      rw [Matrix.submatrix_apply, id_eq, hcoe]
      have hi := hdiag (Fin.rev i)
      rwa [Fin.rev_rev] at hi
    simp only [hd, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Matrix.det_permute rev T] at hdet'
  rcases Int.units_eq_one_or (Equiv.Perm.sign rev) with h | h <;> rw [h] at hdet' <;>
    push_cast at hdet'
  · refine ⟨1, isUnit_one, ?_⟩
    rw [one_mul] at hdet'; rw [one_mul]; exact hdet'
  · refine ⟨-1, isUnit_one.neg, ?_⟩
    rw [neg_one_mul] at hdet'; rw [neg_one_mul, ← hdet', neg_neg]

end Matrix
