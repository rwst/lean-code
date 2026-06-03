/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Hankel matrices

Given a sequence `f : ℕ → R`, its `(n+1) × (n+1)` **Hankel matrix** has constant skew-diagonals:
the `(i, j)` entry is `f (i + j)` (rows and columns indexed `0 … n`). This is the matrix analogue
of `Matrix.circulant`, with the index sum `i + j` in place of the index difference `j - i`.

## Main definitions

* `Matrix.hankel f n` : the `(n+1) × (n+1)` Hankel matrix of `f`.
* `Matrix.kroneckerDet f n` : its determinant, the `n`-th **Kronecker (Hankel) determinant** of `f`.

## Main results

* `Matrix.hankel_isSymm` : a Hankel matrix is symmetric.

The Kronecker (Hankel) determinant of the coefficient sequence of a formal power series is
Bertin's Definition 1.1 [Ber92]; this file is the sequence-level generalization.

## References

* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

namespace Matrix

variable {R : Type*}

/-- The `(n+1) × (n+1)` **Hankel matrix** of a sequence `f : ℕ → R`: its `(i, j)` entry is
`f (i + j)` (rows and columns indexed `0 … n`). Its skew-diagonals are constant. -/
def hankel (f : ℕ → R) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => f (i.val + j.val)

@[simp] theorem hankel_apply (f : ℕ → R) (n : ℕ) (i j : Fin (n + 1)) :
    hankel f n i j = f (i.val + j.val) := rfl

/-- A Hankel matrix is symmetric: its `(i, j)` and `(j, i)` entries are both `f (i + j)`. -/
theorem hankel_isSymm (f : ℕ → R) (n : ℕ) : (hankel f n).IsSymm := by
  ext i j
  simp only [transpose_apply, hankel_apply, Nat.add_comm]

/-- The `n`-th **Kronecker (Hankel) determinant** of a sequence `f : ℕ → R`: the determinant of
the `(n+1) × (n+1)` Hankel matrix `Matrix.hankel f n`.
```
                  ⎡ f 0    f 1    ⋯   f n   ⎤
                  ⎢ f 1    f 2    ⋯   f(n+1)⎥
kroneckerDet f n = ⎢ ⋮     ⋮     ⋱   ⋮     ⎥ .
                  ⎣ f n   f(n+1)  ⋯   f(2n) ⎦
```
-/
def kroneckerDet [CommRing R] (f : ℕ → R) (n : ℕ) : R := (hankel f n).det

theorem kroneckerDet_def [CommRing R] (f : ℕ → R) (n : ℕ) :
    kroneckerDet f n = (hankel f n).det := rfl

end Matrix
