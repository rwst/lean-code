/-
Released under Apache 2.0 license as described in the file LICENSE of
https://github.com/lua-vr/pointwise-birkhoff.
Authors: Lua V. R., Oliver Butterley, Pietro Monticone
-/
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
This module was the PR-bound part of the upstream project, and it has since landed in Mathlib:
`Function.iterate_invariant` (`Logic/Function/Iterate`), `birkhoffSum_of_comp_eq`
(`Dynamics/BirkhoffSum/Basic`), and `birkhoffAverage_of_comp_eq`, `birkhoffAverage_neg`,
`birkhoffAverage_add`, `birkhoffAverage_sub` (`Dynamics/BirkhoffSum/Average`) -- the last three
under those very names, so the upstream copies cannot be kept here at all.  What remains is the
three names the rest of the port uses, as one-line aliases for the Mathlib results.
-/

variable {R α M : Type*} {f : α → α} {n : ℕ}

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then `φ` remains invariant under any number of iterations of `f`. -/
lemma invariant_iter {φ : α → M} (h : φ ∘ f = φ) (i : ℕ) : φ ∘ f^[i] = φ :=
  Function.iterate_invariant h i

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then the Birkhoff sum of `φ` over `f` for `n` iterations is equal to `n • φ`. -/
theorem birkhoffSum_of_invariant [AddCommMonoid M] {φ : α → M} (h : φ ∘ f = φ) :
    birkhoffSum f φ n = n • φ :=
  birkhoffSum_of_comp_eq h n

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then the Birkhoff average of `φ` over `f` for `n` iterations is equal to `φ`
provided `0 < n`. -/
theorem birkhoffAverage_of_invariant [DivisionSemiring R] [AddCommMonoid M] [Module R M]
    [CharZero R] {φ : α → M} (h : φ ∘ f = φ) (hn : 0 < n) : birkhoffAverage R f φ n = φ :=
  birkhoffAverage_of_comp_eq R h (Nat.cast_ne_zero.mpr hn.ne')
