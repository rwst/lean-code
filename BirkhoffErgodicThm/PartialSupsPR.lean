/-
Released under Apache 2.0 license as described in the file LICENSE of
https://github.com/lua-vr/pointwise-birkhoff.
Authors: Oliver Butterley, Lua V. R.
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Order.Hom.Lattice

/-!
Most of this module has landed in Mathlib: upstream's `map_partialSups` is `comp_partialSups`
(`Order/PartialSups`, the name `map_partialSups` being taken there by the pointwise form), and
`partialSups_succ'` and `partialSups_add_one'` are in `Algebra/Order/SuccPred/PartialSups` under
those very names.  Only the translation lemma below is still missing there.
-/

-- To be added to `Mathlib/Order/PartialSups`. Correct name?
open OrderIso in
lemma add_partialSups {ι α : Type*} [Preorder ι] [LocallyFiniteOrderBot ι] [Lattice α] [AddGroup α]
    [AddLeftMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (c + f ·) i = c + partialSups f i := by
  change (partialSups (addLeft c ∘ _)) i = _
  rw [comp_partialSups f (addLeft c)]; rfl
