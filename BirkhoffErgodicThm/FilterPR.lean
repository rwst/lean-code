/-
Released under Apache 2.0 license as described in the file LICENSE of
https://github.com/lua-vr/pointwise-birkhoff.
Authors: Lua V. R., Pietro Monticone, Oliver Butterley
-/
import Mathlib.Order.Filter.Basic

/-!
Upstream's `Filter.EventuallyEq.add_right` and `Filter.EventuallyEq.add_left` for `α → ℝ` are now
in Mathlib (`Order/Filter/Basic`), as the `to_additive` images of `EventuallyEq.mul_right` and
`EventuallyEq.mul_left`, and for an arbitrary `[Add β]` rather than for `ℝ`.  Nothing is left to
state here; the module survives only to keep the import graph of the port intact.
-/
