/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.NumberTheory.Height.NumberField

@[expose] public section

/-!
# Values of the places of a number field on rational numbers

Let `K` be a number field of degree `D = [K : ℚ]`.  A rational number is seen by every place of
`K`, and the two families behave very differently:

* at an **infinite** place the value is the ordinary absolute value, `v (q : K) = |q|`
  (`NumberField.InfinitePlace.apply_ratCast`, a restatement of Mathlib's
  `InfinitePlace.map_ratCast`);
* the **finite** places see only the primes dividing numerator and denominator, and their joint
  contribution is forced by the product formula:

  `∏ᶠ w : FinitePlace K, w (q : K) = (|q|^D)⁻¹`   (`NumberField.finprod_finitePlace_ratCast`).

The second statement is the useful one in Diophantine applications over a number field: it
evaluates the finite part of an `S`-unit *without any ramification theory* — no local degrees, no
`∑_{w ∣ v} e_w f_w = D`.  Everything that is needed about the individual places is that they are
bounded by `1` on the image of `ℤ` (`NumberField.FinitePlace.apply_intCast_le_one`), which also
identifies the finite places among all places: an infinite place takes the value `2` at `2`.

`NumberField.prod_finitePlace_ratCast` is the form consumed in practice: if a finite set `T` of
finite places carries the whole support (all other finite places being trivial on `q` — the
defining property of an `S`-unit), then `∏_{w ∈ T} w (q) = (|q|^D)⁻¹`.

## Contents

* `NumberField.InfinitePlace.apply_ratCast`
* `NumberField.FinitePlace.apply_intCast_le_one`, `NumberField.FinitePlace.apply_natCast_le_one`
* `NumberField.FinitePlace.apply_natCast_eq_one_of_mul_eq_one` — a divisor of a `w`-unit natural
  number is a `w`-unit
* `NumberField.FinitePlace.val_ne_infinitePlace_val` — finite and infinite places are distinct
* **`NumberField.finprod_finitePlace_ratCast`**, **`NumberField.prod_finitePlace_ratCast`**
* `NumberField.prod_finitePlace_intCast_le_one`

## References

* Mathlib, `Mathlib/NumberTheory/NumberField/ProductFormula.lean`
  (`NumberField.prod_abs_eq_one`).
* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, CUP 2006, §1.4–1.5.
-/

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Individual place values -/

omit [NumberField K] in
/-- The underlying absolute value of an infinite place applies as the place does — a `rfl`-lemma
that lets the `InfinitePlace.map_*` evaluations fire on terms phrased with `v.val`. -/
@[simp]
theorem InfinitePlace.val_apply (v : InfinitePlace K) (x : K) : v.val x = v x := rfl

/-- The underlying absolute value of a finite place applies as the place does. -/
@[simp]
theorem FinitePlace.val_apply (w : FinitePlace K) (x : K) : w.val x = w x := rfl

omit [NumberField K] in
/-- An infinite place of a number field takes the ordinary absolute value on rational numbers. -/
theorem InfinitePlace.apply_ratCast (v : InfinitePlace K) (q : ℚ) : v ((q : K)) = |(q : ℝ)| := by
  rw [InfinitePlace.map_ratCast, ← Rat.norm_cast_real]
  exact Real.norm_eq_abs _

namespace FinitePlace

/-- A finite place is bounded by `1` on the image of `ℤ`. -/
theorem apply_intCast_le_one (w : FinitePlace K) (n : ℤ) : w ((n : K)) ≤ 1 :=
  IsNonarchimedean.apply_intCast_le_one (FinitePlace.add_le w)

/-- A finite place is bounded by `1` on the image of `ℕ`. -/
theorem apply_natCast_le_one (w : FinitePlace K) (n : ℕ) : w ((n : K)) ≤ 1 :=
  IsNonarchimedean.apply_natCast_le_one (FinitePlace.add_le w)

/-- If a finite place is trivial on a product of natural numbers, it is trivial on each factor:
both values are at most `1` and they multiply to `1`. -/
theorem apply_natCast_eq_one_of_mul_eq_one (w : FinitePlace K) {m n : ℕ}
    (h : w (((m * n : ℕ) : K)) = 1) : w ((m : K)) = 1 := by
  have hm : w ((m : K)) ≤ 1 := apply_natCast_le_one w m
  have hn : w ((n : K)) ≤ 1 := apply_natCast_le_one w n
  have hmul : w ((m : K)) * w ((n : K)) = 1 := by
    rw [← map_mul]
    push_cast at h ⊢
    exact h
  by_contra hne
  have hm' : w ((m : K)) < 1 := lt_of_le_of_ne hm hne
  have hlt : w ((m : K)) * w ((n : K)) < 1 :=
    calc w ((m : K)) * w ((n : K)) ≤ w ((m : K)) * 1 :=
          mul_le_mul_of_nonneg_left hn (apply_nonneg _ _)
      _ = w ((m : K)) := mul_one _
      _ < 1 := hm'
  linarith

/-- Finite and infinite places are distinct absolute values: an infinite place takes the value
`2` at `2`, a finite place at most `1`. -/
theorem val_ne_infinitePlace_val (w : FinitePlace K) (v : InfinitePlace K) : w.val ≠ v.val := by
  intro h
  have h2 : v.val (((2 : ℕ) : K)) = 2 := InfinitePlace.map_natCast v 2
  have h2' : w.val (((2 : ℕ) : K)) ≤ 1 := apply_natCast_le_one w 2
  rw [h, h2] at h2'
  norm_num at h2'

end FinitePlace

/-! ### The finite part of a rational number -/

/-- **The finite part of a rational number over a number field**: for `q ≠ 0` the product of the
values of *all* finite places of `K` at `q` is `(|q|^{[K:ℚ]})⁻¹`.  Immediate from the product
formula, since the infinite places contribute `|q|` each, with multiplicity, and the
multiplicities add up to the degree (`NumberField.InfinitePlace.sum_mult_eq`). -/
theorem finprod_finitePlace_ratCast {q : ℚ} (hq : q ≠ 0) :
    (∏ᶠ w : FinitePlace K, w ((q : K))) = (|(q : ℝ)| ^ Module.finrank ℚ K)⁻¹ := by
  have hx : ((q : K)) ≠ 0 := by exact_mod_cast hq
  have hpf := NumberField.prod_abs_eq_one (K := K) hx
  have harch : (∏ v : InfinitePlace K, v ((q : K)) ^ v.mult)
      = |(q : ℝ)| ^ Module.finrank ℚ K := by
    simp_rw [InfinitePlace.apply_ratCast]
    rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  rw [harch] at hpf
  have hq0 : |(q : ℝ)| ^ Module.finrank ℚ K ≠ 0 := by
    have : (0 : ℝ) < |(q : ℝ)| := abs_pos.mpr (by exact_mod_cast hq)
    positivity
  field_simp at hpf ⊢
  linarith [hpf]

/-- **The finite part of an `S`-unit**: if the finite places outside a finite set `T` are trivial
at `q ≠ 0`, then `∏_{w ∈ T} w (q) = (|q|^{[K:ℚ]})⁻¹`.  This computes the finite contribution of a
rational `S`-unit with no ramification data at all. -/
theorem prod_finitePlace_ratCast {q : ℚ} (hq : q ≠ 0) (T : Finset (FinitePlace K))
    (hT : ∀ w : FinitePlace K, w ∉ T → w ((q : K)) = 1) :
    (∏ w ∈ T, w ((q : K))) = (|(q : ℝ)| ^ Module.finrank ℚ K)⁻¹ := by
  rw [← finprod_finitePlace_ratCast (K := K) hq]
  refine (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
  intro w hw
  by_contra hwT
  exact hw (hT w (by simpa using hwT))

/-- The finite places contract integers: any finite product of their values at an integer is at
most `1`. -/
theorem prod_finitePlace_intCast_le_one (n : ℤ) (T : Finset (FinitePlace K)) :
    (∏ w ∈ T, w ((n : K))) ≤ 1 :=
  Finset.prod_le_one (fun _ _ ↦ apply_nonneg _ _)
    (fun w _ ↦ FinitePlace.apply_intCast_le_one w n)

end NumberField
