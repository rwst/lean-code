/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.SubspaceInstantiation
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Dual.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The place-`2` product of the `Φ`-side Subspace points (Route (i), the Missing Lemma)

This file **computes the place-`2` factor** of the Subspace product
(`AB.subspace_theorem_E`'s `∏_{v∈S} ∏_i |Lᵢ,ᵥ(x)|ᵥ/|x|ᵥ`) for the `Φ`-side points
([[b3-automatic-cc-corpus-root]], `B3.SubspaceConfinement`). It is the concrete `2`-adic half of the
over-approximation input `hover` (`B3.subspace_contradiction_of_rate`): the place-`2` factor of the
approximant point is exactly `‖n − Φ(αₖ)‖₂`, the `2`-adic distance the construction
(`B3.conditionStar_tooWellApproximated`) drives below `2^{−Nₖ}`.

## The points and forms

For the `Φ`-image value `n = Φ v` (assumed an integer, for contradiction), the `n`-th approximant has
`Φ(αₖ) = −Pₖ/Dₖ` with `Dₖ = subspaceDen cₖ pₖ = 3^{cₖ} − 2^{pₖ}` (`B3.subspaceDen`, an **odd**
integer — a `2`-adic unit, `B3.subspaceDen_odd`). The Subspace point and the place-`2` forms are

> `placePoint Dₖ Pₖ = ![Dₖ, −1, Pₖ]`,  `placeForms n = ![x, y, n·x + z]`

(over `K = ℚ`; the third form `n·x + z` is the Adamczewski–Bugeaud form, here in its base-`3` shape since
the denominator `Dₖ` is itself a coordinate, so no `α(x+y)` combination is needed). They have rank `3`
(`placeForms_linearIndependent`).

## The computation

`placeFactor_eq`: for **any** absolute value `v` with `v Dₖ = 1` and `v Pₖ ≤ 1`, the place-`v` factor

> `∏ᵢ v(Lᵢ(xₖ)) / (⨆ⱼ v(xₖⱼ)) = v(n·Dₖ + Pₖ)`

— the unit coordinates (`v Dₖ = 1`, `v(−1) = 1`) make `|xₖ|_v = 1` and collapse `L₁, L₂`, leaving the
third form. `placeFactor_eq_sub`: writing `Φ(αₖ) = q` with `Dₖ·q = −Pₖ`, the identity
`n·Dₖ + Pₖ = Dₖ·(n − q)` and `v Dₖ = 1` give

> `place-`v` factor = v(n − q) = v(n − Φ(αₖ))`.

For the **actual** `2`-adic place `v = Rat.AbsoluteValue.padic 2` (`padic_eq_padicNorm`), the unit
hypothesis `v Dₖ = 1` is *proved* from oddness (`padicTwo_odd_eq_one`, via `padicNorm.int_eq_one_iff`),
and `v Pₖ ≤ 1` from `padic_le_one`. So `placeFactor_subspaceDen_eq_sub`: the place-`2` factor of the
explicit point `placePoint Dₖ Pₖ` is `‖n − Φ(αₖ)‖₂` — exactly the construction's over-approximation
quantity.

## What is proved here, and what remains

* **Proved.** The full place-`2` factor `= ‖n − Φ(αₖ)‖₂` (the unit cancellation + the
  `n·D + P = D·(n − q)` identity + the `2`-adic-unit-from-odd arithmetic), computed against the *real*
  `Rat.AbsoluteValue.padic 2`; **and the transport** `padicTwo_sub_ratInt_le`/`placeFactor_subspaceDen_le`
  turning the construction's `ℤ_[2]` bound `‖(n : ℤ_[2]) − Φ(αₖ)‖ ≤ 2^{−Nₖ}` into the place-`2` factor
  bound `≤ 2^{−Nₖ}` (via the bridge `padicTwo_eq_norm` and the `ℤ_[2] ↪ ℚ_[2]` isometry). So the place-`2`
  factor `≤ 2^{−Nₖ}` is fully proved, modulo only threading the explicit `RatInt` witness `(x, q, P)` from
  the construction.
* **Deferred (documented bridges, not new mathematics).** (i) that `Rat.AbsoluteValue.padic 2` is the
  `nonarchAbsVal` representative of `subspace_theorem_E`'s place set (Mathlib `IsFinitePlace` plumbing);
  (ii) extracting the explicit numerator/value `(x = Φ(αₖ), q, Pₖ)` with `Dₖ·q = −Pₖ` from
  `Φ_blockValue_mem_ratInt` (the `RatInt` witness `placeFactor_subspaceDen_le` consumes — modulo the
  prefix-induced denominator factor); (iii) the `O(1)` `∞`-place factor. None is new research content; the
  genuinely open input remains non-confinement (`B3.SubspaceConfinement`).

No new `axiom`s.

## Contents
* `placeForms`, `placePoint` — the place-`2` forms `![x, y, n·x + z]` and points `![D, −1, P]`.
* `placeForms_linearIndependent` — the forms have rank `3`.
* `placeFactor_eq`, `placeFactor_eq_sub` — the place-`v` factor `= v(n·D + P) = v(n − q)`.
* `padicTwo_intCast_le_one`, `padicTwo_odd_eq_one`, `padicTwo_subspaceDen_eq_one` — the `2`-adic
  arithmetic (integers have norm `≤ 1`; odd integers, in particular `subspaceDen`, are units).
* `placeFactor_subspaceDen_eq_sub` — (capstone) the place-`2` factor of the `Φ`-side point is
  `‖n − Φ(αₖ)‖₂`.
* `padicTwo_eq_norm`, `padicTwo_sub_ratInt_le` — the place ↔ `ℚ_[2]`-norm bridge and the transport of the
  construction's `ℤ_[2]` over-approximation bound.
* `placeFactor_le_of_ratInt`, `placeFactor_subspaceDen_le` — the place-`2` factor `≤ 2^{−Nₖ}` (the proved
  `2`-adic half of the `subspace_contradiction_of_rate` over-approximation input).

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6: the forms `Lᵢ,ₚ` and the place-`p` over-approximation).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the `Φ`-image `(1.6)` giving the base-`3` denominators `Dₖ = 3^{cₖ} − 2^{pₖ}`).
-/

namespace B3

open Function

/-! ### The place-`2` forms and points -/

/-- The **place-`2` forms** `![x, y, n·x + z]` (functionals `Module.Dual ℚ (Fin 3 → ℚ)`): the two
coordinate forms and the Adamczewski–Bugeaud form `L₃ = n·x + z` with the assumed integer value
`n = Φ v` as coefficient. (Base-`3` shape: the denominator `Dₖ` is the first coordinate, so `L₃` needs
only `n·x + z`, not `n·(x+y) + z`.) -/
noncomputable def placeForms (n : ℤ) : Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) :=
  ![LinearMap.proj 0, LinearMap.proj 1, (n : ℚ) • LinearMap.proj 0 + LinearMap.proj 2]

/-- The **Subspace point** `![D, −1, P]` of the approximant with denominator `D = Dₖ` and numerator
`P = Pₖ` (`Φ(αₖ) = −P/D`). The middle coordinate `−1` keeps the point a `2`-adic unit in that slot (so
`|xₖ|₂ = 1`) and in general position. -/
def placePoint (D P : ℚ) : Fin 3 → ℚ := ![D, -1, P]

/-- **The forms have rank `3` (proved).** `placeForms n` is `ℚ`-linearly independent for every integer
`n` — the rank hypothesis `subspace_theorem_E` needs at the place `2`. (Coefficient matrix
`[[1,0,0],[0,1,0],[n,0,1]]`, determinant `1`.) -/
@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem placeForms_linearIndependent (n : ℤ) : LinearIndependent ℚ (placeForms n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun (congrArg DFunLike.coe hg) (Pi.single 0 1)
  have h1 := congrFun (congrArg DFunLike.coe hg) (Pi.single 1 1)
  have h2 := congrFun (congrArg DFunLike.coe hg) (Pi.single 2 1)
  simp only [placeForms, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.zero_apply, Pi.single_eq_same, smul_eq_mul] at h0 h1 h2
  intro i
  fin_cases i <;> simp_all

/-! ### The place-`v` factor -/

/-- **The place-`v` factor (proved, any absolute value).** If `v D = 1` (the denominator is a `v`-unit)
and `v P ≤ 1` (the numerator is a `v`-integer), the place-`v` factor of the Subspace product at the point
`placePoint D P` and forms `placeForms n` is

> `∏ᵢ v(Lᵢ(xₖ)) / (⨆ⱼ v(xₖⱼ)) = v(n·D + P)`.

*Proof:* the supremum `⨆ⱼ v(xₖⱼ) = max(v D, v(−1), v P) = 1` (all `≤ 1`, and `v D = 1`); the product over
`i` then collapses via `v(L₁) = v D = 1`, `v(L₂) = v(−1) = 1`, `v(L₃) = v(n·D + P)`. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_eq (v : AbsoluteValue ℚ ℝ) (n : ℤ) (D P : ℚ) (hD : v D = 1) (hPle : v P ≤ 1) :
    (∏ i : Fin 3, v (placeForms n i (placePoint D P)) / (⨆ j, v (placePoint D P j)))
      = v ((n : ℚ) * D + P) := by
  have hneg1 : v (-1 : ℚ) = 1 := by rw [AbsoluteValue.map_neg, map_one]
  have hbound : ∀ j, v (placePoint D P j) ≤ 1 := by
    intro j
    fin_cases j
    · show v D ≤ 1; rw [hD]
    · show v (-1 : ℚ) ≤ 1; rw [hneg1]
    · show v P ≤ 1; exact hPle
  have hsup : (⨆ j, v (placePoint D P j)) = 1 := by
    apply le_antisymm (ciSup_le hbound)
    exact le_ciSup_of_le (Set.finite_range _).bddAbove 0 (le_of_eq hD.symm)
  rw [hsup]
  have e0 : placeForms n 0 (placePoint D P) = D := by simp [placeForms, placePoint]
  have e1 : placeForms n 1 (placePoint D P) = -1 := by simp [placeForms, placePoint]
  have e2 : placeForms n 2 (placePoint D P) = (n : ℚ) * D + P := by
    simp [placeForms, placePoint, smul_eq_mul]
  simp only [div_one, Fin.prod_univ_three, e0, e1, e2, hD, hneg1]
  ring

/-- **The place-`v` factor as the approximation error (proved).** Writing the approximant `Φ(αₖ) = q`
with `D·q = −P`, the place-`v` factor equals `v(n − q) = v(n − Φ(αₖ))`. *Proof:* `placeFactor_eq` plus the
identity `n·D + P = D·(n − q)` and `v D = 1` (so `v(D·(n−q)) = v(n−q)`). -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_eq_sub (v : AbsoluteValue ℚ ℝ) (n : ℤ) (D P q : ℚ)
    (hq : D * q = -P) (hD : v D = 1) (hPle : v P ≤ 1) :
    (∏ i : Fin 3, v (placeForms n i (placePoint D P)) / (⨆ j, v (placePoint D P j)))
      = v ((n : ℚ) - q) := by
  rw [placeFactor_eq v n D P hD hPle]
  have hid : (n : ℚ) * D + P = D * ((n : ℚ) - q) := by rw [mul_sub, hq]; ring
  rw [hid, map_mul, hD, one_mul]

/-! ### The `2`-adic arithmetic -/

/-- **Integers are `2`-adic integers.** `‖z‖₂ = Rat.AbsoluteValue.padic 2 (z : ℚ) ≤ 1` for every integer
`z` (`Rat.AbsoluteValue.padic_le_one`) — the hypothesis `v P ≤ 1` of `placeFactor_eq`. -/
@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem padicTwo_intCast_le_one (z : ℤ) : Rat.AbsoluteValue.padic 2 ((z : ℤ) : ℚ) ≤ 1 :=
  Rat.AbsoluteValue.padic_le_one 2 z

/-- **Odd integers are `2`-adic units.** `‖m‖₂ = Rat.AbsoluteValue.padic 2 (m : ℚ) = 1` for every **odd**
integer `m` (`padicNorm.int_eq_one_iff`: `‖m‖₂ = 1 ↔ 2 ∤ m`) — the hypothesis `v D = 1` of
`placeFactor_eq`. -/
@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem padicTwo_odd_eq_one (m : ℤ) (hodd : Odd m) : Rat.AbsoluteValue.padic 2 ((m : ℤ) : ℚ) = 1 := by
  have h2 : ¬ (2 : ℤ) ∣ m := Int.two_dvd_ne_zero.mpr (Int.odd_iff.mp hodd)
  have hpn : padicNorm 2 (m : ℚ) = 1 := (padicNorm.int_eq_one_iff (p := 2) m).mpr h2
  rw [Rat.AbsoluteValue.padic_eq_padicNorm, hpn, Rat.cast_one]

/-- **The base-`3` denominator is a `2`-adic unit.** `‖subspaceDen c p‖₂ = 1`: `Dₖ = 3^c − 2^p` is odd
(`subspaceDen_odd`, `p > 0`), hence a `2`-adic unit. This *proves* the `v D = 1` hypothesis of
`placeFactor_eq_sub` for the actual `Φ`-side denominator. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem padicTwo_subspaceDen_eq_one (c p : ℕ) (hp : 0 < p) :
    Rat.AbsoluteValue.padic 2 ((subspaceDen c p : ℤ) : ℚ) = 1 :=
  padicTwo_odd_eq_one (subspaceDen c p) (subspaceDen_odd c p hp)

/-! ### The capstone: the place-`2` factor of the `Φ`-side point -/

/-- **The place-`2` product of the `Φ`-side point (proved).** For the actual `2`-adic place
`Rat.AbsoluteValue.padic 2`, the explicit base-`3` point `placePoint (subspaceDen c p) P`, and the
approximant `Φ(αₖ) = q` (`Dₖ·q = −Pₖ`), the place-`2` factor of the Subspace product is

> `‖n − Φ(αₖ)‖₂`.

*Proof:* `placeFactor_eq_sub` at `v = Rat.AbsoluteValue.padic 2`, with `v Dₖ = 1`
(`padicTwo_subspaceDen_eq_one`, `Dₖ` odd) and `v Pₖ ≤ 1` (`padicTwo_intCast_le_one`).

This is the `2`-adic half of `B3.subspace_contradiction_of_rate`'s over-approximation input: the place-`2`
factor *is* the construction's distance `‖n − Φ(αₖ)‖₂`, which `B3.conditionStar_tooWellApproximated`
drives `≤ 2^{−Nₖ}`. (Transporting that `ℤ_[2]` bound to this place, and the `∞`-place `O(1)` factor, are
the remaining documented bookkeeping; the genuinely open input is non-confinement.) -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_subspaceDen_eq_sub (n : ℤ) (c p : ℕ) (hp : 0 < p) (P : ℤ) (q : ℚ)
    (hq : ((subspaceDen c p : ℤ) : ℚ) * q = -(P : ℚ)) :
    (∏ i : Fin 3, Rat.AbsoluteValue.padic 2
        (placeForms n i (placePoint ((subspaceDen c p : ℤ) : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint ((subspaceDen c p : ℤ) : ℚ) (P : ℚ) j)))
      = Rat.AbsoluteValue.padic 2 ((n : ℚ) - q) :=
  placeFactor_eq_sub (Rat.AbsoluteValue.padic 2) n _ (P : ℚ) q hq
    (padicTwo_subspaceDen_eq_one c p hp) (padicTwo_intCast_le_one P)

/-! ### The transport to the construction's `2`-adic bound -/

/-- **The place ↔ `ℚ_[2]`-norm bridge (proved).** `Rat.AbsoluteValue.padic 2 r = ‖(r : ℚ_[2])‖`: the
`2`-adic place of `ℚ` is the restriction of the `ℚ_[2]`-norm (`padic_eq_padicNorm`, `Padic.eq_padicNorm`).
This lets the construction's `ℚ_[2]`/`ℤ_[2]` over-approximation bound be read as a bound on the place-`2`
factor. -/
@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem padicTwo_eq_norm (r : ℚ) : Rat.AbsoluteValue.padic 2 r = ‖(r : ℚ_[2])‖ := by
  rw [Rat.AbsoluteValue.padic_eq_padicNorm, Padic.eq_padicNorm]

/-- **The over-approximation transport (proved).** If `x : ℤ_[2]` has rational value `q`
(`(x : ℚ_[2]) = (q : ℚ_[2])` — the `RatInt` witness of `Φ(αₖ) = q`) and `‖(n : ℤ_[2]) − x‖ ≤ r` (the
construction's `2`-adic bound, `B3.conditionStar_tooWellApproximated`), then `‖n − q‖₂ ≤ r`. *Proof:* the
bridge `padicTwo_eq_norm`, the cast identity `((n : ℚ) − q : ℚ_[2]) = ((n : ℤ_[2]) − x : ℤ_[2])`, and the
isometry `ℤ_[2] ↪ ℚ_[2]` (`PadicInt.padic_norm_e_of_padicInt`). -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem padicTwo_sub_ratInt_le (n : ℤ) {x : ℤ_[2]} (q : ℚ) (hq : (x : ℚ_[2]) = (q : ℚ_[2]))
    (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    Rat.AbsoluteValue.padic 2 ((n : ℚ) - q) ≤ r := by
  have key : (((n : ℚ) - q : ℚ) : ℚ_[2]) = (((n : ℤ_[2]) - x : ℤ_[2]) : ℚ_[2]) := by
    push_cast; rw [← hq]
  rw [padicTwo_eq_norm, key, PadicInt.padic_norm_e_of_padicInt]
  exact hbound

/-- **The place-`2` factor is at most the over-approximation rate (proved).** Combining the factor
computation with the transport: for a point `placePoint D P` whose approximant `q` (`D·q = −P`) is the
rational value of `x : ℤ_[2]` (`hx`), with `D` a `2`-adic unit (`hD`) and `P` a `2`-adic integer (`hPle`),
if `‖(n : ℤ_[2]) − x‖ ≤ r` then the place-`2` factor of the Subspace product is `≤ r`. With
`r = 2^{−Nₖ}`, `x = Φ(αₖ)`, this is the proved `2`-adic half of `B3.subspace_contradiction_of_rate`'s
over-approximation input `hover`. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_le_of_ratInt (n : ℤ) (D P q : ℚ) {x : ℤ_[2]} (hDq : D * q = -P)
    (hD : Rat.AbsoluteValue.padic 2 D = 1) (hPle : Rat.AbsoluteValue.padic 2 P ≤ 1)
    (hx : (x : ℚ_[2]) = (q : ℚ_[2])) (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    (∏ i : Fin 3, Rat.AbsoluteValue.padic 2 (placeForms n i (placePoint D P)) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint D P j))) ≤ r := by
  rw [placeFactor_eq_sub (Rat.AbsoluteValue.padic 2) n D P q hDq hD hPle]
  exact padicTwo_sub_ratInt_le n q hx r hbound

/-- **The place-`2` factor bound for the `Φ`-side point (proved).** The `subspaceDen` specialisation of
`placeFactor_le_of_ratInt`: for the explicit base-`3` point `placePoint (subspaceDen c p) P` with
approximant `q` (`Dₖ·q = −Pₖ`, the rational value of `x = Φ(αₖ)`), if `‖(n : ℤ_[2]) − x‖ ≤ r` then the
place-`2` factor is `≤ r`. The unit hypothesis `‖Dₖ‖₂ = 1` is discharged from oddness
(`padicTwo_subspaceDen_eq_one`). This is the fully assembled `2`-adic factor bound the Subspace argument
consumes — only the construction's `RatInt` witness `(x, q, P)` and bound `r = 2^{−Nₖ}` remain to be
threaded from `B3.conditionStar_tooWellApproximated`. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem placeFactor_subspaceDen_le (n : ℤ) (c p : ℕ) (hp : 0 < p) (P : ℤ) (q : ℚ) {x : ℤ_[2]}
    (hDq : ((subspaceDen c p : ℤ) : ℚ) * q = -(P : ℚ)) (hx : (x : ℚ_[2]) = (q : ℚ_[2]))
    (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    (∏ i : Fin 3, Rat.AbsoluteValue.padic 2
        (placeForms n i (placePoint ((subspaceDen c p : ℤ) : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint ((subspaceDen c p : ℤ) : ℚ) (P : ℚ) j))) ≤ r :=
  placeFactor_le_of_ratInt n _ (P : ℚ) q hDq (padicTwo_subspaceDen_eq_one c p hp)
    (padicTwo_intCast_le_one P) hx r hbound

end B3
