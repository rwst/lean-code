/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.PlaceTwoProduct
import B3.BlockConstruction
import B3.RatIntBasic
import Mathlib.NumberTheory.Padics.WithVal
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Wiring the `RatInt` witness into the place-`2` over-approximation `hover` (Route (i))

This file threads the construction's `RatInt` data (`B3.conditionStar_tooWellApproximated`) into the
place-`2` factor bound (`B3.placeFactor_le_of_ratInt`), discharging the `RatInt`-witness extraction that
was the last *plumbing* gap of the `2`-adic half of `hover`
([[b3-automatic-cc-corpus-root]], `B3.subspace_contradiction_of_rate`).

## The key simplification

The earlier worry — that the explicit Subspace denominator `Dₖ` would be `subspaceDen cₖ pₖ` times a
prefix-induced power of `3` — **dissolves**: the place-`2` factor needs only that `Dₖ` is a `2`-adic
*unit* (odd), not its exact base-`3` form. And **every** `RatInt` element `x` (a rational `2`-adic integer)
has an odd-denominator representation: writing its rational value `q` in lowest terms `q = num/den`,
`q ∈ ℤ_[2]` forces `2 ∤ den` (`ratInt_odd_den`). So take `Dₖ = den` (odd), `Pₖ = −num`; then
`Dₖ·q = num = −Pₖ`, and `placeFactor_le_of_ratInt` applies — **no** explicit `subspaceDen` extraction, no
prefix denominator, needed.

## Contents
* `ratInt_odd_den` — (proved) a rational `2`-adic integer has odd denominator
  (`Padic.norm_rat_le_one_iff_padicValuation_le_one`, `Rat.padicValuation_le_one_iff`).
* `hover_place_two_of_ratInt` — (proved) for any `x ∈ RatInt` with `‖(n : ℤ_[2]) − x‖ ≤ r`, there are
  `D` (odd), `P` with the place-`2` factor of `placePoint D P` `≤ r`.
* `conditionStar_place_two_hover` — (capstone, proved) from `Φ v = n` and `ConditionStar`, a family of
  odd-denominator points whose place-`2` factors are `≤ 2^{−Nₖ}` with `Nₖ → ∞` — the fully assembled
  `2`-adic half of `hover` for the construction's approximant family.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (`RatInt = ℚ ∩ ℤ_[2]`, the rational `2`-adic integers).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6: the place-`p` over-approximation).
-/

namespace B3

open BL AB Function Filter

/-- **The place-`2` factor bound from a `RatInt` witness (proved).** For `x ∈ RatInt` (rational value `q`)
with the construction's `2`-adic bound `‖(n : ℤ_[2]) − x‖ ≤ r`, the odd-denominator Subspace point
`placePoint q.den (−q.num)` has place-`2` factor `≤ r`. *Proof:* `D = q.den` is odd (`ratInt_odd_den`,
hence a `2`-adic unit `padicTwo_odd_eq_one`), `P = −q.num` is an integer (`padicTwo_intCast_le_one`), and
`D·q = q.num = −P` (`Rat.mul_den_eq_num`); `placeFactor_le_of_ratInt` then transports the bound. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem hover_place_two_of_ratInt (n : ℤ) {x : ℤ_[2]} (hx : x ∈ RatInt)
    (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    ∃ D P : ℤ, Odd D ∧
      (∏ i : Fin 3, Rat.AbsoluteValue.padic 2 (placeForms n i (placePoint (D : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint (D : ℚ) (P : ℚ) j))) ≤ r := by
  obtain ⟨q, hq⟩ := hx
  have hDodd : Odd ((q.den : ℤ)) := ratInt_odd_den q hq
  have hDq : ((q.den : ℤ) : ℚ) * q = -((-q.num : ℤ) : ℚ) := by
    push_cast; rw [mul_comm, Rat.mul_den_eq_num]; ring
  refine ⟨(q.den : ℤ), -q.num, hDodd, ?_⟩
  exact placeFactor_le_of_ratInt n ((q.den : ℤ) : ℚ) ((-q.num : ℤ) : ℚ) q hDq
    (padicTwo_odd_eq_one (q.den : ℤ) hDodd) (padicTwo_intCast_le_one (-q.num)) hq r hbound

/-- **The place-`2` half of `hover`, fully assembled (capstone, proved).** From `Φ v = n` and the
stammering structure `ConditionStar w` (`w > 1`), there is a family of **odd-denominator** Subspace points
`placePoint (D m) (P m)` and window lengths `N m → ∞` such that the **place-`2` factor** of each is
`≤ 2^{−N m}`. *Proof:* `conditionStar_tooWellApproximated` gives approximants `α m` with
`Φ (α m) ∈ RatInt` and `‖n − Φ (α m)‖ ≤ 2^{−N m}`; `hover_place_two_of_ratInt` extracts the odd
denominator and transports the bound for each `m`.

This is the place-`2` input `hover` of `B3.subspace_contradiction_of_rate` (restricted to the place `2`),
now traced all the way back to the construction — the `RatInt`-witness extraction is complete. (The full
`hover` additionally needs the `O(1)` `∞`-place factor; the genuinely open input remains non-confinement,
`B3.phiPoints_nonConfined`.) -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem conditionStar_place_two_hover {v : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2]))
    {w : ℝ} (hw : 1 < w) (hCS : ConditionStar w (binaryDigit v)) :
    ∃ (D P : ℕ → ℤ) (N : ℕ → ℕ), Tendsto N atTop atTop ∧ (∀ m, Odd (D m)) ∧
      ∀ m, (∏ i : Fin 3, Rat.AbsoluteValue.padic 2
          (placeForms (n : ℤ) i (placePoint (D m : ℚ) (P m : ℚ))) /
          (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint (D m : ℚ) (P m : ℚ) j)))
        ≤ (2 : ℝ) ^ (-(N m : ℤ)) := by
  obtain ⟨α, N, hN, hRat, hbound, _⟩ := conditionStar_tooWellApproximated hv hw hCS
  have hext : ∀ m, ∃ D P : ℤ, Odd D ∧
      (∏ i : Fin 3, Rat.AbsoluteValue.padic 2 (placeForms (n : ℤ) i (placePoint (D : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (placePoint (D : ℚ) (P : ℚ) j))) ≤ (2 : ℝ) ^ (-(N m : ℤ)) := by
    intro m
    refine hover_place_two_of_ratInt (n : ℤ) (hRat m) _ ?_
    rw [Int.cast_natCast]
    exact hbound m
  choose D P hDodd hfac using hext
  exact ⟨D, P, N, hN, hDodd, hfac⟩

end B3
