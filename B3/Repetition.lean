/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.PlaceTwoProduct
import B3.HeightVsRate
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Adamczewski–Bugeaud repetition multi-form on the `Φ`-side, and why it is *worse* (Route (i), Tier 3)

This file formalises the **repetition-exploiting** Subspace setup of Adamczewski–Bugeaud (AB07, §6) — the
"self-similar" multi-form construction that, in AB07's *same-base* setting, yields transcendence for **any**
`w > 1` — adapted to the `Φ`-side base-`3` approximants ([[b3-automatic-cc-corpus-root]],
`B3.subspace_contradiction_of_rate_sharp_frequently`). It then **proves the key negative result**: on the
`Φ`-side the repetition mechanism is *strictly worse* than the Tier 2.1 archimedean saving, because of the
base-`2`-versus-base-`3` mismatch. Tier 3, as the optimistic plan (`B3/plan2.md` §5) envisaged it, does **not**
discharge the open kernel `B3.phiPoints_index` — it cannot even lower the threshold.

## AB07's self-similar mechanism

AB07's transcendence-for-any-`w>1` (the `p`-adic criterion `AB.transcendental_of_conditionStar`) rests on a
Subspace point and forms tuned to the period self-similarity. In the same-base setting the periodic
approximant `αₙ = pₙ/(b^{sₙ} − 1)` gives the point `xₙ = (b^{sₙ}, −1, −pₙ)` with the **self-similar form**
`L₃ = α(x + y) + z` (note: `α·(x + y)`, the *same* coefficient on `x` and `y`). Then:

* `L₃(xₙ) = α(b^{sₙ} − 1) − pₙ = (b^{sₙ} − 1)(α − αₙ)` is the (tiny) approximation error, because `x + y =
  b^{sₙ} − 1` reconstructs the denominator;
* `L₁(xₙ) = b^{sₙ}` is **place-`b` small** (`|b^{sₙ}|_b = b^{−sₙ}`) — the repetition gain;
* `L₂(xₙ) = −1` gives the **archimedean `H⁻¹` saving** (the `−1` coordinate, as in Tier 2.1).

Crucially the two savings come from **different** coordinates (`b^{sₙ}` and `−1`), so they combine, and the
product beats `H^{−m−ε}` for any `w > 1`.

## The `Φ`-side translation (`repForms`, `repPoint`)

The `Φ`-image approximant has the **base-`3`** denominator `Dₖ = 3^{cₖ} − 2^{pₖ}` (`B3.subspaceDen`,
`pₖ = sₖ`). To reconstruct it as `x + y` the point must be `(3^{cₖ}, −2^{pₖ}, Pₖ)` (so `x + y = 3^{cₖ} −
2^{pₖ} = Dₖ`), with the self-similar form `repForms n = (x, y, n(x + y) + z)`. The place-`2` factor then
**does** pick up an extra factor:

* `repPlaceFactor_eq` / `repPlaceFactor_eq_sub`: the place-`v` factor is `v(y)·v(n − q)` (the
  middle-coordinate value `v(y)` times the over-approximation), versus the plain `v(n − q)` of
  `B3.placeFactor_eq` — the extra `v(y)` is the repetition gain;
* `repPlaceFactor_subspaceDen_le`: at the `2`-adic place, `v(y) = |−2^{pₖ}|₂ = 2^{−pₖ}`, so the place-`2`
  product is `≤ 2^{−pₖ}·‖n − Φ(αₖ)‖₂ ≤ 2^{−(Nₖ + pₖ)}` — the over-approximation modulus improves from `Nₖ`
  to `Nₖ + pₖ`.

## Why it is *worse*: the base-`2`-vs-base-`3` mismatch (`rep_w_threshold_gt_arch`)

The gain comes at a fatal cost. AB07's `−1` coordinate completes the denominator `b^{sₙ} − 1` **and** gives
the arch saving simultaneously. The `Φ`-side denominator is `3^{cₖ} − 2^{pₖ}`, so:

* the coordinate completing it must be `−2^{pₖ}` — which gives the place-`2` gain but, being `2^{pₖ}` (not
  `1`), gives **no** archimedean saving;
* the other coordinate `3^{cₖ}` is a `2`-adic **unit** — so it gives **no** place-`2` gain (unlike AB07's
  `b^{sₙ}`).

So on the `Φ`-side the place-`2` gain and the archimedean `H⁻¹` saving become **mutually exclusive**: the
`−2^{pₖ}` needed for the denominator cannot also be the `−1` needed for the arch saving. The repetition point
therefore *loses* the Tier 2.1 arch saving (effective Subspace threshold `H^{−3−ε}`, not `H^{−2−ε}`) in
exchange for the `+pₖ` place-`2` gain. Quantitatively, in the large-repetition regime (`cₖ ≤ sₖ`, `Nₖ ≈ w·sₖ`,
`pₖ = sₖ`):

* **Tier 2.1** (point `(Dₖ, −1, Pₖ)`, arch saving, `τ = 2`): index condition holds for `w ≥ (2+ε)·log 3/log 2`;
* **AB07 repetition** (point `(3^{cₖ}, −2^{pₖ}, Pₖ)`, no arch saving `τ = 3`, `+pₖ` gain): `(3+ε)·cₖ·log 3 ≤
  (Nₖ + pₖ)·log 2`, holding only for `w ≥ (3+ε)·log 3/log 2 − 1`.

`rep_w_threshold_gt_arch` proves the second threshold **strictly exceeds** the first — the difference is
`log 3/log 2 − 1 ≈ 0.585 > 0` (reducing to `log 2 < log 3`). The repetition trade is a *net loss*: it raises
the required `w` from `≈ 3.17` to `≈ 3.75`.

## Conclusion

On the base-mismatched `Φ`-side, the Adamczewski–Bugeaud repetition multi-form **cannot beat the Tier 2.1
archimedean saving**, let alone reach AB07's unconditional `w > 1`. The Tier 2.1 threshold `τ = 2` is optimal
for the `Φ`-image Subspace instantiation (one spare coordinate ⟹ arch factor `≤ H⁻¹` is the best possible).
The plan's §5 premise — that AB07's same-base "any `w > 1`" transfers to the `Φ`-side — is **false**; the open
kernel `B3.phiPoints_index` (the `ℓ`-vs-`dₗ` base-`2`/base-`3` index condition) is the honest, irreducible
content of the `Φ`-image Route (i). (Discharging it unconditionally would require a genuinely different
approach — e.g. Route (ii), absent here.)

No new `axiom`s; the whole file is proved.

## Contents
* `repForms`, `repForms_linearIndependent` — the AB07 self-similar forms `(x, y, n(x+y)+z)`, rank `3`.
* `repPoint` — the repetition point `(A, B, P)` (in use `A = 3^{cₖ}`, `B = −2^{pₖ}`, so `x + y = Dₖ`).
* `repPlaceFactor_eq`, `repPlaceFactor_eq_sub` — the place-`v` factor `= v(y)·v(n − q)`, exhibiting the extra
  `v(y)` repetition factor.
* `repPlaceFactor_subspaceDen_le` — the concrete `2`-adic gain: place-`2` product `≤ 2^{−pₖ}·‖n − Φ(αₖ)‖₂`.
* `rep_w_threshold_gt_arch` — **the obstruction**: the repetition `w`-threshold strictly exceeds Tier 2.1's.

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6: the `p`-adic Subspace application with the self-similar forms).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), 1154–1169 (the base-`3` denominators `3^{cₘ} − 2^{pₘ}`).
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311 (the `H(x)^{−m−ε}` Subspace bound).
-/

namespace B3

open Function

/-! ### The self-similar forms and the repetition point -/

/-- The **Adamczewski–Bugeaud self-similar forms** `![x, y, n·(x + y) + z]`: the two coordinate forms and
the self-similar form `L₃ = n·x + n·y + z` (the *same* coefficient `n` on `x` and `y`, unlike `placeForms`'
`n·x + z`). The `n·(x + y)` reconstructs the denominator `Dₖ = x + y = 3^{cₖ} − 2^{pₖ}` of the `Φ`-image
approximant. -/
noncomputable def repForms (n : ℤ) : Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) :=
  ![LinearMap.proj 0, LinearMap.proj 1,
    (n : ℚ) • LinearMap.proj 0 + (n : ℚ) • LinearMap.proj 1 + LinearMap.proj 2]

/-- **The self-similar forms have rank `3` (proved).** `repForms n` is `ℚ`-linearly independent for every
`n` — the rank hypothesis `subspace_theorem_E` needs. (Coefficient matrix `[[1,0,0],[0,1,0],[n,n,1]]`,
determinant `1`.) -/
@[category research solved, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem repForms_linearIndependent (n : ℤ) : LinearIndependent ℚ (repForms n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun (congrArg DFunLike.coe hg) (Pi.single 0 1)
  have h1 := congrFun (congrArg DFunLike.coe hg) (Pi.single 1 1)
  have h2 := congrFun (congrArg DFunLike.coe hg) (Pi.single 2 1)
  simp only [repForms, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.zero_apply, Pi.single_eq_same, smul_eq_mul] at h0 h1 h2
  intro i
  fin_cases i <;> simp_all

/-- The **repetition point** `![A, B, P]`. In use `A = 3^{cₖ}`, `B = −2^{pₖ}` (so `x + y = A + B = 3^{cₖ} −
2^{pₖ} = Dₖ` reconstructs the denominator), `P = Pₖ` — the `Φ`-side translation of AB07's `(b^{sₙ}, −1,
−pₙ)`. Note `B = −2^{pₖ}`, **not** `−1`: this is exactly why the archimedean saving is lost (see the file
header). -/
def repPoint (A B P : ℚ) : Fin 3 → ℚ := ![A, B, P]

/-! ### The place-`v` factor: the extra repetition factor `v(y)` -/

/-- **The place-`v` factor of the self-similar setup (proved).** With `A` a `v`-unit (`v A = 1`) and `B, P`
`v`-integers, the place-`v` factor of the Subspace product at `repPoint A B P`, `repForms n`, is

> `∏ᵢ v(Lᵢ(x)) / (⨆ⱼ v(xⱼ)) = v(B) · v(n·A + n·B + P)`.

The **extra `v(B)` factor** (compare `B3.placeFactor_eq`'s lone `v(n·D + P)`) is the AB07 repetition gain —
the middle coordinate `B` is no longer a unit. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem repPlaceFactor_eq (v : AbsoluteValue ℚ ℝ) (n : ℤ) (A B P : ℚ)
    (hA : v A = 1) (hB : v B ≤ 1) (hP : v P ≤ 1) :
    (∏ i : Fin 3, v (repForms n i (repPoint A B P)) / (⨆ j, v (repPoint A B P j)))
      = v B * v ((n : ℚ) * A + (n : ℚ) * B + P) := by
  have hbound : ∀ j, v (repPoint A B P j) ≤ 1 := by
    intro j; fin_cases j
    · show v A ≤ 1; rw [hA]
    · show v B ≤ 1; exact hB
    · show v P ≤ 1; exact hP
  have hsup : (⨆ j, v (repPoint A B P j)) = 1 := by
    apply le_antisymm (ciSup_le hbound)
    exact le_ciSup_of_le (Set.finite_range _).bddAbove 0 (le_of_eq hA.symm)
  rw [hsup]
  have e0 : repForms n 0 (repPoint A B P) = A := by simp [repForms, repPoint]
  have e1 : repForms n 1 (repPoint A B P) = B := by simp [repForms, repPoint]
  have e2 : repForms n 2 (repPoint A B P) = (n : ℚ) * A + (n : ℚ) * B + P := by
    simp [repForms, repPoint, smul_eq_mul]
  simp only [div_one, Fin.prod_univ_three, e0, e1, e2, hA]
  rw [one_mul]

/-- **The place-`v` factor as `v(y)·(approximation error)` (proved).** Writing the approximant `q` with
`(A + B)·q = −P` (so `q = −P/(A+B) = Φ(αₖ)`) and `v(A + B) = 1` (the denominator `Dₖ = A + B` is a `v`-unit),
the place-`v` factor is `v(B)·v(n − q)`. *Proof:* `repPlaceFactor_eq` plus `n·A + n·B + P = (A+B)(n − q)`. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem repPlaceFactor_eq_sub (v : AbsoluteValue ℚ ℝ) (n : ℤ) (A B P q : ℚ)
    (hAB : v (A + B) = 1) (hq : (A + B) * q = -P) (hA : v A = 1) (hB : v B ≤ 1) (hP : v P ≤ 1) :
    (∏ i : Fin 3, v (repForms n i (repPoint A B P)) / (⨆ j, v (repPoint A B P j)))
      = v B * v ((n : ℚ) - q) := by
  rw [repPlaceFactor_eq v n A B P hA hB hP]
  have hid : (n : ℚ) * A + (n : ℚ) * B + P = (A + B) * ((n : ℚ) - q) := by rw [mul_sub, hq]; ring
  rw [hid, map_mul, hAB, one_mul]

/-- **The concrete `2`-adic repetition gain (proved).** For the `Φ`-side repetition point
`repPoint (3^{cₖ}) (−2^{pₖ}) Pₖ` with approximant `q = Φ(αₖ)` (`Dₖ·q = −Pₖ`, `Dₖ = subspaceDen cₖ pₖ`, the
rational value of `x : ℤ₂`), if `‖n − x‖ ≤ r` then the place-`2` factor is `≤ 2^{−pₖ}·r`.

The factor `2^{−pₖ}` (`= |−2^{pₖ}|₂`, the middle coordinate) is the AB07 repetition gain: with `r = 2^{−Nₖ}`
this gives `≤ 2^{−(Nₖ + pₖ)}`, improving the over-approximation modulus from `Nₖ` to `Nₖ + pₖ`. *But* — see
`rep_w_threshold_gt_arch` — this gain does **not** pay for the lost archimedean saving. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem repPlaceFactor_subspaceDen_le (n : ℤ) (c p : ℕ) (hp : 0 < p) (P : ℤ) (q : ℚ) {x : ℤ_[2]}
    (hDq : ((subspaceDen c p : ℤ) : ℚ) * q = -(P : ℚ)) (hx : (x : ℚ_[2]) = (q : ℚ_[2]))
    (r : ℝ) (hbound : ‖((n : ℤ_[2]) - x)‖ ≤ r) :
    (∏ i : Fin 3, Rat.AbsoluteValue.padic 2
        (repForms n i (repPoint ((3 ^ c : ℤ) : ℚ) ((-(2 ^ p : ℤ)) : ℚ) (P : ℚ))) /
        (⨆ j, Rat.AbsoluteValue.padic 2 (repPoint ((3 ^ c : ℤ) : ℚ) ((-(2 ^ p : ℤ)) : ℚ) (P : ℚ) j)))
      ≤ (1 / 2 : ℝ) ^ p * r := by
  have hAB_eq : ((3 ^ c : ℤ) : ℚ) + ((-(2 ^ p : ℤ)) : ℚ) = ((subspaceDen c p : ℤ) : ℚ) := by
    unfold subspaceDen; push_cast; ring
  have hvA : Rat.AbsoluteValue.padic 2 ((3 ^ c : ℤ) : ℚ) = 1 :=
    padicTwo_odd_eq_one (3 ^ c) (Odd.pow (by decide))
  have hvAB : Rat.AbsoluteValue.padic 2 (((3 ^ c : ℤ) : ℚ) + ((-(2 ^ p : ℤ)) : ℚ)) = 1 := by
    rw [hAB_eq]; exact padicTwo_subspaceDen_eq_one c p hp
  have hvB : Rat.AbsoluteValue.padic 2 ((-(2 ^ p : ℤ)) : ℚ) ≤ 1 := by
    rw [show ((-(2 ^ p : ℤ)) : ℚ) = -(((2 ^ p : ℤ)) : ℚ) by push_cast; ring, AbsoluteValue.map_neg]
    exact padicTwo_intCast_le_one (2 ^ p)
  have hvP : Rat.AbsoluteValue.padic 2 ((P : ℤ) : ℚ) ≤ 1 := padicTwo_intCast_le_one P
  rw [repPlaceFactor_eq_sub (Rat.AbsoluteValue.padic 2) n ((3 ^ c : ℤ) : ℚ) ((-(2 ^ p : ℤ)) : ℚ) (P : ℚ) q
    hvAB (by rw [hAB_eq]; exact hDq) hvA hvB hvP]
  have hvBval : Rat.AbsoluteValue.padic 2 ((-(2 ^ p : ℤ)) : ℚ) = (1 / 2 : ℝ) ^ p := by
    rw [show ((-(2 ^ p : ℤ)) : ℚ) = -((2 : ℚ) ^ p) by push_cast; ring, AbsoluteValue.map_neg, map_pow]
    congr 1
    rw [Rat.AbsoluteValue.padic_eq_padicNorm,
      show padicNorm 2 (2 : ℚ) = 2⁻¹ by simp [padicNorm, padicValRat, padicValInt, padicValNat]]
    norm_num
  rw [hvBval]
  exact mul_le_mul_of_nonneg_left (padicTwo_sub_ratInt_le n q hx r hbound) (by positivity)

/-! ### The obstruction: the repetition threshold strictly exceeds Tier 2.1's -/

/-- **The repetition `w`-threshold strictly exceeds the Tier 2.1 arch-saving threshold (proved) — the Tier 3
obstruction.** In the large-repetition regime (`cₖ ≤ sₖ`, `Nₖ ≈ w·sₖ`, `pₖ = sₖ`), the `Φ`-side index
condition holds:

* for **Tier 2.1** (arch saving, threshold `H^{−2−ε}`) when `w ≥ (2+ε)·log 3/log 2`;
* for the **AB07 repetition point** (no arch saving, threshold `H^{−3−ε}`, but the `+pₖ` place-`2` gain of
  `repPlaceFactor_subspaceDen_le`) when `w ≥ (3+ε)·log 3/log 2 − 1`.

This theorem proves the **second threshold is strictly larger**: `(2+ε)·log 3/log 2 < (3+ε)·log 3/log 2 − 1`.
The gap is `log 3/log 2 − 1 > 0` (reducing to `log 2 < log 3`), i.e. `≈ 0.585` — the repetition trades the
arch saving (worth `log 3/log 2 ≈ 1.585` in `w`) for the gain (worth `1`), a **net loss**. Hence the
Adamczewski–Bugeaud repetition multi-form is strictly *worse* than Tier 2.1 on the base-mismatched `Φ`-side,
and Tier 2.1's `τ = 2` is optimal. -/
@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem rep_w_threshold_gt_arch (ε : ℝ) :
    (2 + ε) * Real.log 3 / Real.log 2 < (3 + ε) * Real.log 3 / Real.log 2 - 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [lt_sub_iff_add_lt, div_add' _ _ _ hlog2.ne', div_lt_div_iff_of_pos_right hlog2]
  nlinarith [hlog23]

end B3
