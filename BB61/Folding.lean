/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.ProductFormula
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M5 Theorem 7: what folding at a quadratic unit of norm one buys

Formal companion of `note-1061-M5.html` (milestone M5 of `plans/plan-1061.html`) §6.

> **Theorem 7 (folding).**  Let `α > 2` be a quadratic unit with `N(α) = +1`, i.e. `α² = aα - 1`
> and `α₂ = 1/α`.  Then `c_m = -(α-1)α^{-m-1}` for `m ≥ 0`, hence
> `K = -C(α)`,  `X(α) = (C(α) + C(α)) mod 1`,  `G_p(h) = (∏_{j≥1} φ_p(h(α-1)α^{-j}))²`
> for every `h` and every `p`.  If instead `N(α) = -1` then `c_m = (-1)^{m+1}(α+1)α^{-m-1}`.

`BB61/Bernoulli.lean` proves the ladder identity itself (`past_eq_future`), and
`BB61/WeylProduct.lean` draws the `p = 1/2` conclusion for the *modulus*
(`pastProd_eq_futProd`, `weylProd_eq_sq`).  This file draws the other three, which the note
states and nothing so far did:

* **the two sets.**  `wVal_eq_neg_piVal` is the pointwise form — the window value of a word is
  *minus* its Cantor value, so `windowSet_eq_neg` gives `K = -C(α)` and `fRaw_eq_add` turns the
  factor map into a plain sum, `F̃(ω) = π(ω⁺) + π(ω⁻)`.  Feeding that through M1 Prop. 4
  (`confSet_eq`, whose surjectivity half is `joinW`) gives `confSet_eq_add`,
  `X(α) = (C(α) + C(α)) mod 1`;
* **the Fourier coefficient at every `p`.**  `pastProdC_eq_futProdC` and `weylC_eq_sq` are the
  complex statements, i.e. the ones about `G_p(h)` itself rather than about `|G_{1/2}(h)|`.  By
  `BB61/ProductFormula.lean`'s `integral_fourier_map_fMap` this says the `h`-th Fourier
  coefficient of `F_*μ_p` is a perfect square at **every** `p ∈ [0,1]` and every `h`;
* **the other sign.**  `cCoef_eq_of_norm_neg_one`: at `N(α) = -1` the past ladder is the same
  geometric sequence with `(α+1)` in place of `(α-1)` and an alternating sign, so the two
  numerators differ and the products are equal only in the ladder limit — which is
  `BB61/Plateau.lean`'s business, and the reason M1 F9's "quadratic unit" was too weak a
  hypothesis.

What is **not** here is the measure form `F_*μ_p = μ_C^{(p)} * μ_C^{(p)}`.  It needs the
product measure on `{0,1}^ℤ` to be split as (futures) ⊗ (pasts), and `BB61/LimitLaw.lean`
deliberately never takes it apart — its whole design is to do the future/past split on the
*analytic* side.  The pointwise identity `fRaw_eq_add` is the part of that statement which is
about the coding rather than about the measure.
-/

namespace BB61

open Pointwise

namespace QuadSetup

variable (P : QuadSetup)

/-! ## Norm `+1`: the window is minus the Cantor set -/

/-- The past ladder in its `α`-form: `c_m = -(α-1)/α^{m+1}` at a unit of norm `+1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cCoef_eq_neg_future (hb : P.b = -1) (m : ℕ) :
    P.cCoef m = -((P.α - 1) / P.α ^ (m + 1)) := by
  rw [cCoef]; exact P.past_eq_future hb m

/-- **The pointwise form of `K = -C(α)`.**  At a unit of norm `+1` the window value of a digit
word is minus its Cantor value: the same series, read with the opposite sign. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wVal_eq_neg_piVal (hb : P.b = -1) (δ : ℕ → Bool) :
    P.wVal δ = -piVal P.α δ := by
  have hα0 : (0 : ℝ) < P.α := P.alpha_pos
  have hterm : ∀ m : ℕ, P.cCoef m * dR δ m
      = -((P.α - 1) * (dR δ m * (P.α⁻¹) ^ (m + 1))) := by
    intro m
    rw [P.cCoef_eq_neg_future hb, div_eq_mul_inv, ← inv_pow]
    ring
  calc P.wVal δ = ∑' m : ℕ, -((P.α - 1) * (dR δ m * (P.α⁻¹) ^ (m + 1))) :=
        tsum_congr hterm
    _ = -∑' m : ℕ, ((P.α - 1) * (dR δ m * (P.α⁻¹) ^ (m + 1))) := tsum_neg
    _ = -((P.α - 1) * ∑' m : ℕ, dR δ m * (P.α⁻¹) ^ (m + 1)) := by rw [tsum_mul_left]
    _ = -piVal P.α δ := by rw [piVal]

/-- **M5 Thm 7, the window.**  `K = -C(α)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem windowSet_eq_neg (hb : P.b = -1) : P.windowSet = -cantorSet P.α := by
  ext x
  simp only [windowSet, cantorSet, Set.mem_range, Set.mem_neg]
  constructor
  · rintro ⟨δ, rfl⟩
    exact ⟨δ, by rw [P.wVal_eq_neg_piVal hb, neg_neg]⟩
  · rintro ⟨δ, hδ⟩
    exact ⟨δ, by rw [P.wVal_eq_neg_piVal hb, hδ, neg_neg]⟩

/-- **M5 Thm 7, the coding.**  At a unit of norm `+1` the factor map is a plain *sum* of two
independent Cantor values, `F̃(ω) = π(ω⁺) + π(ω⁻)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fRaw_eq_add (hb : P.b = -1) (ω : Shift) :
    P.fRaw ω = piVal P.α (futures ω) + piVal P.α (pasts ω) := by
  rw [fRaw, P.wVal_eq_neg_piVal hb]; ring

/-- **M5 Thm 7, the confinement set.**  `X(α) = (C(α) + C(α)) mod 1`, here before the
reduction: `range F̃ = C(α) + C(α)`.  The inclusion `⊆` is `fRaw_eq_add`; the converse is
M1 Prop. 4's `joinW`, the independence of the two halves of a two-sided word. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confSet_eq_add (hb : P.b = -1) :
    P.confSet = cantorSet P.α + cantorSet P.α := by
  ext x
  simp only [confSet, Set.mem_range, Set.mem_add, cantorSet]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨piVal P.α (futures ω), ⟨futures ω, rfl⟩, piVal P.α (pasts ω), ⟨pasts ω, rfl⟩,
      (P.fRaw_eq_add hb ω).symm⟩
  · rintro ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩
    exact ⟨joinW u v, by rw [P.fRaw_eq_add hb, futures_joinW, pasts_joinW]⟩

/-- The same on the circle: `X(α)` is the image of `C(α) + C(α)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_eq_image_add (hb : P.b = -1) :
    P.confCircle = (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' (cantorSet P.α + cantorSet P.α) := by
  rw [P.confCircle_eq_image, P.confSet_eq_add hb]

/-! ## Norm `+1`: the Fourier coefficient is a perfect square at every `p` -/

/-- **M5 Thm 7, the products, at every `p`.**  `BB61/WeylProduct.lean` has the `p = 1/2`
modulus (`pastProd_eq_futProd`); this is the statement about the coefficient itself. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pastProdC_eq_futProdC (hb : P.b = -1) (p h : ℝ) :
    P.pastProdC p h = P.futProdC p h := by
  simp only [pastProdC, futProdC]
  refine tprod_congr fun m => ?_
  congr 1
  rw [P.cCoef_eq_neg_future hb]
  ring

/-- **M5 Thm 7.**  `G_p(h)` is a perfect square, at every mode `h` and every `p ∈ [0,1]` —
with `integral_fourier_map_fMap` of `BB61/ProductFormula.lean`, every Fourier coefficient of
`F_*μ_p` is a square. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem weylC_eq_sq (hb : P.b = -1) (p h : ℝ) : P.weylC p h = (P.futProdC p h) ^ 2 := by
  rw [weylC, P.pastProdC_eq_futProdC hb, sq]

/-! ## Norm `-1`: the other branch -/

/-- At a quadratic unit of norm `-1` (`b = 1`, `α² = aα + 1`) the conjugate is `-1/α`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_eq_neg_inv (hb : P.b = 1) : P.β = -P.α⁻¹ := by
  have hα0 : (0 : ℝ) < P.α := P.alpha_pos
  have hprod : P.α * P.β = -1 := by
    have h := P.root
    rw [hb] at h
    unfold QuadSetup.β
    push_cast at h ⊢
    nlinarith [h]
  field_simp
  linarith [hprod]

/-- **M5 Thm 7, the other sign.**  At `N(α) = -1` the past ladder is the same geometric
sequence with `(α+1)` in place of `(α-1)`, alternating in sign:
`c_m = (-1)^{m+1}(α+1)/α^{m+1}`.  The two numerators differ, so — unlike at norm `+1` — the
future and past products are equal only in the ladder limit. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cCoef_eq_of_norm_neg_one (hb : P.b = 1) (m : ℕ) :
    P.cCoef m = (-1) ^ (m + 1) * ((P.α + 1) / P.α ^ (m + 1)) := by
  have hα0 : (0 : ℝ) < P.α := P.alpha_pos
  rw [cCoef, P.beta_eq_neg_inv hb, neg_pow, inv_pow, pow_succ]
  field_simp
  ring

end QuadSetup

end BB61
