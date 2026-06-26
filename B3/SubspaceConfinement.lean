/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.HeightVsRate
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.LinearAlgebra.Dual.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The structural Subspace-Theorem application: reduction to non-confinement (Route (i), the Missing Lemma)

This file performs the **structural application** of the multidimensional Subspace Theorem
(`AB.subspace_theorem_E`, Theorem E) to a point family, completing the skeleton of the `Φ`-side argument
([[b3-automatic-cc-corpus-root]], `B3.phi_value_transcendental`): it shows that an infinite family of
nonzero points all satisfying the Subspace inequality must **pile infinitely into one proper subspace**
(the pigeonhole), and so reduces the whole argument to a single **non-confinement** statement.

## The pigeonhole

`subspace_theorem_E` says the solutions of `∏_{v∈S} ∏_i |Lᵢ,ᵥ(x)|ᵥ/|x|ᵥ ≤ H(x)^{−m−ε}` lie in
**finitely many** proper subspaces `W`. If a *whole infinite family* `x : ℕ → Kᵐ` of nonzero points all
satisfy that inequality, then each `xₖ` lies in some `U ∈ W`; as `W` is finite and `ℕ` infinite,
**some** proper `U ∈ W` contains `xₖ` for **infinitely many** `k` (`Finite.exists_infinite_fiber`). That
is `Confinable x` (`subspace_pigeonhole`). So if the family is **not** confinable
(`¬ Confinable x` — no proper subspace catches an infinite subfamily), the Subspace inequality cannot hold
for all `xₖ`: contradiction (`subspace_reduction`).

## Feeding in the height-vs-rate estimate

The Subspace inequality input is exactly where the over-approximation enters: for the `Φ`-side points
`xₖ = (3^{cₖ} − 2^{pₖ}, −1, −Pₖ)` (`B3.subspaceDen`, forms `B3.subForms (Φ v)`), the place-`2`
over-approximation makes the product `≤ 2^{−Nₖ}`, and `B3.HeightVsRate` (`rate_le_..._rpow`, from
`IndexCondition`) gives `2^{−Nₖ} ≤ H(xₖ)^{−m−ε}` — so the product undercuts the height power.
`subspace_contradiction_of_rate` is the full composition: place-`2` over-approximation **+** the
height-vs-rate estimate **+** non-confinement ⟹ `False`. Hence (assuming `Φ v` algebraic, building this
family) `Φ v` is transcendental — the Missing Lemma.

## What is proved here, and what is open

* **Proved (the structural core).** `subspace_pigeonhole`: the pigeonhole, a genuine invocation of
  `subspace_theorem_E`. `subspace_reduction`, `subspace_contradiction_of_rate`: the reductions to
  non-confinement, composing the height-vs-rate estimate as the `H^{−m−ε}` bound.
* **Open / deferred (the two analytic inputs), kept as hypotheses, never axioms.**
  - the **place-`2` over-approximation** `hover` (the product `≤ 2^{−Nₖ}`) — the place-by-place
    computation of `|Lᵢ,ᵥ(xₖ)|ᵥ/|xₖ|ᵥ` for the concrete forms/points (`subspaceDen` is a `2`-adic unit,
    so the place-`2` factor is `‖n − Φ(αₖ)‖₂ ≤ 2^{−Nₖ}`; the `∞`-place factor is `O(1)`);
  - **non-confinement** `¬ Confinable x` — that the explicit points are *not* trapped in one proper
    subspace. This is the genuine residual research content (the base-`2`/base-`3` Diophantine
    independence: a fixed linear relation `a·(3^{cₖ} − 2^{pₖ}) − b − c·Pₖ = 0` cannot hold for infinitely
    many `k`), supplied as a hypothesis.

Together with `B3.HeightVsRate`'s `IndexCondition`, these are precisely the open frontiers of the
Missing Lemma. No new `axiom`s: this file rests only on the cited `subspace_theorem_E` (already upstream).

## Contents
* `Confinable` — `∃` proper subspace catching infinitely many points of the family.
* `subspace_pigeonhole` — (proved) Subspace inequality for all points ⟹ `Confinable` (uses
  `subspace_theorem_E` + `Finite.exists_infinite_fiber`).
* `subspace_reduction` — (proved) Subspace inequality + `¬ Confinable` ⟹ `False`.
* `subspace_contradiction_of_rate` — (proved) place-`2` over-approximation + height-vs-rate +
  `¬ Confinable` ⟹ `False`.
* `subspace_contradiction_of_rate_sharp` — (proved, Tier 2.1) the same with the **archimedean `H⁻¹`
  saving**: `hover` carries an explicit `H⁻¹` factor and `hrate` need only beat `H^{1−m−ε}` (one power of
  `H` less) — lowering the `Φ`-side threshold from `H^{−3−ε}` to `H^{−2−ε}`.
* `subspace_pigeonhole_infinite`, `subspace_contradiction_of_rate_sharp_frequently` — (proved, Tier 2.2)
  the `∃ᶠ` / infinite-index-set relaxation: the Subspace inequality / rate is required only for
  **infinitely many** `k` (a good *subsequence*), not all `k`.

## References
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311 (the Subspace Theorem applied; `AB.subspace_theorem_E`).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§6: the finite-subspaces pigeonhole and the contradiction from
  confinement — the template for this reduction).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the points `xₖ` from the `Φ`-image base-`3` series).
-/

namespace B3

open AB Function Height Height.AdmissibleAbsValues Filter

/-- **Confinability of a point family.** `Confinable x` means *some proper subspace* `U ≠ ⊤` of `ℚᵐ`
contains `xₖ` for **infinitely many** `k`. The Subspace Theorem forces `Confinable x` whenever every `xₖ`
satisfies the Subspace inequality (`subspace_pigeonhole`); so the `Φ`-side contradiction is exactly
`¬ Confinable x` (non-confinement of the explicit approximant points). -/
@[category API, AMS 11 37, ref "Eve96" "AB07"]
def Confinable {m : ℕ} (x : ℕ → (Fin m → ℚ)) : Prop :=
  ∃ U : Submodule ℚ (Fin m → ℚ), U ≠ ⊤ ∧ {k | x k ∈ U}.Infinite

/-- **The Subspace pigeonhole (proved) — the structural application of Theorem E.** Let `S` be a finite
set of places of `ℚ` containing the archimedean place (`hS_inf`, `hS_place`), `L` rank-`m` forms at each
`v ∈ S` (`hL`), and `0 < ε < 1`. If a family `x : ℕ → ℚᵐ` of **nonzero** points *all* satisfy the
Subspace inequality `∏_{v∈S} ∏_i |Lᵢ,ᵥ(xₖ)|ᵥ/|xₖ|ᵥ ≤ H(xₖ)^{−m−ε}` (`hineq`), then the family is
**confinable**: some proper subspace contains infinitely many `xₖ`.

*Proof:* `subspace_theorem_E` gives a finite set `W` of proper subspaces whose union contains every
solution; each `xₖ` lies in some `g k ∈ W`. The assignment `k ↦ g k ∈ W` maps the infinite `ℕ` into the
finite `W`, so some `U ∈ W` is the image of infinitely many `k` (`Finite.exists_infinite_fiber`); for
those `k`, `xₖ ∈ U`, and `U ≠ ⊤`. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem subspace_pigeonhole {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_inf : ∀ v ∈ archAbsVal (K := ℚ), v ∈ S)
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0)
    (hineq : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      Height.mulHeight (x k) ^ (-(m : ℝ) - ε)) :
    Confinable x := by
  obtain ⟨W, hWtop, hWcov⟩ := subspace_theorem_E ℚ m hm S hS_inf hS_place L hL ε hε hε1
  have hmem : ∀ k, ∃ U, U ∈ W ∧ x k ∈ U := fun k => hWcov (x k) (hx0 k) (hineq k)
  choose g hgW hgmem using hmem
  obtain ⟨U₀, hU₀⟩ := Finite.exists_infinite_fiber (fun k => (⟨g k, hgW k⟩ : {U // U ∈ W}))
  refine ⟨(U₀ : Submodule ℚ (Fin m → ℚ)), hWtop _ U₀.2, ?_⟩
  rw [Set.infinite_coe_iff] at hU₀
  have hsub : (fun k => (⟨g k, hgW k⟩ : {U // U ∈ W})) ⁻¹' {U₀} ⊆
      {k | x k ∈ (U₀ : Submodule ℚ (Fin m → ℚ))} := by
    intro k hk
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hk
    have hgk : g k = (U₀ : Submodule ℚ (Fin m → ℚ)) := congrArg Subtype.val hk
    show x k ∈ (U₀ : Submodule ℚ (Fin m → ℚ))
    rw [← hgk]
    exact hgmem k
  exact hU₀.mono hsub

/-- **The reduction to non-confinement (proved).** With the hypotheses of `subspace_pigeonhole`, if the
family is **not** confinable (`hncf : ¬ Confinable x` — no proper subspace contains infinitely many `xₖ`),
then the Subspace inequality cannot hold for every `xₖ`: `False`. (`subspace_pigeonhole` produces the very
confinement `hncf` forbids.) -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem subspace_reduction {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_inf : ∀ v ∈ archAbsVal (K := ℚ), v ∈ S)
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0)
    (hineq : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      Height.mulHeight (x k) ^ (-(m : ℝ) - ε))
    (hncf : ¬ Confinable x) :
    False :=
  hncf (subspace_pigeonhole hm S hS_inf hS_place L hL ε hε hε1 x hx0 hineq)

/-- **The contradiction, with the height-vs-rate estimate fed in (proved).** This is the full `Φ`-side
composition. With the Subspace data and a nonzero point family `x`, suppose:

* `hover` — the **place-`2` over-approximation**: each Subspace product is `≤ 2^{−Nₖ}` (for the explicit
  points this is `‖n − Φ(αₖ)‖₂` times the `O(1)` `∞`-place factor, since `subspaceDen` is a `2`-adic
  unit; the deferred place computation);
* `hrate` — the **height-vs-rate estimate**: `2^{−Nₖ} ≤ H(xₖ)^{−m−ε}` (`B3.HeightVsRate`, from
  `IndexCondition` / proved outright for large repetition);
* `hncf` — **non-confinement**: `¬ Confinable x` (the open Diophantine-independence content).

Then `False`. Composing `hover` with `hrate` discharges the Subspace inequality (transitivity), and
`subspace_reduction` closes the argument. Thus assembling these for the `Φ`-image approximant points gives
the Missing Lemma; the two open inputs are exactly `hover`'s place computation and `hncf`. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07" "BL96", group "b3_missing_lemma"]
theorem subspace_contradiction_of_rate {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_inf : ∀ v ∈ archAbsVal (K := ℚ), v ∈ S)
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0) (N : ℕ → ℕ)
    (hover : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      (2 : ℝ) ^ (-(N k : ℝ)))
    (hrate : ∀ k, (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (x k) ^ (-(m : ℝ) - ε))
    (hncf : ¬ Confinable x) :
    False :=
  subspace_reduction hm S hS_inf hS_place L hL ε hε hε1 x hx0
    (fun k => le_trans (hover k) (hrate k)) hncf

/-- **The contradiction with the *archimedean-saved* rate (proved, Tier 2.1).** The sharpened companion of
`subspace_contradiction_of_rate`: it consumes an over-approximation `hover` carrying an explicit `H(xₖ)⁻¹`
factor and a *weaker* rate `hrate` needing to beat only `H(xₖ)^{1−m−ε}` (one power of `H` less). The
`H(xₖ)⁻¹` comes from the archimedean factor of the gcd-`1` point `(Dₖ, −1, Pₖ)`
(`B3.phi_twoPlace_product_le_invSup` + `B3.sup_vinf_placePoint_eq_mulHeight`), which the plain
`subspace_contradiction_of_rate` discards (`infFactor_le_one`'s `≤ 1`).

Composing, `(∏ …) ≤ H⁻¹·2^{−Nₖ} ≤ H⁻¹·H^{1−m−ε} = H^{−m−ε}` (the last step needs `0 < H`, `hHpos`), so the
Subspace inequality holds and `subspace_reduction` closes it. The net effect is to lower the rate threshold
from `m` to `m−1`: for the `Φ`-side `m = 3`, the height-vs-rate estimate need only reach `H^{−2−ε}` instead
of `H^{−3−ε}` (`B3.phiPoints_rate`, the index condition `B3.phiPoints_index` at threshold `2`). -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07" "BL96", group "b3_missing_lemma"]
theorem subspace_contradiction_of_rate_sharp {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_inf : ∀ v ∈ archAbsVal (K := ℚ), v ∈ S)
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0) (N : ℕ → ℕ)
    (hHpos : ∀ k, 0 < Height.mulHeight (x k))
    (hover : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      (Height.mulHeight (x k))⁻¹ * (2 : ℝ) ^ (-(N k : ℝ)))
    (hrate : ∀ k, (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1))
    (hncf : ¬ Confinable x) :
    False := by
  apply subspace_reduction hm S hS_inf hS_place L hL ε hε hε1 x hx0 _ hncf
  intro k
  have hH := hHpos k
  calc (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j)))
      ≤ (Height.mulHeight (x k))⁻¹ * (2 : ℝ) ^ (-(N k : ℝ)) := hover k
    _ ≤ (Height.mulHeight (x k))⁻¹ * Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1) :=
        mul_le_mul_of_nonneg_left (hrate k) (inv_nonneg.mpr hH.le)
    _ = Height.mulHeight (x k) ^ (-(m : ℝ) - ε) := by
        rw [show (Height.mulHeight (x k))⁻¹ = Height.mulHeight (x k) ^ (-1 : ℝ) from
          (Real.rpow_neg_one _).symm, ← Real.rpow_add hH]
        congr 1; ring

/-- **The Subspace pigeonhole over an infinite index set (proved, Tier 2.2).** As `subspace_pigeonhole`,
but the Subspace inequality (and nonvanishing) is required only on an **infinite** set `I ⊆ ℕ` of indices,
not on all of `ℕ`. The conclusion `Confinable x` is still about the *whole* family (some proper subspace
catches infinitely many `xₖ`), because the pigeonhole restricted to the infinite `I` already produces an
infinite caught subfamily.

*Proof:* `subspace_theorem_E` gives the finite cover `W`; each `xₖ` for `k ∈ I` lies in some `U ∈ W`
(`hWcov`). The assignment `↑I → W` maps the infinite subtype `↥I` into the finite `W`, so some `U₀ ∈ W` has
an infinite fiber (`Finite.exists_infinite_fiber`, using `hI.to_subtype`); its image in `ℕ`
(`Subtype.val` injective) is an infinite subset of `{k | xₖ ∈ U₀}`. -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem subspace_pigeonhole_infinite {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_inf : ∀ v ∈ archAbsVal (K := ℚ), v ∈ S)
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (x : ℕ → (Fin m → ℚ)) (I : Set ℕ) (hI : I.Infinite) (hx0 : ∀ k ∈ I, x k ≠ 0)
    (hineq : ∀ k ∈ I, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      Height.mulHeight (x k) ^ (-(m : ℝ) - ε)) :
    Confinable x := by
  obtain ⟨W, hWtop, hWcov⟩ := subspace_theorem_E ℚ m hm S hS_inf hS_place L hL ε hε hε1
  have hIinf := hI.to_subtype
  have hmem : ∀ k : ↥I, ∃ U, U ∈ W ∧ x ↑k ∈ U := fun k => hWcov (x ↑k) (hx0 ↑k k.2) (hineq ↑k k.2)
  choose g hgW hgmem using hmem
  obtain ⟨U₀, hU₀⟩ := Finite.exists_infinite_fiber (fun k : ↥I => (⟨g k, hgW k⟩ : {U // U ∈ W}))
  refine ⟨(U₀ : Submodule ℚ (Fin m → ℚ)), hWtop _ U₀.2, ?_⟩
  rw [Set.infinite_coe_iff] at hU₀
  have hsub : Subtype.val '' {k : ↥I | (⟨g k, hgW k⟩ : {U // U ∈ W}) = U₀} ⊆
      {k | x k ∈ (U₀ : Submodule ℚ (Fin m → ℚ))} := by
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq] at hk ⊢
    have hgk : g k = (U₀ : Submodule ℚ (Fin m → ℚ)) := congrArg Subtype.val hk
    rw [← hgk]; exact hgmem k
  exact ((Set.infinite_image_iff Subtype.val_injective.injOn).mpr hU₀).mono hsub

/-- **The arch-saved contradiction over a frequent subsequence (proved, Tier 2.2).** The `∃ᶠ` relaxation of
`subspace_contradiction_of_rate_sharp`: the over-approximation `hover` and positivity `hHpos`/nonvanishing
`hx0` are supplied for all `k` (the construction provides them everywhere), but the height-vs-rate estimate
`hrate` is required only **frequently** (`∃ᶠ k in atTop`). On the infinite set `I = {k | hrate holds}`
(`Nat.frequently_atTop_iff_infinite`) the same composition as `subspace_contradiction_of_rate_sharp` gives
the Subspace inequality, and `subspace_pigeonhole_infinite` produces the confinement `hncf` forbids.

This matches Adamczewski–Bugeaud (a good *subsequence* of approximants suffices) and is the form the
weakened open kernel `B3.phiPoints_index` (`B3.IndexConditionExpFreq`) feeds. It does **not** make the
argument unconditional (see `IndexConditionExpFreq`'s caveat). -/
@[category research solved, AMS 11 37, ref "Eve96" "AB07" "BL96", group "b3_missing_lemma"]
theorem subspace_contradiction_of_rate_sharp_frequently {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_inf : ∀ v ∈ archAbsVal (K := ℚ), v ∈ S)
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0) (N : ℕ → ℕ)
    (hHpos : ∀ k, 0 < Height.mulHeight (x k))
    (hover : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      (Height.mulHeight (x k))⁻¹ * (2 : ℝ) ^ (-(N k : ℝ)))
    (hrate : ∃ᶠ k in atTop, (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1))
    (hncf : ¬ Confinable x) :
    False := by
  apply hncf
  refine subspace_pigeonhole_infinite hm S hS_inf hS_place L hL ε hε hε1 x
    {k | (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1)}
    (Nat.frequently_atTop_iff_infinite.mp hrate) (fun k _ => hx0 k) (fun k hk => ?_)
  have hH := hHpos k
  calc (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j)))
      ≤ (Height.mulHeight (x k))⁻¹ * (2 : ℝ) ^ (-(N k : ℝ)) := hover k
    _ ≤ (Height.mulHeight (x k))⁻¹ * Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1) :=
        mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hH.le)
    _ = Height.mulHeight (x k) ^ (-(m : ℝ) - ε) := by
        rw [show (Height.mulHeight (x k))⁻¹ = Height.mulHeight (x k) ^ (-1 : ℝ) from
          (Real.rpow_neg_one _).symm, ← Real.rpow_add hH]
        congr 1; ring

end B3
