/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.RationalK
import CITED.SubspaceTheorem
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Anchored repetitions and the `ℚ(δ)` rehearsal (report B1E2a-v2 N4 / P3)

The **anchored family** ([B1E2a2] §4 N4): repetitions `w[b, b+k) = w[a, a+k)` of the minimal
word whose *absolute base position* `b ≤ B` is bounded — not the gap.  The contraction gives
`‖δ((3/2)^a − (3/2)^b)‖ ≤ (2/3)^k`, and the difference *factors through the anchor*:

  `δ((3/2)^{b+d} − (3/2)^b) = (δ(3/2)^b)·((3/2)^d − 1)`   (`RB.anchored_factor`),

an **inhomogeneous one-power problem** for the multiplier `δ_b = δ(3/2)^b`: how close can
`δ_b v − δ_b` come to an integer along the `S`-unit ray `v = (3/2)^d`?  Per anchor this is a
three-term (`n = 3`) Subspace instance; for algebraic irrational `δ` its forms need
coefficients in `ℚ(δ)` — the family **funnels into the same number-field wall as RPF**, one
step below the pair theorem (no per-gap selection, no uniform-`ε` threading).  That makes it
the designated *rehearsal target* for the RPF infrastructure ([B1E2a2] §6 P3), and this file
is that rehearsal, built directly after the WP-G gate passed (2026-08-06).

## Layer 1 (std3): the family and its reduction to the wall

`RB.anchoredViolators δ θ B` mirrors `RB.algViolators` with the anchor bound replacing the
`2 ≤ a` floor; `RB.anchored_mem_of_repetition` is the combinatorial gate (via the
`K`-agnostic `RB.real_dist_le_of_repetition`).  The wall is named once,
`RB.InhomOnePower δ'`, and `RB.anchoredViolators_finite_of_inhomOnePower` proves the
**reduction**: the wall for the `B+1` multipliers `δ(3/2)^b`, `b ≤ B`, makes the whole
anchored family finite.  The multiplier transport lemmas record that all these multipliers
are algebraic irrational exactly when `δ` is — so *one* number field serves every anchor.

## Layer 2 (std3 + [Sub]): the `n = 3` Subspace application over a number field

`RB.nkForms` generalizes the `ℚ`-forms `NKR.Lforms3` of the one-axiom refactor verbatim to
an arbitrary number field `F` and an arbitrary distinguished place `w₀`: at `w₀` the
approximation form `γ₁X₁ + γ₂X₂ − X₀` replaces the first coordinate form
(`RB.nkForms_apply_self` shows the evaluation `γ₁x₁ + γ₂x₂ − x₀`; for the anchored instance
`γ₁ = −γ₂ = δ_b` and `x = (m, v, 1)` this is `δ_b v − δ_b − m`, the quantity whose distance
to `0` the wall bounds).  `RB.nkForms_linearIndependent` ports the independence proof —
nothing in it was specific to `ℚ` — and `RB.nk_subspace` instantiates
`Subspace.evertseSchlickewei` at these forms: finitely many proper subspaces of `F³` catch
every solution of the `approxProduct`/`mulHeight` inequality.

## Layer 3: the rehearsal at `F = ℚ⟮δ⟯`

`RB.adjoin_real_numberField` (candidate ForMathlib): `ℚ⟮δ⟯` is a number field for every
real algebraic `δ` — one line from `adjoin.finiteDimensional`.  With that instance:
`RB.anchoredPlaces` is the concrete `S` (all archimedean places, plus the finite places
above `2` and `3` captured as `{w | w 6 ≠ 1}`, finite by `FinitePlace.hasFiniteMulSupport`);
`RB.realPlace` is the distinguished archimedean place induced by the defining embedding
`ℚ⟮δ⟯ ↪ ℝ` (`RB.realPlace_apply`); `RB.genMultiplier δ b` is the anchored multiplier as an
*element of the one field* (`RB.genMultiplier_coe`); and **`RB.anchored_rehearsal`** runs
the full instantiation: for every anchor `b`, the Subspace conclusion holds at
`ℚ⟮δ⟯`, `S = anchoredPlaces`, forms `nkForms (genMultiplier δ b) (−genMultiplier δ b)
(realPlace δ)`.

## What the rehearsal does *not* yet contain (the priced remainder)

The distance from `RB.anchored_rehearsal` to `RB.InhomOnePower (δ(3/2)^b)` is exactly the
`ℚ(δ)`-mirror of the NKR *member-solves* stage ([WP-G gate report, bill items 1–2]):
(1) place values of the `S`-units `2^x3^y` over `𝓞_{ℚ(δ)}` (via
`HeightOneSpectrum.adicAbv_def`); (2) `Height.mulHeight` of *rational* triples computed in
`ℚ⟮δ⟯` — Mathlib has no height-extension lemmas, and its height is the relative one
(`logHeight₁ = D·h`); (3) the subspace-escape/ratio-distinctness endgame.  Those are the
RPF bill proper; nothing here pretends otherwise, and no axiom is added for them.

## Contents

* `RB.anchoredViolators`, `RB.anchored_mem_of_repetition`, `RB.anchored_factor`.
* `RB.InhomOnePower` — the named wall (anchored analogue of the pair branch).
* `RB.anchored_multiplier_isAlgebraic`, `RB.anchored_multiplier_irrational`.
* **`RB.anchoredViolators_finite_of_inhomOnePower`** — the reduction (std3).
* `RB.nkForms`, `RB.nkForms_apply_self`, `RB.nkForms_linearIndependent`,
  **`RB.nk_subspace`** — the `n = 3` application over any number field.
* `RB.adjoin_real_numberField`, `RB.anchoredPlaces`, `RB.realPlace`,
  `RB.genMultiplier`, `RB.genMultiplier_coe`, **`RB.anchored_rehearsal`**.

## References

* [B1E2a2] `plans/report-B1E2a-v2.html` (2026-08-06): §4 N4, §6 P3, §7 WP-G; assessed
  proposal `old-plans/report-B1E2a-v2.md` §2–3, §6.
* [NKR25] Nair, Kumar, Rout, arXiv:2506.02898v3 — the `ℚ`-template
  (`CITED/NairKumarRoutLemmas.lean`, `Lforms3`), repaired and derived from [Schmidt91].
* [Schmidt91] W. M. Schmidt, LNM 1467, Thm 1D′ — `Subspace.evertseSchlickewei`.
* [B1E2] `plans/plan-B1E2.html`; [B2A2] `plans/plan-B2A2.html`.
-/

namespace RB

/-! ## Layer 1: the anchored family and its reduction to the wall (std3) -/

/-- The **anchored violating pairs** at scale `θ` with anchor bound `B`: pairs `b < a` with
`b ≤ B` and `‖δ·((3/2)^a − (3/2)^b)‖ ≤ θ^a`.  The bound is on the *absolute position* of
the first occurrence, not on the gap — the family between `RB.algViolators`' bounded-gap
slices and bounded-nothing ([B1E2a2] N4). -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
def anchoredViolators (δ : ℝ) (θ : ℚ) (B : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 ≤ B ∧ p.1 < p.2 ∧
    distToNearestInt (δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1)) ≤ (θ : ℝ) ^ p.2}

/-- **The combinatorial gate**: an anchored length-`k` repetition of the minimal word lands
in the anchored violator set as soon as the geometric contraction `(2/3)^k` beats the scale
`θ^a`.  `K`-agnostic, via `RB.real_dist_le_of_repetition`. -/
@[category research solved, AMS 11 68, ref "B1E2a2" "B2A2", group "rb_anchored"]
theorem anchored_mem_of_repetition {x₀ : ℕ} (hx₀ : 0 < x₀) {b a k : ℕ} {θ : ℚ} {B : ℕ}
    (hbB : b ≤ B) (hba : b < a) (hrep : IsRepetition x₀ b a k)
    (hgate : (2 / 3 : ℝ) ^ k ≤ (θ : ℝ) ^ a) :
    (b, a) ∈ anchoredViolators (K x₀) θ B :=
  ⟨hbB, hba, le_trans (real_dist_le_of_repetition hx₀ hrep) hgate⟩

/-- **The anchor factorization**: the orbit difference at an anchored pair is the anchored
multiplier `δ(3/2)^b` times the *inhomogeneous one-power* quantity `(3/2)^d − 1`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma anchored_factor (δ : ℝ) (b d : ℕ) :
    δ * ((3 / 2 : ℝ) ^ (b + d) - (3 / 2 : ℝ) ^ b)
      = δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1) := by
  rw [pow_add]; ring

/-- **The inhomogeneous one-power wall** ([B1E2a2] N4): for the multiplier `δ'`, only
finitely many `d` bring `δ'((3/2)^d − 1)` within `θ^d` of an integer, for every geometric
scale `θ ∈ (0,1)`.  For rational `δ'` this is a three-term Subspace statement over `ℚ`; for
algebraic irrational `δ'` it is the `n = 3` number-field wall this file rehearses — one step
below RPF (the pair theorem), sharing its entire infrastructure.  Named as a `def` so the
reduction below and future derivations quote the same statement. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
def InhomOnePower (δ' : ℝ) : Prop :=
  ∀ θ : ℚ, 0 < θ → θ < 1 →
    {d : ℕ | 0 < d ∧
      distToNearestInt (δ' * ((3 / 2 : ℝ) ^ d - 1)) ≤ (θ : ℝ) ^ d}.Finite

/-- Anchored multipliers stay algebraic: `δ(3/2)^b` is algebraic over `ℚ` whenever `δ` is. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma anchored_multiplier_isAlgebraic {δ : ℝ} (h : IsAlgebraic ℚ δ) (b : ℕ) :
    IsAlgebraic ℚ (δ * (3 / 2 : ℝ) ^ b) := by
  refine h.mul (IsAlgebraic.pow ?_ b)
  have : ((3 / 2 : ℚ) : ℝ) = (3 / 2 : ℝ) := by norm_num
  exact this ▸ isAlgebraic_algebraMap (3 / 2 : ℚ)

/-- Anchored multipliers stay irrational: `δ(3/2)^b` is irrational whenever `δ` is.
With the previous lemma: *all* anchored multipliers of an algebraic irrational `δ` are
algebraic irrational, and they generate the same field `ℚ(δ)` — one wall serves every
anchor. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma anchored_multiplier_irrational {δ : ℝ} (h : Irrational δ) (b : ℕ) :
    Irrational (δ * (3 / 2 : ℝ) ^ b) := by
  have hcast : (δ * (3 / 2 : ℝ) ^ b) = δ * (((3 / 2 : ℚ) ^ b : ℚ) : ℝ) := by push_cast; ring
  rw [hcast]
  exact h.mul_ratCast (pow_ne_zero b (by norm_num))

/-- **The reduction, at a single scale** ([B1E2a2] N4, std3): the wall *at the scale `θ`* for
the `B+1` anchored multipliers `δ(3/2)^b`, `b ≤ B`, already makes the anchored family at that
scale finite.  Each violator `(b, b+d)` funnels through `RB.anchored_factor` into the wall at its
own anchor (using `θ^{b+d} ≤ θ^d`); the family is the finite union of the resulting images.  The
per-scale form is what a derivation with a `θ`-threshold can supply
(`RB.inhomOnePower_of_threshold`). -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem anchoredViolators_finite_of_wall (δ : ℝ) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (B : ℕ)
    (hwall : ∀ b ≤ B, {d : ℕ | 0 < d ∧
      distToNearestInt (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1)) ≤ (θ : ℝ) ^ d}.Finite) :
    (anchoredViolators δ θ B).Finite := by
  have hθ0' : (0 : ℝ) ≤ (θ : ℝ) := by exact_mod_cast hθ0.le
  have hθ1' : ((θ : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hθ1.le
  have hsub : anchoredViolators δ θ B ⊆
      ⋃ b ∈ Finset.range (B + 1), (fun d => (b, b + d)) ''
        {d : ℕ | 0 < d ∧
          distToNearestInt (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ d - 1)) ≤ (θ : ℝ) ^ d} := by
    rintro ⟨b, a⟩ ⟨(hbB : b ≤ B), (hba : b < a),
      (hdist : distToNearestInt (δ * ((3 / 2 : ℝ) ^ a - (3 / 2 : ℝ) ^ b)) ≤ (θ : ℝ) ^ a)⟩
    refine Set.mem_biUnion (x := b)
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) ?_
    refine ⟨a - b, ⟨by omega, ?_⟩, by
      show (b, b + (a - b)) = (b, a)
      rw [Nat.add_sub_cancel' hba.le]⟩
    have hab : b + (a - b) = a := by omega
    calc distToNearestInt (δ * (3 / 2 : ℝ) ^ b * ((3 / 2 : ℝ) ^ (a - b) - 1))
        = distToNearestInt (δ * ((3 / 2 : ℝ) ^ a - (3 / 2 : ℝ) ^ b)) := by
          rw [← anchored_factor, hab]
      _ ≤ (θ : ℝ) ^ a := hdist
      _ ≤ (θ : ℝ) ^ (a - b) := pow_le_pow_of_le_one hθ0' hθ1' (by omega)
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.range (B + 1)).finite_toSet ?_) hsub
  intro b hb
  have hbB : b ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_coe.mp hb))
  exact (hwall b hbB).image _

/-- **The reduction** ([B1E2a2] N4, std3): the inhomogeneous one-power wall for the `B+1`
anchored multipliers `δ(3/2)^b`, `b ≤ B`, makes the whole anchored family finite — the
`RB.InhomOnePower` form of `RB.anchoredViolators_finite_of_wall`. -/
@[category research solved, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem anchoredViolators_finite_of_inhomOnePower (δ : ℝ) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (B : ℕ) (hwall : ∀ b ≤ B, InhomOnePower (δ * (3 / 2 : ℝ) ^ b)) :
    (anchoredViolators δ θ B).Finite :=
  anchoredViolators_finite_of_wall δ hθ0 hθ1 B (fun b hb => hwall b hb θ hθ0 hθ1)

/-! ## Layer 2: the `n = 3` Subspace application over a number field (std3 + [Sub]) -/

section NumberFieldForms

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

/-- The **approximation triple of forms** `(γ₁X₁ + γ₂X₂ − X₀, X₁, X₂)`, used at the
distinguished place.  Split out of `RB.nkForms` so that it can be reused when the places are
indexed by a *different* field than the one carrying the coefficients — the situation of
Schmidt's Theorem 1D′ (`CITED/SchmidtSubspace.lean`), where the points are rational and only
the coefficients are algebraic. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
noncomputable def approxForms (γ₁ γ₂ : F) : Fin 3 → ((Fin 3 → F) →ₗ[F] F) :=
  ![γ₁ • LinearMap.proj 1 + γ₂ • LinearMap.proj 2 - LinearMap.proj 0,
    LinearMap.proj 1, LinearMap.proj 2]

/-- The **coordinate triple of forms** `(X₀, X₁, X₂)`, used at every non-distinguished place. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
noncomputable def coordForms : Fin 3 → ((Fin 3 → F) →ₗ[F] F) :=
  ![LinearMap.proj 0, LinearMap.proj 1, LinearMap.proj 2]

/-- The per-place linear forms of the anchored/RPF `n = 3` Subspace application over a
number field `F` — `NKR.Lforms3` with `ℚ` replaced by `F` and the distinguished place a
parameter: at `w₀` the approximation form `γ₁X₁ + γ₂X₂ − X₀` replaces the first coordinate
form; at every other place the coordinate forms.  For the anchored instance `γ₁ = −γ₂ = δ_b`
and `w₀` the defining real place of `ℚ(δ)`. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
noncomputable def nkForms (γ₁ γ₂ : F) (w₀ v : AbsoluteValue F ℝ) :
    Fin 3 → ((Fin 3 → F) →ₗ[F] F) :=
  if v = w₀ then approxForms γ₁ γ₂ else coordForms

/-- At the distinguished place, the first form evaluates to `γ₁x₁ + γ₂x₂ − x₀` — for the
anchored triple `x = (m, v, 1)` with `γ₁ = −γ₂ = δ_b` this is `δ_b v − δ_b − m`, the
quantity the wall `RB.InhomOnePower` bounds away from `0`. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma nkForms_apply_self (γ₁ γ₂ : F) (w₀ : AbsoluteValue F ℝ) (x : Fin 3 → F) :
    nkForms γ₁ γ₂ w₀ w₀ 0 x = γ₁ * x 1 + γ₂ * x 2 - x 0 := by
  simp [nkForms, approxForms, smul_eq_mul]

/-- Linear independence of the approximation triple, for *all* coefficients — the `ℚ`-proof of
`NKR.lforms3_linearIndependent` ports to `F` unchanged. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
lemma approxForms_linearIndependent (γ₁ γ₂ : F) :
    LinearIndependent F (approxForms γ₁ γ₂) := by
  unfold approxForms
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := LinearMap.congr_fun hg ![1, 0, 0]
  have h1 := LinearMap.congr_fun hg ![0, 1, 0]
  have h2 := LinearMap.congr_fun hg ![0, 0, 1]
  simp [Fin.sum_univ_three] at h0 h1 h2
  have hg0 : g 0 = 0 := h0
  have hg1 : g 1 = 0 := by
    rw [hg0] at h1
    simpa using h1
  have hg2 : g 2 = 0 := by
    rw [hg0] at h2
    simpa using h2
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-- Linear independence of the coordinate triple. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
lemma coordForms_linearIndependent : LinearIndependent F (coordForms (F := F)) := by
  unfold coordForms
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := LinearMap.congr_fun hg ![1, 0, 0]
  have h1 := LinearMap.congr_fun hg ![0, 1, 0]
  have h2 := LinearMap.congr_fun hg ![0, 0, 1]
  simp [Fin.sum_univ_three] at h0 h1 h2
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Linear independence of the forms, at every place and for *all* coefficients. -/
@[category API, AMS 11, ref "NKR25" "B1E2a2", group "rb_anchored"]
lemma nkForms_linearIndependent (γ₁ γ₂ : F) (w₀ v : AbsoluteValue F ℝ) :
    LinearIndependent F (nkForms γ₁ γ₂ w₀ v) := by
  unfold nkForms
  by_cases h : v = w₀
  · rw [ite_eq_left h]
    exact approxForms_linearIndependent γ₁ γ₂
  · rw [ite_eq_right h]
    exact coordForms_linearIndependent

/-- **The `n = 3` Subspace conclusion over a number field**: at any finite place set `S`,
distinguished place `w₀`, and coefficients `γ₁, γ₂`, the nonzero solutions of the
`approxProduct`/`mulHeight` inequality for `nkForms` lie in finitely many proper subspaces
of `F³`.  Instantiates the cited axiom `Subspace.evertseSchlickewei`; this is the entire
Diophantine engine of the anchored family and of RPF, pinned at the exact forms the
derivations will consume. -/
@[category research solved, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_anchored"]
theorem nk_subspace [NumberField F] (S : Finset (AbsoluteValue F ℝ)) (γ₁ γ₂ : F)
    (w₀ : AbsoluteValue F ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset (Submodule F (Fin 3 → F)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin 3 → F, x ≠ 0 →
        Subspace.approxProduct S (nkForms γ₁ γ₂ w₀) x
          ≤ Height.mulHeight x ^ (-(3 : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  Subspace.evertseSchlickewei (by norm_num) S (nkForms γ₁ γ₂ w₀)
    (fun v _ => nkForms_linearIndependent γ₁ γ₂ w₀ v) ε hε

end NumberFieldForms

/-! ## Layer 3: the rehearsal at `F = ℚ⟮δ⟯` -/

section Rehearsal

open IntermediateField NumberField

/-- `ℚ⟮δ⟯` is a number field, for every real algebraic `δ` — `CharZero` is inherited from
`ℝ`, finite dimensionality is `adjoin.finiteDimensional`.  Candidate ForMathlib. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
theorem adjoin_real_numberField {δ : ℝ} (hδ : IsAlgebraic ℚ δ) : NumberField ℚ⟮δ⟯ :=
  have : FiniteDimensional ℚ ℚ⟮δ⟯ := adjoin.finiteDimensional hδ.isIntegral
  ⟨⟩

variable (δ : ℝ) [NumberField ℚ⟮δ⟯]

/-- The concrete place set of the anchored application at `ℚ(δ)`: **all** archimedean
places, together with the finite places above `2` and `3` — captured as `{w | w 6 ≠ 1}`,
finite by `FinitePlace.hasFiniteMulSupport`.  This is the `S` the WP-G gate probe
validated. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
noncomputable def anchoredPlaces : Finset (AbsoluteValue ℚ⟮δ⟯ ℝ) :=
  haveI := Classical.decEq (AbsoluteValue ℚ⟮δ⟯ ℝ)
  Finset.univ.image (fun v : InfinitePlace ℚ⟮δ⟯ => v.val) ∪
    ((FinitePlace.hasFiniteMulSupport
      (show (6 : ℚ⟮δ⟯) ≠ 0 by norm_num)).image Subtype.val).toFinset

/-- The distinguished archimedean place of `ℚ(δ)`: the absolute value induced by the
defining embedding `ℚ⟮δ⟯ ↪ ℝ`.  At this place the approximation form of `RB.nkForms` is
small; at the conjugate places it is only height-bounded. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
noncomputable def realPlace : AbsoluteValue ℚ⟮δ⟯ ℝ :=
  NumberField.place (algebraMap ℚ⟮δ⟯ ℝ)

omit [NumberField ↥ℚ⟮δ⟯] in
/-- The distinguished place computes the honest real absolute value. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma realPlace_apply (x : ℚ⟮δ⟯) : realPlace δ x = |(x : ℝ)| := by
  rw [realPlace, NumberField.place_apply, Real.norm_eq_abs]
  rfl

/-- The anchored multiplier `δ(3/2)^b`, as an element of the **single** field `ℚ⟮δ⟯` that
serves every anchor. -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
noncomputable def genMultiplier (b : ℕ) : ℚ⟮δ⟯ :=
  AdjoinSimple.gen ℚ δ * ((3 / 2 : ℚ) ^ b : ℚ)

omit [NumberField ↥ℚ⟮δ⟯] in
/-- Under the defining embedding, `RB.genMultiplier δ b` is the real anchored multiplier
`δ(3/2)^b` — the formal content of "one field, one wall, every anchor". -/
@[category API, AMS 11, ref "B1E2a2", group "rb_anchored"]
lemma genMultiplier_coe (b : ℕ) :
    ((genMultiplier δ b : ℚ⟮δ⟯) : ℝ) = δ * (3 / 2 : ℝ) ^ b := by
  have h2 : ((((3 / 2 : ℚ) ^ b : ℚ) : ℚ⟮δ⟯) : ℝ) = (3 / 2 : ℝ) ^ b := by
    rw [SubfieldClass.coe_ratCast]
    push_cast
    norm_num
  calc ((genMultiplier δ b : ℚ⟮δ⟯) : ℝ)
      = δ * ((((3 / 2 : ℚ) ^ b : ℚ) : ℚ⟮δ⟯) : ℝ) := rfl
    _ = δ * (3 / 2 : ℝ) ^ b := by rw [h2]

/-- **The rehearsal** ([B1E2a2] §6 P3, first post-gate target): for every anchor `b`, the
`n = 3` Subspace conclusion holds at the field `ℚ⟮δ⟯`, the place set
`RB.anchoredPlaces δ`, the distinguished place `RB.realPlace δ`, and the anchored
coefficients `γ₁ = −γ₂ = genMultiplier δ b` — finitely many proper subspaces of `ℚ⟮δ⟯³`
catch every solution of the inequality.  Footprint: std3 + `Subspace.evertseSchlickewei`.
The remaining distance to `RB.InhomOnePower (δ(3/2)^b)` is the priced member-solves bill
(module doc); it consumes exactly this statement. -/
@[category research solved, AMS 11, ref "Schmidt91" "B1E2a2", group "rb_anchored"]
theorem anchored_rehearsal (ε : ℝ) (hε : 0 < ε) (b : ℕ) :
    ∃ T : Finset (Submodule ℚ⟮δ⟯ (Fin 3 → ℚ⟮δ⟯)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin 3 → ℚ⟮δ⟯, x ≠ 0 →
        Subspace.approxProduct (anchoredPlaces δ)
            (nkForms (genMultiplier δ b) (-(genMultiplier δ b)) (realPlace δ)) x
          ≤ Height.mulHeight x ^ (-(3 : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  nk_subspace (anchoredPlaces δ) (genMultiplier δ b) (-(genMultiplier δ b))
    (realPlace δ) ε hε

end Rehearsal

end RB
