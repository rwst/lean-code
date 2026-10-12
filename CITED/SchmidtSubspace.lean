/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.SubspaceTheorem
import DiophantineApproximation.SubspaceAlgebraic
import DiophantineApproximation.FormBaseChange
import DiophantineApproximation.PlacesOverInfinite
import DiophantineApproximation.PlacesOverFinite
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Schmidt's Theorem 1D′: the Subspace Theorem with *algebraic* coefficients

`CITED/SubspaceTheorem.lean` records the Evertse–Schlickewei **number-field** form of the Subspace
Theorem: the points range over `Kⁿ` and the threshold is the height *relative to* `K`.  That form
is the right one when the data lives in `K`.  It is the **wrong** one when the data is rational
and only the *coefficients* are algebraic, because Mathlib's `Height.mulHeight` is the relative
height, so a rational point acquires `H_K(x) = H_ℚ(x)^{[K:ℚ]}`
(`NumberField.mulHeight_ratCast`): the exponent `−n−ε` is then measured against an inflated
height while the approximation is small at *one* place only.

The cleanest illustration is Roth.  Over `K` the theorem gives
`|α − β| < H_K(β)^{-2-ε}` finitely often for `β ∈ K`; specialised to `β = p/q ∈ ℚ` that reads
`|α − p/q| < H(p/q)^{-D(2+ε)}`, which is *weaker* than Roth's theorem by the factor
`D = [K : ℚ]` in the exponent — it says nothing about the classical range.  The same factor is
what confined the anchored family of `RB/AnchoredEscape.lean` to the scales
`θ < (3/2)^{n_∞+1−2D} ≤ 2/3`.

The classical tool for rational data with algebraic coefficients is Schmidt's Theorem 1D′ (the
`S`-arithmetic Subspace Theorem, Schlickewei's `p`-adic extension of Schmidt's norm-form theorem),
recorded here.  **No longer an axiom (2026-10-12)**: `schmidt1D'` is *derived* from the
sorry-free, std3 `NumberField.exists_finset_submodule_of_approxProd_le_extension` of the
`Subspace-Theorems` package — see *Derivation* below.

> Let `S` be a finite set of places of `ℚ` containing the archimedean one.  For each `v ∈ S` let
> `L_{1,v}, …, L_{n,v}` be linearly independent linear forms in `n` variables with **algebraic**
> coefficients (in `ℚ̄ ⊆ ℚ̄_v`).  Then for every `ε > 0` the solutions `x ∈ ℤⁿ` of
> $$ \prod_{v\in S}\prod_{i=1}^n |L_{i,v}(x)|_v \ \le\ |x|^{-\varepsilon} $$
> lie in finitely many proper subspaces of `ℚⁿ`.

Here `|x| = maxᵢ|x_i|` and the absolute values are normalized by `|p|_p = p⁻¹`; the extension of
`|·|_v` to `ℚ̄_v` is unique, so "the" value `|L_{i,v}(x)|_v` is well defined.

## Encoding conventions (and safe weakenings)

* **Projective normalization.** For a *primitive* integer vector `x` one has `‖x‖_v = 1` at every
  finite place and `‖x‖_∞ = |x| = H_ℚ(x)`, so the displayed inequality is equivalent to
  `∏_{v} ∏_i |L_{i,v}(x)|_v/‖x‖_v ≤ H(x)^{-n-ε}`.  That is the form recorded here; both sides are
  invariant under scaling `x ↦ cx`, so it extends from primitive integer vectors to all of `ℚⁿ`
  with no change of content, and it matches `Subspace.approxProduct` (the same shape as the
  sibling axiom).
* **Algebraic coefficients at one place.** Every consumer of this statement — and every
  application in the literature of the `S`-unit/`(3/2)ⁿ` type — puts the algebraic coefficients at
  a *single* distinguished place `v₀` (where the approximation happens) and coordinate or
  rational-coefficient forms elsewhere.  The axiom is therefore recorded in that shape:
  `L₀` with coefficients in a number field `K` at `v₀`, and `ℚ`-linear `L v` at the remaining
  places `v ∈ S` (`v₀ ∉ S`).  This is a *special case* of 1D′ (rational coefficients are
  algebraic), hence a safe weakening.
* **The place `v₀` and its extension.** `w₀ : AbsoluteValue K ℝ` is the chosen extension of `v₀`
  to the coefficient field, pinned by `hw₀ : ∀ q : ℚ, w₀ (q : K) = v₀ q`.  For `v₀` archimedean
  this is an infinite place of `K`, i.e. a choice of embedding `K ↪ ℂ` — exactly the choice of
  which conjugate of the algebraic coefficients is meant.
* **Places.** Every member of `S ∪ {v₀}` is a place of `ℚ` (`hv₀P`, `hS`: `Subspace.IsPlace`,
  e.g. `Subspace.isPlace_real`, `Subspace.isPlace_padic_two_three`), and `v₀ ∉ S`, so that no
  place is counted twice.  Until 2026-10-12 place membership was "documented, not enforced",
  which made the then-axiom **inconsistent** (the same counterexample as for
  `Subspace.evertseSchlickewei`: `|·|^{1/j}` is an `AbsoluteValue ℚ ℝ` for every `j ≥ 1`).
* **Conclusion.** Finitely many proper subspaces of `ℚⁿ` — of `ℚⁿ`, not of `Kⁿ`: the subspaces
  are cut out over the field of the *points*.  The finiteness is ineffective.

## Derivation

`Subspace-Theorems` states the theorem with points in `ℚ`, coefficients in `K`, and absolute
values `w v` of `K` **lying over** places `v` of `ℚ` ([BG06] Thm 7.2.2 + Rem. 7.2.3).  Here
`w v₀ := w₀` (lying over `v₀` is `hw₀`) with the forms `L₀`, and at `v ∈ S` any absolute value
of `K` over `v` (`NumberField.exists_liesOver_infinitePlace` / `_finitePlace`) with the base
change `Module.Dual.compRingHom` of `L v` to `K`, which takes the same value at rational points
(`compRingHom_comp`) and stays linearly independent.  Every infinite place of `ℚ` is real, so the
typed product of `Subspace-Theorems` is *equal* to the one stated here — no constant, no
Northcott step.

## Relation to `Subspace.evertseSchlickewei`

Neither statement implies the other by a formal specialization: this one is about `ℚ`-points with
algebraic coefficients, that one about `K`-points with `K`-coefficients.  Both are now derived from
`Subspace-Theorems`; the corpus's `ℚ`-coefficient consumers (`NKR`, `B3`) use the sibling
theorem, where the two coincide, and the derivations with an **algebraic irrational multiplier**
rest on the present one (`RB/AnchoredRational.lean`, `RB/OnePowerRational.lean`).  The
Corvaja–Zannier Main Theorem (`CZ.pseudoPisot_approx_of_subspace`, `CZ.pseudoPisot_approx_alg`)
used both through `CITED/Ridout.lean` until 2026-10-12; it is now a corollary of the
Subspace-Theorems library's own Main Theorem (`CITED/CorvajaZannierProof.lean`).

## Contents

* `Subspace.schmidt1D'` — **the Subspace Theorem with algebraic coefficients** ([S], Thm 1D′),
  derived from `Subspace-Theorems`.

## References

* [S] W. M. Schmidt, *Diophantine Approximation and Diophantine Equations*, Lecture Notes in Math.
  **1467**, Springer 1991 — Chapter V, Theorem 1D′.
* [Sch72] W. M. Schmidt, *Norm form equations*, Ann. of Math. **96** (1972), 526–551 — the
  archimedean Subspace Theorem.
* [Sli77] H. P. Schlickewei, *The p-adic Thue–Siegel–Roth–Schmidt theorem*, Arch. Math. (Basel)
  **29** (1977), 267–270 — the `S`-arithmetic extension quoted as 1D′.
* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, Cambridge 2006, Ch. 7 — the
  number-field form (`CITED/SubspaceTheorem.lean`) and the absolute normalization.
-/

namespace Subspace

open Height NumberField

/-- **The Subspace Theorem with algebraic coefficients** ([S], Theorem 1D′; Schlickewei's
`S`-arithmetic form): for a distinguished place `v₀` of `ℚ` carrying `n` linearly independent
linear forms `L₀` with coefficients in a number field `K` (measured by the extension `w₀` of
`v₀`), and rational-coefficient forms at the remaining places `v ∈ S`, the nonzero rational
solutions `x` of

  `(∏ᵢ |L₀ᵢ(x)|_{w₀}/‖x‖_{v₀}) · ∏_{v ∈ S} ∏ᵢ |L_{v,i}(x)|_v/‖x‖_v ≤ H(x)^{-n-ε}`

lie in finitely many proper subspaces of `ℚⁿ`.

Derived from the sorry-free, std3 theorem
`NumberField.exists_finset_submodule_of_approxProd_le_extension` of `Subspace-Theorems`
([BG06] Thm 7.2.2 + Rem. 7.2.3: points in `ℚ`, coefficients in `K`, absolute values of `K` lying
over the places of `ℚ`); see the module doc, *Derivation*.  The hypotheses `hv₀P`, `hS` (every
place involved is a place of `ℚ`) make it true; without them the former axiom was inconsistent.
Unlike its sibling `Subspace.evertseSchlickewei`, the points here are **rational** and the height
is the naive one: that is what makes it usable when only the coefficients are algebraic. -/
@[category research solved, AMS 11, ref "Schmidt91" "Sli77", group "three_halves_m4"]
theorem schmidt1D' {n : ℕ} (hn : 2 ≤ n) {K : Type*} [Field K] [NumberField K]
    (v₀ : AbsoluteValue ℚ ℝ) (hv₀P : IsPlace v₀) (w₀ : AbsoluteValue K ℝ)
    (hw₀ : ∀ q : ℚ, w₀ ((q : K)) = v₀ q)
    (L₀ : Fin n → ((Fin n → K) →ₗ[K] K)) (hL₀ : LinearIndependent K L₀)
    (S : Finset (AbsoluteValue ℚ ℝ)) (hS : ∀ v ∈ S, IsPlace v) (hv₀ : v₀ ∉ S)
    (L : AbsoluteValue ℚ ℝ → Fin n → ((Fin n → ℚ) →ₗ[ℚ] ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (Fin n → ℚ)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin n → ℚ, x ≠ 0 →
        (∏ i, w₀ (L₀ i (fun j ↦ ((x j : ℚ) : K))) / localNorm v₀ x) * approxProduct S L x
          ≤ Height.mulHeight x ^ (-(n : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  classical
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  set Sall : Finset (AbsoluteValue ℚ ℝ) := insert v₀ S with hSall
  have hSallP : ∀ v ∈ Sall, IsPlace v := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    exacts [hv₀P, hS v hv]
  -- an absolute value of `K` over every place of `ℚ`: `w₀` over `v₀`, a chosen one elsewhere
  have hext : ∀ u : AbsoluteValue ℚ ℝ, IsPlace u → ∃ W : AbsoluteValue K ℝ, W.LiesOver u := by
    rintro u (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · obtain ⟨w, hw⟩ := NumberField.exists_liesOver_infinitePlace (F := K) v
      exact ⟨w.1, hw⟩
    · exact NumberField.exists_liesOver_finitePlace (F := K) v
  let wext : AbsoluteValue ℚ ℝ → AbsoluteValue K ℝ := fun u ↦
    if h : ∃ W : AbsoluteValue K ℝ, W.LiesOver u then h.choose else w₀
  let w : AbsoluteValue ℚ ℝ → AbsoluteValue K ℝ := fun u ↦ if u = v₀ then w₀ else wext u
  -- the forms: `L₀` at `v₀`, the base change of `L v` to `K` elsewhere
  let L' : AbsoluteValue ℚ ℝ → Fin n → Module.Dual K (Fin n → K) := fun u ↦
    if u = v₀ then L₀ else fun i ↦ Module.Dual.compRingHom (L u i) (algebraMap ℚ K)
  have hwext : ∀ u ∈ S, (wext u).LiesOver u := fun u hu ↦ by
    have hex := hext u (hS u hu)
    simp only [wext, dite_eq_left hex]
    exact hex.choose_spec
  have hwlies : ∀ u ∈ Sall, (w u).LiesOver u := by
    intro u hu
    by_cases h : u = v₀
    · subst h
      simp only [w, ite_eq_left rfl]
      exact ⟨AbsoluteValue.ext fun q ↦ by
        change w₀ (algebraMap ℚ K q) = u q
        rw [eq_ratCast]
        exact hw₀ q⟩
    · simp only [w, ite_eq_right h]
      exact hwext u ((Finset.mem_insert.1 hu).resolve_left h)
  have hLI : ∀ u ∈ Sall, LinearIndependent K (L' u) := by
    intro u hu
    by_cases h : u = v₀
    · simp only [L', ite_eq_left h]
      exact hL₀
    · simp only [L', ite_eq_right h]
      exact Module.Dual.linearIndependent_compRingHom
        (hL u ((Finset.mem_insert.1 hu).resolve_left h)) _
  set Sinf : Finset (InfinitePlace ℚ) := Finset.univ.filter fun w ↦ w.1 ∈ Sall with hSinf
  set Sfin : Finset (FinitePlace ℚ) :=
    Sall.preimage (fun w ↦ w.1) (fun _ _ _ _ h ↦ Subtype.ext h) with hSfin
  obtain ⟨T, hT, hcov⟩ := NumberField.exists_finset_submodule_of_approxProd_le_extension
    (F := K) Sinf Sfin w
    (fun v hv ↦ hwlies _ (Finset.mem_filter.1 hv).2) (fun v hv ↦ hwlies _ (Finset.mem_preimage.1 hv))
    L' (fun v hv ↦ hLI _ (Finset.mem_filter.1 hv).2) (fun v hv ↦ hLI _ (Finset.mem_preimage.1 hv))
    hε
  refine ⟨T, hT, fun x hx happ ↦ hcov x hx ?_⟩
  -- the typed product is this one: every infinite place of `ℚ` has multiplicity one
  set G : AbsoluteValue ℚ ℝ → ℝ := fun u ↦
    ∏ i, w u (L' u i fun j ↦ algebraMap ℚ K (x j)) / ⨆ j, u (x j) with hG
  have hmult : ∀ v : InfinitePlace ℚ, v.mult = 1 := by
    intro v
    have h1 := Finset.single_le_sum (f := fun w : InfinitePlace ℚ ↦ w.mult)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)
    rw [InfinitePlace.sum_mult_eq, Module.finrank_self] at h1
    have h2 : 1 ≤ v.mult := by
      unfold InfinitePlace.mult
      split_ifs <;> norm_num
    omega
  have hlhs : NumberField.approxProd Sinf Sfin w L' x = ∏ u ∈ Sall, G u := by
    rw [prod_eq_prod_places hSallP G]
    change (∏ v ∈ Sinf, G v.1 ^ v.mult) * ∏ v ∈ Sfin, G v.1 = _
    simp only [hmult, pow_one]
    rfl
  have hG0 : G v₀ = ∏ i, w₀ (L₀ i fun j ↦ ((x j : ℚ) : K)) / localNorm v₀ x := by
    simp only [hG, w, L', eq_ratCast]
    rfl
  have hGS : ∀ u ∈ S, G u = ∏ i, u (L u i x) / localNorm u x := by
    intro u hu
    have h : u ≠ v₀ := fun h ↦ hv₀ (h ▸ hu)
    have hl := hwext u hu
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp only [w, L', ite_eq_right h]
    rw [Module.Dual.compRingHom_comp]
    exact congrArg (· / localNorm u x)
      (congrArg (fun φ : AbsoluteValue ℚ ℝ ↦ φ (L u i x)) (AbsoluteValue.LiesOver.under_eq _ _))
  rw [hlhs, hSall, Finset.prod_insert hv₀, hG0, Finset.prod_congr rfl hGS, Fintype.card_fin]
  exact happ

end Subspace
