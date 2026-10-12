/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import DiophantineApproximation.SubspaceTheorem
import DiophantineApproximation.RationalPlaces
import ArithmeticHeights.Northcott
import ForMathlib.NumberTheory.FinitePlaceProduct
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Subspace Theorem (Evertse–Schlickewei number-field form)

The `S`-arithmetic **Subspace Theorem** in the Evertse–Schlickewei *number-field*
form ([BG06] Ch. 7): points in `Kⁿ`, forms with coefficients in `K`, threshold
the height relative to `K`.  **No longer an axiom (2026-10-12)**: `evertseSchlickewei` is
*derived* from the sorry-free, std3 Subspace Theorem of the `Subspace-Theorems` package
(`NumberField.exists_finset_submodule_of_approxProd_le`, [BG06] Thm 7.2.2 with `F = K`,
Layer 6.2 of its `DiophantineApproximation` roadmap) — see *Derivation* below.  It was the
deepest Diophantine engine behind the `(3/2)ⁿ` complexity program.  It is the
black box that both formerly-bespoke axioms of the program bottomed out at —
**both derivations are now complete (2026-07-14)**:

* the [CZ04] Main Theorem is this theorem at `n = 2` with a *fixed* linear
  form — i.e. **Ridout's theorem** — applied once; derived as
  `CZ.pseudoPisot_approx_of_subspace` (`CITED/CorvajaZannierProof.lean`,
  sorry-free), the bespoke axiom retired.
* the repaired [NKR25] Theorem 1.3(i) is this theorem at `n = 3` over `ℚ`;
  derived as `NKR.sUnit_pair_integrality_of_subspace`
  (`CITED/NairKumarRoutProof.lean`, sorry-free).  The *unrepaired* axiom was
  **provably false** (missing strict positivity — machine-checked refutation
  `NKR.thm13i_unrepaired_false` in `CITED/NairKumarRout.lean`); the axiom is
  deleted, not merely derived (`report-formalize-subspace.html` §4, §6).

Recording it once, and deriving those two consequences in Lean, collapses the
program's Mahler-problem / `S`-unit Diophantine backbone to a single famous
axiom (Ridout is itself a corollary of the Subspace Theorem, so the whole
`Roth → Ridout → Subspace` tower reduces to this one statement).  The
one-axiom end state is reached: `TH.complexity_superlinear` depends on
std3 + `Subspace.evertseSchlickewei` only.

## The theorem

> Let `K` be a number field, `n ≥ 2`, and `S` a finite set of places of `K`
> containing the archimedean ones.  For each `v ∈ S` let `L_{v,1}, …, L_{v,n}`
> be `n` linearly independent linear forms in `X_1, …, X_n` with coefficients in
> `K`.  For every `ε > 0`, the nonzero solutions `x ∈ Kⁿ` of
> $$ \prod_{v \in S} \prod_{i=1}^n \frac{|L_{v,i}(x)|_v}{\lVert x\rVert_v}
>     \ \le\ H(x)^{-n-\varepsilon} $$
> lie in **finitely many proper linear subspaces** of `Kⁿ`.

Here `‖x‖_v = maxᵢ |x_i|_v` is the local sup-norm and `H(x) = ∏_v ‖x‖_v` the
absolute (projective) multiplicative height — exactly Mathlib's
`Height.mulHeight`, whose definition uses the *same* local norm `⨆ i, v (x i)`
over the admissible family `Height.AdmissibleAbsValues`.

## Encoding conventions (and safe weakenings)

Recorded on the authority of [S] / [BG06]; a faithful transcription, with the
following documented choices (each of which a consumer may only *weaken*):

* **Field**: stated for a general `[NumberField K]`.  Every consumer specializes
  `K := ℚ` (degree 1); the ready-made `Subspace.evertseSchlickewei_rat` is that
  instantiation.  **Caveat (2026-08-07)**: at `[K : ℚ] = D > 1` this statement is
  *not* interchangeable with Schmidt's Theorem 1D′ on rational data.  Mathlib's
  `Height.mulHeight` is the height relative to `K`, so a point of `ℚⁿ ⊆ Kⁿ`
  carries `H_K(x) = H_ℚ(x)^D` (`NumberField.mulHeight_ratCast`) while the
  approximation is small at one place only; the conclusion one gets is weaker by
  the factor `D` in the exponent.  (Roth: over `K` one only excludes
  `|α − p/q| < H(p/q)^{-D(2+ε)}`.)  For rational points with *algebraic*
  coefficients use `Subspace.schmidt1D'` (`CITED/SchmidtSubspace.lean`), which is
  Schmidt's 1D′ proper; the two statements are genuinely different, and neither
  specializes to the other.
* **Places**: `S : Finset (AbsoluteValue K ℝ)` with the hypothesis `hS` that every
  member **is a place** (`Subspace.IsPlace`: the absolute value of an infinite or a
  finite place of `K`) — e.g. `{∞, 2, 3}` over `ℚ` (`Subspace.isPlace_real`,
  `Subspace.isPlace_padic`).  Until 2026-10-12 this membership was "documented, not
  enforced", which made the then-axiom **inconsistent**: `|·|^{1/j}` is an
  `AbsoluteValue ℚ ℝ` for every `j ≥ 1`, and `S = {|·|, |·|^{1/2}, |·|^{1/3}, |·|^{1/4}}`
  with coordinate forms and `ε = 1/12` is satisfied by every `(1, q)`.  `S` need not
  contain the archimedean places.  Each place counts **once** in `approxProduct`, a
  complex one included (Mathlib's normalization would count it twice); that is harmless
  — see *Derivation*.
* **Forms**: `L v : Fin n → ((Fin n → K) →ₗ[K] K)`, `K`-linear forms with
  coefficients in `K`, required linearly independent per place (`hL`).  For the
  `ℚ`-consumers the forms have *rational* coefficients (e.g. `x₀ − δ·x₁` with
  `δ ∈ ℚ`, and coordinate forms), a special case of the general statement.
* **Norm / threshold**: the local norm is `⨆ i, v (x i)` (Mathlib's), the
  double product is `Subspace.approxProduct`, and `H(x)^{-n-ε}` lives in `ℝ` via
  `rpow` with `ε : ℝ` free.  Matches [NKR25] Theorem 2.1 verbatim.
* **Conclusion**: `∃ T : Finset (Submodule K (Fin n → K))`, all members proper
  (`W ≠ ⊤`), covering every solution.  The finiteness is **ineffective**
  (Subspace-based): no bound on the number or the height of the subspaces.

## Derivation

`Subspace-Theorems` states the theorem for typed place sets `Sinf : Finset (InfinitePlace K)`,
`Sfin : Finset (FinitePlace K)`, with the factor of an infinite place raised to `v.mult`.  Here
`S` is split along `hS` into those two sets (an absolute value is never both, since
`w 2 = 2` at an infinite place and `w 2 ≤ 1` at a finite one).  The two products differ by
`∏_{v ∈ Sinf} f_v^{mult v - 1}`, and every local factor is bounded by a constant of the forms
alone, `f_v ≤ ∏ᵢ ∑ⱼ |L_{v,i}(e_j)|_v` (`localFactor_le`).  So a solution at exponent `ε` of
large height is a solution of the typed theorem at `ε/2`; the points of small height span
finitely many lines (Northcott, `Projectivization.finite_setOfPred_mulHeight_le`).

## Contents

* `Subspace.localNorm` — the local sup-norm `‖x‖_v = ⨆ i |x_i|_v`.
* `Subspace.approxProduct` — the double product `∏_{v∈S} ∏_i |L_{v,i}(x)|_v/‖x‖_v`.
* `Subspace.IsPlace` — an absolute value of `K` that is an infinite or a finite place.
* `Subspace.evertseSchlickewei` — **the Subspace Theorem**, number-field form
  ([BG06] Ch. 7), derived from `Subspace-Theorems`; finitely many proper subspaces of `Kⁿ`
  contain all solutions.
* `Subspace.evertseSchlickewei_rat` — the `K := ℚ` specialization consumers use.
* `Subspace.isPlace_real`, `Subspace.isPlace_padic`,
  `Subspace.isPlace_real_padic_two_three` — the places of `ℚ` the consumers use.

## Sibling axiom

`Subspace.schmidt1D'` (`CITED/SchmidtSubspace.lean`) records Schmidt's Theorem 1D′:
**rational** points, forms with **algebraic** coefficients, naive height.  That is
the form the anchored/RPF derivations with algebraic irrational multipliers need
(`RB/AnchoredRational.lean`); see the `Field` bullet above for why this file's
axiom cannot serve there.  The two are recorded separately and consumed by
disjoint lanes.

## References

* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, Cambridge
  2006, Ch. 7 — **the form recorded here** (number-field points and heights),
  quoted by [NKR25] as their Theorem 2.1.
* [S] W. M. Schmidt, *Diophantine Approximation and Diophantine Equations*,
  Lecture Notes in Math. **1467**, Springer 1991 — Theorem 2A (Roth) and Theorem
  1D′ (`S`-arithmetic Subspace with algebraic coefficients over `ℚ`; recorded
  separately in `CITED/SchmidtSubspace.lean`, *not* the statement below).
* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004), 175–191 (`CITED/CorvajaZannier.lean`).
* [NKR25] Nair–Kumar–Rout, arXiv:2506.02898v3 (`CITED/NairKumarRout.lean`).
* `report-formalize-subspace.html` (this repository, 2026-07): the dependency
  analysis and effort estimate that motivates this file; §3 (CZ → Ridout),
  §4 (NKR → Subspace n = 3), §6 (the one-axiom refactor).
* [M4A3] `plan-M4A3.html`, §5–6.
-/

namespace Subspace

variable {K : Type*} [Field K] [NumberField K]

/-- The local sup-norm `‖x‖_v = maxᵢ |x_i|_v` at a place `v`, as an `ℝ`-value.
This is the very quantity Mathlib's `Height.mulHeight` maximizes over the
coordinates at each place. -/
@[category API, AMS 11, ref "Schmidt91", group "three_halves_m4"]
noncomputable def localNorm {n : ℕ} (v : AbsoluteValue K ℝ) (x : Fin n → K) : ℝ :=
  ⨆ i, v (x i)

/-- The Subspace-Theorem double product `∏_{v∈S} ∏_i |L_{v,i}(x)|_v / ‖x‖_v`
whose smallness (below `H(x)^{-n-ε}`) confines `x` to finitely many subspaces. -/
@[category API, AMS 11, ref "Schmidt91", group "three_halves_m4"]
noncomputable def approxProduct {n : ℕ} (S : Finset (AbsoluteValue K ℝ))
    (L : AbsoluteValue K ℝ → Fin n → ((Fin n → K) →ₗ[K] K)) (x : Fin n → K) : ℝ :=
  ∏ v ∈ S, ∏ i, v (L v i x) / localNorm v x

open NumberField

/-- An absolute value of `K` that **is a place**: the absolute value of an infinite place or
of a finite place of `K` (in Mathlib's normalization).  The Subspace Theorem quantifies over
finite sets of these; over arbitrary absolute values it is false. -/
@[category API, AMS 11, ref "BG06", group "three_halves_m4"]
def IsPlace (v : AbsoluteValue K ℝ) : Prop :=
  (∃ w : InfinitePlace K, w.1 = v) ∨ ∃ w : FinitePlace K, w.1 = v

/-- An absolute value of `K` is never both an infinite and a finite place: `w 2 = 2` at the
first, `w 2 ≤ 1` at the second. -/
@[category API, AMS 11, ref "BG06", group "three_halves_m4"]
theorem infinitePlace_val_ne_finitePlace_val (w : InfinitePlace K) (u : FinitePlace K) :
    w.1 ≠ u.1 := by
  intro h
  have h1 : w.1 (2 : K) = 2 := by
    have := w.map_natCast 2
    change w.1 ((2 : ℕ) : K) = ((2 : ℕ) : ℝ) at this
    exact_mod_cast this
  have h2 : u.1 (2 : K) ≤ 1 := by
    have := FinitePlace.apply_intCast_le_one u 2
    change u.1 ((2 : ℤ) : K) ≤ 1 at this
    exact_mod_cast this
  rw [h] at h1
  linarith

/-- The absolute values of Mathlib's height structure on a number field
(`Height.AdmissibleAbsValues`: the infinite places with multiplicity, and the finite places) are
places. -/
@[category API, AMS 11, ref "BG06", group "three_halves_m4"]
theorem isPlace_of_mem_admissible {v : AbsoluteValue K ℝ}
    (hv : v ∈ Height.AdmissibleAbsValues.archAbsVal (K := K) ∨
      v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := K)) : IsPlace v := by
  rcases hv with h | h
  · exact Or.inl ⟨⟨v, NumberField.mem_multisetInfinitePlace.mp h⟩, rfl⟩
  · exact Or.inr ⟨⟨v, h⟩, rfl⟩

/-- A bound on the local factor of the forms `L` at `v` that depends on the forms alone:
`∏ᵢ ∑ⱼ |L_i(e_j)|_v`. -/
@[category API, AMS 11, ref "BG06", group "three_halves_m4"]
noncomputable def formBound {n : ℕ} (v : AbsoluteValue K ℝ)
    (L : Fin n → ((Fin n → K) →ₗ[K] K)) : ℝ :=
  ∏ i, ∑ j, v (L i fun k ↦ if j = k then 1 else 0)

omit [NumberField K] in
/-- **The local factor is bounded by the coefficients**: `∏ᵢ |L_i(x)|_v / ‖x‖_v ≤ formBound`,
by the triangle inequality, at any absolute value. -/
@[category API, AMS 11, ref "BG06", group "three_halves_m4"]
theorem localFactor_le {n : ℕ} (v : AbsoluteValue K ℝ) (L : Fin n → ((Fin n → K) →ₗ[K] K))
    (x : Fin n → K) : ∏ i, v (L i x) / localNorm v x ≤ formBound v L := by
  have hN : 0 ≤ localNorm v x := Real.iSup_nonneg fun _ ↦ v.nonneg _
  refine Finset.prod_le_prod₀ (fun i _ ↦ div_nonneg (v.nonneg _) hN) fun i _ ↦ ?_
  rcases hN.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact Finset.sum_nonneg fun _ _ ↦ v.nonneg _
  rw [div_le_iff₀ hpos, LinearMap.pi_apply_eq_sum_univ (L i) x, Finset.sum_mul]
  refine (v.sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [smul_eq_mul, map_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (le_ciSup (f := fun k ↦ v (x k)) (Finite.bddAbove_range _) j)
    (v.nonneg _)

open scoped Classical in
/-- **A product over a set of places, split by kind**: over the infinite places in `S` times over
the finite places in `S`.  The typed place sets are exactly the ones `Subspace-Theorems` takes. -/
@[category API, AMS 11, ref "BG06", group "three_halves_m4"]
theorem prod_eq_prod_places {S : Finset (AbsoluteValue K ℝ)} (hS : ∀ v ∈ S, IsPlace v)
    (f : AbsoluteValue K ℝ → ℝ) :
    ∏ v ∈ S, f v = (∏ w ∈ Finset.univ.filter (fun w : InfinitePlace K ↦ w.1 ∈ S), f w.1) *
      ∏ w ∈ S.preimage (fun w : FinitePlace K ↦ w.1) (fun _ _ _ _ h ↦ Subtype.ext h), f w.1 := by
  set Sinf : Finset (InfinitePlace K) := Finset.univ.filter fun w ↦ w.1 ∈ S with hSinf
  set Sfin : Finset (FinitePlace K) :=
    S.preimage (fun w ↦ w.1) (fun _ _ _ _ h ↦ Subtype.ext h) with hSfin
  let e₁ : InfinitePlace K ↪ AbsoluteValue K ℝ := ⟨fun w ↦ w.1, fun _ _ h ↦ Subtype.ext h⟩
  let e₂ : FinitePlace K ↪ AbsoluteValue K ℝ := ⟨fun w ↦ w.1, fun _ _ h ↦ Subtype.ext h⟩
  have hS' : S = Sinf.map e₁ ∪ Sfin.map e₂ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_map, hSinf, Finset.mem_filter,
      Finset.mem_univ, true_and, e₁, e₂]
    constructor
    · intro hv
      rcases hS v hv with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · exact Or.inl ⟨w, hv, rfl⟩
      · exact Or.inr ⟨w, Finset.mem_preimage.2 hv, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact hw
      · exact Finset.mem_preimage.1 hw
  have hdisj : Disjoint (Sinf.map e₁) (Sfin.map e₂) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 h1
    obtain ⟨u, -, hu⟩ := Finset.mem_map.1 h2
    exact infinitePlace_val_ne_finitePlace_val w u hu.symm
  rw [hS', Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
  rfl

open scoped Classical in
/-- **This file's product against `Subspace-Theorems`' one.**  Splitting `S` along `hS` into
infinite and finite places, the typed product `NumberField.approxProd` (complex places
squared) is at most `approxProduct S L x` (every place once) times a constant of the forms. -/
@[category API, AMS 11, ref "BG06", group "three_halves_m4"]
theorem approxProd_le_mul {n : ℕ} {S : Finset (AbsoluteValue K ℝ)} (hS : ∀ v ∈ S, IsPlace v)
    (L : AbsoluteValue K ℝ → Fin n → ((Fin n → K) →ₗ[K] K)) (x : Fin n → K) :
    NumberField.approxProd (Finset.univ.filter fun w : InfinitePlace K ↦ w.1 ∈ S)
        (S.preimage (fun w : FinitePlace K ↦ w.1) (fun _ _ _ _ h ↦ Subtype.ext h))
        (fun v ↦ v) L x
      ≤ approxProduct S L x * ∏ w ∈ Finset.univ.filter (fun w : InfinitePlace K ↦ w.1 ∈ S),
          max 1 (formBound w.1 (L w.1)) := by
  set Sinf : Finset (InfinitePlace K) := Finset.univ.filter fun w ↦ w.1 ∈ S with hSinf
  set Sfin : Finset (FinitePlace K) :=
    S.preimage (fun w ↦ w.1) (fun _ _ _ _ h ↦ Subtype.ext h) with hSfin
  set g : AbsoluteValue K ℝ → ℝ := fun v ↦ ∏ i, v (L v i x) / localNorm v x with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v ↦ Finset.prod_nonneg fun i _ ↦
    div_nonneg (v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  have hlhs : NumberField.approxProd Sinf Sfin (fun v ↦ v) L x
      = (∏ w ∈ Sinf, g w.1 ^ w.mult) * ∏ w ∈ Sfin, g w.1 := rfl
  have hsplit : approxProduct S L x = (∏ w ∈ Sinf, g w.1) * ∏ w ∈ Sfin, g w.1 :=
    prod_eq_prod_places hS g
  have hmult : ∀ w : InfinitePlace K, g w.1 ^ w.mult = g w.1 * g w.1 ^ (w.mult - 1) := by
    intro w
    by_cases hw : w.IsReal <;> simp [InfinitePlace.mult, hw, pow_two]
  have hsurplus : ∏ w ∈ Sinf, g w.1 ^ (w.mult - 1)
      ≤ ∏ w ∈ Sinf, max 1 (formBound w.1 (L w.1)) := by
    refine Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (hg0 _) _) fun w _ ↦ ?_
    by_cases hw : w.IsReal
    · rw [show w.mult - 1 = 0 by simp [InfinitePlace.mult, hw], pow_zero]
      exact le_max_left _ _
    · rw [show w.mult - 1 = 1 by simp [InfinitePlace.mult, hw], pow_one]
      exact (localFactor_le w.1 (L w.1) x).trans (le_max_right _ _)
  rw [hlhs, Finset.prod_congr rfl fun w _ ↦ hmult w, Finset.prod_mul_distrib, hsplit,
    mul_right_comm]
  exact mul_le_mul_of_nonneg_left hsurplus
    (mul_nonneg (Finset.prod_nonneg fun w _ ↦ hg0 w.1) (Finset.prod_nonneg fun w _ ↦ hg0 w.1))

open scoped Classical in
/-- **The Subspace Theorem**, Evertse–Schlickewei `S`-arithmetic *number-field*
form ([BG06] Ch. 7): for a number field `K`, `n ≥ 2`, a finite place set `S`,
per-place linearly independent linear forms `L` with coefficients in `K`, and
`ε > 0`, the nonzero `x ∈ Kⁿ` with `approxProduct S L x ≤ H(x)^{-n-ε}` — the
height being the one relative to `K` — lie in finitely many proper subspaces of
`Kⁿ`.

Derived from the sorry-free, std3 theorem
`NumberField.exists_finset_submodule_of_approxProd_le` of `Subspace-Theorems` ([BG06]
Thm 7.2.2 with `F = K`); see the module doc, *Derivation*.  The hypothesis `hS` (every
member of `S` is a place) is what makes the statement true; without it the former axiom was
inconsistent.  The finiteness is ineffective.  See the module doc for the encoding
conventions, for the two derived `ℚ`-consumers (`CZ.pseudoPisot_approx_of_subspace` at
`n = 2`, `TH.pairRepulsion_all` at `n = 3`, directly), and for why rational data with
algebraic coefficients needs the sibling axiom `Subspace.schmidt1D'` instead. -/
@[category research solved, AMS 11, ref "BG06" "Schmidt91", group "three_halves_m4"]
theorem evertseSchlickewei {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (AbsoluteValue K ℝ)) (hS : ∀ v ∈ S, IsPlace v)
    (L : AbsoluteValue K ℝ → Fin n → ((Fin n → K) →ₗ[K] K))
    (hL : ∀ v ∈ S, LinearIndependent K (L v))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (Fin n → K)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin n → K, x ≠ 0 →
        approxProduct S L x ≤ Height.mulHeight x ^ (-(n : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  set Sinf : Finset (InfinitePlace K) := Finset.univ.filter fun w ↦ w.1 ∈ S with hSinf
  set Sfin : Finset (FinitePlace K) :=
    S.preimage (fun w ↦ w.1) (fun a _ b _ h ↦ Subtype.ext h) with hSfin
  obtain ⟨T₁, hT₁, hcov₁⟩ := NumberField.exists_finset_submodule_of_approxProd_le Sinf Sfin L
    (fun v hv ↦ hL _ (Finset.mem_filter.1 hv).2) (fun v hv ↦ hL _ (Finset.mem_preimage.1 hv))
    (half_pos hε)
  -- the constant bounding the surplus factors of the complex places
  set C : ℝ := ∏ w ∈ Sinf, max 1 (formBound w.1 (L w.1)) with hCdef
  have hC0 : 0 < C := Finset.prod_pos fun w _ ↦ lt_of_lt_of_le one_pos (le_max_left _ _)
  have hkey : ∀ x : Fin n → K,
      NumberField.approxProd Sinf Sfin (fun v ↦ v) L x ≤ approxProduct S L x * C :=
    approxProd_le_mul hS L
  -- the lines of small height, by Northcott
  set Q₀ : ℝ := C ^ (2 / ε) with hQ₀
  have hNor : {P : Projectivization K (Fin n → K) | Projectivization.mulHeight P ≤ Q₀}.Finite :=
    Projectivization.finite_setOfPred_mulHeight_le Q₀
  set Tsmall : Finset (Submodule K (Fin n → K)) :=
    (hNor.image Projectivization.submodule).toFinset with hTsmall
  refine ⟨T₁ ∪ Tsmall, ?_, ?_⟩
  · intro W hW
    rcases Finset.mem_union.1 hW with hW | hW
    · exact hT₁ W hW
    · rw [hTsmall, Set.Finite.mem_toFinset] at hW
      obtain ⟨P, -, rfl⟩ := hW
      intro h
      have h1 : Module.finrank K P.submodule = 1 := by
        rw [Projectivization.submodule_eq]
        exact finrank_span_singleton P.rep_nonzero
      rw [h, finrank_top, Module.finrank_fin_fun] at h1
      omega
  · intro x hx happ
    rcases le_or_gt (Height.mulHeight x) Q₀ with hsmall | hlarge
    · refine ⟨(Projectivization.mk K x hx).submodule, Finset.mem_union_right _ ?_, ?_⟩
      · rw [hTsmall, Set.Finite.mem_toFinset]
        exact ⟨Projectivization.mk K x hx, by
          simpa [Projectivization.mulHeight_mk] using hsmall, rfl⟩
      · rw [Projectivization.submodule_mk]
        exact Submodule.mem_span_singleton_self x
    · -- at large height, `C ≤ H ^ (ε / 2)` absorbs the surplus factors
      have hH : 0 < Height.mulHeight x := lt_of_lt_of_le one_pos (Height.one_le_mulHeight x)
      have hCH : C ≤ Height.mulHeight x ^ (ε / 2) := by
        have h := Real.rpow_le_rpow (by positivity) hlarge.le (by positivity : 0 ≤ ε / 2)
        rwa [hQ₀, ← Real.rpow_mul hC0.le, show 2 / ε * (ε / 2) = 1 by field_simp,
          Real.rpow_one] at h
      have happ' : NumberField.approxProd Sinf Sfin (fun v ↦ v) L x
          ≤ Height.mulHeight x ^ (-(Fintype.card (Fin n) : ℝ) - ε / 2) :=
        calc NumberField.approxProd Sinf Sfin (fun v ↦ v) L x
            ≤ approxProduct S L x * C := hkey x
          _ ≤ Height.mulHeight x ^ (-(n : ℝ) - ε) * Height.mulHeight x ^ (ε / 2) :=
              mul_le_mul happ hCH hC0.le (by positivity)
          _ = Height.mulHeight x ^ (-(Fintype.card (Fin n) : ℝ) - ε / 2) := by
              rw [← Real.rpow_add hH, Fintype.card_fin]
              congr 1
              ring
      obtain ⟨W, hW, hxW⟩ := hcov₁ x hx happ'
      exact ⟨W, Finset.mem_union_left _ hW, hxW⟩

/-- The `K := ℚ` specialization of `evertseSchlickewei` — the form the program's
consumers use (`Γ = ⟨2,3⟩ ⊂ ℚ*`, places `{∞, 2, 3}`, rational-coefficient
forms). -/
@[category API, AMS 11, ref "Schmidt91", group "three_halves_m4"]
theorem evertseSchlickewei_rat {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (AbsoluteValue ℚ ℝ)) (hS : ∀ v ∈ S, IsPlace v)
    (L : AbsoluteValue ℚ ℝ → Fin n → ((Fin n → ℚ) →ₗ[ℚ] ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (Fin n → ℚ)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin n → ℚ, x ≠ 0 →
        approxProduct S L x ≤ Height.mulHeight x ^ (-(n : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  evertseSchlickewei hn S hS L hL ε hε

/-- The archimedean absolute value of `ℚ` is a place: that of `Rat.infinitePlace`. -/
@[category API, AMS 11, ref "Schmidt91", group "three_halves_m4"]
theorem isPlace_real : IsPlace Rat.AbsoluteValue.real :=
  Or.inl ⟨Rat.infinitePlace, AbsoluteValue.ext fun x ↦ by
    change Rat.infinitePlace x = |(x : ℝ)|
    rw [Rat.infinitePlace_apply, Rat.cast_abs]⟩

/-- The `p`-adic absolute value of `ℚ` is a place: that of `Rat.finitePlace`. -/
@[category API, AMS 11, ref "Schmidt91", group "three_halves_m4"]
theorem isPlace_padic (p : ℕ) [Fact p.Prime] : IsPlace (Rat.AbsoluteValue.padic p) :=
  Or.inr (Rat.exists_finitePlace_val_eq_padic p)

/-- The place set `{2, 3}` of the program's consumers. -/
@[category API, AMS 11, ref "Schmidt91", group "three_halves_m4"]
theorem isPlace_padic_two_three [DecidableEq (AbsoluteValue ℚ ℝ)] [Fact (Nat.Prime 3)] :
    ∀ v ∈ ({Rat.AbsoluteValue.padic 2, Rat.AbsoluteValue.padic 3} :
      Finset (AbsoluteValue ℚ ℝ)), IsPlace v := by
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact isPlace_padic 2
  · exact isPlace_padic 3

/-- The place set `{∞, 2, 3}` of the program's consumers. -/
@[category API, AMS 11, ref "Schmidt91", group "three_halves_m4"]
theorem isPlace_real_padic_two_three [DecidableEq (AbsoluteValue ℚ ℝ)] [Fact (Nat.Prime 3)] :
    ∀ v ∈ ({Rat.AbsoluteValue.real, Rat.AbsoluteValue.padic 2, Rat.AbsoluteValue.padic 3} :
      Finset (AbsoluteValue ℚ ℝ)), IsPlace v := by
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact isPlace_real
  · exact isPlace_padic 2
  · exact isPlace_padic 3

end Subspace
