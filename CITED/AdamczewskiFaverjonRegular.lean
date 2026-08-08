/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonProof
import CITED.AdamczewskiFaverjonPrimitive
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF17] Lemme 2.2: the solution field of a Mahler system is a regular extension

plan-formalize-AF17's **WP8-bis**, and the **one cited axiom of Stage 2**.

[AF22] §2.4 splits a lifted linear relation `Q(z, f(z)) = 0`, whose coefficients are polynomials in
`z` *and* in a primitive element `ϕ` of the relation matrix, into one relation per power of `ϕ`.
That step is linear disjointness, and linear disjointness comes from **regularity** of
`K(z)(f₁,…,f_n)` over `K(z)` — in characteristic zero, exactly `algebraicClosure K(z) L = ⊥`.

Gate G5 (plan §2.9) took this requirement apart into three layers and cut at the middle one:

| layer | statement | status |
|---|---|---|
| top | regular ⇒ linearly disjoint ⇒ the relation splits | **proved**, `ForMathlib/FieldTheory/RegularExtension.lean`, and consumed here through `AF.linearForm_split_solField` |
| **middle** | **[AF17] Lemme 2.2**: `K(z)(f)/K(z)` is regular, for `f` a solution of a linear `q`-Mahler system | **cited — this file** |
| bottom | an algebraic `q`-Mahler function is rational ([Nis96] Thm 5.1.7) | out of reach; its proof is analytic |

## The proof that is being cited, and where it stops

[AF17] p. 10 (arXiv v2), four steps. (i) `L = K(z)(f)` is finitely generated over `K(z)`, hence so
is every subextension — **[Lan02] Chap. VIII, Exercise 4**, which Mathlib does not have: it has
`IntermediateField.FG` and `algebraicClosure F E` and nothing joining them. (ii) So `L'`, the
relative algebraic closure of `K(z)` in `L`, is algebraic *and* finitely generated, hence finite,
say of degree `d`. (iii) The system makes `L` stable under `z ↦ z^q`, so for `g ∈ L'` all iterates
`g(z^{q^ℓ})` lie in `L'`; `d+1` of them are `K(z)`-linearly dependent, i.e. `g` is `q`-Mahlerian.
(iv) Algebraic + Mahlerian ⇒ rational, the bottom layer, so `L' = K(z)`.

Step (i) is the obstacle, and it is why the cut is here: proving Lemme 2.2 would mean formalizing
a piece of the theory of finitely generated field extensions first. Step (iii)'s pigeonhole is six
lines (gate G5, probe 6) and contains nothing Mahler-specific.

**The bottom layer is on disk.** [Nis96] is not, but [Ran92] (`RandeDiss.pdf`) proves it in full:
**Thm 4.3** — a function meromorphic on the unit disc satisfying `∑_k a_k u(z^{q^k}) = 0` with
`a_k ∈ ℂ(z)` not all zero and `u ∉ ℂ(z)` has the unit circle as a natural boundary — with
**Corollaire 1** (hence `u` is transcendental over `ℂ(z)`) and **Corollaire 2** (the same for
`f ∈ ℂ[[z]]`). Two classical bridges separate that from [AF17]'s use — Randé works over `ℂ` and
with functions meromorphic on the unit disc — and both are internal to the cited statement.

**Numbering trap.** [AF22] cite this as «[1, Lemme 3.2]», the published PLMS numbering. In the
arXiv v2 on disk it is **Lemme 2.2**, p. 10; that paper's own Lemme 3.2 is an unrelated
linear-algebra statement quoted from [BBC15].

## The shape of the axiom, and two departures from the plan

Plan risk **R13** demands that the axiom acquire no analytic hypothesis it does not need: it is a
statement about one field extension, and phrasing it over germs or over analytic functions on a
disc would re-import the difficulty gate G3 removed. So the system is stated **formally**, on
`PowerSeries K` (`AF.IsFormalMahlerSolution`), and the solution field is taken inside
`LaurentSeries K` — the shape gate G5's probe 7 fixed.

Two things that shape needs and the plan's sketch did not record:

* **`[CharZero K]` is essential, not decoration.** In characteristic `p` the statement is *false*:
  by Christol's theorem the algebraic power series over `𝔽_p(z)` are exactly the `p`-automatic ones,
  and those satisfy Mahler equations, so `L'` is large. The whole weight of the bottom layer is
  carried by characteristic zero.
* **No convergence hypothesis is needed**, even though [AF17] state Lemme 2.2 for
  `f_i ∈ ℚ̄{z}`. The bottom layer is applied only to elements `g` of the relative algebraic
  closure `L'`, and those are *algebraic* over `K(z)`, hence automatically given by convergent
  series; the `f_i` themselves are never required to converge. This is what makes the purely formal
  statement below the right one to cite rather than a strengthening of it.

## The axiom is in a shape the corpus can feed

`AF.isFormalMahlerSolution_iff_expand` puts the system in the shape gate G4's files use, and with
it both non-trivial hypotheses of the axiom are supplied by theorems the corpus already has.  This
was checked out of tree — `CITED/` must not import `RB/`, the dependency runs the other way — and
both of the following compile against the pinned toolchain:

```
theorem _ {q} (hq : 2 ≤ q) {A} {F} (hsys : AF.IsFormalMahlerSolution q A F) :
    AF.IsRegularSolField K fun i => ((F i : PowerSeries K) : LaurentSeries K) := by
  obtain ⟨A', hdet, hsys'⟩ := RB.exists_det_ne_zero_of_mahlerSystem hq (by omega)
    ((AF.isFormalMahlerSolution_iff_expand (by omega) A F).1 hsys)
  exact AF.lemme_2_2 hq hdet ((AF.isFormalMahlerSolution_iff_expand (by omega) A' F).2 hsys')
```

— so `det A ≠ 0` costs nothing, being **repaired** by `RB.exists_det_ne_zero_of_mahlerSystem` (gate
G4); it is kept as a hypothesis here because a weaker axiom is a safer one.  And
`RB.mahlerSystem_formal` produces the system itself from a kernel model of an automatic sequence,
so the chain runs from `RB.IsKernelModel` to `AF.IsRegularSolField` with the axiom as its only
non-`std3` step.

## What this file adds beyond the axiom

* `AF.isRegularSolField_map` — regularity travels along any `K(z)`-algebra homomorphism of ambient
  fields, because `algebraicClosure K(z) L = ⊥` is a property of the abstract field `L` and
  `IntermediateField.adjoin` commutes with the map. This is what carries the axiom from
  `LaurentSeries K`, where it is stated, to the ambient field of [AF22] §2.4, where it is used.
* `AF.isRegularSolField_of_formalMahler` — the two combined, in the ambient shape.
* `AF.linearForm_split_of_formalMahler` — the splitting of §2.4 with regularity discharged, which
  machine-checks that the axiom is in a shape `AF.exists_lift` can consume.

## References

* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* Proc. LMS 115 (2017) 55–90; arXiv:1508.07158v2, Lemme 2.2
  (p. 10) — cited by [AF22] as «[1, Lemme 3.2]».
* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.4.
* [Ran92] B. Randé. *Équations fonctionnelles de Mahler et applications aux suites p-régulières.*
  Thèse, Univ. Bordeaux I (1992), §4: Thm 4.3, Corollaires 1–2 (`RandeDiss.pdf`, on disk).
* [Nis96] Ku. Nishioka. *Mahler functions and transcendence.* LNM 1631, Springer 1997, Thm 5.1.7.
* [Lan02] S. Lang. *Algebra*, 3rd ed., GTM 211, Chap. VIII, Exercise 4.
* [AF17f] `plans/plan-formalize-AF17.html`: WP8-bis, gate G5 (§2.9), risk R13.
-/

open scoped LaurentSeries Polynomial RatFunc

namespace AF

/-! ## The formal Mahler system -/

section FormalSystem

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- **A linear `q`-Mahler system, formally**: `f(z) = A(z)·f(z^q)` read in `K⟦z⟧`, with `A` a matrix
of polynomials.  [AF17]'s systems of type (1.2), with no analysis in the statement — `AF.substPowSeries`
is the substitution `z ↦ z^q` on power series (`CITED/AdamczewskiFaverjonProof`). -/
@[category API, AMS 11 30 39, ref "AF17", group "af_mahler_alternative"]
def IsFormalMahlerSolution (q : ℕ) (A : Matrix ι ι K[X]) (F : ι → PowerSeries K) : Prop :=
  ∀ i, F i = ∑ j, (A i j : PowerSeries K) * substPowSeries q (F j)

/-- **The corpus's own Mahler systems are of this shape.**  `AF.substPowSeries` is Mathlib's
`PowerSeries.expand` (the identity `RB.substPowSeries_eq_expand` records for the substitution
itself), so a system written with `PowerSeries.expand` — the shape `RB.mahlerSystem_formal`
produces and `RB.exists_det_ne_zero_of_mahlerSystem` consumes and repairs — is a
`AF.IsFormalMahlerSolution`.  This is what makes the axiom below usable: gate G4's repair theorem
supplies *both* of its non-trivial hypotheses, the system and `det A ≠ 0`. -/
@[category API, AMS 11 30 39, ref "AF17", group "af_mahler_alternative"]
theorem isFormalMahlerSolution_iff_expand {q : ℕ} (hq0 : q ≠ 0) (A : Matrix ι ι K[X])
    (F : ι → PowerSeries K) :
    IsFormalMahlerSolution q A F ↔
      ∀ i, F i = ∑ j, (A i j : PowerSeries K) * PowerSeries.expand q hq0 (F j) := by
  have hsub : ∀ f : PowerSeries K, substPowSeries q f = PowerSeries.expand q hq0 f := by
    intro f
    ext n
    rw [substPowSeries, PowerSeries.coeff_mk, PowerSeries.coeff_expand]
  simp only [IsFormalMahlerSolution, hsub]

end FormalSystem

/-! ## The cited axiom -/

section Axiom

/-- **[AF17] Lemme 2.2 — the cited axiom of Stage 2.**  *«Soient `f₁,…,f_n` des solutions d'un
système mahlérien de type (1.2).  Alors l'extension `ℚ̄(z)(f₁,…,f_n)/ℚ̄(z)` est régulière.»*

In characteristic zero «regular» is exactly «`K(z)` is relatively algebraically closed», which is
Mathlib's `algebraicClosure (RatFunc K) ↥(AF.solField K f) = ⊥` — the predicate
`AF.IsRegularSolField` of `CITED/AdamczewskiFaverjonPrimitive`.

The hypotheses are those of [AF17]'s (1.2) and nothing more: the base field has characteristic
zero (**essential** — see the module doc: in characteristic `p` the statement fails by Christol's
theorem), the system is `q`-Mahlerian with `q ≥ 2`, and its matrix is invertible over `K(z)`, which
is what makes the solution field stable under `z ↦ z^q` in step (iii) of the cited proof.

No analysis appears, no convergence is assumed of the `fᵢ`, and no Puiseux or germ construction is
involved: the statement is about a single field extension.  Its literature proof chain is recorded
in the module doc; the one step of it that Mathlib cannot yet supply is [Lan02] Chap. VIII Ex. 4. -/
@[category research solved, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
axiom lemme_2_2 {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (hq : 2 ≤ q)
    {A : Matrix ι ι K[X]} (hA : A.det ≠ 0) {F : ι → PowerSeries K}
    (hF : IsFormalMahlerSolution q A F) :
    IsRegularSolField K fun i => ((F i : PowerSeries K) : LaurentSeries K)

end Axiom

/-! ## Regularity travels along a homomorphism of ambient fields -/

section Transport

variable {K : Type*} [Field K]

/-- `algebraicClosure F E = ⊥` is a property of the abstract field `E`: it transports along any
`F`-algebra isomorphism.  Mathlib has the pointwise half (`map_mem_algebraicClosure_iff`); this is
the statement about the intermediate field. -/
@[category API, AMS 12, ref "AF17", group "af_mahler_alternative"]
theorem algebraicClosure_eq_bot_of_algEquiv {F E₁ E₂ : Type*} [Field F] [Field E₁] [Field E₂]
    [Algebra F E₁] [Algebra F E₂] (e : E₁ ≃ₐ[F] E₂) (h : algebraicClosure F E₁ = ⊥) :
    algebraicClosure F E₂ = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have h1 : e.symm x ∈ algebraicClosure F E₁ :=
    (map_mem_algebraicClosure_iff (e.symm : E₂ →ₐ[F] E₁)).2 hx
  rw [h, IntermediateField.mem_bot] at h1
  obtain ⟨y, hy⟩ := h1
  refine IntermediateField.mem_bot.2 ⟨y, ?_⟩
  have := congrArg e hy
  rwa [AlgEquiv.apply_symm_apply, AlgEquiv.commutes] at this

/-- **The solution field of the image is the image of the solution field.** -/
@[category API, AMS 11 12, ref "AF17", group "af_mahler_alternative"]
theorem solField_map {Ω₁ Ω₂ : Type*} [Field Ω₁] [Field Ω₂] [Algebra (RatFunc K) Ω₁]
    [Algebra (RatFunc K) Ω₂] (ψ : Ω₁ →ₐ[RatFunc K] Ω₂) {ι : Type*} (f : ι → Ω₁) :
    solField K (fun i => ψ (f i)) = (solField K f).map ψ := by
  rw [solField, solField, IntermediateField.adjoin_map]
  congr 1
  rw [← Set.range_comp]
  rfl

/-- **Regularity of the solution field is ambient-independent.**  This is what carries [AF17]
Lemme 2.2 from `LaurentSeries K`, where `AF.lemme_2_2` states it, to the ambient field of
[AF22] §2.4, where `AF.exists_lift` consumes it. -/
@[category research solved, AMS 11 12, ref "AF17", group "af_mahler_alternative"]
theorem isRegularSolField_map {Ω₁ Ω₂ : Type*} [Field Ω₁] [Field Ω₂] [Algebra (RatFunc K) Ω₁]
    [Algebra (RatFunc K) Ω₂] (ψ : Ω₁ →ₐ[RatFunc K] Ω₂) {ι : Type*} {f : ι → Ω₁}
    (h : IsRegularSolField K f) : IsRegularSolField K fun i => ψ (f i) := by
  refine algebraicClosure_eq_bot_of_algEquiv
    (((solField K f).equivMap ψ).trans
      (IntermediateField.equivOfEq (solField_map ψ f).symm)) h

end Transport

/-! ## The axiom in the shape §2.4 consumes -/

section Consume

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [Field Ω] [Algebra (RatFunc K) Ω] [Algebra (LaurentSeries K) Ω]
  [IsScalarTower (RatFunc K) (LaurentSeries K) Ω]

/-- **[AF17] Lemme 2.2 in the ambient field.**  The axiom, transported along the structure map
`K⸨z⸩ → Ω`; `Ω` is [AF22] §2.4's algebraically closed extension containing both the solutions and
the relation matrix (`CITED/AdamczewskiFaverjonPrimitive`, plan §2.10). -/
@[category research solved, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
theorem isRegularSolField_of_formalMahler {q : ℕ} (hq : 2 ≤ q) {A : Matrix ι ι K[X]}
    (hA : A.det ≠ 0) {F : ι → PowerSeries K} (hF : IsFormalMahlerSolution q A F) :
    IsRegularSolField K fun i =>
      algebraMap (LaurentSeries K) Ω ((F i : PowerSeries K) : LaurentSeries K) :=
  isRegularSolField_map (IsScalarTower.toAlgHom (RatFunc K) (LaurentSeries K) Ω)
    (lemme_2_2 hq hA hF)

/-- **The splitting of [AF22] §2.4, with regularity discharged.**  `AF.linearForm_split_solField`
takes regularity as a hypothesis; here it is supplied by the cited axiom.  This is the machine
check that `AF.lemme_2_2` is stated in a shape §2.4 can consume — the tower
`K(z) → K⸨z⸩ → Ω` is found by instance search, with no plumbing. -/
@[category research solved, AMS 11 12 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem linearForm_split_of_formalMahler {q : ℕ} (hq : 2 ≤ q) {A : Matrix ι ι K[X]}
    (hA : A.det ≠ 0) {F : ι → PowerSeries K} (hF : IsFormalMahlerSolution q A F)
    {x : Ω} (hx : IsIntegral (RatFunc K) x) {δ : ℕ}
    (hδ : δ ≤ (minpoly (RatFunc K) x).natDegree) (w : ι → ℕ → RatFunc K)
    (hrel : ∑ i, (∑ j ∈ Finset.range δ, algebraMap (RatFunc K) Ω (w i j) * x ^ j) *
      algebraMap (LaurentSeries K) Ω ((F i : PowerSeries K) : LaurentSeries K) = 0) :
    ∀ j ∈ Finset.range δ, ∑ i, algebraMap (RatFunc K) Ω (w i j) *
      algebraMap (LaurentSeries K) Ω ((F i : PowerSeries K) : LaurentSeries K) = 0 :=
  linearForm_split_solField K (isRegularSolField_of_formalMahler hq hA hF) hx hδ w hrel

end Consume

end AF
