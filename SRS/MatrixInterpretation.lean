/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.Interpretation
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Natural matrix interpretations (EWZ08)

A concrete recipe for building the (weakly / extended) monotone Σ-algebras of `Definition 2.14`
(`StringRewriting.WeaklyMonotoneAlgebra` / `ExtendedMonotoneAlgebra`): **natural matrix
interpretations** ([EWZ08]). Fix a dimension `d ∈ ℕ⁺`, take the carrier `A = ℕᵈ` (`Fin d → ℕ`), and
interpret each symbol by an **affine** map
`[σ](x) = Mₛ x + vₛ`, with `Mₛ` a `d × d` matrix over `ℕ` and `vₛ ∈ ℕᵈ`. The two order relations on
`ℕᵈ` are

* `StringRewriting.MatrixInterpretation.vecGt` (`>`): strict in the **first** coordinate and weak in
  the rest — `x > y ↔ y₀ < x₀ ∧ x ≳ y`;
* `StringRewriting.MatrixInterpretation.vecGe` (`≳`): the pointwise order `∀ i, yᵢ ≤ xᵢ`.

`>` is well-founded (the first coordinate is a strictly decreasing `ℕ`-measure,
`vecGt_wf`) and `> · ≳ ⊆ >` holds (`vecGt_compat`). Since the matrix entries are natural numbers,
every affine map is `≳`-monotone (`affine_vecGe`), so the structure is always a **weakly** monotone
algebra (`weaklyMonotoneAlgebra`). Requiring `(Mₛ)₀₀ = 1` for every symbol makes each affine map
strictly increase the first coordinate whenever its input does (`affine_vecGt`), upgrading it to an
**extended** monotone algebra (`extendedMonotoneAlgebra`).

Composed with `Theorem 2.15` (`StringRewriting.theorem_2_15_relative` /
`theorem_2_15_top`) this is the basis of the *matrix-interpretation* method for proving
(relative / top) termination of string rewriting automatically: search for matrices `Mₛ` and vectors
`vₛ` making every rule decrease.

**Checking the conditions is decidable** ([EWZ08, Lemma 4]). The composition of affine maps is
affine (`affine_comp`), so the interpretation `[s]` of *every* string — in particular of each rule
side — is itself affine (`strInterp_affine`). Comparing two affine interpretations over *all* of
`ℕᵈ` then reduces to a finite **entrywise** comparison of their matrices and constant vectors
(`matGe`): this is equation (2), `affine_vecGt_iff` (`[ℓ] > [r]` everywhere `↔ Mℓ ≳ Mᵣ ∧ vℓ > vᵣ`)
and `affine_vecGe_iff` (`[ℓ] ≳ [r]` everywhere `↔ Mℓ ≳ Mᵣ ∧ vℓ ≳ vᵣ`). Consequently the rule
conditions of Theorem 2.15 are decidable (`decidableAffineVecGt` / `decidableAffineVecGe`), so one
can algorithmically check whether a candidate matrix interpretation proves termination.

**Example 2.16** (`terminating_R_relative_S_matrix`) runs the method end to end on `R = {aa → aba}`,
`S = {b → bb}` (Example 2.5): the matrices `Mₐ = !![1,1;0,0]`, `M_b = !![1,0;0,0]` with vectors
`vₐ = ![0,1]`, `v_b = ![0,0]` give an extended monotone algebra in which the `R`-rule strictly
decreases and the `S`-rule weakly decreases, reproving `SN(R / S)` via Theorem 2.15.

## References
* [EWZ08] Endrullis, Jörg, Waldmann, Johannes, and Zantema, Hans. "Matrix interpretations for
  proving termination of term rewriting." *Journal of Automated Reasoning* 40.2–3 (2008), 195–220.
-/

namespace StringRewriting.MatrixInterpretation

open Matrix

variable {α : Type*} {d : ℕ}

/-- The quasi-order `≳` on `ℕᵈ` of the matrix-interpretation method: the **pointwise** order,
`x ≳ y ↔ yᵢ ≤ xᵢ` for every coordinate `i`. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation"]
def vecGe (x y : Fin d → ℕ) : Prop := ∀ i, y i ≤ x i

/-- The well-founded order `>` on `ℕᵈ` of the matrix-interpretation method: **strict in the first
coordinate, weak in the rest** — `x > y ↔ y₀ < x₀ ∧ x ≳ y`. (Requires `d ≠ 0` for the coordinate
`0` to exist.) -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation"]
def vecGt [NeZero d] (x y : Fin d → ℕ) : Prop := y 0 < x 0 ∧ vecGe x y

/-- `>` is **well-founded**: the first coordinate `x ↦ x₀` is a strictly decreasing `ℕ`-measure
along it, so there is no infinite `>`-descending chain. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation", formal_uses terminating_of_measure]
theorem vecGt_wf [NeZero d] : Terminating (vecGt : (Fin d → ℕ) → (Fin d → ℕ) → Prop) :=
  terminating_of_measure (fun x => x 0) (fun _ _ h => h.1)

/-- Compatibility `> · ≳ ⊆ >`: a strict step `a > b` followed by a weak step `b ≳ c` is again
strict, `a > c`. (First coordinate: `c₀ ≤ b₀ < a₀`; other coordinates by transitivity of `≤`.) -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation"]
theorem vecGt_compat [NeZero d] (a b c : Fin d → ℕ) (hab : vecGt a b) (hbc : vecGe b c) :
    vecGt a c :=
  ⟨lt_of_le_of_lt (hbc 0) hab.1, fun i => le_trans (hbc i) (hab.2 i)⟩

/-- The **affine interpretation** `[σ](x) = M x + v` of a symbol: matrix–vector product plus a
constant vector, over `ℕ`. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation"]
def affine (M : Matrix (Fin d) (Fin d) ℕ) (v x : Fin d → ℕ) : Fin d → ℕ := M *ᵥ x + v

/-- Matrix–vector product is **monotone** in the vector (coordinatewise): natural-number entries are
nonnegative, so `y ≤ x` (pointwise) gives `M y ≤ M x` (pointwise). -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation"]
theorem mulVec_mono (M : Matrix (Fin d) (Fin d) ℕ) {x y : Fin d → ℕ}
    (h : ∀ j, y j ≤ x j) (i : Fin d) : (M *ᵥ y) i ≤ (M *ᵥ x) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul le_rfl (h j)

/-- Every affine interpretation is **`≳`-monotone**: `x ≳ y → [σ]x ≳ [σ]y` (the constant `v`
cancels and `M` is coordinatewise monotone). This holds for *all* natural matrices — hence any
choice of `M, v` yields a weakly monotone algebra. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation", formal_uses mulVec_mono]
theorem affine_vecGe (M : Matrix (Fin d) (Fin d) ℕ) (v : Fin d → ℕ) {x y : Fin d → ℕ}
    (h : vecGe x y) : vecGe (affine M v x) (affine M v y) := fun i => by
  simp only [affine, Pi.add_apply]
  exact Nat.add_le_add_right (mulVec_mono M h i) (v i)

/-- If the top-left entry is `(M)₀₀ = 1`, the affine interpretation is **`>`-monotone**:
`x > y → [σ]x > [σ]y`. The other coordinates are handled by `≳`-monotonicity; the first
coordinate `∑ⱼ M₀ⱼ xⱼ` is strict because the `j = 0` term contributes `1 · x₀ > 1 · y₀` while the
rest are `≥`. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation", formal_uses affine_vecGe]
theorem affine_vecGt [NeZero d] (M : Matrix (Fin d) (Fin d) ℕ) (v : Fin d → ℕ)
    (hM : M 0 0 = 1) {x y : Fin d → ℕ} (h : vecGt x y) :
    vecGt (affine M v x) (affine M v y) := by
  refine ⟨?_, affine_vecGe M v h.2⟩
  simp only [affine, Pi.add_apply]
  apply Nat.add_lt_add_right
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_lt_sum (fun j _ => Nat.mul_le_mul le_rfl (h.2 j)) ⟨0, Finset.mem_univ 0, ?_⟩
  rw [hM, one_mul, one_mul]
  exact h.1

/-- **Natural matrix interpretations give a weakly monotone algebra** ([EWZ08]). For any choice of
natural matrices `Mₛ` and constant vectors `vₛ`, the affine interpretations `[σ]x = Mₛ x + vₛ` over
the carrier `ℕᵈ`, with the orders `vecGt`/`vecGe`, form a `WeaklyMonotoneAlgebra`. No condition on
the matrices is needed. -/
@[category research solved, AMS 68, ref "EWZ08", group "matrix_interpretation",
  formal_uses WeaklyMonotoneAlgebra vecGt_wf vecGt_compat affine_vecGe]
def weaklyMonotoneAlgebra [NeZero d] (M : α → Matrix (Fin d) (Fin d) ℕ)
    (v : α → Fin d → ℕ) : WeaklyMonotoneAlgebra α (Fin d → ℕ) where
  den := fun σ => affine (M σ) (v σ)
  gt := vecGt
  ge := vecGe
  gt_wf := vecGt_wf
  compat := vecGt_compat
  mono_ge := fun σ _ _ h => affine_vecGe (M σ) (v σ) h

/-- **Natural matrix interpretations with `(Mₛ)₀₀ = 1` give an extended monotone algebra**
([EWZ08]). Requiring the top-left entry of every symbol's matrix to be `1` makes every affine
interpretation `>`-monotone, upgrading `weaklyMonotoneAlgebra` to an `ExtendedMonotoneAlgebra`. -/
@[category research solved, AMS 68, ref "EWZ08", group "matrix_interpretation",
  formal_uses ExtendedMonotoneAlgebra weaklyMonotoneAlgebra affine_vecGt]
def extendedMonotoneAlgebra [NeZero d] (M : α → Matrix (Fin d) (Fin d) ℕ)
    (v : α → Fin d → ℕ) (hM : ∀ σ, M σ 0 0 = 1) : ExtendedMonotoneAlgebra α (Fin d → ℕ) where
  toWeaklyMonotoneAlgebra := weaklyMonotoneAlgebra M v
  mono_gt := fun σ _ _ h => affine_vecGt (M σ) (v σ) (hM σ) h

/-! ### Checking the conditions: equation (2) and decidability ([EWZ08, Lemma 4])

Because the composition of affine maps is affine, the interpretation `[s]` of any string — in
particular a rule side `ℓ` or `r` — is again affine, `[s] = Mₛ x + vₛ`. Comparing two affine
interpretations *pointwise over all of `ℕᵈ`* (the rule conditions of Theorem 2.15) then reduces to a
**finite entrywise** comparison of the matrices and constant vectors (equation (2)), making the
check decidable. -/

/-- **Composition of affine maps is affine.** Composing `affine B b` after `affine A a` gives the
affine map with matrix `B * A` and constant vector `B *ᵥ a + b`, since
`B (A x + a) + b = (B A) x + (B a + b)`. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation"]
theorem affine_comp (B A : Matrix (Fin d) (Fin d) ℕ) (b a : Fin d → ℕ) :
    affine B b ∘ affine A a = affine (B * A) (B *ᵥ a + b) := by
  funext x
  simp only [affine, Function.comp_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  rw [add_assoc]

/-- **Every string interpretation is affine** ([EWZ08]). Since composition of affine maps is affine
(`affine_comp`), for a per-symbol affine interpretation `den σ = [σ] = affine (M σ) (v σ)` the
interpretation `[s]` of *any* string `s ∈ Σ*` is itself affine: there are a matrix `Mₛ` and a vector
`vₛ` with `[s] = affine Mₛ vₛ` (empty string: `Mₛ = 1`, `vₛ = 0`; cons: multiply the matrices and
transport the constant). This is why the conditions of Theorem 2.15 — stated on the string sides
`ℓ, r` of the rules — reduce to comparisons of affine maps. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation", formal_uses affine_comp]
theorem strInterp_affine (Mσ : α → Matrix (Fin d) (Fin d) ℕ) (vσ : α → Fin d → ℕ) (s : List α) :
    ∃ (M : Matrix (Fin d) (Fin d) ℕ) (v : Fin d → ℕ),
      strInterp (fun σ => affine (Mσ σ) (vσ σ)) s = affine M v := by
  induction s with
  | nil => exact ⟨1, 0, by funext x; simp [strInterp, affine]⟩
  | cons σ t ih =>
    obtain ⟨M, v, hMv⟩ := ih
    refine ⟨Mσ σ * M, Mσ σ *ᵥ v + vσ σ, ?_⟩
    simp only [strInterp]
    rw [hMv, affine_comp]

/-- The **matrix order `≳`** of equation (2): extend the pointwise vector order `vecGe` to `d × d`
natural matrices entrywise, `M ≳ N ↔ Nᵢⱼ ≤ Mᵢⱼ` for all `i, j`. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation"]
def matGe (M N : Matrix (Fin d) (Fin d) ℕ) : Prop := ∀ i j, N i j ≤ M i j

/-- Entrywise matrix dominance is preserved by the matrix–vector product over `ℕ`:
`M ≳ N → (N x)ᵢ ≤ (M x)ᵢ` for every (nonnegative) vector `x` and coordinate `i`. Companion to
`mulVec_mono`, which instead fixes the matrix and varies the vector. -/
@[category API, AMS 68, ref "EWZ08", group "matrix_interpretation"]
theorem matGe_mulVec {M N : Matrix (Fin d) (Fin d) ℕ} (h : matGe M N) (x : Fin d → ℕ) (i : Fin d) :
    (N *ᵥ x) i ≤ (M *ᵥ x) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul (h i j) le_rfl

/-- **Equation (2), weak form** ([EWZ08, Lemma 4]). Two affine interpretations satisfy
`[ℓ](x) ≳ [r](x)` for **all** `x ∈ ℕᵈ` **iff** the matrices and constant vectors compare entrywise,
`Mℓ ≳ Mᵣ ∧ vℓ ≳ vᵣ`. (`⇐`: add the two dominances coordinatewise. `⇒`: read off `vℓ ≳ vᵣ` at
`x = 0`, and recover `Mℓ ≳ Mᵣ` by probing with `x = (vℓ ᵢ + 1)·eⱼ` — were `(Mℓ)ᵢⱼ < (Mᵣ)ᵢⱼ` it
would force `vℓ ᵢ + 1 ≤ vℓ ᵢ`.) The quantifier over the infinite set `ℕᵈ` thus collapses to a
finite, decidable check (`decidableAffineVecGe`). -/
@[category research solved, AMS 68, ref "EWZ08", group "matrix_interpretation",
  formal_uses matGe_mulVec]
theorem affine_vecGe_iff (Mℓ Mᵣ : Matrix (Fin d) (Fin d) ℕ) (vℓ vᵣ : Fin d → ℕ) :
    (matGe Mℓ Mᵣ ∧ vecGe vℓ vᵣ) ↔ ∀ x, vecGe (affine Mℓ vℓ x) (affine Mᵣ vᵣ x) := by
  have hval : ∀ (P : Matrix (Fin d) (Fin d) ℕ) (j i : Fin d) (T : ℕ),
      (P *ᵥ Pi.single j T) i = P i j * T := fun P j i T => by simp [Matrix.mulVec_single]
  constructor
  · rintro ⟨hM, hv⟩ x i
    simp only [affine, Pi.add_apply]
    exact Nat.add_le_add (matGe_mulVec hM x i) (hv i)
  · intro H
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · have h := H (Pi.single j (vℓ i + 1)) i
      simp only [affine, Pi.add_apply, hval] at h
      nlinarith [h]
    · have h := H 0 i
      simp only [affine, Pi.add_apply, Matrix.mulVec_zero, Pi.zero_apply, zero_add] at h
      exact h

/-- **Equation (2), strict form** ([EWZ08, Lemma 4]). Two affine interpretations satisfy
`[ℓ](x) > [r](x)` for **all** `x ∈ ℕᵈ` **iff** `Mℓ ≳ Mᵣ ∧ vℓ > vᵣ` — the matrices dominate
entrywise and the constant vectors compare in the strict vector order `>` (strict in the first
coordinate, weak in the rest). The matrix-and-weak-vector part is the weak form `affine_vecGe_iff`;
the strict first coordinate comes from evaluating at `x = 0`, where `[ℓ](0) = vℓ` and `[r](0) = vᵣ`.
Again the `∀ x ∈ ℕᵈ` condition becomes a finite decidable check (`decidableAffineVecGt`). -/
@[category research solved, AMS 68, ref "EWZ08", group "matrix_interpretation",
  formal_uses affine_vecGe_iff matGe_mulVec]
theorem affine_vecGt_iff [NeZero d] (Mℓ Mᵣ : Matrix (Fin d) (Fin d) ℕ) (vℓ vᵣ : Fin d → ℕ) :
    (matGe Mℓ Mᵣ ∧ vecGt vℓ vᵣ) ↔ ∀ x, vecGt (affine Mℓ vℓ x) (affine Mᵣ vᵣ x) := by
  constructor
  · rintro ⟨hM, hv⟩ x
    refine ⟨?_, (affine_vecGe_iff Mℓ Mᵣ vℓ vᵣ).mp ⟨hM, hv.2⟩ x⟩
    simp only [affine, Pi.add_apply]
    exact add_lt_add_of_le_of_lt (matGe_mulVec hM x 0) hv.1
  · intro H
    obtain ⟨hM, hvge⟩ := (affine_vecGe_iff Mℓ Mᵣ vℓ vᵣ).mpr (fun x => (H x).2)
    refine ⟨hM, ?_, hvge⟩
    have h := (H 0).1
    simp only [affine, Pi.add_apply, Matrix.mulVec_zero, Pi.zero_apply, zero_add] at h
    exact h

/-- The vector order `vecGe` is decidable — a finite conjunction of `≤` over the `d` coordinates. -/
instance decVecGe (x y : Fin d → ℕ) : Decidable (vecGe x y) := by unfold vecGe; infer_instance

/-- The matrix order `matGe` is decidable — a finite entrywise check. -/
instance decMatGe (M N : Matrix (Fin d) (Fin d) ℕ) : Decidable (matGe M N) := by
  unfold matGe; infer_instance

/-- The strict vector order `vecGt` is decidable. -/
instance decVecGt [NeZero d] (x y : Fin d → ℕ) : Decidable (vecGt x y) := by
  unfold vecGt; infer_instance

/-- **Decidability of the strict checking condition** ([EWZ08, Lemma 4]). The *a priori* infinite
condition "`[ℓ](x) > [r](x)` for all `x ∈ ℕᵈ`" is decidable: by equation (2) (`affine_vecGt_iff`)
it is equivalent to the finite matrix/vector comparison `matGe Mℓ Mᵣ ∧ vecGt vℓ vᵣ`. -/
instance decidableAffineVecGt [NeZero d] (Mℓ Mᵣ : Matrix (Fin d) (Fin d) ℕ) (vℓ vᵣ : Fin d → ℕ) :
    Decidable (∀ x, vecGt (affine Mℓ vℓ x) (affine Mᵣ vᵣ x)) :=
  decidable_of_iff _ (affine_vecGt_iff Mℓ Mᵣ vℓ vᵣ)

/-- **Decidability of the weak checking condition** ([EWZ08, Lemma 4]). Likewise
"`[ℓ](x) ≳ [r](x)` for all `x ∈ ℕᵈ`" is decidable via `affine_vecGe_iff`. Together with
`decidableAffineVecGt`, this shows it is decidable to check whether a given collection of natural
matrix interpretations constitutes a proof of (relative / top) termination. -/
instance decidableAffineVecGe (Mℓ Mᵣ : Matrix (Fin d) (Fin d) ℕ) (vℓ vᵣ : Fin d → ℕ) :
    Decidable (∀ x, vecGe (affine Mℓ vℓ x) (affine Mᵣ vᵣ x)) :=
  decidable_of_iff _ (affine_vecGe_iff Mℓ Mᵣ vℓ vᵣ)

/-! ### Example 2.16 — `SN(R / S)` by a natural matrix interpretation

A worked instance of the method on `R = {aa → aba}`, `S = {b → bb}` over `Σ = {a, b}`
(Example 2.5): a second proof of `SN(R / S)` — already shown by the ad-hoc `aa`-factor measure
(`terminating_R_relative_S`) — now through the matrix-interpretation machinery, exactly as
Example 2.13 (`terminating_R₃_interpretation`) reproved `terminating_R₃`. -/

/-- The interpretation matrices of **Example 2.16**, over the carrier `ℕ²`: `Mₐ = !![1,1;0,0]` and
`M_b = !![1,0;0,0]`. Both have top-left entry `1`, so each affine map is `>`-monotone and the algebra
is *extended* monotone. -/
@[category API, AMS 68, ref "EWZ08", group "example_2_16"]
def M₂₁₆ : Sym → Matrix (Fin 2) (Fin 2) ℕ
  | Sym.a => !![1, 1; 0, 0]
  | Sym.b => !![1, 0; 0, 0]

/-- The interpretation constant vectors of **Example 2.16**: `vₐ = ![0,1]`, `v_b = ![0,0]`, so
`[a](x) = Mₐ x + ![0,1]` and `[b](x) = M_b x`. -/
@[category API, AMS 68, ref "EWZ08", group "example_2_16"]
def v₂₁₆ : Sym → Fin 2 → ℕ
  | Sym.a => ![0, 1]
  | Sym.b => ![0, 0]

/-- **Example 2.16** ([EWZ08]). A second proof that `R = {aa → aba}` is terminating relative to
`S = {b → bb}` (cf. `terminating_R_relative_S`, via the `aa`-factor count `adjAA`), now by a
**natural matrix interpretation** over `ℕ²`: `[a](x) = !![1,1;0,0] x + ![0,1]`,
`[b](x) = !![1,0;0,0] x`. Both matrices have top-left entry `1`, so this is an *extended* monotone
algebra (`extendedMonotoneAlgebra`). Composing the symbols (`affine_comp`) gives the rule sides'
interpretations — `[aa](x) = !![1,1;0,0] x + ![1,1]`, `[aba](x) = !![1,1;0,0] x + ![0,1]`, and
`[b](x) = [bb](x) = !![1,0;0,0] x` — and equation (2) (`affine_vecGt_iff` / `affine_vecGe_iff`) turns
the rule conditions into finite, decidable comparisons: the `R`-rule strictly decreases
(same matrix, `![1,1] > ![0,1]` in the vector order) and the `S`-rule weakly decreases
(`[b] = [bb]`). Theorem 2.15 soundness (`terminatingRelativeTo_of_extendedMonotone`) then concludes
`SN(R / S)`. -/
@[category textbook, AMS 68, ref "EWZ08", group "example_2_16",
  formal_uses terminatingRelativeTo_of_extendedMonotone extendedMonotoneAlgebra affine_vecGt_iff
    affine_vecGe_iff affine_comp M₂₁₆ v₂₁₆]
theorem terminating_R_relative_S_matrix :
    TerminatingRelativeTo (RewriteStep R) (RewriteStep S) := by
  have hM : ∀ σ, M₂₁₆ σ 0 0 = 1 := fun σ => by cases σ <;> rfl
  have haa : strInterp (fun σ => affine (M₂₁₆ σ) (v₂₁₆ σ)) [Sym.a, Sym.a]
      = affine !![1, 1; 0, 0] ![1, 1] := by
    simp only [strInterp, Function.comp_id]
    rw [affine_comp,
      show M₂₁₆ Sym.a * M₂₁₆ Sym.a = !![1, 1; 0, 0] from by decide,
      show M₂₁₆ Sym.a *ᵥ v₂₁₆ Sym.a + v₂₁₆ Sym.a = ![1, 1] from by decide]
  have haba : strInterp (fun σ => affine (M₂₁₆ σ) (v₂₁₆ σ)) [Sym.a, Sym.b, Sym.a]
      = affine !![1, 1; 0, 0] ![0, 1] := by
    simp only [strInterp, Function.comp_id]
    rw [affine_comp, affine_comp,
      show M₂₁₆ Sym.a * (M₂₁₆ Sym.b * M₂₁₆ Sym.a) = !![1, 1; 0, 0] from by decide,
      show M₂₁₆ Sym.a *ᵥ (M₂₁₆ Sym.b *ᵥ v₂₁₆ Sym.a + v₂₁₆ Sym.b) + v₂₁₆ Sym.a = ![0, 1] from by
        decide]
  have hb : strInterp (fun σ => affine (M₂₁₆ σ) (v₂₁₆ σ)) [Sym.b]
      = affine !![1, 0; 0, 0] ![0, 0] := by
    simp only [strInterp, Function.comp_id]; rfl
  have hbb : strInterp (fun σ => affine (M₂₁₆ σ) (v₂₁₆ σ)) [Sym.b, Sym.b]
      = affine !![1, 0; 0, 0] ![0, 0] := by
    simp only [strInterp, Function.comp_id]
    rw [affine_comp,
      show M₂₁₆ Sym.b * M₂₁₆ Sym.b = !![1, 0; 0, 0] from by decide,
      show M₂₁₆ Sym.b *ᵥ v₂₁₆ Sym.b + v₂₁₆ Sym.b = ![0, 0] from by decide]
  apply terminatingRelativeTo_of_extendedMonotone (extendedMonotoneAlgebra M₂₁₆ v₂₁₆ hM)
  · rintro ℓ r ⟨rfl, rfl⟩ x
    show vecGt (strInterp (fun σ => affine (M₂₁₆ σ) (v₂₁₆ σ)) [Sym.a, Sym.a] x)
      (strInterp (fun σ => affine (M₂₁₆ σ) (v₂₁₆ σ)) [Sym.a, Sym.b, Sym.a] x)
    rw [haa, haba]
    exact (affine_vecGt_iff !![1, 1; 0, 0] !![1, 1; 0, 0] ![1, 1] ![0, 1]).mp (by decide) x
  · rintro ℓ r ⟨rfl, rfl⟩ x
    show vecGe (strInterp (fun σ => affine (M₂₁₆ σ) (v₂₁₆ σ)) [Sym.b] x)
      (strInterp (fun σ => affine (M₂₁₆ σ) (v₂₁₆ σ)) [Sym.b, Sym.b] x)
    rw [hb, hbb]
    exact (affine_vecGe_iff !![1, 0; 0, 0] !![1, 0; 0, 0] ![0, 0] ![0, 0]).mp (by decide) x

end StringRewriting.MatrixInterpretation
