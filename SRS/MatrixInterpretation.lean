/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.Interpretation
import Mathlib.Data.Matrix.Mul
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

end StringRewriting.MatrixInterpretation
