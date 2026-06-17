/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.MatrixInterpretation
import Mathlib.Data.Matrix.Block
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Affine-to-linear homogenization of matrix interpretations (YAH §3; EWZ08 Theorem 6)

[EWZ08, Theorem 6] turns a `d`-dimensional **affine** interpretation `[σ](x) = Mσ·x + vσ`
(`affine`, from `SRS.MatrixInterpretation`) into a `(d+1)`-dimensional **linear** one
`[σ]⁺(x) = Dσ·x`, where `Dσ` is the block matrix `[[Mσ, vσ], [0ᵀ, 1]]`. In homogeneous coordinates
`Dσ` realises the affine map, `Dσ·(x, 1) = (Mσ·x + vσ, 1)`, and composition of affine maps becomes
the matrix product of the `Dσ`'s — so a whole rule's interpretation is again of this block form.

* `homogenize M v` — the matrix `Dσ = [[M, v], [0, 1]]`, indexed by `Fin d ⊕ Fin 1` (the `d+1`
  rows/columns: the original `Fin d`, then one extra). `linInterp M v x = Dσ ⬝ᵥ x` is the map `[σ]⁺`.
* `theorem_3_7` — **Theorem 3.7** ([EWZ08, Theorem 6]): if `Mℓ ⪰ Mᵣ` (`matGe`) and `vℓ ⪰ vᵣ`
  (`vecGe`) then `Dℓ ⪰ Dᵣ` entrywise. Homogenization is monotone for the `⪰` order (the `0` and `1`
  blocks are shared, so the comparison reduces to the `M`- and `v`-blocks).
* `corollary_3_7` — the strict addendum ("Additionally …"): if `vℓ > vᵣ` (`vecGt`, strict in the
  first coordinate) then the `(1, d+1)` entry is strict, `(Dℓ)_{1,d+1} > (Dᵣ)_{1,d+1}` — that entry
  is exactly the first coordinate `v 0` of the top-right block.
-/

namespace StringRewriting.MatrixInterpretation

open Matrix

variable {d : ℕ}

/-- The `(d+1)`-dimensional **homogenization** `Dσ = [[M, v], [0ᵀ, 1]]` of the affine map
`x ↦ M·x + v`, as a block matrix indexed by `Fin d ⊕ Fin 1`. -/
@[category API, AMS 68, ref "EWZ08", group "homogenization"]
def homogenize (M : Matrix (Fin d) (Fin d) ℕ) (v : Fin d → ℕ) :
    Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) ℕ :=
  Matrix.fromBlocks M (Matrix.of fun i (_ : Fin 1) => v i) 0 1

/-- The `(d+1)`-dimensional **linear interpretation** `[σ]⁺(x) = Dσ·x`. -/
@[category API, AMS 68, ref "EWZ08", group "homogenization"]
def linInterp (M : Matrix (Fin d) (Fin d) ℕ) (v : Fin d → ℕ) (x : Fin d ⊕ Fin 1 → ℕ) :
    Fin d ⊕ Fin 1 → ℕ := homogenize M v *ᵥ x

/-- **Theorem 3.7** ([EWZ08, Theorem 6]). If the affine data compare as `Mℓ ⪰ Mᵣ` and `vℓ ⪰ vᵣ`,
then the homogenizations compare entrywise, `Dℓ ⪰ Dᵣ` (i.e. `(Dᵣ) i j ≤ (Dℓ) i j` for all `i, j`).
The bottom row `[0ᵀ, 1]` is identical on both sides, so the comparison comes down to the `M`-block
(from `hM`) and the `v`-block (from `hv`). -/
@[category research solved, AMS 68, ref "EWZ08", group "homogenization"]
theorem theorem_3_7 {Mℓ Mᵣ : Matrix (Fin d) (Fin d) ℕ} {vℓ vᵣ : Fin d → ℕ}
    (hM : matGe Mℓ Mᵣ) (hv : vecGe vℓ vᵣ) :
    ∀ i j, homogenize Mᵣ vᵣ i j ≤ homogenize Mℓ vℓ i j := by
  rintro (i | i) (j | j)
  · simpa [homogenize] using hM i j
  · simpa [homogenize] using hv i
  · simp [homogenize]
  · simp [homogenize]

/-- **Corollary** to Theorem 3.7 (its "Additionally …" clause). If moreover `vℓ > vᵣ` (`vecGt` —
strict in the first coordinate), then the `(1, d+1)` entry of the homogenization is strict:
`(Dℓ)_{1,d+1} > (Dᵣ)_{1,d+1}`. Here `(1, d+1)` is the first row / last column, `(Sum.inl 0,
Sum.inr 0)`, whose value is the first coordinate `v 0` of the top-right `v`-block. -/
@[category research solved, AMS 68, ref "EWZ08", group "homogenization"]
theorem corollary_3_7 [NeZero d] {Mℓ Mᵣ : Matrix (Fin d) (Fin d) ℕ} {vℓ vᵣ : Fin d → ℕ}
    (hv : vecGt vℓ vᵣ) :
    homogenize Mᵣ vᵣ (Sum.inl 0) (Sum.inr 0) < homogenize Mℓ vℓ (Sum.inl 0) (Sum.inr 0) := by
  simpa [homogenize] using hv.1

end StringRewriting.MatrixInterpretation
