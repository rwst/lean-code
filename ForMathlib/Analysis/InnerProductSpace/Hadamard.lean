/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hadamard's determinant inequality

`OrthonormalBasis.norm_det_le_prod_norm`: for a family `v : ι → E` of vectors in a finite-dimensional
inner product space and any orthonormal basis `a`, the determinant of `v` expressed in `a` is bounded
in norm by the product of the norms of the `v i`:
`‖a.toBasis.det v‖ ≤ ∏ i, ‖v i‖`.

This is **Hadamard's inequality**. The proof orthonormalises `v` by Gram–Schmidt: in the resulting
orthonormal basis `b` the determinant is `∏ i, ⟪b i, v i⟫` (an upper-triangular determinant), each
factor bounded by `‖v i‖` via Cauchy–Schwarz since `‖b i‖ = 1`; the determinant in any other
orthonormal basis has the same norm because the change-of-basis matrix is unitary
(`OrthonormalBasis.det_to_matrix_orthonormalBasis`). For the real, oriented analogue via the volume
form see `Orientation.abs_volumeForm_apply_le`.
-/

open Finset InnerProductSpace
open scoped InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-- **Hadamard's inequality.** The determinant of a family `v` of vectors, expressed in an
orthonormal basis `a`, is bounded in norm by the product of the norms of the `v i`. -/
theorem norm_det_le_prod_norm (a : OrthonormalBasis (Fin n) 𝕜 E) (v : Fin n → E) :
    ‖a.toBasis.det v‖ ≤ ∏ i, ‖v i‖ := by
  haveI : FiniteDimensional 𝕜 E := Module.Finite.of_basis a.toBasis
  have hcard : Module.finrank 𝕜 E = Fintype.card (Fin n) := Module.finrank_eq_card_basis a.toBasis
  let b : OrthonormalBasis (Fin n) 𝕜 E := gramSchmidtOrthonormalBasis hcard v
  have hgs : b.toBasis.det v = ∏ i, ⟪b i, v i⟫_𝕜 := gramSchmidtOrthonormalBasis_det hcard v
  have hcob : a.toBasis.det v = a.toBasis.det ⇑b * b.toBasis.det v := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul]
    congr 1
    rw [← OrthonormalBasis.coe_toBasis, Module.Basis.toMatrix_mul_toMatrix]
  rw [hcob, norm_mul, a.det_to_matrix_orthonormalBasis b, one_mul, hgs, norm_prod]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  calc ‖⟪b i, v i⟫_𝕜‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]

end OrthonormalBasis
