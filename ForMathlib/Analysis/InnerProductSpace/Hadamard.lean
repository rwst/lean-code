/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalities

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
form see `Orientation.abs_volumeForm_apply_le`. The matrix specialisation
`Matrix.norm_det_le_prod_col_norm` bounds `‖det X‖` by the product of the Euclidean norms of the
columns of `X`.
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

/-- **Hadamard's inequality, matrix form.** The determinant of a square matrix over `𝕜 = ℝ` or `ℂ`
is bounded in modulus by the product of the Euclidean norms of its columns:
`‖det X‖ ≤ ∏ j, √(∑ i, ‖X i j‖²)`. This specialises `OrthonormalBasis.norm_det_le_prod_norm` to the
standard orthonormal basis of `EuclideanSpace 𝕜 (Fin n)`, in which the determinant of the column
family of `X` is `Matrix.det X`. -/
theorem Matrix.norm_det_le_prod_col_norm {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) 𝕜) :
    ‖X.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖X i j‖ ^ 2) := by
  let v : Fin n → EuclideanSpace 𝕜 (Fin n) :=
    fun j => (EuclideanSpace.equiv (Fin n) 𝕜).symm (fun i => X i j)
  have hdet : (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.det v = X.det := by
    rw [Module.Basis.det_apply]; congr 1
  have hnorm : ∀ j, ‖v j‖ = Real.sqrt (∑ i, ‖X i j‖ ^ 2) := fun j => by
    rw [EuclideanSpace.norm_eq]; rfl
  calc ‖X.det‖ = ‖(EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.det v‖ := by rw [hdet]
    _ ≤ ∏ j, ‖v j‖ := (EuclideanSpace.basisFun (Fin n) 𝕜).norm_det_le_prod_norm v
    _ = ∏ j, Real.sqrt (∑ i, ‖X i j‖ ^ 2) := by simp only [hnorm]

/-- A square matrix `X` of order `n + 1` over `𝕜 = ℝ` or `ℂ` whose squared Frobenius norm is strictly
below its order, `∑_{i,j} ‖X i j‖² < n + 1`, has determinant of modulus `< 1`. This combines
Hadamard's inequality `‖det X‖ ≤ ∏ⱼ ‖colⱼ‖` (`Matrix.norm_det_le_prod_col_norm`) with the
arithmetic–geometric mean inequality:
`‖det X‖² ≤ ∏ⱼ (∑ᵢ ‖X i j‖²) ≤ ((∑_{i,j} ‖X i j‖²)/(n+1))^{n+1} < 1`. -/
theorem Matrix.norm_det_lt_one_of_sum_normSq_lt {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (hX : ∑ j, ∑ i, ‖X i j‖ ^ 2 < (n + 1 : ℝ)) :
    ‖X.det‖ < 1 := by
  set c : Fin (n + 1) → ℝ := fun j => ∑ i, ‖X i j‖ ^ 2 with hc
  have hcnn : ∀ j, 0 ≤ c j := fun j => Finset.sum_nonneg fun i _ => by positivity
  -- AM–GM: the product of the column squared-norms is `< 1`.
  have hprodc : ∏ j, c j < 1 := by
    have hw : ∑ _j : Fin (n + 1), ((n + 1 : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ (by positivity)]
    have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => ((n + 1 : ℝ))⁻¹) c
      (fun i _ => by positivity) hw (fun i _ => hcnn i)
    rw [Real.finsetProd_rpow Finset.univ c (fun i _ => hcnn i)] at hgm
    have harith : ∑ j, ((n + 1 : ℝ))⁻¹ * c j < 1 := by
      rw [← Finset.mul_sum]
      have hmul : (n + 1 : ℝ)⁻¹ * ∑ j, c j < (n + 1 : ℝ)⁻¹ * (n + 1 : ℝ) :=
        mul_lt_mul_of_pos_left hX (inv_pos.mpr (by positivity))
      rwa [inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)] at hmul
    have hlt : (∏ j, c j) ^ ((n + 1 : ℝ))⁻¹ < 1 := lt_of_le_of_lt hgm harith
    by_contra hge
    rw [not_lt] at hge
    have h1 : (1 : ℝ) ≤ (∏ j, c j) ^ ((n + 1 : ℝ))⁻¹ :=
      calc (1 : ℝ) = (1 : ℝ) ^ ((n + 1 : ℝ))⁻¹ := (Real.one_rpow _).symm
        _ ≤ (∏ j, c j) ^ ((n + 1 : ℝ))⁻¹ := Real.rpow_le_rpow zero_le_one hge (by positivity)
    linarith
  -- Hadamard `‖det X‖ ≤ ∏ⱼ √(cⱼ)`, and `(∏ⱼ √(cⱼ))² = ∏ⱼ cⱼ < 1`.
  have had : ‖X.det‖ ≤ ∏ j, Real.sqrt (c j) := Matrix.norm_det_le_prod_col_norm X
  have hsqrtnn : 0 ≤ ∏ j, Real.sqrt (c j) := Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
  have hsq : (∏ j, Real.sqrt (c j)) ^ 2 = ∏ j, c j := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => Real.sq_sqrt (hcnn j)
  have hprodsqrt : ∏ j, Real.sqrt (c j) < 1 := by nlinarith [hsq, hprodc, hsqrtnn]
  linarith [had, hprodsqrt]
