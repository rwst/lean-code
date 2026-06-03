/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
/-
# Rational formal power series and linear recurrences (Bertin, Proposition 1.1)

A formal series `F = ∑ aₙ Xⁿ`, an element of `K⟦X⟧` over a commutative semiring `K`, is a *rational
series* if and only if its coefficients eventually satisfy a linear recurrence

`q₀ aₙ + q₁ aₙ₋₁ + ⋯ + q_s aₙ₋ₛ = 0`   for all `n ≥ n₀`,   with `q₀ ≠ 0`.   (∗)

Reference: Bertin [Ber92], Proposition 1.1 (statement and proof transcribed from the source).

Proof (transcribed from the source):
* If `F` is a rational series it can be written `F = P/Q` with `P Q : K[X]`, `Q(0) ≠ 0`,
  `deg Q = r`. From the formal identity `Q F = P`, equating the coefficient of `Xⁿ` for
  `n ≥ n₀ := max (r + 1) s` yields exactly the relation (∗).
* Conversely set `Q := ∑_{0 ≤ i ≤ s} qᵢ Xⁱ` (so `Q(0) = q₀ ≠ 0`). The relations (∗) say
  every coefficient of `Q F` of index `≥ n₀` vanishes, hence `Q F = P` with `deg P ≤ n₀ - 1`,
  so `F = P/Q` is a rational series.

We work over an arbitrary commutative semiring — no division is used, so neither a field nor
even a ring structure is needed; the argument is purely combinatorial on coefficients. We also
do not assume the chosen denominator has nonzero constant term: the forward direction reads the
recurrence off `Q F = P` after shifting indices by `Q.natTrailingDegree`, which makes the
leading coefficient `Q`'s trailing coefficient (`≠ 0`).

## References

* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import ForMathlib.LinearAlgebra.Matrix.Hankel
import ForMathlib.LinearAlgebra.Matrix.Determinant.AntiDiagonal

open scoped Polynomial PowerSeries

variable {K : Type*} [CommSemiring K]

/-- `F ∈ K⟦X⟧` is a **rational series** when it is the power-series expansion of a ratio
`P/Q` of polynomials, i.e. the formal identity `Q * F = P` holds for some `P Q : K[X]`
with `Q ≠ 0`. (Over a field or integral domain this says `F` is the power-series expansion of a
rational function — the image of `K(X)` inside `K⟦X⟧`; over a general semiring `Q ≠ 0` need not
be regular, so it is just the formal "has a polynomial denominator".) -/
def IsRationalSeries (F : K⟦X⟧) : Prop :=
  ∃ P Q : K[X], Q ≠ 0 ∧ (Q : K⟦X⟧) * F = (P : K⟦X⟧)

/-- The `n`-th coefficient of `Q * F` for a polynomial `Q` is the finite convolution
`∑_{i ≤ n} Q.coeff i * a_{n-i}`. This is the bridge between the formal identity `Q * F = P`
and the coefficient relation (∗). -/
theorem coeff_coe_mul (Q : K[X]) (G : K⟦X⟧) (m : ℕ) :
    PowerSeries.coeff m ((Q : K⟦X⟧) * G)
      = ∑ i ∈ Finset.range (m + 1), Q.coeff i * PowerSeries.coeff (m - i) G := by
  simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_coe]

/-- **Proposition 1.1, forward direction.** The coefficients of a rational series eventually
satisfy a linear recurrence (∗) with nonzero leading coefficient. -/
theorem IsRationalSeries.exists_recurrence {F : K⟦X⟧} (hF : IsRationalSeries F) :
    ∃ (s n₀ : ℕ) (q : ℕ → K), q 0 ≠ 0 ∧ s ≤ n₀ ∧
      ∀ n, n₀ ≤ n → ∑ i ∈ Finset.range (s + 1), q i * PowerSeries.coeff (n - i) F = 0 := by
  obtain ⟨P, Q, hQ, hQF⟩ := hF
  have hk : Q.natTrailingDegree ≤ Q.natDegree := Q.natTrailingDegree_le_natDegree
  refine ⟨Q.natDegree - Q.natTrailingDegree, max Q.natDegree (P.natDegree + 1),
    fun j => Q.coeff (Q.natTrailingDegree + j), ?_, ?_, ?_⟩
  · -- `q 0 = Q`'s trailing coefficient, nonzero since `Q ≠ 0`.
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hQ
  · -- `s ≤ n₀`.
    exact (Nat.sub_le _ _).trans (le_max_left _ _)
  · -- the recurrence, read off `Q * F = P` at index `n + Q.natTrailingDegree`.
    intro n hn
    show ∑ i ∈ Finset.range (Q.natDegree - Q.natTrailingDegree + 1),
        Q.coeff (Q.natTrailingDegree + i) * PowerSeries.coeff (n - i) F = 0
    obtain ⟨hnQ, hnP⟩ := max_le_iff.mp hn
    have key : PowerSeries.coeff (n + Q.natTrailingDegree) ((Q : K⟦X⟧) * F)
        = ∑ i ∈ Finset.range (Q.natDegree - Q.natTrailingDegree + 1),
            Q.coeff (Q.natTrailingDegree + i) * PowerSeries.coeff (n - i) F :=
      calc PowerSeries.coeff (n + Q.natTrailingDegree) ((Q : K⟦X⟧) * F)
          = ∑ i ∈ Finset.range (n + Q.natTrailingDegree + 1),
              Q.coeff i * PowerSeries.coeff (n + Q.natTrailingDegree - i) F :=
            coeff_coe_mul Q F _
        _ = ∑ i ∈ Finset.Ico Q.natTrailingDegree (Q.natDegree + 1),
              Q.coeff i * PowerSeries.coeff (n + Q.natTrailingDegree - i) F :=
            (Finset.sum_subset
              (fun x hx => by simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega)
              (fun x _ hx => by
                simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx
                obtain h | h := hx
                · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree h, zero_mul]
                · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul])).symm
        _ = ∑ i ∈ Finset.range (Q.natDegree - Q.natTrailingDegree + 1),
              Q.coeff (Q.natTrailingDegree + i) * PowerSeries.coeff (n - i) F := by
            rw [Finset.sum_Ico_eq_sum_range, show Q.natDegree + 1 - Q.natTrailingDegree
                = Q.natDegree - Q.natTrailingDegree + 1 from by omega]
            exact Finset.sum_congr rfl fun i _ => by
              rw [show n + Q.natTrailingDegree - (Q.natTrailingDegree + i) = n - i from by omega]
    rw [← key, hQF, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Proposition 1.1, converse direction.** A formal series whose coefficients eventually
satisfy a linear recurrence (∗) with nonzero leading coefficient is a rational series. -/
theorem exists_recurrence.isRationalSeries {F : K⟦X⟧}
    (h : ∃ (s n₀ : ℕ) (q : ℕ → K), q 0 ≠ 0 ∧ s ≤ n₀ ∧
        ∀ n, n₀ ≤ n → ∑ i ∈ Finset.range (s + 1), q i * PowerSeries.coeff (n - i) F = 0) :
    IsRationalSeries F := by
  obtain ⟨s, n₀, q, hq0, hsn, hrec⟩ := h
  set Q : K[X] := ∑ i ∈ Finset.range (s + 1), Polynomial.monomial i (q i) with hQdef
  have hQcoeff : ∀ j, Q.coeff j = if j < s + 1 then q j else 0 := by
    intro j
    simp only [hQdef, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finset.sum_ite_eq', Finset.mem_range]
  -- Every coefficient of `Q * F` of index `≥ n₀` vanishes, by the recurrence.
  have hvanish : ∀ m, n₀ ≤ m → PowerSeries.coeff m ((Q : K⟦X⟧) * F) = 0 := by
    intro m hm
    have hsplit : ∑ i ∈ Finset.range (m + 1), Q.coeff i * PowerSeries.coeff (m - i) F
        = ∑ i ∈ Finset.range (s + 1), Q.coeff i * PowerSeries.coeff (m - i) F :=
      (Finset.sum_subset
        (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
        (fun x _ hx => by
          rw [Finset.mem_range, not_lt] at hx
          rw [hQcoeff, if_neg (show ¬ x < s + 1 by omega), zero_mul])).symm
    rw [coeff_coe_mul, hsplit,
      Finset.sum_congr rfl fun i hi => by rw [hQcoeff, if_pos (Finset.mem_range.mp hi)]]
    exact hrec m hm
  refine ⟨PowerSeries.trunc n₀ ((Q : K⟦X⟧) * F), Q, ?_, ?_⟩
  · -- `Q ≠ 0`, since `Q.coeff 0 = q 0 ≠ 0`.
    refine fun hQ0 => hq0 ?_
    have h0 := hQcoeff 0
    rw [hQ0, Polynomial.coeff_zero, if_pos (Nat.succ_pos s)] at h0
    exact h0.symm
  · -- `Q * F` agrees with its truncation, as all higher coefficients vanish.
    ext m
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hm
    exacts [rfl, hvanish m (by omega)]

/-- **Proposition 1.1.** A formal power series `F = ∑ aₙ Xⁿ ∈ K⟦X⟧` over a commutative semiring
is a rational series if and only if there exist `s n₀ : ℕ` and coefficients `q : ℕ → K` with
`q 0 ≠ 0` such that the coefficients `aₙ = PowerSeries.coeff n F` satisfy

`q 0 * aₙ + q 1 * aₙ₋₁ + ⋯ + q s * aₙ₋ₛ = 0`   for every `n ≥ n₀`.

The side hypothesis `s ≤ n₀` records that the recurrence is read at indices `n ≥ n₀ ≥ s`,
so the lowest index `n - s` is a genuine (non-truncated) natural number; it is automatically
satisfiable, since both directions produce such witnesses. -/
theorem isRationalSeries_iff_exists_recurrence (F : K⟦X⟧) :
    IsRationalSeries F ↔
      ∃ (s n₀ : ℕ) (q : ℕ → K), q 0 ≠ 0 ∧ s ≤ n₀ ∧
        ∀ n, n₀ ≤ n →
          ∑ i ∈ Finset.range (s + 1), q i * PowerSeries.coeff (n - i) F = 0 :=
  ⟨IsRationalSeries.exists_recurrence, exists_recurrence.isRationalSeries⟩

section Kronecker

/-! ## Kronecker (Hankel) determinants (Bertin, Definition 1.1)

`Matrix.det` is a signed sum over permutations, so it needs additive inverses: this section
works over a commutative ring. (The rationality results above use no subtraction and stay over
a `CommSemiring`.) -/

variable {K : Type*} [CommRing K]

/-- The `(n+1) × (n+1)` **Hankel matrix** of `F`: its `(i, j)` entry is
`a_{i+j} = PowerSeries.coeff (i + j) F` (rows and columns indexed `0 … n`). It is symmetric.
This is the generic `Matrix.hankel` of the coefficient sequence `k ↦ PowerSeries.coeff k F`. -/
noncomputable def hankelMatrix (F : K⟦X⟧) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.hankel (fun k => PowerSeries.coeff k F) n

@[simp] theorem hankelMatrix_apply (F : K⟦X⟧) (n : ℕ) (i j : Fin (n + 1)) :
    hankelMatrix F n i j = PowerSeries.coeff (i.val + j.val) F := rfl

/-- **Definition 1.1 (Bertin).** The `n`-th **Kronecker determinant** `Dₙ(F)` of a formal power
series `F = ∑ aₖ Xᵏ ∈ K⟦X⟧` (with `aₖ = PowerSeries.coeff k F`) is the determinant of the
`(n+1) × (n+1)` *Hankel matrix* whose `(i, j)` entry is `a_{i+j}` (rows and columns indexed
`0 … n`):
```
        ⎡ a₀    a₁    ⋯   aₙ   ⎤
        ⎢ a₁    a₂    ⋯   aₙ₊₁ ⎥
Dₙ(F) = ⎢ ⋮     ⋮     ⋱   ⋮    ⎥ .
        ⎣ aₙ    aₙ₊₁  ⋯   a₂ₙ  ⎦
```
It is the generic `Matrix.kroneckerDet` of the coefficient sequence `k ↦ PowerSeries.coeff k F`. -/
noncomputable def kroneckerDet (F : K⟦X⟧) (n : ℕ) : K := (hankelMatrix F n).det

end Kronecker

section KroneckerStep

variable {K : Type*} [CommRing K]

/-- **Inductive step of Kronecker's theorem (the determinant identity).** Write `vₙ` for
`∑_{i≤s} qᵢ a_{n-i}`. If `q 0 = 1` and `vₖ = 0` for `s ≤ k < t + s`, then the principal Hankel
determinant `D_t` is, up to a unit, `D_{s-1}` times a power of `v_{t+s}`. Bertin's column operations
`Aⱼ ↦ ∑_{i≤s} qᵢ A_{j-i}` are realized as right multiplication by a unitriangular matrix `U`
(so `det (Hₜ · U) = D_t`); `Hₜ · U` is block-triangular with top-left block `H_{s-1}` and an
anti-triangular bottom-right block with `v_{t+s}` on the anti-diagonal. -/
theorem kroneckerDet_step (F : K⟦X⟧) (q : ℕ → K) (s t : ℕ)
    (hq0 : q 0 = 1) (hs : 1 ≤ s) (hst : s ≤ t)
    (hv : ∀ k, s ≤ k → k < t + s →
      (∑ i ∈ Finset.range (s + 1), q i * PowerSeries.coeff (k - i) F) = 0) :
    ∃ u : K, IsUnit u ∧ kroneckerDet F t =
      u * kroneckerDet F (s - 1) *
        (∑ i ∈ Finset.range (s + 1), q i * PowerSeries.coeff (t + s - i) F) ^ (t - s + 1) := by
  classical
  -- `U` encodes the column operations: column `j` becomes `∑_{i≤s} qᵢ·(column j-i)` for `j ≥ s`,
  -- and stays put for `j < s`. It is upper-triangular with unit diagonal.
  set U : Matrix (Fin (t + 1)) (Fin (t + 1)) K :=
    Matrix.of fun k j =>
      if (k : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) ≤ (k : ℕ) + s ∧ (s ≤ (j : ℕ) ∨ (k : ℕ) = (j : ℕ))
        then q ((j : ℕ) - (k : ℕ)) else 0 with hU
  have hbt : Matrix.BlockTriangular U id := by
    intro i j hij
    simp only [id_eq] at hij
    rw [hU, Matrix.of_apply, if_neg (by rintro ⟨h1, -, -⟩; omega)]
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    apply Finset.prod_eq_one
    intro i _
    rw [hU, Matrix.of_apply, if_pos ⟨le_refl _, Nat.le_add_right _ _, Or.inr rfl⟩,
      Nat.sub_self, hq0]
  have hdetHU : (hankelMatrix F t * U).det = kroneckerDet F t := by
    simp only [Matrix.det_mul, hdetU, mul_one, kroneckerDet]
  -- Entry formula for `B = Hₜ · U`: Hankel for `j < s`, the recurrence value `vₙ` for `j ≥ s`.
  have hBentry : ∀ i j : Fin (t + 1), (hankelMatrix F t * U) i j =
      if (j : ℕ) < s then PowerSeries.coeff ((i : ℕ) + (j : ℕ)) F
      else ∑ l ∈ Finset.range (s + 1), q l * PowerSeries.coeff ((i : ℕ) + (j : ℕ) - l) F := by
    intro i j
    rw [Matrix.mul_apply]
    simp only [hankelMatrix_apply, hU, Matrix.of_apply]
    by_cases hj : (j : ℕ) < s
    · rw [if_pos hj,
        Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
          (fun k _ hkj => by rw [if_neg (by rintro ⟨-, -, (h | h)⟩ <;> omega), mul_zero])]
      simp [hq0]
    · rw [if_neg hj]
      have hsj : s ≤ (j : ℕ) := not_lt.mp hj
      simp only [eq_true hsj, true_or, and_true]
      rw [← Finset.sum_subset
          (Finset.subset_univ ((Finset.range (s + 1)).image
            (fun l => (⟨(j : ℕ) - l, by omega⟩ : Fin (t + 1)))))
          (fun x _ hx => by
            rw [if_neg, mul_zero]
            rintro ⟨hc1, hc2⟩
            refine hx (Finset.mem_image.mpr
              ⟨(j : ℕ) - (x : ℕ), Finset.mem_range.mpr (by omega), ?_⟩)
            apply Fin.ext
            show (j : ℕ) - ((j : ℕ) - (x : ℕ)) = (x : ℕ)
            omega),
        Finset.sum_image (fun a ha b hb hab => by
          simp only [Finset.mem_coe, Finset.mem_range] at ha hb
          have hv2 : (j : ℕ) - a = (j : ℕ) - b := congrArg Fin.val hab
          omega)]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mem_range] at hl
      show PowerSeries.coeff ((i : ℕ) + ((j : ℕ) - l)) F *
          (if (j : ℕ) - l ≤ (j : ℕ) ∧ (j : ℕ) ≤ ((j : ℕ) - l) + s
            then q ((j : ℕ) - ((j : ℕ) - l)) else 0) =
          q l * PowerSeries.coeff ((i : ℕ) + (j : ℕ) - l) F
      rw [if_pos ⟨by omega, by omega⟩, show (j : ℕ) - ((j : ℕ) - l) = l by omega,
        show (i : ℕ) + ((j : ℕ) - l) = (i : ℕ) + (j : ℕ) - l by omega]
      ring
  rw [← hdetHU]
  have hsum : s + (t - s + 1) = t + 1 := by omega
  set e : Fin s ⊕ Fin (t - s + 1) ≃ Fin (t + 1) := finSumFinEquiv.trans (finCongr hsum) with he
  have heL : ∀ i : Fin s, ((e (Sum.inl i)) : ℕ) = (i : ℕ) := fun i => by simp [he]
  have heR : ∀ i : Fin (t - s + 1), ((e (Sum.inr i)) : ℕ) = s + (i : ℕ) := fun i => by simp [he]
  -- Reindexed by `e`, `B = Hₜ·U` is block-triangular: its top-right block vanishes by the IH.
  have hfb : (hankelMatrix F t * U).submatrix e e =
      Matrix.fromBlocks
        ((hankelMatrix F t * U).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)) 0
        ((hankelMatrix F t * U).submatrix (e ∘ Sum.inr) (e ∘ Sum.inl))
        ((hankelMatrix F t * U).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [Matrix.submatrix_apply, Function.comp_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]
    rw [hBentry, if_neg (by rw [heR]; omega), heL, heR]
    exact hv _ (by omega) (by omega)
  have hBdet : (hankelMatrix F t * U).det =
      ((hankelMatrix F t * U).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).det *
      ((hankelMatrix F t * U).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)).det := by
    rw [← Matrix.det_submatrix_equiv_self e, hfb, Matrix.det_fromBlocks_zero₁₂]
  -- The top-left block is the Hankel matrix `H_{s-1}`.
  have hTL : ((hankelMatrix F t * U).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).det =
      kroneckerDet F (s - 1) := by
    have hcast : s = s - 1 + 1 := by omega
    rw [kroneckerDet, ← Matrix.det_submatrix_equiv_self (finCongr hcast)]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Function.comp_apply, hankelMatrix_apply]
    rw [hBentry, if_pos (by rw [heL]; omega), heL, heL, finCongr_apply_coe, finCongr_apply_coe]
  -- The bottom-right block is anti-triangular with `v_{t+s}` on its anti-diagonal.
  obtain ⟨u, hu, hBR⟩ := Matrix.det_eq_unit_mul_pow_of_antidiag_const
    ((hankelMatrix F t * U).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))
    (∑ l ∈ Finset.range (s + 1), q l * PowerSeries.coeff (t + s - l) F)
    (fun i j hij => by
      simp only [Matrix.submatrix_apply, Function.comp_apply]
      rw [hBentry, if_neg (by rw [heR]; omega), heR, heR]
      exact hv _ (by omega) (by omega))
    (fun i => by
      simp only [Matrix.submatrix_apply, Function.comp_apply]
      rw [hBentry, if_neg (by rw [heR]; omega), heR, heR]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [show (s + (i : ℕ)) + (s + ((i.rev : Fin (t - s + 1)) : ℕ)) = t + s from by
        rw [Fin.val_rev]; omega])
  refine ⟨u, hu, ?_⟩
  rw [hBdet, hTL, hBR]
  ring

end KroneckerStep

section KroneckerTheorem

variable {K : Type*} [Field K]

/-- If every Kronecker determinant of `F` vanishes then `F = 0`. Strong induction: once
`a₀ = ⋯ = a_{k-1} = 0`, the Hankel matrix `Hₖ` vanishes above its anti-diagonal and is constantly
`aₖ` on it, so `Dₖ = ± aₖ ^ (k+1)`; as `Dₖ = 0` in a field, `aₖ = 0`. -/
theorem eq_zero_of_forall_kroneckerDet_eq_zero {F : K⟦X⟧}
    (h : ∀ k, kroneckerDet F k = 0) : F = 0 := by
  ext k
  rw [map_zero]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨u, hu, hdet⟩ := Matrix.det_eq_unit_mul_pow_of_antidiag_const (hankelMatrix F k)
      (PowerSeries.coeff k F)
      (fun i j hij => by rw [hankelMatrix_apply]; exact ih _ hij)
      (fun i => by
        rw [hankelMatrix_apply]
        have hik : i.val + (i.rev : Fin (k + 1)).val = k := by rw [Fin.val_rev]; omega
        rw [hik])
    have hd0 : (hankelMatrix F k).det = 0 := h k
    rw [hd0] at hdet
    have hxk : PowerSeries.coeff k F ^ (k + 1) = 0 := by
      rcases mul_eq_zero.mp hdet.symm with hu0 | hx
      · exact absurd hu0 hu.ne_zero
      · exact hx
    exact (pow_eq_zero_iff (Nat.succ_ne_zero k)).mp hxk

/-- **Sufficiency of Kronecker's criterion.** A formal power series whose Kronecker
determinants vanish from some index on is rational: if they all vanish then `F = 0`,
otherwise the greatest index `s₀` with `D_{s₀} ≠ 0` yields an order-`(s₀+1)` recurrence
(kernel of `H_{s₀+1}`, propagated by `kroneckerDet_step`), and Proposition 1.1 applies. -/
private theorem isRationalSeries_of_eventually_kroneckerDet_zero {F : K⟦X⟧}
    (hD : ∃ N, ∀ n, N ≤ n → kroneckerDet F n = 0) : IsRationalSeries F := by
  -- Sufficiency. If all determinants vanish, `F = 0` (rational). Otherwise let `s₀` be the
  -- greatest index with `D_{s₀} ≠ 0`; then `Dₙ = 0` for `n ≥ s₀ + 1`, and the order-`(s₀+1)`
  -- recurrence this forces (base case from `H_{s₀+1}`'s kernel, propagated by the determinant
  -- identity `D_{m-s} = ± D_{s-1} · vₘ^(m+1-2s)`) makes `F` rational by Proposition 1.1.
  classical
  by_cases hall : ∀ k, kroneckerDet F k = 0
  · rw [eq_zero_of_forall_kroneckerDet_eq_zero hall]
    exact ⟨0, 1, one_ne_zero, by simp⟩
  · obtain ⟨N, hN⟩ := hD
    rw [not_forall] at hall
    obtain ⟨k₀, hk₀⟩ := hall
    have hk₀N : k₀ ≤ N := by
      by_contra hc
      exact hk₀ (hN k₀ (not_le.mp hc).le)
    set s₀ : ℕ := Nat.findGreatest (fun k => kroneckerDet F k ≠ 0) N with hs₀def
    have hDs₀ : kroneckerDet F s₀ ≠ 0 :=
      Nat.findGreatest_spec (P := fun k => kroneckerDet F k ≠ 0) hk₀N hk₀
    have hzero : ∀ n, s₀ + 1 ≤ n → kroneckerDet F n = 0 := by
      intro n hn
      by_cases hnN : n ≤ N
      · exact not_not.mp
          (Nat.findGreatest_is_greatest (P := fun k => kroneckerDet F k ≠ 0) (by omega) hnN)
      · exact hN n (by omega)
    -- The recurrence of order `s₀ + 1` exists; conclude by Proposition 1.1.
    refine exists_recurrence.isRationalSeries ?_
    have hDsucc : kroneckerDet F (s₀ + 1) = 0 := hzero (s₀ + 1) le_rfl
    obtain ⟨w, hw_ne, hw0⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M := hankelMatrix F (s₀ + 1))).mpr hDsucc
    -- The last entry of the kernel vector is nonzero (else it would kill the nonsingular
    -- `H_{s-1}`).
    have hwlast : w (Fin.last (s₀ + 1)) ≠ 0 := by
      intro hlast
      refine hDs₀ ((Matrix.exists_mulVec_eq_zero_iff (M := hankelMatrix F s₀)).mp
        ⟨fun j => w j.castSucc, ?_, ?_⟩)
      · intro hw'0
        refine hw_ne (funext fun k => ?_)
        rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
        · exact congrFun hw'0 j
        · exact hlast
      · funext i
        have h : ∑ j : Fin (s₀ + 2), hankelMatrix F (s₀ + 1) i.castSucc j * w j = 0 :=
          congrFun hw0 i.castSucc
        rw [Fin.sum_univ_castSucc] at h
        simp only [hankelMatrix_apply, Fin.val_castSucc, hlast, mul_zero, add_zero] at h
        show ∑ j : Fin (s₀ + 1), hankelMatrix F s₀ i j * w j.castSucc = 0
        simpa only [hankelMatrix_apply, Fin.val_castSucc] using h
    -- Normalize so the leading coefficient is `1`.
    set q : ℕ → K := fun l => (w (Fin.last (s₀ + 1)))⁻¹ * w ⟨s₀ + 1 - l, by omega⟩ with hq
    have hq0 : q 0 = 1 := by
      simp only [hq, Nat.sub_zero]
      exact inv_mul_cancel₀ hwlast
    -- Base case: the recurrence holds on `[s, 2s]` (rows of the kernel relation).
    have hbase : ∀ i : Fin (s₀ + 2),
        ∑ l ∈ Finset.range (s₀ + 2), q l * PowerSeries.coeff ((i : ℕ) + (s₀ + 1) - l) F = 0 := by
      intro i
      have hrow : ∑ j : Fin (s₀ + 2), PowerSeries.coeff ((i : ℕ) + (j : ℕ)) F * w j = 0 := by
        have h : ∑ j : Fin (s₀ + 2), hankelMatrix F (s₀ + 1) i j * w j = 0 := congrFun hw0 i
        simpa only [hankelMatrix_apply] using h
      have key : ∑ l ∈ Finset.range (s₀ + 2), q l * PowerSeries.coeff ((i : ℕ) + (s₀ + 1) - l) F =
          (w (Fin.last (s₀ + 1)))⁻¹ *
            ∑ j : Fin (s₀ + 2), PowerSeries.coeff ((i : ℕ) + (j : ℕ)) F * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij' (fun l _ => (⟨s₀ + 1 - l, by omega⟩ : Fin (s₀ + 2)))
          (fun j _ => s₀ + 1 - (j : ℕ)) (fun l _ => Finset.mem_univ _)
          (fun j _ => Finset.mem_range.mpr (by omega))
          (fun l hl => by rw [Finset.mem_range] at hl; show s₀ + 1 - (s₀ + 1 - l) = l; omega)
          (fun j _ => by apply Fin.ext; show s₀ + 1 - (s₀ + 1 - (j : ℕ)) = (j : ℕ); omega)
          (fun l hl => by
            rw [Finset.mem_range] at hl
            simp only [hq]
            show (w (Fin.last (s₀ + 1)))⁻¹ * w ⟨s₀ + 1 - l, by omega⟩ *
                PowerSeries.coeff ((i : ℕ) + (s₀ + 1) - l) F =
              (w (Fin.last (s₀ + 1)))⁻¹ *
                (PowerSeries.coeff ((i : ℕ) + (s₀ + 1 - l)) F * w ⟨s₀ + 1 - l, by omega⟩)
            rw [show (i : ℕ) + (s₀ + 1) - l = (i : ℕ) + (s₀ + 1 - l) from by omega]
            ring)
      rw [key, hrow, mul_zero]
    -- Propagate to all `n ≥ s` by strong induction, using the determinant identity.
    have hall : ∀ n, s₀ + 1 ≤ n →
        ∑ l ∈ Finset.range (s₀ + 2), q l * PowerSeries.coeff (n - l) F = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro hn
        by_cases hle : n ≤ 2 * s₀ + 2
        · have h := hbase ⟨n - (s₀ + 1), by omega⟩
          rw [show ((⟨n - (s₀ + 1), by omega⟩ : Fin (s₀ + 2)) : ℕ) + (s₀ + 1) = n from by
            have hval : ((⟨n - (s₀ + 1), by omega⟩ : Fin (s₀ + 2)) : ℕ) = n - (s₀ + 1) := rfl
            omega] at h
          exact h
        · obtain ⟨u, hu, hstep⟩ := kroneckerDet_step F q (s₀ + 1) (n - (s₀ + 1)) hq0
            (by omega) (by omega) (fun k hk1 hk2 => ih k (by omega) hk1)
          rw [hzero (n - (s₀ + 1)) (by omega)] at hstep
          have hvexp : (∑ i ∈ Finset.range (s₀ + 1 + 1),
              q i * PowerSeries.coeff (n - (s₀ + 1) + (s₀ + 1) - i) F) ^
              (n - (s₀ + 1) - (s₀ + 1) + 1) = 0 := by
            rcases mul_eq_zero.mp hstep.symm with h | h
            · rcases mul_eq_zero.mp h with h' | h'
              · exact absurd h' hu.ne_zero
              · exact absurd h' hDs₀
            · exact h
          have hv0 := (pow_eq_zero_iff (by omega : n - (s₀ + 1) - (s₀ + 1) + 1 ≠ 0)).mp hvexp
          rw [show n - (s₀ + 1) + (s₀ + 1) = n from by omega] at hv0
          exact hv0
    exact ⟨s₀ + 1, s₀ + 1, q, by rw [hq0]; exact one_ne_zero, le_rfl, hall⟩

/-- **Theorem 1.1.1 (Kronecker; Bertin).** A formal power series `F ∈ K⟦X⟧` over a field is a
rational series if and only if its Kronecker (Hankel) determinants vanish from some index on.
(The right-hand side is `∀ᶠ n in Filter.atTop, kroneckerDet F n = 0` spelled out.)

Proof (transcribed from Bertin; needs an integral domain — stated here over a field):

* **(⇒) Necessity.** By `IsRationalSeries.exists_recurrence` there are `s`, `n₀` and `q` with
  `q 0 ≠ 0` and `∑_{i ≤ s} qᵢ · a_{n-i} = 0` for all `n ≥ n₀`. Fix `n ≥ max n₀ s` and let
  `w : Fin (n+1) → K` send column index `n - i ↦ qᵢ` for `i ≤ s` and everything else to `0`.
  Each row of `Hₙ *ᵥ w` is a shifted instance of the recurrence, so `Hₙ *ᵥ w = 0`; and `w ≠ 0`
  because its top entry is `q 0 ≠ 0`. Hence `Dₙ(F) = 0` by `Matrix.exists_mulVec_eq_zero_iff`.

* **(⇐) Sufficiency** (the hard direction). Suppose `Dₙ(F) = 0` for `n ≥ n₀`. If every `Dₙ = 0`
  then `F = 0` (each `aₖ = 0` by induction on the principal minors), which is rational. Otherwise
  pick `s` minimal with `D_{s-1}(F) ≠ 0` and `Dₙ(F) = 0` for all `n ≥ s`. A nonzero kernel vector
  of `H_s` (from `exists_mulVec_eq_zero_iff`) has nonzero last entry — else it would kill the
  nonsingular `H_{s-1}` — so after scaling we get `q₁ … q_s` with
  `vₙ := aₙ + ∑_{i=1}^{s} qᵢ · a_{n-i} = 0` for `s ≤ n ≤ 2s`. Strong induction on `n`: from
  `D_{m-s}(F) = 0`, the column operations `Aⱼ ↦ ∑_{i≤s} qᵢ A_{j-i}` — realized as right
  multiplication by a unitriangular matrix (`kroneckerDet_step`) — put the matrix in block form
  whose determinant is `± D_{s-1}(F) · vₘ ^ (m+1-2s)`; since `D_{s-1}(F) ≠ 0` in a domain,
  `vₘ = 0`. So the recurrence holds for every `n ≥ s`, and `exists_recurrence.isRationalSeries`
  yields rationality. -/
theorem isRationalSeries_iff_kroneckerDet_eventually_zero (F : K⟦X⟧) :
    IsRationalSeries F ↔ ∃ N, ∀ n, N ≤ n → kroneckerDet F n = 0 := by
  constructor
  · intro hF
    -- Necessity: the recurrence gives a nonzero kernel vector of every large Hankel matrix,
    -- so its determinant vanishes (`Matrix.exists_mulVec_eq_zero_iff`).
    obtain ⟨s, n₀, q, hq0, -, hrec⟩ := hF.exists_recurrence
    refine ⟨max n₀ s, fun n hn => ?_⟩
    have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
    have hsn : s ≤ n := (le_max_right _ _).trans hn
    -- Reversed recurrence coefficients on the last `s+1` columns: the Hankel kernel vector.
    set v : Fin (n + 1) → K := fun j => if n - (j : ℕ) ≤ s then q (n - (j : ℕ)) else 0 with hv
    show (hankelMatrix F n).det = 0
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, ?_, ?_⟩
    · -- `v ≠ 0`: its last entry is `q 0 ≠ 0`.
      intro h
      have hl := congrFun h (Fin.last n)
      simp only [hv, Fin.val_last, Nat.sub_self, Nat.zero_le, if_true, Pi.zero_apply] at hl
      exact hq0 hl
    · -- Row `i` of `H *ᵥ v` is the recurrence at index `i + n ≥ n₀`.
      funext i
      show ∑ j : Fin (n + 1), hankelMatrix F n i j * v j = 0
      simp only [hankelMatrix_apply, hv]
      rw [Fin.sum_univ_eq_sum_range
        (fun x => PowerSeries.coeff (i.val + x) F * if n - x ≤ s then q (n - x) else 0) (n + 1),
        ← Finset.sum_range_reflect
        (fun x => PowerSeries.coeff (i.val + x) F * if n - x ≤ s then q (n - x) else 0) (n + 1)]
      simp only [Nat.add_sub_cancel]
      rw [← Finset.sum_subset (s₁ := Finset.range (s + 1))
          (fun x hx =>
            Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le (by omega : s + 1 ≤ n + 1)))
          (fun x hx hx' => by
            rw [Finset.mem_range] at hx
            rw [Finset.mem_range, not_lt] at hx'
            rw [if_neg (by omega), mul_zero])]
      refine Eq.trans (Finset.sum_congr rfl fun x hx => ?_) (hrec (i.val + n) (by omega))
      rw [Finset.mem_range] at hx
      have h1 : n - (n - x) = x := by omega
      have h2 : i.val + (n - x) = i.val + n - x := by omega
      rw [h1, if_pos (by omega : x ≤ s), h2]
      exact mul_comm _ _
  · exact isRationalSeries_of_eventually_kroneckerDet_zero

end KroneckerTheorem
