/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Certificate
import BB61.WeakStar
import BB61.LadderScope
import BB61.FullSupport
import Mathlib.LinearAlgebra.Matrix.PosDef
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M3 Theorems 7 and 8: the kernel criterion, and the collapse of Route B

`note-1061-M3.html` §5 is where Route B is repaired and then dissolved.  Theorem 7 states the
B-criterion correctly — for a finite `Γ ⊂ 𝔡⁻¹` and a Hermitian positive semi-definite `B`, with
`Q = ∑ B_{γγ'} χ_{γ-γ'}` and `c(0) = tr B`,

* (i) the autocorrelation `c(δ)` sums to zero along each `α`-orbit missing `ℤ`, and
* (ii) `sup_{λ ∈ M(Ω,M̄)} ∫ Q dλ < c(0)`

together prove 10.61 at `α`.  Theorem 8 then says the criterion has no strength outside the
integers: it depends only on the **integer reach** `H_Γ = {h ∈ ℤ∖{0} : αᵐh ∈ Γ-Γ}`, and every
Route D certificate is realised by a kernel whose frequency set is a set of integers.  Hence
*the non-integer, multi-scale, Meyer and ladder frequencies are inert*.

## Why this file is stated over `ℤ`

Because M3 Corollary 6 (`BB61/LadderScope.lean`) says nothing else is available.  Under the
counterexample hypothesis only `γ ∈ α^ℤ(ℤ∖{0})` is forced to vanish, and by Theorem 4
(`BB61/LadderReduction.lean`) the whole `α`-orbit of an integer `h` carries the single
constraint `Φ_h(μ)`.  So over `ℤ` the note's `H_Γ` collapses to `(Γ-Γ)∖{0}` and its
condition (i) is **vacuous** — which is exactly what Theorem 8(c) observes.  Everything here
is therefore stated for `Γ : Finset ℤ` and `B : Matrix ↥Γ ↥Γ ℂ`.

## Two things the note needs and this file does not

**Bochner.**  The note gets `Q ≥ 0` from `B ⪰ 0` by Bochner's theorem.  Put `B` in *Gram*
form, `B_{γγ'} = ∑_k w_k(γ) conj(w_k(γ'))`, and `matKernel_gram` computes the kernel as
`Q = ∑_k |∑_γ w_k(γ) e(γ·)|²` — nonnegative by inspection (`matKernel_gram_nonneg`), with
`gram_posSemidef` recording that these are honest positive semi-definite matrices.  Positivity
turns out to be irrelevant to the *validity* of Theorem 7 anyway: the proof never uses it, and
`not_equidistributed_of_kernel` is stated for an arbitrary matrix.  `B ⪰ 0` is what makes the
criterion *satisfiable*, not what makes it *sound*.

**Fejér–Riesz.**  The note proves 8(c) by factoring `A - G = |P|²`, which Mathlib does not
have.  It is not needed, because the criterion has slack: it is enough to write down *one*
explicit sum of squares with the right non-constant part, and the one-term polynomials
`1 - a_h e(h·)` do it.  Their squared moduli are `1 + |a_h|² - 2 Re(a_h e(h·))`, so summing
over `h ∈ H` gives, on the nose,

`Q = c(0) - 2G`   (`exists_kernel_of_trigCertificate`),

with `Γ = {0} ∪ H`.  The same identity read backwards is Theorem 7: a kernel with a uniform
gap **is** a Route D certificate, `G = c(0) - Q` (`kernelCertificate`).  *Route B and Route D
are the same object up to a change of sign*, and that is the whole of Theorem 8.

## What is here

* `matKernel`, `matTrace` — `Q_B` and `c(0)`; `integral_matKernel` is `∫_𝕋 Q_B = c(0)`, and
  `integral_matKernel_comp` reads `∫ Q_B ∘ F dμ` in the coefficients `Φ_δ(μ)`;
* `kernelCertificate`, `not_equidistributed_of_kernel` — **Theorem 7**;
* `no_killer_of_kernel` — **Theorem 8(a)**: a kernel forbids every invariant measure that
  kills its integer reach;
* `no_killer_of_trigCertificate`, `exists_trigCertificate_of_no_killer` — **Theorem 8(b)**,
  both directions.  The completeness half is M3 Theorem 9's separation
  (`BB61/Certificate.lean`) with the test family **prescribed** instead of extracted: the
  Hahn–Banach argument runs in `ℝ^{H × Bool}`, the real and imaginary parts of the `|H|`
  numbers `Φ_h(μ)`;
* `exists_kernel_of_trigCertificate` — **Theorem 8(c)**;
* `exists_kernel_iff` — **Theorem 8**, as a three-way equivalence: an integer kernel, a
  trigonometric certificate, and the master target of M1 Theorem 7 are the same condition;
* `exists_gap_of_pointwise`, `confCircle_ne_univ_of_kernel` — the note's first sanity check.
  The parenthetical strong form of (ii), `sup_Ω Q < c(0)`, does supply the uniform gap, and it
  forces `X(α) ≠ 𝕋`: **a pointwise kernel is never more than M4/X8's confinement gap.**  With
  `BB61/FullSupport.lean` that makes it *empty* at the two `α` where `X(α) = 𝕋`
  (`silver_not_pointwise_kernel`, `goldenSq_not_pointwise_kernel`).

## What is not here

* **The note's second sanity check** (the G-R freedom is neutral) is M2 Proposition 8,
  `BB61/BlockRecoding.lean`, and is not repeated.
* **`Γ ⊂ 𝔡⁻¹` in general**, with the note's condition (i).  Corollary 6 is the reason: over
  the non-integer part of the codifferent the hypothesis `τ̄_*λ = Leb` supplies nothing, so
  condition (i) is the demand that the kernel not use what it cannot know.  Making that
  precise would need the characters `χ_γ` of the solenoid, which the repository does not have
  and which Theorem 8 says are inert.
* **`PosSemidef → Gram`.**  Only the easy direction is proved (`gram_posSemidef`); the
  converse is the Cholesky/spectral factorisation, absent from Mathlib.  Nothing is lost:
  Theorem 7 is proved for an arbitrary matrix, and 8(c)'s realisation lands in the Gram class.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M3.html` §5 (Theorems 7 and 8 and the two sanity checks that follow them).
  Numerics `BB61/m3_thm78_lean.py`.
-/
noncomputable section

namespace BB61

open MeasureTheory Filter Topology BoundedContinuousFunction Matrix
open scoped ComplexOrder

/-! ## Kernels on a finite set of integer frequencies -/

/-- `e((m-n)z) = e(mz) · conj(e(nz))`. -/
@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem fourier_sub_apply (m n : ℤ) (z : AddCircle (1 : ℝ)) :
    fourier (m - n) z = fourier m z * (starRingEnd ℂ) (fourier n z) := by
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem normSq_fourier (n : ℤ) (z : AddCircle (1 : ℝ)) : Complex.normSq (fourier n z) = 1 := by
  have h : ((Complex.normSq (fourier n z) : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, ← fourier_neg, ← fourier_add]
    simp
  exact_mod_cast h

variable {Γ : Finset ℤ}

/-- **The kernel of a matrix on a finite set of integer frequencies**,
`Q_B = ∑_{γ,γ' ∈ Γ} B_{γγ'} e((γ-γ')·)` — the note's `∑ B_{γγ'} χ_{γ-γ'}` at `Γ ⊂ ℤ`. -/
def matKernel (B : Matrix ↥Γ ↥Γ ℂ) : AddCircle (1 : ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => (∑ i : ↥Γ, ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) z).re,
      Complex.continuous_re.comp (continuous_finsetSum _ fun _ _ =>
        continuous_finsetSum _ fun _ _ => continuous_const.mul (map_continuous (fourier _)))⟩

@[simp, category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem matKernel_apply (B : Matrix ↥Γ ↥Γ ℂ) (z : AddCircle (1 : ℝ)) :
    matKernel B z = (∑ i : ↥Γ, ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) z).re := rfl

/-- `c(0) = tr B`, the note's normalisation. -/
def matTrace (B : Matrix ↥Γ ↥Γ ℂ) : ℝ := (Matrix.trace B).re

/-! ### The Gram form, and why Bochner is not needed -/

variable {κ : Type*} [Fintype κ]

/-- The **Gram matrix** `B_{γγ'} = ∑_k w_k(γ) conj(w_k(γ'))` of a finite family of coefficient
vectors on `Γ`. -/
def gram (w : κ → ↥Γ → ℂ) : Matrix ↥Γ ↥Γ ℂ :=
  Matrix.of fun i j => ∑ k, w k i * (starRingEnd ℂ) (w k j)

@[category API, AMS 11 15, ref "Bug12", group "bugeaud_10_61"]
theorem gram_posSemidef (w : κ → ↥Γ → ℂ) : (gram w).PosSemidef := by
  have h : gram w = (Matrix.of fun k i => (starRingEnd ℂ) (w k i))ᴴ *
      (Matrix.of fun k i => (starRingEnd ℂ) (w k i)) := by
    ext i j
    simp [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `∑_k |w_k|²`, which is `tr` of the Gram matrix. -/
def gramTrace (w : κ → ↥Γ → ℂ) : ℝ := ∑ k, ∑ i : ↥Γ, Complex.normSq (w k i)

/-- **The kernel of a Gram matrix is a sum of squared moduli.**  This is the note's
"`Q ≥ 0` by Bochner", and it needs no Bochner theorem: the positive-definiteness of `B` has
been put into the *form* of `B`. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem matKernel_gram (w : κ → ↥Γ → ℂ) (z : AddCircle (1 : ℝ)) :
    matKernel (gram w) z
      = ∑ k, Complex.normSq (∑ i : ↥Γ, w k i * fourier (i : ℤ) z) := by
  have h1 : ∀ i j : ↥Γ, gram w i j * fourier ((i : ℤ) - (j : ℤ)) z
      = ∑ k, (w k i * fourier (i : ℤ) z) * (starRingEnd ℂ) (w k j * fourier (j : ℤ) z) := by
    intro i j
    rw [gram, Matrix.of_apply, fourier_sub_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    ring
  have h2 : ∀ k : κ, ((∑ i : ↥Γ, w k i * fourier (i : ℤ) z)
        * (starRingEnd ℂ) (∑ i : ↥Γ, w k i * fourier (i : ℤ) z))
      = ∑ i : ↥Γ, ∑ j : ↥Γ, (w k i * fourier (i : ℤ) z)
          * (starRingEnd ℂ) (w k j * fourier (j : ℤ) z) := by
    intro k
    rw [map_sum, Finset.sum_mul_sum]
  have key : (∑ i : ↥Γ, ∑ j : ↥Γ, gram w i j * fourier ((i : ℤ) - (j : ℤ)) z)
      = ∑ k, (∑ i : ↥Γ, w k i * fourier (i : ℤ) z)
          * (starRingEnd ℂ) (∑ i : ↥Γ, w k i * fourier (i : ℤ) z) := by
    simp only [h1, h2]
    calc (∑ i : ↥Γ, ∑ j : ↥Γ, ∑ k, (w k i * fourier (i : ℤ) z)
              * (starRingEnd ℂ) (w k j * fourier (j : ℤ) z))
        = ∑ i : ↥Γ, ∑ k, ∑ j : ↥Γ, (w k i * fourier (i : ℤ) z)
              * (starRingEnd ℂ) (w k j * fourier (j : ℤ) z) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i : ↥Γ, ∑ j : ↥Γ, (w k i * fourier (i : ℤ) z)
              * (starRingEnd ℂ) (w k j * fourier (j : ℤ) z) := Finset.sum_comm
  rw [matKernel_apply, key]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj]
  simp

@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem matKernel_gram_nonneg (w : κ → ↥Γ → ℂ) (z : AddCircle (1 : ℝ)) :
    0 ≤ matKernel (gram w) z := by
  rw [matKernel_gram]
  exact Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _

@[category API, AMS 11 15, ref "Bug12", group "bugeaud_10_61"]
theorem matTrace_gram (w : κ → ↥Γ → ℂ) : matTrace (gram w) = gramTrace w := by
  rw [matTrace, Matrix.trace, gramTrace]
  simp only [Matrix.diag_apply, gram, Matrix.of_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj]
  simp

/-! ## The two integrals

The kernel's Lebesgue average is `c(0)`, and its average along the factor map is the same
double sum read against the Fourier coefficients `Φ_δ(μ)` of `BB61/LadderReduction.lean`. -/

@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem coe_sub_eq_zero_iff (i j : ↥Γ) : (i : ℤ) - (j : ℤ) = 0 ↔ i = j := by
  rw [sub_eq_zero]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩

@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourier_circle_zero :
    ∫ z : AddCircle (1 : ℝ), fourier 0 z ∂(volume : Measure (AddCircle (1 : ℝ))) = 1 := by
  simp

@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourier_circle_ne {δ : ℤ} (hδ : δ ≠ 0) :
    ∫ z : AddCircle (1 : ℝ), fourier δ z ∂(volume : Measure (AddCircle (1 : ℝ))) = 0 := by
  rw [← haarAddCircle_eq_volume]
  exact integral_fourier_eq_zero hδ

/-- **`∫_𝕋 Q_B = c(0)`.**  The kernel's Lebesgue average is the trace: every off-diagonal
character integrates to zero, and `Γ ⊂ ℤ` makes `γ - γ' = 0` mean `γ = γ'`. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem integral_matKernel (B : Matrix ↥Γ ↥Γ ℂ) :
    ∫ z, matKernel B z ∂(volume : Measure (AddCircle (1 : ℝ))) = matTrace B := by
  have hij : ∀ i j : ↥Γ, Integrable
      (fun z : AddCircle (1 : ℝ) => B i j * fourier ((i : ℤ) - (j : ℤ)) z)
      (volume : Measure (AddCircle (1 : ℝ))) := fun i j =>
    (continuous_const.mul (map_continuous (fourier _))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : ∀ i : ↥Γ, Integrable
      (fun z : AddCircle (1 : ℝ) => ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) z)
      (volume : Measure (AddCircle (1 : ℝ))) := fun i =>
    integrable_finsetSum _ fun j _ => hij i j
  have hI : Integrable (fun z : AddCircle (1 : ℝ) =>
      ∑ i : ↥Γ, ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) z)
      (volume : Measure (AddCircle (1 : ℝ))) := integrable_finsetSum _ fun i _ => hi i
  have hre : ∀ z : AddCircle (1 : ℝ), matKernel B z
      = RCLike.re (∑ i : ↥Γ, ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) z) := fun _ => rfl
  simp_rw [hre]
  rw [integral_re hI]
  have hsum : ∫ z, (∑ i : ↥Γ, ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) z)
      ∂(volume : Measure (AddCircle (1 : ℝ))) = Matrix.trace B := by
    rw [MeasureTheory.integral_finsetSum
      (f := fun (i : ↥Γ) (z : AddCircle (1 : ℝ)) =>
        ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) z) Finset.univ (fun i _ => hi i)]
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_finsetSum
      (f := fun (j : ↥Γ) (z : AddCircle (1 : ℝ)) => B i j * fourier ((i : ℤ) - (j : ℤ)) z)
      Finset.univ (fun j _ => hij i j), Finset.sum_eq_single i]
    · rw [integral_const_mul, sub_self, integral_fourier_circle_zero, mul_one]
    · intro j _ hj
      rw [integral_const_mul, integral_fourier_circle_ne
        (fun hc => hj (((coe_sub_eq_zero_iff i j).mp hc).symm)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hsum]
  rfl

namespace QuadSetup

variable (P : QuadSetup)

/-- **`∫ Q_B ∘ F dμ = Re ∑ B_{γγ'} Φ_{γ-γ'}(μ)`.**  The kernel's average along the factor map,
in the Fourier coefficients of `BB61/LadderReduction.lean`. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem integral_matKernel_comp (B : Matrix ↥Γ ↥Γ ℂ) (μ : Measure Shift)
    [IsProbabilityMeasure μ] :
    ∫ ω, matKernel B (P.fMap ω) ∂μ
      = RCLike.re (∑ i : ↥Γ, ∑ j : ↥Γ, B i j * P.phiCoeff μ ((i : ℤ) - (j : ℤ))) := by
  have hij : ∀ i j : ↥Γ, Integrable
      (fun ω : Shift => B i j * fourier ((i : ℤ) - (j : ℤ)) (P.fMap ω)) μ := fun i j =>
    (continuous_const.mul ((map_continuous (fourier _)).comp
      P.continuous_fMap)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : ∀ i : ↥Γ, Integrable
      (fun ω : Shift => ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) (P.fMap ω)) μ := fun i =>
    integrable_finsetSum _ fun j _ => hij i j
  have hI : Integrable (fun ω : Shift =>
      ∑ i : ↥Γ, ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) (P.fMap ω)) μ :=
    integrable_finsetSum _ fun i _ => hi i
  have hre : ∀ ω : Shift, matKernel B (P.fMap ω)
      = RCLike.re (∑ i : ↥Γ, ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) (P.fMap ω)) :=
    fun _ => rfl
  simp_rw [hre]
  rw [integral_re hI]
  congr 1
  rw [MeasureTheory.integral_finsetSum
    (f := fun (i : ↥Γ) (ω : Shift) =>
      ∑ j : ↥Γ, B i j * fourier ((i : ℤ) - (j : ℤ)) (P.fMap ω)) Finset.univ (fun i _ => hi i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum
    (f := fun (j : ↥Γ) (ω : Shift) => B i j * fourier ((i : ℤ) - (j : ℤ)) (P.fMap ω))
    Finset.univ (fun j _ => hij i j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- If `μ` kills every non-zero difference of `Γ` then the kernel's average along `F` is
exactly its Lebesgue average.  **This one computation is what both Theorem 7 and Theorem 8(a)
run on.** -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem integral_matKernel_comp_eq_trace (B : Matrix ↥Γ ↥Γ ℂ) (μ : Measure Shift)
    [IsProbabilityMeasure μ]
    (hkill : ∀ i j : ↥Γ, i ≠ j → P.phiCoeff μ ((i : ℤ) - (j : ℤ)) = 0) :
    ∫ ω, matKernel B (P.fMap ω) ∂μ = matTrace B := by
  rw [P.integral_matKernel_comp B μ]
  have key : (∑ i : ↥Γ, ∑ j : ↥Γ, B i j * P.phiCoeff μ ((i : ℤ) - (j : ℤ)))
      = Matrix.trace B := by
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · have h : P.phiCoeff μ ((i : ℤ) - (i : ℤ)) = 1 := by
        simp only [sub_self, phiCoeff, fourier_zero]
        simp
      rw [h, mul_one]
    · intro j _ hj
      rw [hkill i j (fun hc => hj hc.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [key]
  rfl

/-! ## Theorem 7: the kernel criterion, and Route B inside Route D -/

/-- **M3 Theorem 7, as a Route D certificate.**  A kernel whose `F`-averages stay a fixed
distance below its own Lebesgue average `c(0)` *is* a certificate, namely `G = c(0) - Q`.
Half of Theorem 8 is already here: Route B lands inside Route D by a change of sign. -/
def kernelCertificate (B : Matrix ↥Γ ↥Γ ℂ) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ μ ∈ invMeasures,
      ∫ ω, matKernel B (P.fMap ω) ∂(μ : Measure Shift) ≤ matTrace B - c) :
    Certificate P where
  G := BoundedContinuousFunction.const _ (matTrace B) - matKernel B
  c := c
  c_pos := hc
  mean_zero := by
    have hInt : Integrable (fun z : AddCircle (1 : ℝ) => matKernel B z)
        (volume : Measure (AddCircle (1 : ℝ))) := (matKernel B).integrable _
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply]
    rw [integral_sub (integrable_const _) hInt, integral_const, integral_matKernel]
    simp
  le_integral := fun μ hμ => by
    have hInt : Integrable (fun ω : Shift => matKernel B (P.fMap ω)) (μ : Measure Shift) :=
      ((matKernel B).compContinuous ⟨P.fMap, P.continuous_fMap⟩).integrable _
    have hg := hgap μ hμ
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply]
    have hone : (μ : Measure Shift).real Set.univ = 1 := by simp
    rw [integral_sub (integrable_const _) hInt, integral_const, hone, one_smul]
    linarith

/-- **M3 Theorem 7 (the B-criterion, precise form), at `Γ ⊂ ℤ`.**  If a kernel on a finite set
of integer frequencies averages strictly below its trace against every invariant measure, then
no `ξ ∈ C(α)` has `(ξ αⁿ)` uniformly distributed modulo one: **10.61 holds at `α`**. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_kernel (B : Matrix ↥Γ ↥Γ ℂ) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ μ ∈ invMeasures,
      ∫ ω, matKernel B (P.fMap ω) ∂(μ : Measure Shift) ≤ matTrace B - c)
    {ξ : ℝ} (hξ : ξ ∈ cantorSet P.α) :
    ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  Certificate.not_equidistributed (P.kernelCertificate B hc hgap) hξ

/-- The kernel criterion kills every invariant measure. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem no_invariant_of_kernel (B : Matrix ↥Γ ↥Γ ℂ) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ μ ∈ invMeasures,
      ∫ ω, matKernel B (P.fMap ω) ∂(μ : Measure Shift) ≤ matTrace B - c)
    {μ : ProbabilityMeasure Shift} (hμ : μ ∈ invMeasures) :
    pmap P.measurable_fMap μ ≠ haarT :=
  Certificate.no_invariant (P.kernelCertificate B hc hgap) hμ

/-! ## Theorem 8(a): a kernel sees only its integer reach -/

/-- **M3 Theorem 8(a).**  A kernel on `Γ` forbids every invariant measure that kills the
non-zero differences `Γ - Γ` — the kernel's **integer reach**.  By M3 Corollary 6
(`BB61/LadderScope.lean`) the note's larger reach `H_Γ = {h : αᵐh ∈ Γ-Γ}` adds nothing: the
whole `α`-orbit of `h` carries the single constraint `Φ_h(μ)`. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem no_killer_of_kernel (B : Matrix ↥Γ ↥Γ ℂ) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ μ ∈ invMeasures,
      ∫ ω, matKernel B (P.fMap ω) ∂(μ : Measure Shift) ≤ matTrace B - c)
    {μ : ProbabilityMeasure Shift} (hμ : μ ∈ invMeasures)
    (hkill : ∀ i j : ↥Γ, i ≠ j → P.phiCoeff (μ : Measure Shift) ((i : ℤ) - (j : ℤ)) = 0) :
    False := by
  have h := P.integral_matKernel_comp_eq_trace B (μ : Measure Shift) hkill
  have h2 := hgap μ hμ
  rw [h] at h2
  linarith

/-! ## Theorem 8(b): the kernel's reach and a trigonometric certificate -/

@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem integrable_fourier_fMap (h : ℤ) (μ : Measure Shift) [IsFiniteMeasure μ] :
    Integrable (fun ω : Shift => fourier h (P.fMap ω)) μ :=
  ((map_continuous (fourier h)).comp P.continuous_fMap).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem phiCoeff_re (h : ℤ) (μ : Measure Shift) [IsProbabilityMeasure μ] :
    RCLike.re (P.phiCoeff μ h) = ∫ ω, fourierRe h (P.fMap ω) ∂μ := by
  rw [phiCoeff, ← integral_re (P.integrable_fourier_fMap h μ)]
  rfl

@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem phiCoeff_im (h : ℤ) (μ : Measure Shift) [IsProbabilityMeasure μ] :
    RCLike.im (P.phiCoeff μ h) = ∫ ω, fourierIm h (P.fMap ω) ∂μ := by
  rw [phiCoeff, ← integral_im (P.integrable_fourier_fMap h μ)]
  rfl

/-- `∫ G ∘ F dμ = Re ∑_{h ∈ H} a_h Φ_h(μ)` for a real trigonometric polynomial. -/
@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem integral_trigPoly_comp (H : Finset ℤ) (a : ℤ → ℂ) (μ : Measure Shift)
    [IsProbabilityMeasure μ] :
    ∫ ω, trigPoly H a (P.fMap ω) ∂μ = RCLike.re (∑ h ∈ H, a h * P.phiCoeff μ h) := by
  have hint : ∀ h ∈ H, Integrable (fun ω : Shift => a h * fourier h (P.fMap ω)) μ :=
    fun h _ => (P.integrable_fourier_fMap h μ).const_mul _
  have hI : Integrable (fun ω : Shift => ∑ h ∈ H, a h * fourier h (P.fMap ω)) μ :=
    integrable_finsetSum _ hint
  have hre : ∀ ω : Shift, trigPoly H a (P.fMap ω)
      = RCLike.re (∑ h ∈ H, a h * fourier h (P.fMap ω)) := fun _ => rfl
  simp_rw [hre]
  rw [integral_re hI]
  congr 1
  rw [MeasureTheory.integral_finsetSum
    (f := fun (h : ℤ) (ω : Shift) => a h * fourier h (P.fMap ω)) H hint]
  exact Finset.sum_congr rfl fun h _ => integral_const_mul _ _

/-- **M3 Theorem 8(b), the easy direction.**  A trigonometric certificate carried by `H` kills
every invariant measure that kills `H`. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem no_killer_of_trigCertificate {H : Finset ℤ} {a : ℤ → ℂ} {c : ℝ} (hc : 0 < c)
    (hlb : ∀ μ ∈ invMeasures, c ≤ ∫ ω, trigPoly H a (P.fMap ω) ∂(μ : Measure Shift))
    {μ : ProbabilityMeasure Shift} (hμ : μ ∈ invMeasures)
    (hkill : ∀ h ∈ H, P.phiCoeff (μ : Measure Shift) h = 0) : False := by
  have h1 := hlb μ hμ
  rw [P.integral_trigPoly_comp H a (μ : Measure Shift)] at h1
  have h2 : (∑ h ∈ H, a h * P.phiCoeff (μ : Measure Shift) h) = 0 :=
    Finset.sum_eq_zero fun h hh => by rw [hkill h hh, mul_zero]
  rw [h2] at h1
  simp only [map_zero] at h1
  linarith

/-- **M3 Theorem 8(b), the completeness direction.**  If no invariant measure kills the finite
frequency set `H`, a trigonometric certificate *carried by `H`* exists.  This is M3 Theorem 9
(`BB61/Certificate.lean`) with the family of test functions **prescribed** rather than
extracted: the separation is performed in `ℝ^{H × Bool}`, the real and imaginary parts of the
`|H|` coefficients `Φ_h`. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem exists_trigCertificate_of_no_killer (H : Finset ℤ)
    (hno : ∀ μ ∈ invMeasures, ∃ h ∈ H, P.phiCoeff (μ : Measure Shift) h ≠ 0) :
    ∃ (a : ℤ → ℂ) (c : ℝ), 0 < c ∧
      ∀ μ ∈ invMeasures, c ≤ ∫ ω, trigPoly H a (P.fMap ω) ∂(μ : Measure Shift) := by
  classical
  set T : ↥H × Bool → (AddCircle (1 : ℝ) →ᵇ ℝ) := fun p =>
    cond p.2 (fourierIm (p.1 : ℤ)) (fourierRe (p.1 : ℤ)) with hT
  set Ψ : ProbabilityMeasure Shift → (↥H × Bool → ℝ) := fun μ p =>
    ∫ ω, T p (P.fMap ω) ∂(μ : Measure Shift) with hΨ
  have hre : ∀ (μ : ProbabilityMeasure Shift) (h : ↥H),
      Ψ μ (h, false) = RCLike.re (P.phiCoeff (μ : Measure Shift) (h : ℤ)) :=
    fun μ h => (P.phiCoeff_re _ _).symm
  have him : ∀ (μ : ProbabilityMeasure Shift) (h : ↥H),
      Ψ μ (h, true) = RCLike.im (P.phiCoeff (μ : Measure Shift) (h : ℤ)) :=
    fun μ h => (P.phiCoeff_im _ _).symm
  have hΨcont : Continuous Ψ := by
    refine continuous_pi fun p => ?_
    exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      ((T p).compContinuous ⟨P.fMap, P.continuous_fMap⟩)
  have hVcompact : IsCompact (Ψ '' invMeasures) := isCompact_invMeasures.image hΨcont
  have hVconv : Convex ℝ (Ψ '' invMeasures) := by
    rintro _ ⟨μ₀, h₀, rfl⟩ _ ⟨μ₁, h₁, rfl⟩ x y hx hy hxy
    refine ⟨mix hx hy hxy μ₀ μ₁, mix_mem_invMeasures hx hy hxy h₀ h₁, ?_⟩
    funext p
    simp only [hΨ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      integral_mix_comp hx hy hxy μ₀ μ₁ (T p) P.continuous_fMap]
  have h0V : (0 : ↥H × Bool → ℝ) ∉ Ψ '' invMeasures := by
    rintro ⟨μ, hμ, hz⟩
    obtain ⟨h, hh, hne⟩ := hno μ hμ
    refine hne (Complex.ext ?_ ?_)
    · have := congrFun hz (⟨h, hh⟩, false)
      rw [hre μ ⟨h, hh⟩] at this
      simpa using this
    · have := congrFun hz (⟨h, hh⟩, true)
      rw [him μ ⟨h, hh⟩] at this
      simpa using this
  obtain ⟨f, wsep, hf0, hfV⟩ := geometric_hahn_banach_point_closed hVconv hVcompact.isClosed h0V
  have hw : 0 < wsep := by simpa using hf0
  set A : ↥H × Bool → ℝ := fun p => f (fun q => if p = q then 1 else 0) with hA
  have hfeq : ∀ v : ↥H × Bool → ℝ, f v = ∑ p : ↥H × Bool, v p * A p := by
    intro v
    have h := LinearMap.pi_apply_eq_sum_univ (f : (↥H × Bool → ℝ) →ₗ[ℝ] ℝ) v
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
    exact h
  set Are : ℤ → ℝ := fun x => if hx : x ∈ H then A (⟨x, hx⟩, false) else 0 with hAre
  set Aim : ℤ → ℝ := fun x => if hx : x ∈ H then A (⟨x, hx⟩, true) else 0 with hAim
  refine ⟨fun x => ((Are x : ℝ) : ℂ) - Complex.I * ((Aim x : ℝ) : ℂ), wsep, hw, fun μ hμ => ?_⟩
  have hsep := hfV (Ψ μ) ⟨μ, hμ, rfl⟩
  rw [hfeq (Ψ μ)] at hsep
  rw [P.integral_trigPoly_comp _ _ (μ : Measure Shift), map_sum]
  have hterm : ∀ x ∈ H, RCLike.re ((((Are x : ℝ) : ℂ) - Complex.I * ((Aim x : ℝ) : ℂ))
        * P.phiCoeff (μ : Measure Shift) x)
      = Are x * RCLike.re (P.phiCoeff (μ : Measure Shift) x)
        + Aim x * RCLike.im (P.phiCoeff (μ : Measure Shift) x) := by
    intro x _
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, RCLike.re_to_complex,
      RCLike.im_to_complex]
    ring
  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_coe_sort H (fun x : ℤ => Are x * RCLike.re (P.phiCoeff (μ : Measure Shift) x)
      + Aim x * RCLike.im (P.phiCoeff (μ : Measure Shift) x))]
  have hsum : (∑ i : ↥H, (Are (i : ℤ) * RCLike.re (P.phiCoeff (μ : Measure Shift) (i : ℤ))
        + Aim (i : ℤ) * RCLike.im (P.phiCoeff (μ : Measure Shift) (i : ℤ))))
      = ∑ p : ↥H × Bool, Ψ μ p * A p := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Are (i : ℤ) = A (i, false) := by simp [hAre, i.2]
    have h2 : Aim (i : ℤ) = A (i, true) := by simp [hAim, i.2]
    rw [Fintype.sum_bool, h1, h2, hre μ i, him μ i]
    ring
  rw [hsum]
  linarith [hsep]

/-! ## Theorem 8(c): every trigonometric certificate is an integer kernel

The note obtains the kernel from `G` by Fejér–Riesz: `A - G ≥ 0` on `𝕋`, hence `A - G = |P|²`.
That factorisation is not in Mathlib and is not needed.  The criterion has slack, so it is
enough to write down *one* explicit sum of squares with the right non-constant part, and the
one-term polynomials `1 - a_h e(h·)` do it: their squared moduli are
`1 + |a_h|² - 2 Re(a_h e(h·))`, so summing over `h ∈ H` gives `Q = c(0) - 2G` on the nose. -/

/-- **M3 Theorem 8(c).**  Every trigonometric certificate is realised by a kernel on a set of
*integer* frequencies, namely `Γ = {0} ∪ H` with the Gram matrix of the one-term polynomials
`1 - a_h e(h·)`.  The kernel is `Q = c(0) - 2G` exactly, so the note's Fejér–Riesz step is
not needed: **the certifying power of an `Ω`-kernel is already reached inside `ℤ`.** -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem exists_kernel_of_trigCertificate {H : Finset ℤ} (h0 : (0 : ℤ) ∉ H) (a : ℤ → ℂ)
    {c : ℝ}
    (hlb : ∀ μ ∈ invMeasures, c ≤ ∫ ω, trigPoly H a (P.fMap ω) ∂(μ : Measure Shift)) :
    ∃ B : Matrix ↥(insert (0 : ℤ) H) ↥(insert (0 : ℤ) H) ℂ,
      B.PosSemidef ∧ (∀ z, 0 ≤ matKernel B z)
        ∧ (∀ z, matKernel B z = matTrace B - 2 * trigPoly H a z)
        ∧ ∀ μ ∈ invMeasures,
            ∫ ω, matKernel B (P.fMap ω) ∂(μ : Measure Shift) ≤ matTrace B - 2 * c := by
  classical
  set Wc : ℤ → ℤ → ℂ := fun k x => if x = 0 then 1 else if x = k then -(a k) else 0 with hWc
  set w : ↥H → ↥(insert (0 : ℤ) H) → ℂ := fun k i => Wc (k : ℤ) (i : ℤ) with hw
  have hk0 : ∀ k : ↥H, (k : ℤ) ≠ 0 := fun k hk => h0 (hk ▸ k.2)
  have hsum : ∀ (k : ↥H) (g : ℤ → ℂ),
      (∑ i : ↥(insert (0 : ℤ) H), w k i * g (i : ℤ)) = g 0 + -(a (k : ℤ)) * g (k : ℤ) := by
    intro k g
    rw [hw]
    rw [Finset.sum_coe_sort (insert (0 : ℤ) H) (fun x : ℤ => Wc (k : ℤ) x * g x),
      Finset.sum_insert h0]
    have hz : Wc (k : ℤ) 0 = 1 := by simp [hWc]
    have htail : (∑ x ∈ H, Wc (k : ℤ) x * g x) = -(a (k : ℤ)) * g (k : ℤ) := by
      rw [Finset.sum_eq_single (k : ℤ)]
      · have : Wc (k : ℤ) (k : ℤ) = -(a (k : ℤ)) := by simp [hWc, hk0 k]
        rw [this]
      · intro x _ hx
        have hx0 : x ≠ 0 := fun hc0 => h0 (hc0 ▸ ‹x ∈ H›)
        simp [hWc, hx0, hx]
      · intro hk
        exact absurd k.2 hk
    rw [hz, htail, one_mul]
  have hnsq : ∀ k : ↥H, (∑ i : ↥(insert (0 : ℤ) H), Complex.normSq (w k i))
      = 1 + Complex.normSq (a (k : ℤ)) := by
    intro k
    rw [hw]
    rw [Finset.sum_coe_sort (insert (0 : ℤ) H) (fun x : ℤ => Complex.normSq (Wc (k : ℤ) x)),
      Finset.sum_insert h0]
    have hz : Complex.normSq (Wc (k : ℤ) 0) = 1 := by simp [hWc]
    have htail : (∑ x ∈ H, Complex.normSq (Wc (k : ℤ) x)) = Complex.normSq (a (k : ℤ)) := by
      rw [Finset.sum_eq_single (k : ℤ)]
      · have : Wc (k : ℤ) (k : ℤ) = -(a (k : ℤ)) := by simp [hWc, hk0 k]
        rw [this, Complex.normSq_neg]
      · intro x _ hx
        have hx0 : x ≠ 0 := fun hc0 => h0 (hc0 ▸ ‹x ∈ H›)
        simp [hWc, hx0, hx]
      · intro hk
        exact absurd k.2 hk
    rw [hz, htail]
  have hgt : gramTrace w = ∑ k : ↥H, (1 + Complex.normSq (a (k : ℤ))) :=
    Finset.sum_congr rfl fun k _ => hnsq k
  have hker : ∀ z, matKernel (gram w) z = matTrace (gram w) - 2 * trigPoly H a z := by
    intro z
    rw [matKernel_gram, matTrace_gram]
    have hpt : ∀ k : ↥H, Complex.normSq (∑ i : ↥(insert (0 : ℤ) H), w k i * fourier (i : ℤ) z)
        = (1 + Complex.normSq (a (k : ℤ)))
          - 2 * RCLike.re (a (k : ℤ) * fourier (k : ℤ) z) := by
      intro k
      rw [hsum k (fun x => fourier x z), fourier_zero]
      have h1 : (1 : ℂ) + -(a (k : ℤ)) * fourier (k : ℤ) z
          = 1 - a (k : ℤ) * fourier (k : ℤ) z := by ring
      rw [h1, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul, normSq_fourier,
        mul_one, one_mul]
      simp
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hpt k, Finset.sum_sub_distrib, ← hgt]
    congr 1
    rw [trigPoly_apply, ← Finset.sum_coe_sort H (fun x : ℤ => a x * fourier x z),
      Complex.re_sum, Finset.mul_sum]
    rfl
  refine ⟨gram w, gram_posSemidef w, matKernel_gram_nonneg w, hker, fun μ hμ => ?_⟩
  have hInt : Integrable (fun ω : Shift => trigPoly H a (P.fMap ω)) (μ : Measure Shift) :=
    ((trigPoly H a).compContinuous ⟨P.fMap, P.continuous_fMap⟩).integrable _
  have hb := hlb μ hμ
  have : ∫ ω, matKernel (gram w) (P.fMap ω) ∂(μ : Measure Shift)
      = matTrace (gram w) - 2 * ∫ ω, trigPoly H a (P.fMap ω) ∂(μ : Measure Shift) := by
    simp_rw [hker]
    have hone : (μ : Measure Shift).real Set.univ = 1 := by simp
    rw [integral_sub (integrable_const _) (hInt.const_mul 2), integral_const, hone, one_smul,
      integral_const_mul]
  rw [this]
  linarith

/-! ## Route B ≡ Route D -/

/-- **M3 Theorem 8.**  Three statements, all equivalent: an integer kernel satisfying the
criterion of Theorem 7, a Route D trigonometric certificate, and the master target of M1
Theorem 7.  Route B's kernels are exactly Route D's certificates, read as `Q = c(0) - G`, so
**the non-integer, multi-scale, Meyer and ladder frequencies are inert**. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem exists_kernel_iff :
    (∃ (Γ : Finset ℤ) (B : Matrix ↥Γ ↥Γ ℂ) (c : ℝ), 0 < c ∧
        ∀ μ ∈ invMeasures,
          ∫ ω, matKernel B (P.fMap ω) ∂(μ : Measure Shift) ≤ matTrace B - c)
      ↔ ∀ μ ∈ invMeasures, pmap P.measurable_fMap μ ≠ haarT := by
  refine ⟨fun ⟨Γ, B, c, hc, hgap⟩ μ hμ => P.no_invariant_of_kernel B hc hgap hμ, fun hno => ?_⟩
  obtain ⟨H, a, c, h0, hc, -, hlb⟩ := P.exists_trigCertificate hno
  obtain ⟨B, -, -, -, hgap⟩ := P.exists_kernel_of_trigCertificate h0 a hlb
  exact ⟨insert (0 : ℤ) H, B, 2 * c, by linarith, hgap⟩

/-! ## The note's first sanity check: a pointwise kernel is the confinement gap -/

/-- If the kernel stays below `m` on the confinement set `X(α) = range F`, it stays below `m`
in mean against every probability measure — no invariance needed. -/
@[category API, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem integral_matKernel_comp_le (B : Matrix ↥Γ ↥Γ ℂ) {m : ℝ}
    (hle : ∀ z ∈ P.confCircle, matKernel B z ≤ m) (μ : Measure Shift)
    [IsProbabilityMeasure μ] : ∫ ω, matKernel B (P.fMap ω) ∂μ ≤ m := by
  have hInt : Integrable (fun ω : Shift => matKernel B (P.fMap ω)) μ :=
    ((matKernel B).compContinuous ⟨P.fMap, P.continuous_fMap⟩).integrable _
  have h : ∀ ω : Shift, matKernel B (P.fMap ω) ≤ m := fun ω =>
    hle _ (by rw [confCircle]; exact Set.mem_range_self ω)
  have hmono := integral_mono hInt (integrable_const m) h
  rwa [integral_const, show (μ.real Set.univ) = 1 by simp, one_smul] at hmono

/-- **The pointwise form of Theorem 7(ii) supplies the uniform gap**, so it really is a
sufficient condition and not just a suggestive one. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem exists_gap_of_pointwise (B : Matrix ↥Γ ↥Γ ℂ)
    (hlt : ∀ z ∈ P.confCircle, matKernel B z < matTrace B) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ invMeasures,
      ∫ ω, matKernel B (P.fMap ω) ∂(μ : Measure Shift) ≤ matTrace B - c := by
  obtain ⟨z₀, hz₀, hmax⟩ := P.isCompact_confCircle.exists_isMaxOn
    ⟨P.fMap (fun _ => false), by rw [confCircle]; exact Set.mem_range_self _⟩
    (matKernel B).continuous.continuousOn
  refine ⟨matTrace B - matKernel B z₀, by linarith [hlt z₀ hz₀], fun μ hμ => ?_⟩
  have h := P.integral_matKernel_comp_le B (fun z hz => hmax hz) (μ : Measure Shift)
  linarith

/-- **The note's first sanity check.**  A kernel that is pointwise below its own trace on the
confinement set forces `X(α) ≠ 𝕋`: in its pointwise form, Route B's move 3 is never more than
M4/X8's confinement gap.  The proof is one line of bookkeeping — `∫_𝕋 Q = c(0)` is the trace,
so `Q < c(0)` everywhere on `𝕋` contradicts `Q`'s own mean. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_ne_univ_of_kernel (B : Matrix ↥Γ ↥Γ ℂ)
    (hlt : ∀ z ∈ P.confCircle, matKernel B z < matTrace B) :
    P.confCircle ≠ Set.univ := by
  intro huniv
  obtain ⟨z₀, -, hmax⟩ := (@isCompact_univ (AddCircle (1 : ℝ)) _ _).exists_isMaxOn
    Set.univ_nonempty (matKernel B).continuous.continuousOn
  have hInt : Integrable (fun z : AddCircle (1 : ℝ) => matKernel B z)
      (volume : Measure (AddCircle (1 : ℝ))) := (matKernel B).integrable _
  have hmono := integral_mono hInt (integrable_const (matKernel B z₀))
    (fun z => hmax (Set.mem_univ z))
  rw [integral_const, show ((volume : Measure (AddCircle (1 : ℝ))).real Set.univ) = 1 by simp,
    one_smul, integral_matKernel] at hmono
  have hz := hlt z₀ (by rw [huniv]; trivial)
  linarith

end QuadSetup

/-- **No pointwise kernel at `1 + √2`.**  `BB61/FullSupport.lean` proves `X(1+√2) = 𝕋`, so
the strong form of the B-criterion is *empty* there — exactly as at `(3+√5)/2`.  Route B has
no reserve of strength over M4 at the two `α` where M4 is known to be blind. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem silver_not_pointwise_kernel {Γ : Finset ℤ} (B : Matrix ↥Γ ↥Γ ℂ) :
    ¬ ∀ z ∈ silver.confCircle, matKernel B z < matTrace B :=
  fun h => silver.confCircle_ne_univ_of_kernel B h silver_confCircle

/-- The same at `(3+√5)/2`. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem goldenSq_not_pointwise_kernel {Γ : Finset ℤ} (B : Matrix ↥Γ ↥Γ ℂ) :
    ¬ ∀ z ∈ goldenSq.confCircle, matKernel B z < matTrace B :=
  fun h => goldenSq.confCircle_ne_univ_of_kernel B h goldenSq_confCircle

end BB61
