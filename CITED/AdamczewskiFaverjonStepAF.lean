/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonStepUB
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] Step (AF), quantitatively: the choice of `δ₂` and of the truncation order

plan-formalize-AF17's **WP14**, gap (3) of Stage 2.

`AF.exists_auxiliary` (WP10) is Lemma 2.12 with its dimension count left as a *hypothesis*:

  `d(D,p-1) < (δ₁+1)·d(δ₁,δ₂)`.

Nothing downstream can use it until someone produces, for a given `δ₁`, a `δ₂` and a truncation
order `p` that satisfy it — and not just any `p`: Step (UB) turns the truncation order into the
exponent, `AF.eventually_norm_evalAt_le_exp_of_sums` giving `e^{-γq^k}` with
`γ = p·log(1/t)/(2q^{k₀})`, and Lemma 2.11's contradiction needs `γ ≍ δ₁δ₂` with an *absolute*
constant.  So the count has to be met with `p` bounded **below** by a fixed multiple of `δ₁δ₂`.
That is what this file does.

## The constant is `2^{m²⌈log₂(m²+1)⌉}`, and that is where the bidegree repair is paid for

Write `B := afConst σ`.  Two facts do the whole job:

* `d(δ₁,·)` is **exactly** affine from some point on (`AF.exists_relDim_eq`, WP7's sharpening of
  [AF22] Lemma 2.2): `d(δ₁,v) = a + c(v-N₀)` for `v ≥ N₀`, with `c ≥ 1`;
* the first index may be inflated at a bounded cost (`AF.relDim_le_of_le_two_pow`, the repair of
  [AF22]'s false bidegree claim): `d((m²+1)δ₁, v) ≤ B·d(δ₁,v)`.

`D = (m²+1)δ₁` is the smallest index `AF.exists_auxiliary` allows, so the count to meet is
`B(a+ct) < (δ₁+1)(a+cw)`, where `t` and `w` are the offsets of `p-1` and of `δ₂` above `N₀`.  Take
`w = 2Bs` and `t = (δ₁+1)s`: the two `c`-terms become `Q` and `2Q`, and what remains is `Ba < Q`,
which holds as soon as `s > a`.  **`B` depends only on `m`** — not on `δ₁`, not on `δ₂` — and that
is the entire point: it is the constant `c₂ = log(1/t)/(8Bq^{k₀})` of Lemma 2.11.

## One `δ₂` per `δ₁`, chosen — not «all large `δ₂`»

[AF22] say *«let `δ₂ ≫ δ₁`»*, and the first shape one writes is «for all sufficiently large `δ₂`».
That shape forces a division `p := ⌊(δ₁+1)(δ₂-N₀)/2B⌋` and with it a floor error to carry through
every estimate.  It is also more than Lemma 2.11 wants: `AF.key_lemma_contradiction` asks only for
`∀ δ₁, ∃ δ₂`.  Choosing `δ₂ := N₀ + 2Bs` makes the count *exact* — no division anywhere — and the
lower bound on `p` comes out of the same choice.

## The degree bounds are free, and they are `b₁ = b₂ = 1`

`AF.key_lemma_of_auxiliary` needs `deg_{y_{ij}}P ≤ b₁δ₂` and `deg_z(coefficients) ≤ b₂δ₂` with
`b₁,b₂` independent of `δ₁,δ₂`; Step (LB)'s constant is `c₃ = m²b₁γ + b₂h(α)`.  Both come from
membership in `K[Y,z]_{δ₁,δ₂}` alone — `AF.degreeOf_le_of_mem_bidegP` and
`AF.natDegree_coeff_le_of_mem_bidegP`, proved here by induction on the spanning monomials — so
`b₁ = b₂ = 1`, provided `δ₁ ≤ δ₂`, which the choice of `δ₂` arranges.  Note that the *sharp*
`deg_{y_{ij}} ≤ δ₁` is what makes `b₁ = 1`: the total-degree bound already in the file
(`AF.totalDegree_le_of_mem_bidegP`) would only give `b₁ = m²`, harmless but wasteful.

## Contents

* `AF.degreeOf_le_of_mem_bidegP`, `AF.natDegree_coeff_le_of_mem_bidegP` and their `relComplP`
  corollaries — the two degree bounds of Step (LB), read off the bidegree;
* `AF.afConst`, `AF.relDim_succ_card_mul_le` — the constant of the bidegree repair;
* **`AF.exists_truncation_order`** — the dimension count met, with `δ₁δ₂ ≤ 4Bp`;
* `AF.frequently_evalAt_ne_zero_of_mem_relComplP` — Step (NV) for a member of the complement;
* **`AF.exists_auxiliary_quantitative`** — Step (AF) in the shape Steps (UB) and (LB) consume:
  the auxiliary family re-indexed by `ℕ`, its first non-zero index `v₀`, the degree bounds, and
  `E_p(MY,z) ∈ 𝓘`.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3, Step (AF) and the choice of parameters in §2.3.3.
* [AF17f] `plans/plan-formalize-AF17.html`: WP14, gap (3) of Stage 2, milestone M4.
-/

open Filter MvPolynomial

open scoped Polynomial

namespace AF

/-! ## The two degree bounds, read off the bidegree -/

section Degrees

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
/-- **The degree in each `y_{i,j}`** of a member of `K[Y,z]_{u,v}` is at most `u`.  This is the
sharp form; `AF.totalDegree_le_of_mem_bidegP` only gives `m²u`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem degreeOf_le_of_mem_bidegP {u v : ℕ} {P : MvPolynomial σ K[X]}
    (hP : P ∈ bidegP K σ u v) (s : σ) : P.degreeOf s ≤ u := by
  classical
  induction hP using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨k, a⟩, ⟨hk, -⟩, rfl⟩ := hx
      refine degreeOf_le_iff.2 fun m hm => ?_
      rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
      exact hk s
  | zero => simp
  | add x y _ _ hx hy => exact le_trans (degreeOf_add_le s x y) (max_le hx hy)
  | smul c x _ hx =>
      exact degreeOf_le_iff.2 fun m hm => degreeOf_le_iff.1 hx m (support_smul hm)

omit [Fintype σ] in
/-- **The degree in `z`** of every coefficient of a member of `K[Y,z]_{u,v}` is at most `v`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem natDegree_coeff_le_of_mem_bidegP {u v : ℕ} {P : MvPolynomial σ K[X]}
    (hP : P ∈ bidegP K σ u v) (ν : σ →₀ ℕ) : (P.coeff ν).natDegree ≤ v := by
  classical
  induction hP using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨k, a⟩, ⟨-, ha⟩, rfl⟩ := hx
      rw [coeff_monomial]
      split
      · rw [Polynomial.natDegree_X_pow]; exact ha
      · simp
  | zero => simp
  | add x y _ _ hx hy =>
      rw [MvPolynomial.coeff_add]
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hx hy)
  | smul c x _ hx =>
      rw [MvPolynomial.coeff_smul]
      exact le_trans (Polynomial.natDegree_smul_le _ _) hx

variable (I : Ideal (MvPolynomial σ (RatFunc K)))

omit [Fintype σ] [DecidableEq σ] in
/-- `b₁ = 1`: the degree in each `y_{i,j}` of an auxiliary polynomial is at most `δ₁`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem degreeOf_le_of_mem_relComplP {δ₁ δ₂ : ℕ} {P : MvPolynomial σ K[X]}
    (hP : P ∈ relComplP I δ₁ δ₂) (s : σ) : P.degreeOf s ≤ δ₁ :=
  degreeOf_le_of_mem_bidegP hP.2 s

omit [Fintype σ] in
/-- `b₂ = 1`: the degree in `z` of every coefficient of an auxiliary polynomial is at most `δ₂`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem natDegree_coeff_le_of_mem_relComplP {δ₁ δ₂ : ℕ} {P : MvPolynomial σ K[X]}
    (hP : P ∈ relComplP I δ₁ δ₂) (ν : σ →₀ ℕ) : (P.coeff ν).natDegree ≤ δ₂ :=
  natDegree_coeff_le_of_mem_bidegP hP.2 ν

end Degrees

/-! ## The constant of the bidegree repair -/

section Constant

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The constant of the bidegree repair**, `2^{m²⌈log₂(m²+1)⌉}`: the price of replacing
[AF22]'s false claim that `Y ↦ MY` preserves `K[Y,z]_{δ₁,δ₂}` by the true statement that it maps
it into `K[Y,z]_{m²δ₁,δ₂}`.  It depends on `m` alone, which is all Lemma 2.11 needs. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
def afConst (σ : Type*) [Fintype σ] : ℕ :=
  (2 ^ Fintype.card σ) ^ Nat.clog 2 (Fintype.card σ + 1)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem afConst_pos (σ : Type*) [Fintype σ] : 0 < afConst σ := by
  rw [afConst]
  positivity

variable (I : Ideal (MvPolynomial σ (RatFunc K)))

/-- Lemma 2.3 iterated to exactly the first index Step (AF) needs: inflating `δ₁` to
`(m²+1)δ₁` — the smallest index `AF.exists_auxiliary` admits — costs the factor `afConst σ`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem relDim_succ_card_mul_le (δ₁ v : ℕ) :
    relDim I ((Fintype.card σ + 1) * δ₁) v ≤ afConst σ * relDim I δ₁ v :=
  relDim_le_of_le_two_pow I (Nat.le_pow_clog (by norm_num) _)

end Constant

/-! ## The dimension count met -/

section Count

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (I : Ideal (MvPolynomial σ (RatFunc K)))

/-- **The choice of `δ₂` and of the truncation order.**  For every `δ₁` there are a `δ₂ ≥ δ₁` and
a truncation order `p > 0` meeting the dimension count of [AF22] Lemma 2.12 at the smallest
admissible first index `D = (m²+1)δ₁`, and with

  `δ₁δ₂ ≤ 4·afConst σ·p`.

The lower bound on `p` is the reason the whole file exists: Step (UB) reads the truncation order
as the exponent, so `p ≳ δ₁δ₂` with a constant depending on `m` alone is exactly [AF22]'s
`e^{-c₂δ₁δ₂q^k}` with `c₂` absolute.

The parameters are chosen, not quantified: `δ₂ := N₀+2Bs` and `p := N₀+1+(δ₁+1)s` with
`s := N₀+a+δ₁+1`, where `d(δ₁,v) = a + c(v-N₀)` is WP7's exact affine form.  The count then holds
*exactly*, with no division and no floor error. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem exists_truncation_order (hI : I ≠ ⊤) (δ₁ : ℕ) :
    ∃ δ₂ p : ℕ, δ₁ ≤ δ₂ ∧ 0 < δ₂ ∧ 0 < p ∧ δ₁ * δ₂ ≤ 4 * afConst σ * p ∧
      relDim I ((Fintype.card σ + 1) * δ₁) (p - 1) < (δ₁ + 1) * relDim I δ₁ δ₂ := by
  obtain ⟨c, N₀, hc, hlin⟩ := exists_relDim_eq I hI δ₁
  have hBpos : 0 < afConst σ := afConst_pos σ
  set B := afConst σ with hBdef
  set a := relDim I δ₁ N₀ with hadef
  set s := N₀ + a + δ₁ + 1 with hsdef
  have hs1 : 1 ≤ s := by omega
  have hsB : s ≤ 2 * B * s := Nat.le_mul_of_pos_left s (by omega)
  refine ⟨N₀ + 2 * B * s, N₀ + 1 + (δ₁ + 1) * s, ?_, ?_, ?_, ?_, ?_⟩
  · calc δ₁ ≤ s := by omega
      _ ≤ 2 * B * s := hsB
      _ ≤ N₀ + 2 * B * s := Nat.le_add_left _ _
  · calc 0 < s := hs1
      _ ≤ 2 * B * s := hsB
      _ ≤ N₀ + 2 * B * s := Nat.le_add_left _ _
  · positivity
  · -- the lower bound on the truncation order
    have h1 : δ₁ * N₀ ≤ 2 * B * (δ₁ * s) := by
      calc δ₁ * N₀ ≤ δ₁ * s := Nat.mul_le_mul_left δ₁ (by omega)
        _ ≤ 2 * B * (δ₁ * s) := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : δ₁ * s ≤ N₀ + 1 + (δ₁ + 1) * s :=
      le_trans (Nat.mul_le_mul_right s (Nat.le_succ δ₁)) (Nat.le_add_left _ _)
    calc δ₁ * (N₀ + 2 * B * s) = δ₁ * N₀ + 2 * B * (δ₁ * s) := by ring
      _ ≤ 2 * B * (δ₁ * s) + 2 * B * (δ₁ * s) := Nat.add_le_add_right h1 _
      _ = 4 * B * (δ₁ * s) := by ring
      _ ≤ 4 * B * (N₀ + 1 + (δ₁ + 1) * s) := Nat.mul_le_mul_left _ h2
  · -- the dimension count
    have hpm : N₀ + 1 + (δ₁ + 1) * s - 1 = N₀ + (δ₁ + 1) * s := by omega
    rw [hpm]
    refine lt_of_le_of_lt (relDim_succ_card_mul_le I δ₁ (N₀ + (δ₁ + 1) * s)) ?_
    rw [hlin _ (Nat.le_add_right _ _), hlin _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      Nat.add_sub_cancel_left]
    -- `B(a + c(δ₁+1)s) < (δ₁+1)(a + 2cBs)`, i.e. `Ba + Q < (δ₁+1)a + 2Q`
    have hQ : B * a < c * ((δ₁ + 1) * (B * s)) := by
      calc B * a + 1 ≤ B * a + B := by omega
        _ = B * (a + 1) := by ring
        _ ≤ B * s := Nat.mul_le_mul_left B (by omega)
        _ ≤ (δ₁ + 1) * (B * s) := Nat.le_mul_of_pos_left _ (by omega)
        _ ≤ c * ((δ₁ + 1) * (B * s)) := Nat.le_mul_of_pos_left _ (by omega)
    calc B * (a + c * ((δ₁ + 1) * s))
        = B * a + c * ((δ₁ + 1) * (B * s)) := by ring
      _ < c * ((δ₁ + 1) * (B * s)) + c * ((δ₁ + 1) * (B * s)) := by omega
      _ ≤ (δ₁ + 1) * a + (c * ((δ₁ + 1) * (B * s)) + c * ((δ₁ + 1) * (B * s))) :=
          Nat.le_add_left _ _
      _ = (δ₁ + 1) * (a + c * (2 * B * s)) := by ring

end Count

/-! ## The junction: the truncation order becomes Lemma 2.11's `c₂` -/

section Junction

/-- **What the lower bound on the truncation order is for.**  Step (UB)
(`AF.eventually_norm_evalAt_le_exp_of_sums`) produces `e^{-γq^k}` with `γ = pL/2Q`, `L = log(1/t)`
and `Q = q^{k₀}`; Lemma 2.11 (`AF.key_lemma_of_auxiliary`) demands `e^{-c₂δ₁δ₂q^k}` with `c₂`
**independent of `δ₁` and `δ₂`**.  `AF.exists_truncation_order`'s `δ₁δ₂ ≤ 4Bp` converts the first
into the second with

  `c₂ = L/(8BQ) = log(1/t) / (8·afConst σ·q^{k₀})`,

in which every ingredient — `t` and `k₀` fixed before the parameters vary, `B` a function of `m`
alone — is absolute.  That is the whole reason Step (AF) had to be done quantitatively. -/
@[category research solved, AMS 11 26, ref "AF22", group "af_mahler_alternative"]
theorem exp_neg_gamma_le {B δ₁ δ₂ p : ℕ} (hB : 0 < B) (hple : δ₁ * δ₂ ≤ 4 * B * p)
    {L Q x : ℝ} (hL : 0 ≤ L) (hQ : 0 < Q) (hx : 0 ≤ x) :
    Real.exp (-((p : ℝ) * L / (2 * Q) * x)) ≤ Real.exp (-(L / (8 * B * Q) * δ₁ * δ₂ * x)) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hpos : (0 : ℝ) < 8 * B * Q := mul_pos (mul_pos (by norm_num) hB') hQ
  have h1 : L * ((δ₁ : ℝ) * δ₂) ≤ L * (4 * B * p) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hple) hL
  have hkey : L / (8 * B * Q) * δ₁ * δ₂ ≤ (p : ℝ) * L / (2 * Q) := by
    rw [← sub_nonneg]
    have heq : (p : ℝ) * L / (2 * Q) - L / (8 * B * Q) * δ₁ * δ₂
        = (L * (4 * B * p) - L * ((δ₁ : ℝ) * δ₂)) / (8 * B * Q) := by
      field_simp
      ring
    rw [heq]
    exact div_nonneg (by linarith) hpos.le
  rw [Real.exp_le_exp]
  exact neg_le_neg (mul_le_mul_of_nonneg_right hkey hx)

end Junction

/-! ## Step (NV) for a member of the complement -/

section StepNV

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **Step (NV), packaged.**  A non-zero member of `𝓘^⊥(δ₁,δ₂)` is not a relation, hence does not
vanish at the iterates for infinitely many `k`.  This is `AF.toRat_notMem_of_mem_relComplP` and
`AF.frequently_evalAt_ne_zero` composed, in the form Lemma 2.11 consumes. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem frequently_evalAt_ne_zero_of_mem_relComplP {pt : ℕ → K} (hpt : Function.Injective pt)
    (Yval : ℕ → σ → K) {δ₁ δ₂ : ℕ} {P : MvPolynomial σ K[X]}
    (hP : P ∈ relComplP (relationIdeal hpt Yval) δ₁ δ₂) (hP0 : P ≠ 0) :
    ∃ᶠ n in atTop, evalAt pt Yval n P ≠ 0 :=
  frequently_evalAt_ne_zero hpt Yval (toRat_notMem_of_mem_relComplP _ hP hP0)

end StepNV

/-! ## Step (AF) in the shape Steps (UB) and (LB) consume -/

section Package

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (I : Ideal (MvPolynomial (ι × ι) (RatFunc K))) (M : Matrix ι ι K)
variable (F : MvPolynomial (ι × ι) (PowerSeries K))

/-- **[AF22] Step (AF), quantitatively** — Lemma 2.12 with its dimension count discharged and its
output re-indexed the way Steps (UB) and (LB) want it.

For every `δ₁` there are `δ₂`, a truncation order `p` with `δ₁δ₂ ≤ 4·afConst(ι×ι)·p`, an auxiliary
family `P : ℕ → K[Y,z]` supported in `[0,δ₁]` with every member in `𝓘^⊥(δ₁,δ₂)`, and a first
non-zero index `v₀ ≤ δ₁` — [AF22]'s *«let `v₀` be the smallest index such that `P_{v₀} ≠ 0`»* —
such that `E_p(MY,z) ∈ 𝓘`, where `E = ∑_{j≤δ₁} P_jF^j`.

The degree bounds are those of `AF.key_lemma_of_auxiliary` with `b₁ = b₂ = 1`, and Step (NV) is
`AF.frequently_evalAt_ne_zero_of_mem_relComplP` applied to `P v₀`, which the membership and
`P v₀ ≠ 0` supply. -/
@[category research solved, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem exists_auxiliary_quantitative (hI : I ≠ ⊤) (hF : F.totalDegree ≤ 1) (δ₁ : ℕ) :
    ∃ (δ₂ p v₀ : ℕ) (P : ℕ → MvPolynomial (ι × ι) K[X]),
      0 < δ₂ ∧ 0 < p ∧ δ₁ * δ₂ ≤ 4 * afConst (ι × ι) * p ∧
      v₀ < δ₁ + 1 ∧ (∀ j, j < v₀ → P j = 0) ∧ P v₀ ≠ 0 ∧
      (∀ j, P j ∈ relComplP I δ₁ δ₂) ∧
      (∀ s, (P v₀).degreeOf s ≤ δ₂) ∧ (∀ ν, ((P v₀).coeff ν).natDegree ≤ δ₂) ∧
      toRat K (ι × ι) (subMat K[X] M (truncMv K (ι × ι) p (bigSeries P F (δ₁ + 1)))) ∈ I := by
  classical
  obtain ⟨δ₂, p, hδ₁δ₂, hδ₂, hp, hple, hdim⟩ := exists_truncation_order I hI δ₁
  obtain ⟨Q, hQ0, hQI⟩ := exists_auxiliary I M F δ₁ δ₂ p hF
    (D := (Fintype.card (ι × ι) + 1) * δ₁) (le_of_eq (by ring)) hdim
  set P : ℕ → MvPolynomial (ι × ι) K[X] :=
    fun j => if h : j < δ₁ + 1 then (Q ⟨j, h⟩ : MvPolynomial (ι × ι) K[X]) else 0 with hPdef
  have hPQ : ∀ j : Fin (δ₁ + 1), P (j : ℕ) = (Q j : MvPolynomial (ι × ι) K[X]) := by
    intro j
    rw [hPdef]
    simp only [j.2, dif_pos, Fin.eta]
  have hPmem : ∀ j, P j ∈ relComplP I δ₁ δ₂ := by
    intro j
    rw [hPdef]
    by_cases h : j < δ₁ + 1
    · simpa only [h, dif_pos] using (Q ⟨j, h⟩).2
    · simpa only [h, dif_neg, not_false_iff] using Submodule.zero_mem _
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hQ0
  have hex : ∃ j, P j ≠ 0 := by
    refine ⟨(i : ℕ), ?_⟩
    rw [hPQ i]
    exact fun h => hi (Subtype.ext h)
  have hiP : P (i : ℕ) ≠ 0 := by rw [hPQ i]; exact fun h => hi (Subtype.ext h)
  refine ⟨δ₂, p, Nat.find hex, P, hδ₂, hp, hple, lt_of_le_of_lt (Nat.find_le hiP) i.2,
    fun j hj => not_not.1 (Nat.find_min hex hj), Nat.find_spec hex, hPmem,
    fun s => le_trans (degreeOf_le_of_mem_relComplP I (hPmem _) s) hδ₁δ₂,
    fun ν => natDegree_coeff_le_of_mem_relComplP I (hPmem _) ν, ?_⟩
  have hbs : bigSeries P F (δ₁ + 1)
      = ∑ j : Fin (δ₁ + 1), toPS K (ι × ι) (Q j : MvPolynomial (ι × ι) K[X]) * F ^ (j : ℕ) := by
    rw [bigSeries, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by rw [hPQ j]
  rw [hbs]
  exact hQI

end Package

end AF
