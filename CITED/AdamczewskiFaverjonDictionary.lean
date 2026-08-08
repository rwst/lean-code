/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonAnalyticUB
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Cauchy-product dictionary: the formal auxiliary series *is* the auxiliary function

WP12(a) of `plans/plan-formalize-AF17.html`.  `CITED/AdamczewskiFaverjonAuxiliary` produces the
**formal** auxiliary series `E = ∑_{j<N} P_j F^j ∈ K⟦z⟧[Y]` (`AF.exists_auxiliary`);
`CITED/AdamczewskiFaverjonAnalyticUB` estimates the **analytic** auxiliary function
`AF.bigAux φ P τ fs N Y u = ∑_{j<N} P_j(Y,u)·F(Y,u)^j`, and carries the identification of the two
as a hypothesis (`hreal`).  This file proves it.

## The route

Everything goes through one ring homomorphism.  Fix a point `Y : σ → ℂ` for the matrix variables;
then

  `AF.psEval φ Y : K⟦z⟧[Y] →+* ℂ⟦z⟧`,   `Y_s ↦ z⁰·Y_s`, coefficients along `φ`,

and `AF.coeff_psEval` says its `n`-th coefficient is exactly `AF.auxCoeff φ E n Y`, the polynomial
in `Y` that Step (UB) has to majorize.  So «`E` is the Taylor expansion of the auxiliary function»
becomes: the single power series `psEval φ Y E ∈ ℂ⟦z⟧` sums to that function on a disc.

That statement, `AF.IsSumOn`, is closed under the ring operations, and **the multiplicative case is
the Cauchy product** — the one piece Stage 1's dictionary (`AF.IsSumOnBall`,
`CITED/AdamczewskiFaverjonProof`) deliberately avoids, because there a *polynomial* multiplier
always sufficed.  Absolute convergence, which Mertens' theorem needs, is free: `AF.IsSumOn` asserts
convergence on the *whole* disc of radius `r`, so `AF.summable_norm_mul_pow_of_summable` gives
absolute convergence at every point strictly inside (`AF.IsSumOn.summable_norm_mul_pow`).

With that, `psEval` transports the shape of `E` term by term:

* `AF.isSumOn_psEval_toPS` — a polynomial coefficient sums to its value (`P_j`);
* `AF.isSumOn_psEval_linForm` — the linear form sums to `AF.formVal`, [AF22]'s `F(Y,z)`;
* `AF.isSumOn_psEval_bigSeries` — hence `E = ∑_j P_j F^j` sums to `AF.bigAux`.

## What is delivered

* **`AF.hasSum_auxCoeff_bigSeries`** — the hypothesis `hreal`: the series with coefficients
  `AF.auxCoeff φ E n Y` sums to `AF.bigAux φ P τ fs N Y u` for `‖u‖ < r`.
* **`AF.tail_auxFun_of_truncMv_eq_zero`** — the hypothesis `htail` of
  `AF.eventually_norm_evalAt_le_exp`, granted only [AF22] Lemma 2.7 (`hEp`, the vanishing of the
  truncation `E_p` along the branch), which is WP12(b) — **discharged in
  `CITED/AdamczewskiFaverjonGerm`** from a branch realization of the ambient field
  (`AF.eventually_norm_evalAt_le_exp_of_branch`).
* **`AF.summable_norm_auxCoeff_mul_pow`** and **`AF.tsum_norm_auxCoeff_le`** — the hypotheses
  `hsum` and `hmaj`: the majorant on the circle, uniform in `k` up to the geometric factor that
  `AF.eventually_le_exp_of_pow_div` absorbs.
* **`AF.linForm`**, with `AF.totalDegree_linForm_le` — the linear form `F` itself, which
  `AF.exists_auxiliary` had only as a variable subject to `F.totalDegree ≤ 1`.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3, Lemma 2.12 and (2.13)–(2.20).
* [AF17f] `plans/plan-formalize-AF17.html`: WP12(a).
-/

open Filter Metric Topology MvPolynomial

open scoped Polynomial

namespace AF

/-! ## `IsSumOn`: a complex power series and its sum on a disc -/

section IsSumOn

variable {r : ℝ}

/-- **A power series over `ℂ` and the function it sums to on the open disc of radius `r`.**  The
target of `AF.IsSeriesSumOn` after the coefficients have been pushed along `φ`; unlike that
predicate it is stated for a series *already* over `ℂ`, which is what makes it closed under
multiplication. -/
@[category API, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
def IsSumOn (r : ℝ) (g : PowerSeries ℂ) (H : ℂ → ℂ) : Prop :=
  ∀ u : ℂ, ‖u‖ < r → HasSum (fun n => PowerSeries.coeff n g * u ^ n) (H u)

@[category API, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem isSeriesSumOn_iff_isSumOn_map {K : Type*} [Field K] {φ : K →+* ℂ} {g : PowerSeries K}
    {H : ℂ → ℂ} : IsSeriesSumOn r φ g H ↔ IsSumOn r (g.map φ) H := by
  simp only [IsSeriesSumOn, IsSumOn, PowerSeries.coeff_map]

/-- **Absolute convergence strictly inside the disc.**  A power series that converges on the whole
disc of radius `r` converges absolutely at every radius `s < r` — the input Mertens' theorem needs,
and the reason `AF.IsSumOn` carries no separate summability hypothesis. -/
@[category research solved, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.summable_norm_mul_pow {g : PowerSeries ℂ} {H : ℂ → ℂ} (h : IsSumOn r g H) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s < r) : Summable fun n => ‖PowerSeries.coeff n g‖ * s ^ n := by
  set s' : ℝ := (s + r) / 2 with hs'
  have hss' : s < s' := by rw [hs']; linarith
  have hs'r : s' < r := by rw [hs']; linarith
  have hs'0 : 0 < s' := lt_of_le_of_lt hs0 hss'
  have hnorm : ‖(s' : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs'0.le]
    exact hs'r
  exact summable_norm_mul_pow_of_summable hs0 hss' (h (s' : ℂ) hnorm).summable

@[category API, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.summable_norm {g : PowerSeries ℂ} {H : ℂ → ℂ} (h : IsSumOn r g H) {u : ℂ}
    (hu : ‖u‖ < r) : Summable fun n => ‖PowerSeries.coeff n g * u ^ n‖ := by
  simpa only [norm_mul, norm_pow] using h.summable_norm_mul_pow (norm_nonneg u) hu

/-- A coerced polynomial sums to its value — the base case of the dictionary. -/
@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem isSumOn_coe (r : ℝ) (p : ℂ[X]) :
    IsSumOn r ((p : PowerSeries ℂ)) (fun u => p.eval u) := by
  intro u _
  have hz : ∀ n ∉ p.support, PowerSeries.coeff n (p : PowerSeries ℂ) * u ^ n = 0 := by
    intro n hn
    rw [Polynomial.coeff_coe, Polynomial.notMem_support_iff.1 hn, zero_mul]
  have hval : ∑ n ∈ p.support, PowerSeries.coeff n (p : PowerSeries ℂ) * u ^ n = p.eval u := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    exact Finset.sum_congr rfl fun n _ => by rw [Polynomial.coeff_coe]
  show HasSum (fun n => PowerSeries.coeff n (p : PowerSeries ℂ) * u ^ n) (p.eval u)
  rw [← hval]
  exact hasSum_sum_of_ne_finset_zero hz

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem isSumOn_C (r : ℝ) (c : ℂ) : IsSumOn r (PowerSeries.C c) (fun _ => c) := by
  have h := isSumOn_coe r (Polynomial.C c)
  simpa using h

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.add {g₁ g₂ : PowerSeries ℂ} {H₁ H₂ : ℂ → ℂ} (h₁ : IsSumOn r g₁ H₁)
    (h₂ : IsSumOn r g₂ H₂) : IsSumOn r (g₁ + g₂) (fun u => H₁ u + H₂ u) := by
  intro u hu
  have h := (h₁ u hu).add (h₂ u hu)
  refine h.congr_fun fun n => ?_
  rw [map_add, add_mul]

/-- **The Cauchy product of the terms of two power series**, in the `Finset.range` form that
Mathlib's Mertens theorem uses.  Purely formal; it is what lets the analytic and the
absolute-value halves of the dictionary share one computation. -/
@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem sum_range_coeff_mul (g₁ g₂ : PowerSeries ℂ) (u : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.coeff k g₁ * u ^ k) * (PowerSeries.coeff (n - k) g₂ * u ^ (n - k))
      = PowerSeries.coeff n (g₁ * g₂) * u ^ n := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hpow : u ^ k * u ^ (n - k) = u ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [← hpow]
  ring

/-- **The Cauchy product** — Mertens' theorem, in the form the dictionary needs.  This is the one
step that Stage 1's `AF.IsSumOnBall` avoids: there a *polynomial* multiplier made the rearrangement
finite, whereas `E = ∑_j P_j F^j` multiplies two genuine power series. -/
@[category research solved, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.mul {g₁ g₂ : PowerSeries ℂ} {H₁ H₂ : ℂ → ℂ} (h₁ : IsSumOn r g₁ H₁)
    (h₂ : IsSumOn r g₂ H₂) : IsSumOn r (g₁ * g₂) (fun u => H₁ u * H₂ u) := by
  intro u hu
  have ha : Summable fun n => ‖PowerSeries.coeff n g₁ * u ^ n‖ := h₁.summable_norm hu
  have hb : Summable fun n => ‖PowerSeries.coeff n g₂ * u ^ n‖ := h₂.summable_norm hu
  have hs := hasSum_sum_range_mul_of_summable_norm ha hb
  rw [(h₁ u hu).tsum_eq, (h₂ u hu).tsum_eq] at hs
  simpa only [sum_range_coeff_mul] using hs

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.pow {g : PowerSeries ℂ} {H : ℂ → ℂ} (h : IsSumOn r g H) :
    ∀ j : ℕ, IsSumOn r (g ^ j) (fun u => H u ^ j)
  | 0 => by simpa using isSumOn_C r 1
  | j + 1 => by
      have := (h.pow j).mul h
      simpa [pow_succ] using this

/-- **The absolute-value half of the dictionary**: `∑ₙ‖gₙ‖sⁿ < ∞`.  Step (UB) needs it because the
majorant `AF.norm_auxCoeff_le` is taken *coefficient by coefficient* in `Y`, which the analytic
statement `AF.IsSumOn` — one point `Y` at a time — does not see. -/
@[category API, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
def SumNormOn (s : ℝ) (g : PowerSeries ℂ) : Prop :=
  Summable fun n => ‖PowerSeries.coeff n g‖ * s ^ n

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_iff {s : ℝ} (hs0 : 0 ≤ s) {g : PowerSeries ℂ} :
    SumNormOn s g ↔ Summable fun n => ‖PowerSeries.coeff n g * (s : ℂ) ^ n‖ := by
  simp only [SumNormOn, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0]

/-- Convergence on a disc gives absolute convergence at every smaller radius. -/
@[category API, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.sumNormOn {g : PowerSeries ℂ} {H : ℂ → ℂ} (h : IsSumOn r g H) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s < r) : SumNormOn s g :=
  h.summable_norm_mul_pow hs0 hs

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_zero (s : ℝ) : SumNormOn s 0 := by
  simp [SumNormOn]

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_coe (s : ℝ) (p : ℂ[X]) : SumNormOn s (p : PowerSeries ℂ) := by
  refine summable_of_ne_finset_zero (s := p.support) fun n hn => ?_
  rw [Polynomial.coeff_coe, Polynomial.notMem_support_iff.1 hn, norm_zero, zero_mul]

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_C (s : ℝ) (c : ℂ) : SumNormOn s (PowerSeries.C c) := by
  simpa using sumNormOn_coe s (Polynomial.C c)

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_one (s : ℝ) : SumNormOn s 1 := by
  simpa using sumNormOn_coe s 1

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_add {s : ℝ} (hs0 : 0 ≤ s) {g₁ g₂ : PowerSeries ℂ} (h₁ : SumNormOn s g₁)
    (h₂ : SumNormOn s g₂) : SumNormOn s (g₁ + g₂) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hs0 n))
    (fun n => ?_) (h₁.add h₂)
  rw [map_add]
  calc ‖PowerSeries.coeff n g₁ + PowerSeries.coeff n g₂‖ * s ^ n
      ≤ (‖PowerSeries.coeff n g₁‖ + ‖PowerSeries.coeff n g₂‖) * s ^ n :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hs0 n)
    _ = ‖PowerSeries.coeff n g₁‖ * s ^ n + ‖PowerSeries.coeff n g₂‖ * s ^ n := by ring

/-- The Cauchy product, on the absolute values. -/
@[category research solved, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_mul {s : ℝ} (hs0 : 0 ≤ s) {g₁ g₂ : PowerSeries ℂ} (h₁ : SumNormOn s g₁)
    (h₂ : SumNormOn s g₂) : SumNormOn s (g₁ * g₂) := by
  rw [sumNormOn_iff hs0] at h₁ h₂ ⊢
  simpa only [sum_range_coeff_mul] using summable_norm_sum_mul_range_of_summable_norm h₁ h₂

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_pow {s : ℝ} (hs0 : 0 ≤ s) {g : PowerSeries ℂ} (h : SumNormOn s g) :
    ∀ j : ℕ, SumNormOn s (g ^ j)
  | 0 => by simpa using sumNormOn_one s
  | j + 1 => by
      have := sumNormOn_mul hs0 (sumNormOn_pow hs0 h j) h
      simpa [pow_succ] using this

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem sumNormOn_finsetSum {α : Type*} {s : ℝ} (hs0 : 0 ≤ s) (T : Finset α)
    {g : α → PowerSeries ℂ} (h : ∀ x ∈ T, SumNormOn s (g x)) : SumNormOn s (∑ x ∈ T, g x) := by
  classical
  induction T using Finset.induction with
  | empty => simpa using sumNormOn_zero s
  | insert x T hx ih =>
      rw [Finset.sum_insert hx]
      exact sumNormOn_add hs0 (h x (Finset.mem_insert_self x T))
        (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem isSumOn_finsetSum {ι : Type*} (s : Finset ι) {g : ι → PowerSeries ℂ} {H : ι → ℂ → ℂ}
    (h : ∀ i ∈ s, IsSumOn r (g i) (H i)) :
    IsSumOn r (∑ i ∈ s, g i) (fun u => ∑ i ∈ s, H i u) := by
  intro u hu
  have hs := hasSum_sum (f := fun i n => PowerSeries.coeff n (g i) * u ^ n)
    (a := fun i => H i u) (s := s) fun i hi => h i hi u hu
  have key : ∀ n : ℕ, ∑ i ∈ s, PowerSeries.coeff n (g i) * u ^ n
      = PowerSeries.coeff n (∑ i ∈ s, g i) * u ^ n := by
    intro n
    rw [map_sum, Finset.sum_mul]
  simpa only [key] using hs

end IsSumOn

/-! ## `psEval`: the auxiliary series as one complex power series -/

section PsEval

variable {K : Type*} [Field K] {σ : Type*}

/-- **The evaluation of the matrix variables at a complex point**, leaving `z` formal:
`K⟦z⟧[Y] →+* ℂ⟦z⟧`.  Its `n`-th coefficient is `AF.auxCoeff`, so it is the single object that
carries the whole formal-to-analytic dictionary. -/
@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def psEval (φ : K →+* ℂ) (Y : σ → ℂ) :
    MvPolynomial σ (PowerSeries K) →+* PowerSeries ℂ :=
  eval₂Hom (PowerSeries.map φ) fun s => PowerSeries.C (Y s)

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem psEval_eq (φ : K →+* ℂ) (Y : σ → ℂ) (E : MvPolynomial σ (PowerSeries K)) :
    psEval φ Y E
      = ∑ ν ∈ E.support, PowerSeries.map φ (E.coeff ν) * PowerSeries.C (monoVal Y ν) := by
  rw [psEval, coe_eval₂Hom, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  rw [monoVal, Finsupp.prod, map_prod]
  exact Finset.prod_congr rfl fun s _ => by rw [map_pow]

/-- **The bridge**: the coefficients of `AF.psEval` are the `AF.auxCoeff` of Step (UB). -/
@[category research solved, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeff_psEval (φ : K →+* ℂ) (Y : σ → ℂ) (E : MvPolynomial σ (PowerSeries K)) (n : ℕ) :
    PowerSeries.coeff n (psEval φ Y E) = auxCoeff φ E n Y := by
  rw [psEval_eq, map_sum, auxCoeff]
  exact Finset.sum_congr rfl fun ν _ => by
    rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_map]

/-- **The polynomial coefficients realize to their values.**  `AF.toPS` embeds `K[Y,z]` in
`K⟦z⟧[Y]`; after `AF.psEval` the result is a polynomial in `z`, and it sums to `AF.mvEvalC`. -/
@[category research solved, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem isSumOn_psEval_toPS (r : ℝ) (φ : K →+* ℂ) (Y : σ → ℂ) (Q : MvPolynomial σ K[X]) :
    IsSumOn r (psEval φ Y (toPS K σ Q))
      (fun u => mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) Q)) := by
  induction Q using MvPolynomial.induction_on with
  | C p =>
      have hC : toPS K σ (C p) = C ((p : PowerSeries K)) := by simp [toPS]
      have h1 : psEval φ Y (toPS K σ (C p)) = ((p.map φ : ℂ[X]) : PowerSeries ℂ) := by
        rw [hC]
        simp only [psEval, coe_eval₂Hom, eval₂_C]
        exact Polynomial.polynomial_map_coe.symm
      have h2 : ∀ u : ℂ, mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) (C p))
          = (p.map φ).eval u := by
        intro u
        simp [mvEvalC]
      rw [h1]
      simpa only [h2] using isSumOn_coe r (p.map φ)
  | add P Q hP hQ =>
      have h1 : psEval φ Y (toPS K σ (P + Q))
          = psEval φ Y (toPS K σ P) + psEval φ Y (toPS K σ Q) := by
        rw [map_add, map_add]
      have h2 : ∀ u : ℂ, mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) (P + Q))
          = mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) P)
            + mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) Q) := by
        intro u
        rw [map_add, map_add]
      rw [h1]
      simpa only [h2] using hP.add hQ
  | mul_X P s hP =>
      have h1 : psEval φ Y (toPS K σ (P * X s))
          = psEval φ Y (toPS K σ P) * PowerSeries.C (Y s) := by
        rw [map_mul, map_mul]
        congr 1
        simp [toPS, psEval]
      have h2 : ∀ u : ℂ, mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) (P * X s))
          = mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) P) * Y s := by
        intro u
        rw [map_mul, map_mul]
        congr 1
        simp [mvEvalC]
      rw [h1]
      simpa only [h2] using hP.mul (isSumOn_C r (Y s))

end PsEval

/-! ## Coefficientwise absolute convergence -/

section CoeffSummable

variable {K : Type*} [Field K] {σ : Type*} {s : ℝ} {φ : K →+* ℂ}

/-- **The coefficients of `E ∈ K⟦z⟧[Y]` are absolutely convergent at radius `s`.**  Step (UB)
needs this and not just `AF.IsSumOn`, because its majorant `AF.norm_auxCoeff_le` is taken
coefficient by coefficient in `Y`, so that it holds uniformly along the circle. -/
@[category API, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
def CoeffSummable (s : ℝ) (φ : K →+* ℂ) (E : MvPolynomial σ (PowerSeries K)) : Prop :=
  ∀ ν : σ →₀ ℕ, SumNormOn s ((E.coeff ν).map φ)

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem CoeffSummable.summable {E : MvPolynomial σ (PowerSeries K)} (h : CoeffSummable s φ E)
    (ν : σ →₀ ℕ) : Summable fun n => ‖φ (PowerSeries.coeff n (E.coeff ν))‖ * s ^ n := by
  simpa only [SumNormOn, PowerSeries.coeff_map] using h ν

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_C [DecidableEq σ] {g : PowerSeries K} (hg : SumNormOn s (g.map φ)) :
    CoeffSummable s φ (C g : MvPolynomial σ (PowerSeries K)) := by
  intro ν
  rw [MvPolynomial.coeff_C]
  split_ifs with h
  · exact hg
  · simpa using sumNormOn_zero s

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_X [DecidableEq σ] (t : σ) :
    CoeffSummable s φ (X t : MvPolynomial σ (PowerSeries K)) := by
  intro ν
  rw [MvPolynomial.coeff_X]
  split_ifs with h
  · simpa using sumNormOn_one s
  · simpa using sumNormOn_zero s

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_add [DecidableEq σ] (hs0 : 0 ≤ s)
    {E₁ E₂ : MvPolynomial σ (PowerSeries K)} (h₁ : CoeffSummable s φ E₁)
    (h₂ : CoeffSummable s φ E₂) : CoeffSummable s φ (E₁ + E₂) := by
  intro ν
  rw [MvPolynomial.coeff_add, map_add]
  exact sumNormOn_add hs0 (h₁ ν) (h₂ ν)

/-- **The Cauchy product, coefficientwise in `Y`.**  `MvPolynomial.coeff_mul` turns a coefficient
of a product into a finite sum of products of power series, and `AF.sumNormOn_mul` handles each. -/
@[category research solved, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_mul [DecidableEq σ] (hs0 : 0 ≤ s)
    {E₁ E₂ : MvPolynomial σ (PowerSeries K)} (h₁ : CoeffSummable s φ E₁)
    (h₂ : CoeffSummable s φ E₂) : CoeffSummable s φ (E₁ * E₂) := by
  intro ν
  rw [MvPolynomial.coeff_mul, map_sum]
  refine sumNormOn_finsetSum hs0 _ fun x _ => ?_
  rw [map_mul]
  exact sumNormOn_mul hs0 (h₁ x.1) (h₂ x.2)

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_pow [DecidableEq σ] (hs0 : 0 ≤ s) {E : MvPolynomial σ (PowerSeries K)}
    (h : CoeffSummable s φ E) : ∀ j : ℕ, CoeffSummable s φ (E ^ j)
  | 0 => by
      rw [pow_zero, ← MvPolynomial.C_1]
      exact coeffSummable_C (by simpa using sumNormOn_one s)
  | j + 1 => by
      have := coeffSummable_mul hs0 (coeffSummable_pow hs0 h j) h
      simpa [pow_succ] using this

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_finsetSum [DecidableEq σ] {α : Type*} (hs0 : 0 ≤ s) (T : Finset α)
    {E : α → MvPolynomial σ (PowerSeries K)} (h : ∀ x ∈ T, CoeffSummable s φ (E x)) :
    CoeffSummable s φ (∑ x ∈ T, E x) := by
  intro ν
  rw [MvPolynomial.coeff_sum, map_sum]
  exact sumNormOn_finsetSum hs0 _ fun x hx => h x hx ν

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_toPS (s : ℝ) (φ : K →+* ℂ) (Q : MvPolynomial σ K[X]) :
    CoeffSummable s φ (toPS K σ Q) := by
  intro ν
  have h : (toPS K σ Q).coeff ν = ((Q.coeff ν : K[X]) : PowerSeries K) := by
    simp [toPS, MvPolynomial.coeff_map]
  rw [h, ← Polynomial.polynomial_map_coe]
  exact sumNormOn_coe s _

end CoeffSummable

/-! ## The linear form `F` -/

section LinForm

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- **[AF22]'s linear form** `F(Y,z) = ∑_{i,j} τ_i·Y_{i,j}·f_j(z)`.  `AF.exists_auxiliary` takes
it as a variable subject only to `F.totalDegree ≤ 1`; this is the form itself, and
`AF.totalDegree_linForm_le` discharges that hypothesis. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def linForm (τ : ι → K) (f : ι → PowerSeries K) :
    MvPolynomial (ι × ι) (PowerSeries K) :=
  ∑ i : ι, ∑ j : ι, C (PowerSeries.C (τ i) * f j) * X (i, j)

@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem totalDegree_linForm_le (τ : ι → K) (f : ι → PowerSeries K) :
    (linForm τ f).totalDegree ≤ 1 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have h1 : (C (PowerSeries.C (τ i) * f j) :
      MvPolynomial (ι × ι) (PowerSeries K)).totalDegree = 0 := MvPolynomial.totalDegree_C _
  have h2 : (X (i, j) : MvPolynomial (ι × ι) (PowerSeries K)).totalDegree ≤ 1 := by
    simp [MvPolynomial.X, Finsupp.sum_single_index]
  omega

@[category API, AMS 11 13 30, ref "AF22", group "af_mahler_alternative"]
theorem psEval_linForm (φ : K →+* ℂ) (M : Matrix ι ι ℂ) (τ : ι → K) (f : ι → PowerSeries K) :
    psEval φ (fun t : ι × ι => M t.1 t.2) (linForm τ f)
      = ∑ i : ι, ∑ j : ι,
          PowerSeries.C (φ (τ i)) * ((f j).map φ) * PowerSeries.C (M i j) := by
  rw [linForm, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  congr 1
  · simp only [psEval, coe_eval₂Hom, eval₂_C, map_mul, PowerSeries.map_C]
  · simp only [psEval, coe_eval₂Hom, eval₂_X]

/-- **The linear form realizes to `AF.formVal`** — [AF22]'s `F(Y,z)`, the object whose vanishing
at `(A_k(α),α^{q^k})` collapses the auxiliary function to `P_{v₀}`. -/
@[category research solved, AMS 11 13 30, ref "AF22", group "af_mahler_alternative"]
theorem isSumOn_psEval_linForm {r : ℝ} (φ : K →+* ℂ) (M : Matrix ι ι ℂ) (τ : ι → K)
    {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ} (hf : ∀ j, IsSumOn r ((f j).map φ) (fs j)) :
    IsSumOn r (psEval φ (fun t : ι × ι => M t.1 t.2) (linForm τ f))
      (fun u => formVal (fun i => φ (τ i)) fs M u) := by
  rw [psEval_linForm]
  have h : IsSumOn r
      (∑ i : ι, ∑ j : ι, PowerSeries.C (φ (τ i)) * ((f j).map φ) * PowerSeries.C (M i j))
      (fun u => ∑ i : ι, ∑ j : ι, φ (τ i) * fs j u * M i j) :=
    isSumOn_finsetSum _ fun i _ => isSumOn_finsetSum _ fun j _ =>
      ((isSumOn_C r (φ (τ i))).mul (hf j)).mul (isSumOn_C r (M i j))
  have heq : ∀ u : ℂ, (∑ i : ι, ∑ j : ι, φ (τ i) * fs j u * M i j)
      = formVal (fun i => φ (τ i)) fs M u := by
    intro u
    rw [formVal]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simpa only [heq] using h

@[category API, AMS 11 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_linForm [DecidableEq ι] {s : ℝ} (hs0 : 0 ≤ s) {φ : K →+* ℂ} (τ : ι → K)
    {f : ι → PowerSeries K} (hf : ∀ j, SumNormOn s ((f j).map φ)) :
    CoeffSummable s φ (linForm τ f) := by
  rw [linForm]
  refine coeffSummable_finsetSum hs0 _ fun i _ => coeffSummable_finsetSum hs0 _ fun j _ => ?_
  refine coeffSummable_mul hs0 (coeffSummable_C ?_) (coeffSummable_X _)
  rw [map_mul, PowerSeries.map_C]
  exact sumNormOn_mul hs0 (sumNormOn_C s _) (hf j)

end LinForm

/-! ## The auxiliary series, and the auxiliary function it sums to -/

section BigSeries

variable {K : Type*} [Field K] {σ : Type*}

/-- **The formal auxiliary series `E = ∑_{j<N} P_j F^j`** of [AF22] Lemma 2.12, exactly as
`AF.exists_auxiliary` builds it. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def bigSeries (P : ℕ → MvPolynomial σ K[X]) (F : MvPolynomial σ (PowerSeries K))
    (N : ℕ) : MvPolynomial σ (PowerSeries K) :=
  ∑ j ∈ Finset.range N, toPS K σ (P j) * F ^ j

@[category research solved, AMS 11 13 30, ref "AF22", group "af_mahler_alternative"]
theorem isSumOn_psEval_bigSeries {r : ℝ} (φ : K →+* ℂ) (Y : σ → ℂ)
    (P : ℕ → MvPolynomial σ K[X]) (F : MvPolynomial σ (PowerSeries K)) (N : ℕ) {G : ℂ → ℂ}
    (hF : IsSumOn r (psEval φ Y F) G) :
    IsSumOn r (psEval φ Y (bigSeries P F N))
      (fun u => ∑ j ∈ Finset.range N,
        mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) (P j)) * G u ^ j) := by
  rw [bigSeries, map_sum]
  refine isSumOn_finsetSum _ fun j _ => ?_
  rw [map_mul, map_pow]
  exact (isSumOn_psEval_toPS r φ Y (P j)).mul (hF.pow j)

@[category API, AMS 11 13 30, ref "AF22", group "af_mahler_alternative"]
theorem coeffSummable_bigSeries [DecidableEq σ] {s : ℝ} (hs0 : 0 ≤ s) {φ : K →+* ℂ}
    (P : ℕ → MvPolynomial σ K[X]) {F : MvPolynomial σ (PowerSeries K)}
    (hF : CoeffSummable s φ F) (N : ℕ) : CoeffSummable s φ (bigSeries P F N) := by
  rw [bigSeries]
  exact coeffSummable_finsetSum hs0 _ fun j _ =>
    coeffSummable_mul hs0 (coeffSummable_toPS s φ (P j)) (coeffSummable_pow hs0 hF j)

/-- **`hsum`**: the coefficients of the auxiliary function are absolutely summable at every radius
`s` inside the disc of realization. -/
@[category research solved, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem summable_norm_auxCoeff_mul_pow {r : ℝ} {φ : K →+* ℂ} {E : MvPolynomial σ (PowerSeries K)}
    {Y : σ → ℂ} {G : ℂ → ℂ} (h : IsSumOn r (psEval φ Y E) G) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < r) :
    Summable fun n => ‖auxCoeff φ E n Y‖ * s ^ n := by
  simpa only [coeff_psEval] using h.summable_norm_mul_pow hs0 hs

end BigSeries

/-! ## `hreal` and `htail` -/

section Dictionary

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The dictionary — WP12(a).**  The formal auxiliary series `E = ∑_{j<N} P_j F^j` of
`AF.exists_auxiliary` *is* the Taylor expansion in `z` of the analytic auxiliary function
`AF.bigAux`.  This is the hypothesis `hreal` that `CITED/AdamczewskiFaverjonAnalyticUB` carries. -/
@[category research solved, AMS 11 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem hasSum_auxCoeff_bigSeries {r : ℝ} (φ : K →+* ℂ) (M : Matrix ι ι ℂ)
    (P : ℕ → MvPolynomial (ι × ι) K[X]) (τ : ι → K) {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ}
    (hf : ∀ j, IsSumOn r ((f j).map φ) (fs j)) (N : ℕ) {u : ℂ} (hu : ‖u‖ < r) :
    HasSum (fun n => auxCoeff φ (bigSeries P (linForm τ f) N) n
        (fun t : ι × ι => M t.1 t.2) * u ^ n)
      (bigAux φ P (fun i => φ (τ i)) fs N M u) := by
  have h := isSumOn_psEval_bigSeries φ (fun t : ι × ι => M t.1 t.2) P (linForm τ f) N
    (isSumOn_psEval_linForm φ M τ hf)
  simpa only [coeff_psEval, bigAux] using h u hu

/-- **`htail`**: the hypothesis of `AF.eventually_norm_evalAt_le_exp`, granted only the vanishing
of the truncated auxiliary function along the branch.  That vanishing — [AF22] Lemma 2.7 combined
with Lemma 2.12 — is the *other* realization map, WP12(b), proved in
`CITED/AdamczewskiFaverjonGerm`; everything else is proved here. -/
@[category research solved, AMS 11 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem tail_auxFun_of_truncMv_eq_zero {r : ℝ} (φ : K →+* ℂ) (M : Matrix ι ι ℂ)
    (P : ℕ → MvPolynomial (ι × ι) K[X]) (τ : ι → K) {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ}
    (hf : ∀ j, IsSumOn r ((f j).map φ) (fs j)) {v₀ N p : ℕ} (hP : ∀ j, j < v₀ → P j = 0)
    {u : ℂ} (hu : ‖u‖ < r)
    (hEp : mvEvalC u (fun t : ι × ι => M t.1 t.2)
      (MvPolynomial.map (Polynomial.mapRingHom φ)
        (truncMv K (ι × ι) p (bigSeries P (linForm τ f) N))) = 0) :
    auxFun φ P (fun i => φ (τ i)) fs v₀ (N - v₀) M u
        * formVal (fun i => φ (τ i)) fs M u ^ v₀
      = ∑' n : ℕ, auxCoeff φ (bigSeries P (linForm τ f) N) (n + p)
          (fun t : ι × ι => M t.1 t.2) * u ^ (n + p) := by
  have hre := hasSum_auxCoeff_bigSeries φ M P τ hf N hu
  rw [← bigAux_eq_auxFun_mul φ P (fun i => φ (τ i)) fs hP M u]
  exact tail_of_realization_truncMv hre hEp

end Dictionary

/-! ## `hmaj`: the majorant on the circle -/

section Majorant

variable {K : Type*} [Field K] {σ : Type*}

/-- The constant of the majorant: `∑ₙ(∑_ν‖φE_{ν,n}‖)sⁿ`, which depends on the auxiliary series
and the radius alone — not on the point, and so not on `k`. -/
@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def auxMajorant (s : ℝ) (φ : K →+* ℂ) (E : MvPolynomial σ (PowerSeries K)) : ℝ :=
  ∑' n : ℕ, (∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * s ^ n

@[category API, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem summable_auxMajorant {s : ℝ} {φ : K →+* ℂ} {E : MvPolynomial σ (PowerSeries K)}
    (hCS : CoeffSummable s φ E) :
    Summable fun n => (∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * s ^ n := by
  have key : ∀ n : ℕ, (∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * s ^ n
      = ∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖ * s ^ n :=
    fun n => Finset.sum_mul _ _ _
  simpa only [key] using summable_sum fun ν _ => hCS.summable ν

/-- **The majorant, at one point.**  `AF.norm_auxCoeff_le` termwise, summed. -/
@[category research solved, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem tsum_norm_auxCoeff_le {s : ℝ} (hs0 : 0 ≤ s) {φ : K →+* ℂ}
    {E : MvPolynomial σ (PowerSeries K)} (hCS : CoeffSummable s φ E) {B : ℝ} (hB : 1 ≤ B)
    {Y : σ → ℂ} (hY : ∀ t, ‖Y t‖ ≤ B) :
    ∑' n : ℕ, ‖auxCoeff φ E n Y‖ * s ^ n ≤ auxMajorant s φ E * B ^ E.totalDegree := by
  have hmaj := summable_auxMajorant hCS
  have hle : ∀ n : ℕ, ‖auxCoeff φ E n Y‖ * s ^ n
      ≤ ((∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * s ^ n)
        * B ^ E.totalDegree := by
    intro n
    have h := norm_auxCoeff_le (φ := φ) (E := E) hB hY n
    calc ‖auxCoeff φ E n Y‖ * s ^ n
        ≤ ((∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * B ^ E.totalDegree)
            * s ^ n := mul_le_mul_of_nonneg_right h (pow_nonneg hs0 n)
      _ = ((∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * s ^ n)
            * B ^ E.totalDegree := by ring
  have hsumR : Summable fun n =>
      ((∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * s ^ n) * B ^ E.totalDegree :=
    hmaj.mul_right _
  have hsumL : Summable fun n => ‖auxCoeff φ E n Y‖ * s ^ n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hs0 n)) hle hsumR
  calc ∑' n : ℕ, ‖auxCoeff φ E n Y‖ * s ^ n
      ≤ ∑' n : ℕ, ((∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * s ^ n)
          * B ^ E.totalDegree := Summable.tsum_le_tsum hle hsumL hsumR
    _ = auxMajorant s φ E * B ^ E.totalDegree := tsum_mul_right

/-- **`hmaj`, in the shape Step (UB) asks for**: a bound `M·Dᵏ` with `M` and `D ≥ 1` independent
of `k`, from a geometric bound `B₁B₂ᵏ` on the point.  The geometric factor is exactly what
`AF.eventually_le_exp_of_pow_div` absorbs. -/
@[category research solved, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem tsum_norm_auxCoeff_le_of_geometric {s : ℝ} (hs0 : 0 ≤ s) {φ : K →+* ℂ}
    {E : MvPolynomial σ (PowerSeries K)} (hCS : CoeffSummable s φ E) {B₁ B₂ : ℝ} (hB₁ : 1 ≤ B₁)
    (hB₂ : 1 ≤ B₂) {k : ℕ} {Y : σ → ℂ} (hY : ∀ t, ‖Y t‖ ≤ B₁ * B₂ ^ k) :
    ∑' n : ℕ, ‖auxCoeff φ E n Y‖ * s ^ n
      ≤ (auxMajorant s φ E * B₁ ^ E.totalDegree) * (B₂ ^ E.totalDegree) ^ k := by
  have hp : (1 : ℝ) ≤ B₂ ^ k := one_le_pow₀ hB₂
  have hB : (1 : ℝ) ≤ B₁ * B₂ ^ k := by nlinarith
  refine (tsum_norm_auxCoeff_le hs0 hCS hB hY).trans_eq ?_
  have hexp : (B₁ * B₂ ^ k) ^ E.totalDegree
      = B₁ ^ E.totalDegree * (B₂ ^ E.totalDegree) ^ k := by
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k E.totalDegree]
  rw [hexp, mul_assoc]

end Majorant

/-! ## `hmaj` along the analytic branch -/

section MajorantTheta

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The majorant along `Θ_k`.**  `AF.norm_theta_le` supplies the geometric bound on the point,
so the coefficients of the auxiliary function on the circle are majorized by `M·Dᵏ` with `M` and
`D` free of `k`: the hypothesis `hmaj` of `AF.eventually_norm_evalAt_le_exp`. -/
@[category research solved, AMS 11 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem tsum_norm_auxCoeff_theta_le {s : ℝ} (hs0 : 0 ≤ s) {φ : K →+* ℂ}
    {E : MvPolynomial (ι × ι) (PowerSeries K)} (hCS : CoeffSummable s φ E) {q k₀ k : ℕ}
    (hq : 1 ≤ q) {A : Matrix ι ι ℂ[X]} {a : Matrix ι ι ℂ} {Φ : ℂ → Matrix ι ι ℂ}
    {t Cb B₀ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hC1 : 1 ≤ Cb) (hB₀ : 0 ≤ B₀)
    (hA : ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(A i j).eval z‖ ≤ Cb) {z : ℂ} (hz : ‖z‖ ≤ t)
    (haΦ : ∀ i j, ‖(a * Φ z) i j‖ ≤ B₀) (h1B : 1 ≤ (Fintype.card ι : ℝ) * B₀)
    (h1C : 1 ≤ (Fintype.card ι : ℝ) * Cb) :
    ∑' n : ℕ, ‖auxCoeff φ E n (fun w : ι × ι => theta q k₀ A a Φ k z w.1 w.2)‖ * s ^ n
      ≤ (auxMajorant s φ E * ((Fintype.card ι : ℝ) * B₀) ^ E.totalDegree)
        * (((Fintype.card ι : ℝ) * Cb) ^ E.totalDegree) ^ k := by
  refine tsum_norm_auxCoeff_le_of_geometric hs0 hCS h1B h1C fun w => ?_
  refine (norm_theta_le hq ht0 ht1 hC1 hB₀ hA hz haΦ w.1 w.2).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1C (Nat.sub_le k k₀))
    (le_trans zero_le_one h1B)

end MajorantTheta

/-! ## Step (UB), with the dictionary supplied -/

section Capstone

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`𝔉` does not depend on `k`.**  [AF22] (2.6) along the branch: `Θ_k = aΦ·A_{k-k₀}` and the
iterated Mahler relation absorb the factor `A_{k-k₀}(z)`, so `F(Θ_k(z), z^{q^{k-k₀}})` is the
`k`-independent function `F(aΦ(z), z)`.  This is what lets Step (UB) divide by one fixed `𝔉`. -/
@[category research solved, AMS 11 15 39, ref "AF22", group "af_mahler_alternative"]
theorem formVal_theta {q k₀ k : ℕ} {A : Matrix ι ι ℂ[X]} {fs : ι → ℂ → ℂ} {S : Set ℂ}
    (hS : ∀ z ∈ S, z ^ q ∈ S) (hf : IsMahlerSolution q A fs S) (τ : ι → ℂ) (a : Matrix ι ι ℂ)
    (Φ : ℂ → Matrix ι ι ℂ) {z : ℂ} (hz : z ∈ S) :
    formVal τ fs (theta q k₀ A a Φ k z) (z ^ q ^ (k - k₀)) = formVal τ fs (a * Φ z) z := by
  rw [theta]
  exact formVal_mul_evalMat_iterMatrix hS hf τ (a * Φ z) (k - k₀) hz

/-- **Step (UB), with everything the dictionary can supply supplied.**  Compared with
`AF.eventually_norm_evalAt_le_exp`, the four hypotheses `hgval`, `hsum`, `hmaj` and `htail` are
gone: they are now theorems of this file.  What is left is the analytic layer's own business —
the analyticity of the auxiliary function on the closed disc, the geometry of the circle, Lemma
2.8 at one good `k₀` — and **`hEp`**, the vanishing of the truncated auxiliary function along the
branch, which is [AF22] Lemma 2.7 transported by the germ realization: WP12(b).

That single remaining hypothesis is the exact statement of what WP12(b) owes.  It is discharged in
`CITED/AdamczewskiFaverjonGerm` — `AF.mvEvalC_theta_eq_zero_of_branch`, from a branch realization
of the ambient field together with [AF22] Lemmas 2.5 and 2.12 — so that
`AF.eventually_norm_evalAt_le_exp_of_branch` is this statement with `hEp` gone. -/
@[category research solved, AMS 11 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem eventually_norm_evalAt_le_exp_of_vanishing {q k₀ p v₀ N : ℕ} (hq : 2 ≤ q) (hvN : v₀ < N)
    {A : Matrix ι ι K[X]} {α : K} (φ : K →+* ℂ) {P : ℕ → MvPolynomial (ι × ι) K[X]}
    (hP : ∀ j, j < v₀ → P j = 0) (τ : ι → K) {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ}
    {a : Matrix ι ι ℂ} {Φ : ℂ → Matrix ι ι ℂ} {ξ : ℂ} {S : Set ℂ}
    {ρ r s t m γ Cb B₀ : ℝ}
    (hreal : ∀ j, IsSumOn r ((f j).map φ) (fs j))
    (hS : ∀ z ∈ S, z ^ q ∈ S) (hmah : IsMahlerSolution q (mapMat φ A) fs S) (hα : φ α ∈ S)
    (hL : formVal (fun i => φ (τ i)) fs 1 (φ α) = 0) (hSsph : ∀ z ∈ sphere ξ ρ, z ∈ S)
    (hξ : ξ = φ α ^ q ^ k₀) (ha : a * Φ ξ = evalMat (φ α) (iterMatrix q (mapMat φ A) k₀))
    (hρ : 0 < ρ) (hs0 : 0 < s) (hsr : s < r) (ht0 : 0 < t) (ht1 : t ≤ 1) (htr : t < r)
    (hsph : ∀ z ∈ sphere ξ ρ, ‖z‖ ≤ t) (hm : 0 < m)
    (hFf : ∀ z ∈ sphere ξ ρ, m ≤ ‖formVal (fun i => φ (τ i)) fs (a * Φ z) z ^ v₀‖)
    (hC1 : 1 ≤ Cb) (hB₀ : 0 ≤ B₀)
    (hA : ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(mapMat φ A i j).eval z‖ ≤ Cb)
    (haΦ : ∀ z ∈ sphere ξ ρ, ∀ i j, ‖(a * Φ z) i j‖ ≤ B₀)
    (h1B : 1 ≤ (Fintype.card ι : ℝ) * B₀) (h1C : 1 ≤ (Fintype.card ι : ℝ) * Cb)
    (hgan : ∀ k, k₀ ≤ k → DiffContOnCl ℂ
      (fun z => auxFun φ P (fun i => φ (τ i)) fs v₀ (N - v₀)
        (theta q k₀ (mapMat φ A) a Φ k z) (z ^ q ^ (k - k₀))) (ball ξ ρ))
    (hEp : ∀ k, k₀ ≤ k → ∀ z ∈ sphere ξ ρ,
      mvEvalC (z ^ q ^ (k - k₀)) (fun w : ι × ι => theta q k₀ (mapMat φ A) a Φ k z w.1 w.2)
        (MvPolynomial.map (Polynomial.mapRingHom φ)
          (truncMv K (ι × ι) p (bigSeries P (linForm τ f) N))) = 0)
    (hγ0 : 0 < γ) (hγ : 2 * γ * (q : ℝ) ^ k₀ ≤ p * Real.log (1 / t)) :
    ∀ᶠ k in atTop, ‖φ (evalAt (fun k => α ^ q ^ k)
      (fun k w => (iterMatrix q A k w.1 w.2).eval α) k (P v₀))‖
      ≤ Real.exp (-(γ * (q : ℝ) ^ k)) := by
  have hs0' : (0 : ℝ) ≤ s := hs0.le
  set E := bigSeries P (linForm τ f) N with hEdef
  -- the coefficients of the auxiliary series converge absolutely at radius `s`
  have hCS : CoeffSummable s φ E :=
    coeffSummable_bigSeries hs0' P
      (coeffSummable_linForm hs0' τ fun j => (hreal j).sumNormOn hs0' hsr) N
  -- the point `z^{q^{k-k₀}}` stays inside the disc of realization
  have hur : ∀ (k : ℕ), ∀ z ∈ sphere ξ ρ, ‖z ^ q ^ (k - k₀)‖ < r := by
    intro k z hz
    rw [norm_pow]
    calc ‖z‖ ^ q ^ (k - k₀)
        ≤ t ^ q ^ (k - k₀) := pow_le_pow_left₀ (norm_nonneg z) (hsph z hz) _
      _ ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le ht1 (Nat.one_le_pow _ _ (by omega))
      _ = t := pow_one t
      _ < r := htr
  -- the realization of the auxiliary series at each point of the circle
  have hpt : ∀ (k : ℕ) (z : ℂ), IsSumOn r
      (psEval φ (fun w : ι × ι => theta q k₀ (mapMat φ A) a Φ k z w.1 w.2) E)
      (fun u => ∑ j ∈ Finset.range N,
        mvEvalC u (fun w : ι × ι => theta q k₀ (mapMat φ A) a Φ k z w.1 w.2)
          (MvPolynomial.map (Polynomial.mapRingHom φ) (P j))
        * formVal (fun i => φ (τ i)) fs (theta q k₀ (mapMat φ A) a Φ k z) u ^ j) :=
    fun k z => isSumOn_psEval_bigSeries φ _ P (linForm τ f) N
      (isSumOn_psEval_linForm φ (theta q k₀ (mapMat φ A) a Φ k z) τ hreal)
  -- the majorant constant
  have hMaj0 : 0 ≤ auxMajorant s φ E :=
    tsum_nonneg fun n =>
      mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (pow_nonneg hs0' n)
  have hpow0 : 0 ≤ ((Fintype.card ι : ℝ) * B₀) ^ E.totalDegree :=
    pow_nonneg (le_trans zero_le_one h1B) _
  set M : ℝ := auxMajorant s φ E * ((Fintype.card ι : ℝ) * B₀) ^ E.totalDegree + 1 with hMdef
  have hM0 : 0 < M := by positivity
  set D : ℝ := ((Fintype.card ι : ℝ) * Cb) ^ E.totalDegree with hDdef
  have hD1 : 1 ≤ D := one_le_pow₀ h1C
  refine eventually_norm_evalAt_le_exp (q := q) (k₀ := k₀) (p := p) hq (A := A) (α := α) φ
    (Pv := P v₀)
    (gk := fun k z => auxFun φ P (fun i => φ (τ i)) fs v₀ (N - v₀)
      (theta q k₀ (mapMat φ A) a Φ k z) (z ^ q ^ (k - k₀)))
    (Ff := fun z => formVal (fun i => φ (τ i)) fs (a * Φ z) z ^ v₀)
    (c := fun k n z => auxCoeff φ E n
      (fun w : ι × ι => theta q k₀ (mapMat φ A) a Φ k z w.1 w.2))
    (ξ := ξ) (ρ := ρ) (t := t) (s := s) (m := m) (M := M) (D := D) (γ := γ)
    hρ hs0 ht0 hm hM0 hD1 hγ0 hγ hsph hFf hgan ?_ ?_ ?_ ?_
  · -- `hgval`: the value at the centre is the algebraic number of Step (LB)
    intro k hk
    exact auxFun_theta_center hk (Nat.sub_pos_of_lt hvN) φ hξ ha hS hmah
      (fun i => φ (τ i)) hα hL P
  · -- `hsum`
    intro k hk z _
    exact summable_norm_auxCoeff_mul_pow (hpt k z) hs0' hsr
  · -- `hmaj`
    intro k hk z hz
    refine le_trans (tsum_norm_auxCoeff_theta_le hs0' hCS (by omega) ht0.le ht1 hC1 hB₀ hA
      (hsph z hz) (haΦ z hz) h1B h1C) ?_
    exact mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) (by positivity)
  · -- `htail`
    intro k hk z hz
    have h := tail_auxFun_of_truncMv_eq_zero φ (theta q k₀ (mapMat φ A) a Φ k z) P τ hreal hP
      (hur k z hz) (hEp k hk z hz)
    rwa [formVal_theta hS hmah (fun i => φ (τ i)) a Φ (hSsph z hz)] at h

end Capstone

end AF
