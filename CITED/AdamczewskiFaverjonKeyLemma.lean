/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonStepAF
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] Lemma 2.11, assembled

plan-formalize-AF17's **WP15**, gap (4) of Stage 2.

Steps (AF), (NV), (UB) and (LB) are all formalized; this file runs them against each other.  The
result is [AF22]'s key lemma in the positive form they state it:

> *«`F(Θ_{k₀}(z),z) = 0`.»*

`AF.key_lemma_of_auxiliary` (WP10) already contains the contradiction and supplies Step (LB); what
was missing was a supplier for its hypothesis — *for every* `δ₁`, an auxiliary polynomial with the
two degree bounds, non-vanishing at infinitely many iterates, and small at all large ones, with
`c₂` independent of `δ₁,δ₂`.  WP14 gives the first three and the truncation order; WP13 gives the
fourth.  What this file adds is the wiring, plus two observations.

## The contradiction hypothesis does not depend on `v₀`

Step (UB) needs `𝔉 = F(Θ_{k₀}(z),z)^{v₀}` not to vanish identically near `ξ`, and `v₀` — the first
index with `P_{v₀} ≠ 0` — depends on the auxiliary polynomial, hence on `δ₁` and `δ₂`.  So the
hypothesis one is entitled to assume once, before `δ₁` varies, is the one at exponent one.  It
suffices: `ℂ` has no zero divisors, so `g^{v} = 0` near `ξ` forces `g = 0` near `ξ` when `v ≠ 0`,
and for `v = 0` the statement is `1 = 0` on a non-trivial filter (`AF.not_eventually_pow_eq_zero`).

## The two-field obstruction, and why the branch stays a hypothesis here

This is the finding of WP15, and it is structural.  **Step (UB)'s field and Step (LB)'s field
cannot be introduced by the same instance.**

* `AF.lemma_2_8` — the branch-existence axiom — needs `[IsAlgClosed K]`: its `Φ₀ : Matrix ι ι K`
  is a matrix of *values of algebraic functions at an algebraic point*, and asking those to lie in
  `φ(K)` is only reasonable when `K` is algebraically closed ([AF22] work over `ℚ̄` throughout).
* `AF.key_lemma_of_auxiliary` needs `[NumberField K]`: Step (LB) is Liouville's inequality, and
  the corpus's height layer is `Mathlib.NumberTheory.Height`, which is built on
  `[AdmissibleAbsValues K]` — an instance `ℚ̄` does not carry, and cannot without the direct-limit
  construction of the absolute Weil height.

No field is both.  [AF22] do not see this because their heights are absolute; here the resolution
is a **descent**: `M := A_{k₀}(α)Ψ(ξ)⁻¹` has finitely many entries, all algebraic, and `k₀` and the
branch are chosen *once*, before `δ₁` varies, so `L := K(entries of M)` is a number field fixed
for the whole argument and the entire contradiction can be run over `L`.  Nothing in Steps (AF),
(NV), (LB) is disturbed — they are simply run over `L` from the start.

That descent belongs to the assembly (gap (6)), not here: it is where `AF.theoreme_2_1`'s
arbitrary field of algebraic numbers meets `AF.lemma_2_8`'s algebraically closed one.  What this
file does is to state Lemma 2.11 over the number field, with the branch and the Mahler data as
hypotheses — the same discipline `CITED/AdamczewskiFaverjonStepUB` follows, and the reason this
file's own footprint is `std3`.

## Contents

* `AF.not_eventually_pow_eq_zero` — the contradiction hypothesis is `v₀`-free;
* **`AF.key_lemma`** — [AF22] Lemma 2.11: under the Mahler data and a branch at `ξ = φ(α)^{q^{k₀}}`,
  the linear form `F(Θ_{k₀}(z),z)` vanishes identically near `ξ`.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3.3 (Lemma 2.11).
* [AF17f] `plans/plan-formalize-AF17.html`: WP15, gap (4) of Stage 2, milestone M4.
-/

open Filter Metric Topology Height MvPolynomial

open scoped Polynomial

namespace AF

/-! ## The contradiction hypothesis is free of `v₀` -/

section Pow

/-- **The contradiction hypothesis does not depend on the auxiliary polynomial.**  Step (UB) asks
that `𝔉^{v₀}` not vanish identically near `ξ`, with `v₀` depending on `δ₁` and `δ₂`; what Lemma
2.11 assumes once, for all `δ₁`, is the case `v₀ = 1`. -/
@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem not_eventually_pow_eq_zero {ξ : ℂ} {g : ℂ → ℂ} (h : ¬ ∀ᶠ z in 𝓝 ξ, g z = 0) (v : ℕ) :
    ¬ ∀ᶠ z in 𝓝 ξ, g z ^ v = 0 := by
  intro hv
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · simp only [pow_zero] at hv
    obtain ⟨z, hz⟩ := hv.exists
    exact one_ne_zero hz
  · exact h (hv.mono fun z hz => (pow_eq_zero_iff hv0.ne').1 hz)

end Pow

/-! ## [AF22] Lemma 2.11 -/

section KeyLemma

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **[AF22] Lemma 2.11.**  *«Let `k₀` be as above.  Then `F(Θ_{k₀}(z),z) = 0`.»*

The four steps meet here.  For every `δ₁`, Step (AF) in its quantitative form
(`AF.exists_auxiliary_quantitative`) produces `δ₂`, a truncation order `p ≳ δ₁δ₂` and an auxiliary
family whose first non-zero member `P_{v₀}` has bidegree `(δ₁,δ₂)`; Step (NV) says it does not
vanish at infinitely many iterates; Step (UB) (`AF.eventually_norm_evalAt_le_exp_of_sums`) bounds
its value by `e^{-γq^k}` with `γ = p·log(1/t)/(2q^{k₀})`, which `AF.exp_neg_gamma_le` turns into
`e^{-c₂δ₁δ₂q^k}` with

  `c₂ = log(1/t) / (8·afConst(ι×ι)·q^{k₀})`

independent of `δ₁` and `δ₂`; and `AF.key_lemma_of_auxiliary` supplies Step (LB) and derives the
contradiction, `c₃ ≥ c₂δ₁` being untenable for large `δ₁`.

The branch is carried as a hypothesis rather than taken from `AF.lemma_2_8`, because the axiom
speaks over an algebraically closed field and Step (LB)'s height layer over a number field; see
the module docstring — the descent is the assembly's business. -/
@[category research solved, AMS 11 12 13 15 30 39, ref "AF22", group "af_mahler_alternative"]
theorem key_lemma {q k₀ : ℕ} (hq : 2 ≤ q) {A : Matrix ι ι K[X]} {α : K} {φ : K →+* ℂ}
    (τ : ι → K) {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ} {Φalg : Matrix ι ι Ω} {R : Subring Ω}
    {U : Set ℂ} {real : R →+* Germ (𝓟 U) ℂ} {Ψ : ℂ → Matrix ι ι ℂ} {Φ₀ M : Matrix ι ι K}
    {ξ : ℂ} {S : Set ℂ} {ρ₁ r s t Cb : ℝ}
    (hpt : Function.Injective fun k : ℕ => α ^ q ^ k)
    (hrel : IsRelationMatrix
      (relationIdeal hpt fun (n : ℕ) (w : ι × ι) => (iterMatrix q A n w.1 w.2).eval α) Φalg)
    (hb : IsAnalyticBranch φ Φalg ξ U R real Ψ Φ₀) (hball : closedBall ξ ρ₁ ⊆ U) (hρ₁ : 0 < ρ₁)
    (hsph₁ : ∀ z ∈ closedBall ξ ρ₁, ‖z‖ ≤ t)
    (hreal : ∀ j, IsSumOn r ((f j).map φ) (fs j)) (hr0 : 0 < r)
    (hS : ∀ z ∈ S, z ^ q ∈ S) (hmah : IsMahlerSolution q (mapMat φ A) fs S) (hαS : φ α ∈ S)
    (hL : formVal (fun i => φ (τ i)) fs 1 (φ α) = 0) (hSt : ∀ z : ℂ, ‖z‖ ≤ t → z ∈ S)
    (hξ : ξ = φ α ^ q ^ k₀)
    (ha : M.map φ * Ψ ξ = evalMat (φ α) (iterMatrix q (mapMat φ A) k₀))
    (hs0 : 0 < s) (hsr : s < r) (ht0 : 0 < t) (ht1 : t < 1) (htr : t < r) (hC1 : 1 ≤ Cb)
    (hA : ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(mapMat φ A i j).eval z‖ ≤ Cb)
    (h1C : 1 ≤ (Fintype.card ι : ℝ) * Cb) :
    ∀ᶠ z in 𝓝 ξ, formVal (fun i => φ (τ i)) fs (M.map φ * Ψ z) z = 0 := by
  classical
  by_contra hNV
  -- Step (LB)'s height constant, [AF22] Lemma A.1
  obtain ⟨γ, -, hγ⟩ := exists_logHeight₁_iterMatrix_eval_le hq A
    (D := Finset.univ.sup fun w : ι × ι => (A w.1 w.2).natDegree)
    (fun i j => Finset.le_sup (f := fun w : ι × ι => (A w.1 w.2).natDegree)
      (Finset.mem_univ (i, j))) α
  -- Lemma 2.11's constant `c₂`, absolute by WP14
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le two_pos hq
  have hQ : (0 : ℝ) < (q : ℝ) ^ k₀ := pow_pos hq0 k₀
  have hlog : 0 < Real.log (1 / t) := Real.log_pos (by rw [lt_div_iff₀ ht0]; linarith)
  have hBpos : 0 < afConst (ι × ι) := afConst_pos _
  have hB' : (0 : ℝ) < (afConst (ι × ι) : ℝ) := by exact_mod_cast hBpos
  have hc₂ : 0 < Real.log (1 / t) / (8 * (afConst (ι × ι) : ℝ) * (q : ℝ) ^ k₀) :=
    div_pos hlog (mul_pos (mul_pos (by norm_num) hB') hQ)
  refine key_lemma_of_auxiliary (b₁ := 1) (b₂ := 1) hq φ hγ hc₂ fun δ₁ => ?_
  -- Step (AF), quantitatively
  obtain ⟨δ₂, p, v₀, P, hδ₂, hp, hple, hv₀N, hPlt, hPv0, hPmem, hdY, hdZ, hmem⟩ :=
    exists_auxiliary_quantitative
      (relationIdeal hpt fun (n : ℕ) (w : ι × ι) => (iterMatrix q A n w.1 w.2).eval α)
      M (linForm τ f) (relationIdeal_ne_top hpt _) (totalDegree_linForm_le τ f) δ₁
  refine ⟨δ₂, P v₀, hδ₂, fun w => by simpa using hdY w, fun ν => by simpa using hdZ ν, ?_, ?_⟩
  · -- Step (NV)
    exact frequently_evalAt_ne_zero_of_mem_relComplP hpt _ (hPmem v₀) hPv0
  · -- Step (UB), with the truncation order converted into `c₂δ₁δ₂`
    exact (eventually_norm_evalAt_le_exp_of_sums hq hv₀N hPlt τ hpt hrel hb hball hρ₁ hsph₁
      hmem hreal hr0 hS hmah hαS hL hSt hξ ha hs0 hsr ht0 ht1 htr hp hC1 hA h1C
      (not_eventually_pow_eq_zero hNV v₀)).mono fun k hk =>
      hk.trans (exp_neg_gamma_le hBpos hple hlog.le hQ (by positivity))

end KeyLemma

end AF
