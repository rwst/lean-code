/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonBranchExistence
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] Step (UB), with nothing left but the contradiction hypothesis

plan-formalize-AF17's **WP13**, the first of the packages that close Stage 2.

`CITED/AdamczewskiFaverjonBranchExistence` reduced Step (UB) to two things:

* the Mahler solutions' own analytic data — that the `fᵢ` are analytic on the disc where they are
  summed, which Step (UB) needs both for `Θ_k`'s auxiliary function and for the linear form; and
* **Step (NV) on the circle**: a radius `ρ` and an `m > 0` with `m ≤ |𝔉(z)|` for `|z-ξ| = ρ`,
  where `𝔉(z) := F(a·Ψ(z), z)^{v₀}` is [AF22]'s `F(Θ_{k₀}(z),z)^{v₀}`.

Both are settled here, and neither needs a new cited input.

## The solutions are analytic because they are sums

`AF.IsSumOn r g H` says `H(u) = ∑ₙ gₙuⁿ` for `|u| < r`, which is *stronger* than analyticity but
is not phrased as it.  The bridge is Mathlib's `FormalMultilinearSeries.ofScalars`: absolute
convergence at every radius `s < r` (`AF.IsSumOn.summable_norm_mul_pow`, already proved in
`CITED/AdamczewskiFaverjonDictionary` for Mertens' theorem) bounds the radius of convergence below
by `r`, and the `HasSum` hypothesis *is* the `hasSum` field of `HasFPowerSeriesOnBall`.  This is
the same recipe `RB/MahlerAnalytic` uses for the generating function, with the bound on the
coefficients replaced by the summability the dictionary already carries.

## The circle is Step (NV), not a new idea

[AF22]'s Step (UB) argues by maximum modulus on one circle, and the constant it produces must not
depend on `k`.  That is possible because `𝔉` does not depend on `k` — `AF.formVal_theta`, the
analytic form of (2.6) — so the circle can be chosen once and for all.  It is chosen by the
principle of isolated zeros: `𝔉` is analytic at `ξ` and, *under the contradiction hypothesis of
Lemma 2.11*, not identically zero near `ξ`, so some circle about `ξ` misses its zeros and
compactness gives `m > 0`.  `AF.exists_radius_norm_pos` (WP10) is that argument; what is new here
is only that its input — analyticity of `𝔉` at `ξ` — now has a supplier, namely the branch.

The contradiction hypothesis stays a hypothesis: it is what Lemma 2.11 assumes for contradiction,
and discharging it is WP15's business, not this file's.

## What comes out

`AF.eventually_norm_evalAt_le_exp_of_sums` — Step (UB) with every hypothesis about the circle and
the analytic layer discharged, from `AF.IsSumOn` for the solutions, the Mahler relation on a set
stable under `z ↦ z^q`, the vanishing `F(1,α) = 0` of the linear form at the point, and the
contradiction hypothesis `¬ ∀ᶠ z near ξ, 𝔉(z) = 0`.

Two deliberate choices of shape.  The **radius is chosen inside the theorem**: it has to avoid the
zeros of `𝔉`, which no caller can know in advance, so what the caller supplies is a `ρ₁` on which
the disc sits inside the branch's domain and `|z| ≤ t`.  And the **exponent is explicit**,
`γ = p·log(1/t)/(2q^{k₀})` — linear in the truncation order `p`, with a constant that depends only
on `k₀` and `t`.  That is what Lemma 2.11's contradiction needs: with [AF22]'s `p ≍ δ₁δ₂` it is
their `e^{-c₂δ₁δ₂q^k}` with `c₂` absolute.

The branch itself stays a hypothesis here, as it does in `…BranchExistence`: producing it is the
cited axiom's job, and keeping it a hypothesis is what makes this file's own footprint `std3`.
The auxiliary polynomial is likewise threaded through unchanged — `hI`, that `E_p(MY,z)` is a
relation, is Step (AF)'s output and WP14's business.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3.2–§2.3.3 (Step (UB) and the circle).
* [AF17f] `plans/plan-formalize-AF17.html`: WP13, milestone M4.
-/

open Filter Metric Topology

open scoped Polynomial

namespace AF

/-! ## A sum of a power series is analytic on the disc -/

section Analytic

variable {r : ℝ} {g : PowerSeries ℂ} {H : ℂ → ℂ}

/-- The formal power series of `AF.IsSumOn`, as the object carrying Mathlib's radius of
convergence. -/
@[category API, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
noncomputable def sumSeries (g : PowerSeries ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n g

/-- **The radius of convergence is at least `r`.**  From the absolute convergence at every
`s < r` that `CITED/AdamczewskiFaverjonDictionary` proves for Mertens' theorem. -/
@[category research solved, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.le_radius (h : IsSumOn r g H) : ENNReal.ofReal r ≤ (sumSeries g).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun s hs => ?_
  refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
  have h1 : ENNReal.ofReal (s : ℝ) < ENNReal.ofReal r := by rwa [ENNReal.ofReal_coe_nnreal]
  have hsr : (s : ℝ) < r := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg s.coe_nonneg).1 h1
  refine (h.summable_norm_mul_pow s.coe_nonneg hsr).congr fun n => ?_
  rw [sumSeries, FormalMultilinearSeries.ofScalars_norm]

/-- **The sum is the sum of its power series on the whole disc.** -/
@[category research solved, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.hasFPowerSeriesOnBall (h : IsSumOn r g H) (hr : 0 < r) :
    HasFPowerSeriesOnBall H (sumSeries g) 0 (ENNReal.ofReal r) where
  r_le := h.le_radius
  r_pos := by simpa using hr
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < r := by
      rw [Metric.eball_ofReal, mem_ball, dist_zero_right] at hy
      exact hy
    have hsum := h y hy'
    rw [zero_add]
    simpa [sumSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hsum

/-- **The solutions are analytic on the disc where they are summed** — the hypothesis `hfsan` of
`AF.eventually_norm_evalAt_le_exp_of_analyticBranch`, and the input `AF.analyticAt_formVal` needs
at `ξ`. -/
@[category research solved, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.analyticOnNhd (h : IsSumOn r g H) (hr : 0 < r) :
    AnalyticOnNhd ℂ H (ball 0 r) := by
  have := (h.hasFPowerSeriesOnBall hr).analyticOnNhd
  rwa [Metric.eball_ofReal] at this

@[category research solved, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem IsSumOn.analyticAt (h : IsSumOn r g H) (hr : 0 < r) {u : ℂ} (hu : ‖u‖ < r) :
    AnalyticAt ℂ H u :=
  h.analyticOnNhd hr u (by simpa [dist_zero_right] using hu)

end Analytic

/-! ## The circle of Step (NV) -/

section Circle

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **[AF22]'s circle, from the branch.**  `𝔉(z) = F(a·Ψ(z), z)^{v₀}` is analytic at `ξ` — the
branch supplies the matrix entries, the solutions supply `fs` — so if it is not identically zero
near `ξ` the principle of isolated zeros gives a circle, of any prescribed smallness, on which it
is bounded away from zero.

The bound is *independent of `k`*, which is the whole point: by `AF.formVal_theta` (the analytic
form of (2.6)) the function `F(Θ_k(z), z^{q^{k-k₀}})` does not depend on `k` at all. -/
@[category research solved, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem exists_circle_norm_formVal_pos {φ : K →+* ℂ} {τ : ι → K} {fs : ι → ℂ → ℂ} {r : ℝ}
    {a : Matrix ι ι ℂ} {Ψ : ℂ → Matrix ι ι ℂ} {U : Set ℂ} {ξ : ℂ} {v₀ : ℕ}
    (hΨ : ∀ i j, AnalyticOnNhd ℂ (fun z => Ψ z i j) U) (hξU : ξ ∈ U) (hU : IsOpen U)
    (hfs : ∀ i, AnalyticOnNhd ℂ (fs i) (ball 0 r)) (hr : ‖ξ‖ < r)
    (hne : ¬ ∀ᶠ z in 𝓝 ξ, formVal (fun i => φ (τ i)) fs (a * Ψ z) z ^ v₀ = 0)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∃ ρ m : ℝ, 0 < ρ ∧ ρ < ρ₀ ∧ 0 < m ∧
      ∀ z ∈ sphere ξ ρ, m ≤ ‖formVal (fun i => φ (τ i)) fs (a * Ψ z) z ^ v₀‖ := by
  have hid : AnalyticAt ℂ (fun z : ℂ => z) ξ := analyticAt_id
  have hY : ∀ i j, AnalyticAt ℂ (fun z => (a * Ψ z) i j) ξ := by
    intro i j
    simp only [Matrix.mul_apply]
    exact Finset.analyticAt_fun_sum _ fun l _ =>
      analyticAt_const.mul (hΨ l j ξ (mem_of_mem_nhds (hU.mem_nhds hξU)))
  have hfsξ : ∀ i, AnalyticAt ℂ (fs i) ((fun z : ℂ => z) ξ) := fun i =>
    hfs i ξ (by simpa [dist_zero_right] using hr)
  have hF : AnalyticAt ℂ (fun z => formVal (fun i => φ (τ i)) fs (a * Ψ z) z) ξ :=
    analyticAt_formVal _ fs hid hY hfsξ
  exact exists_radius_norm_pos (hF.pow v₀) hne hρ₀

end Circle

/-! ## Step (UB) with the analytic layer discharged -/

section Consume

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Step (UB) with the analytic layer discharged, and with an explicit exponent.**

`AF.eventually_norm_evalAt_le_exp_of_analyticBranch` carries the branch and six of Step (UB)'s
hypotheses; four of the remainder are the Mahler solutions' analytic data and Step (NV) on the
circle, and both are supplied here — the first from `AF.IsSumOn`, the second from
`AF.exists_circle_norm_formVal_pos`, whose input is the contradiction hypothesis of Lemma 2.11.

Two things about the shape.  The **radius is chosen inside**: it must avoid the zeros of `𝔉`, and
that is not something a caller can know in advance; it is shrunk from a given `ρ₁` on which the
disc is inside the branch's domain and `|z| ≤ t`.  And the **exponent is explicit**,

  `γ = p·log(1/t) / (2q^{k₀})`,

which is the point of the whole estimate: `k₀` and `t` are fixed once, before the auxiliary
function's parameters vary, so `γ` is *linear in the truncation order* `p` with a constant
`c₂ = log(1/t)/(2q^{k₀})` that Lemma 2.11's contradiction may treat as absolute.  With [AF22]'s
`p ≍ δ₁δ₂` this is their `e^{-c₂δ₁δ₂q^k}`. -/
@[category research solved, AMS 11 12 13 15 30 40, ref "AF22", group "af_mahler_alternative"]
theorem eventually_norm_evalAt_le_exp_of_sums {q k₀ p v₀ N : ℕ} (hq : 2 ≤ q) (hvN : v₀ < N)
    {A : Matrix ι ι K[X]} {α : K} {P : ℕ → MvPolynomial (ι × ι) K[X]}
    (hP : ∀ j, j < v₀ → P j = 0) {φ : K →+* ℂ} (τ : ι → K) {f : ι → PowerSeries K}
    {fs : ι → ℂ → ℂ} {Φalg : Matrix ι ι Ω} {R : Subring Ω} {U : Set ℂ}
    {real : R →+* Germ (𝓟 U) ℂ} {Ψ : ℂ → Matrix ι ι ℂ} {Φ₀ M : Matrix ι ι K}
    {ξ : ℂ} {S : Set ℂ} {ρ₁ r s t Cb : ℝ}
    (hpt : Function.Injective fun k : ℕ => α ^ q ^ k)
    (hrel : IsRelationMatrix
      (relationIdeal hpt fun (n : ℕ) (w : ι × ι) => (iterMatrix q A n w.1 w.2).eval α) Φalg)
    (hb : IsAnalyticBranch φ Φalg ξ U R real Ψ Φ₀) (hball : closedBall ξ ρ₁ ⊆ U) (hρ₁ : 0 < ρ₁)
    (hsph₁ : ∀ z ∈ closedBall ξ ρ₁, ‖z‖ ≤ t)
    (hI : toRat K (ι × ι) (subMat K[X] M
        (truncMv K (ι × ι) p (bigSeries P (linForm τ f) N))) ∈
      relationIdeal hpt fun (n : ℕ) (w : ι × ι) => (iterMatrix q A n w.1 w.2).eval α)
    (hreal : ∀ j, IsSumOn r ((f j).map φ) (fs j)) (hr0 : 0 < r)
    (hS : ∀ z ∈ S, z ^ q ∈ S) (hmah : IsMahlerSolution q (mapMat φ A) fs S) (hα : φ α ∈ S)
    (hL : formVal (fun i => φ (τ i)) fs 1 (φ α) = 0) (hSt : ∀ z : ℂ, ‖z‖ ≤ t → z ∈ S)
    (hξ : ξ = φ α ^ q ^ k₀)
    (ha : M.map φ * Ψ ξ = evalMat (φ α) (iterMatrix q (mapMat φ A) k₀))
    (hs0 : 0 < s) (hsr : s < r) (ht0 : 0 < t) (ht1 : t < 1) (htr : t < r) (hp : 0 < p)
    (hC1 : 1 ≤ Cb)
    (hA : ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(mapMat φ A i j).eval z‖ ≤ Cb)
    (h1C : 1 ≤ (Fintype.card ι : ℝ) * Cb)
    (hNV : ¬ ∀ᶠ z in 𝓝 ξ, formVal (fun i => φ (τ i)) fs (M.map φ * Ψ z) z ^ v₀ = 0) :
    ∀ᶠ k in atTop, ‖φ (evalAt (fun k => α ^ q ^ k)
      (fun k w => (iterMatrix q A k w.1 w.2).eval α) k (P v₀))‖
      ≤ Real.exp (-((p : ℝ) * Real.log (1 / t) / (2 * (q : ℝ) ^ k₀) * (q : ℝ) ^ k)) := by
  classical
  have hfsan : ∀ i, AnalyticOnNhd ℂ (fs i) (ball 0 r) := fun i => (hreal i).analyticOnNhd hr0
  have hξt : ‖ξ‖ ≤ t := hsph₁ ξ (mem_closedBall_self hρ₁.le)
  obtain ⟨ρ, m, hρ0, hρlt, hm, hFf⟩ :=
    exists_circle_norm_formVal_pos (φ := φ) (τ := τ) (v₀ := v₀) hb.analytic
      hb.mem_dom hb.isOpen_dom hfsan (lt_of_le_of_lt hξt htr) hNV hρ₁
  have hsphρ : ∀ z ∈ closedBall ξ ρ, ‖z‖ ≤ t := fun z hz =>
    hsph₁ z (closedBall_subset_closedBall hρlt.le hz)
  have hlog : 0 < Real.log (1 / t) := Real.log_pos (by rw [lt_div_iff₀ ht0]; linarith)
  have hqk : (0 : ℝ) < (q : ℝ) ^ k₀ := by positivity
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  refine eventually_norm_evalAt_le_exp_of_analyticBranch hq hvN hP τ hpt hrel hb
    (subset_trans (closedBall_subset_closedBall hρlt.le) hball) hI hreal hfsan hS hmah hα hL
    (fun z hz => hSt z (hsphρ z (sphere_subset_closedBall hz))) hξ ha hρ0 hs0 hsr ht0 ht1.le htr
    hsphρ hm hFf hC1 hA h1C (by positivity) ?_
  have heq : 2 * ((p : ℝ) * Real.log (1 / t) / (2 * (q : ℝ) ^ k₀)) * (q : ℝ) ^ k₀
      = (p : ℝ) * Real.log (1 / t) := by
    field_simp
  rw [heq]

end Consume

end AF
