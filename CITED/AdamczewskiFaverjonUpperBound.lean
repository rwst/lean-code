/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Normed
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] §2.3 Step (UB): the analytic upper bound

The analytic half of plan-formalize-AF17's **WP10**, and the step its risk register singled out
(**R5**) as the one where «extracting `e^{-c₂q^kδ₁δ₂}` with constants independent of `k` is exactly
the kind of bookkeeping that blows up».

## The printed proof, and the route taken here

[AF22] prove their bound (2.14) by *identifying Taylor coefficients*.  They expand the three
functions

  `𝔈_k(z) = E(Θ_k(z), z^{q^{k-k₀}})`,  `𝔉(z) = F(Θ_{k₀}(z),z)^{v₀}`,  `ℰ_k(z) = 𝔈_k(z)𝔉(z)`

in powers of `z - ξ`, take the least `λ₀` with `a_{λ₀} ≠ 0` in the expansion of `𝔉`, read off
`e_{0,k}a_{λ₀} = ε_{λ₀,k}`, and then spend three pages (their Lemma 2.13 and its proof) bounding
`ε_{λ,k}`: Cauchy–Hadamard for the coefficients of the `G_i`, a binomial re-expansion at `ξ` with
`binom(γ,λ) ≤ γ^λ`, a separate `O(e^{γ₃q^k})` estimate for the coefficients of `Θ_k(z)`, and a
convolution at the end.

**None of that is necessary.**  The quantity to be bounded is a single *value*,
`𝔈_k(ξ) = E(A_k(α),α^{q^k})`, and the maximum modulus principle bounds a value by a supremum on a
circle:

  `|𝔈_k(ξ)| ≤ sup_{|z-ξ|=ρ} |𝔈_k(z)| = sup_{|z-ξ|=ρ} |ℰ_k(z)| / |𝔉(z)| ≤ (sup |ℰ_k|) / m`,

where `m > 0` is the minimum of `|𝔉|` on the circle — a constant, because `𝔉` does not depend on
`k` and, being analytic and not identically zero near `ξ`, has isolated zeros, so *some* circle
avoids them.  The whole of [AF22]'s Lemma 2.13, including the growth estimate for the Taylor
coefficients of `Θ_k`, collapses into a sup-norm bound on that one circle, where `‖Θ_k(z)‖` grows
only like `C^k` — not like `e^{γq^k}`, which is an artefact of the coefficient route.

What remains of the analysis is a single elementary fact: a power series with a zero of order `p`
at the origin is small at a small argument,

  `|∑_{n≥p} c_n w^n| ≤ (∑_n |c_n| s^n) · (|w|/s)^p`   for `|w| ≤ s`,

and `|w| = |z^{q^{k-k₀}}| ≤ t^{q^{k-k₀}}` with `t = |ξ| + ρ < 1`, which turns `(|w|/s)^p` into
`e^{-γq^kp}` — [AF22]'s (2.14), with the constant explicit and manifestly independent of `k`, `δ₁`
and `δ₂`.

## Contents

* `AF.exists_min_norm_on_sphere` — a continuous non-vanishing function has a positive minimum on
  a sphere;
* `AF.exists_radius_norm_pos` — an analytic function that is not identically zero near `ξ` has a
  circle around `ξ` on which it is bounded away from `0`;
* **`AF.norm_le_div_of_mul_eq_on_sphere`** — the maximum modulus step, `|g(ξ)| ≤ B/m`;
* `AF.norm_tsum_tail_le` — the tail bound for a power series of order `≥ p`;
* **`AF.norm_le_of_tail_on_sphere`** — the two combined, `|g(ξ)| ≤ (M/m)(r/s)^p`;
* `AF.pow_div_le_exp` — `(t^Q/s)^p ≤ e^{-γQp}` for `Q ≫ 1`, the conversion to [AF22]'s (2.14).

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3, Step (UB) and Lemma 2.13.
* [AF17f] `plans/plan-formalize-AF17.html`: WP10, risk R5, milestone M4 (Stage 2).
-/

open Filter Metric Topology

namespace AF

/-! ## A positive minimum on a circle -/

/-- A continuous function without zeros on a sphere is bounded away from zero there.  The sphere
of a *positive* radius in `ℂ` is non-empty and compact, so the minimum is attained. -/
@[category API, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem exists_min_norm_on_sphere {ξ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {f : ℂ → ℂ}
    (hcont : ContinuousOn f (sphere ξ ρ)) (hne : ∀ z ∈ sphere ξ ρ, f z ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ sphere ξ ρ, m ≤ ‖f z‖ := by
  have hcpt : IsCompact (sphere ξ ρ) := isCompact_sphere ξ ρ
  have hnonempty : (sphere ξ ρ).Nonempty := NormedSpace.sphere_nonempty.2 hρ.le
  obtain ⟨z₀, hz₀, hmin⟩ := hcpt.exists_isMinOn hnonempty hcont.norm
  exact ⟨‖f z₀‖, norm_pos_iff.2 (hne z₀ hz₀), fun z hz => hmin hz⟩

/-- **A circle on which an analytic function is bounded away from zero.**  This is where the
`k`-independence of the constant in Step (UB) comes from: the function `𝔉` of [AF22] does not
depend on `k`, and the principle of isolated zeros gives one circle, once and for all, on which
`|𝔉| ≥ m > 0`. -/
@[category research solved, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem exists_radius_norm_pos {ξ : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f ξ)
    (hne : ¬ ∀ᶠ z in 𝓝 ξ, f z = 0) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∃ ρ m : ℝ, 0 < ρ ∧ ρ < ρ₀ ∧ 0 < m ∧ ∀ z ∈ sphere ξ ρ, m ≤ ‖f z‖ := by
  obtain ⟨ε₁, hε₁, hana⟩ := Metric.eventually_nhds_iff.1 hf.eventually_analyticAt
  have h := hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left hne
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨ε₂, hε₂, hnz⟩ := h
  set ρ := min (min ε₁ ε₂) ρ₀ / 2 with hρdef
  have hρpos : 0 < ρ := by
    have : 0 < min (min ε₁ ε₂) ρ₀ := lt_min (lt_min hε₁ hε₂) hρ₀
    simp only [hρdef]; linarith
  have hρlt : ρ < ρ₀ := by
    have : min (min ε₁ ε₂) ρ₀ ≤ ρ₀ := min_le_right _ _
    simp only [hρdef]; linarith
  have hsub : ∀ z ∈ sphere ξ ρ, dist z ξ < ε₁ ∧ dist z ξ < ε₂ ∧ z ≠ ξ := by
    intro z hz
    have hz' : dist z ξ = ρ := by rwa [mem_sphere] at hz
    have h1 : min (min ε₁ ε₂) ρ₀ ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : min (min ε₁ ε₂) ρ₀ ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
    refine ⟨?_, ?_, ?_⟩
    · rw [hz']; simp only [hρdef]; linarith
    · rw [hz']; simp only [hρdef]; linarith
    · intro hzeq
      rw [hzeq, dist_self] at hz'
      exact absurd hz'.symm (ne_of_gt hρpos)
  have hcont : ContinuousOn f (sphere ξ ρ) := fun z hz =>
    (hana (hsub z hz).1).continuousAt.continuousWithinAt
  have hnzs : ∀ z ∈ sphere ξ ρ, f z ≠ 0 := fun z hz =>
    hnz (hsub z hz).2.1 (hsub z hz).2.2
  obtain ⟨m, hm, hmle⟩ := exists_min_norm_on_sphere hρpos hcont hnzs
  exact ⟨ρ, m, hρpos, hρlt, hm, hmle⟩

/-! ## The maximum modulus step -/

/-- **The whole of [AF22] Step (UB), structurally.**  If `g·f` is bounded by `B` on a circle and
`|f| ≥ m > 0` there, then the *value* `g(ξ)` at the centre is bounded by `B/m`.

This replaces the identification of Taylor coefficients at `ξ` in [AF22] (2.15)–(2.19): there is
no need to know the order `λ₀` of vanishing of `f` at `ξ`, nor any coefficient of `g`. -/
@[category research solved, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem norm_le_div_of_mul_eq_on_sphere {ξ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {g f h : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (ball ξ ρ)) {m B : ℝ} (hm : 0 < m)
    (hf : ∀ z ∈ sphere ξ ρ, m ≤ ‖f z‖)
    (hmul : ∀ z ∈ sphere ξ ρ, g z * f z = h z)
    (hh : ∀ z ∈ sphere ξ ρ, ‖h z‖ ≤ B) :
    ‖g ξ‖ ≤ B / m := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg ?_
    (subset_closure (mem_ball_self hρ))
  intro z hz
  rw [frontier_ball ξ (ne_of_gt hρ)] at hz
  rw [le_div_iff₀ hm]
  calc ‖g z‖ * m ≤ ‖g z‖ * ‖f z‖ := mul_le_mul_of_nonneg_left (hf z hz) (norm_nonneg _)
    _ = ‖h z‖ := by rw [← norm_mul, hmul z hz]
    _ ≤ B := hh z hz

/-! ## The tail of a power series -/

/-- **A power series with a zero of order `p` is small.**  If `∑ ‖c n‖ s^n` converges and
`‖w‖ ≤ s`, then the tail from `p` on is at most `(∑ ‖c n‖ s^n)·(‖w‖/s)^p`.

This one inequality replaces [AF22]'s Cauchy–Hadamard estimate (2.21), their re-expansion (2.26)
at `ξ` with the binomial bound (2.27), and the convolution at the end of their Lemma 2.13. -/
@[category research solved, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem norm_tsum_tail_le {c : ℕ → ℂ} {s : ℝ} (hs : 0 < s)
    (hsum : Summable fun n => ‖c n‖ * s ^ n) (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ s) :
    ‖∑' n : ℕ, c (n + p) * w ^ (n + p)‖ ≤ (∑' n : ℕ, ‖c n‖ * s ^ n) * (‖w‖ / s) ^ p := by
  set a : ℕ → ℝ := fun n => ‖c n‖ * s ^ n with ha
  set r : ℝ := ‖w‖ / s with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hs]; exact hw
  have ha0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have hshift : Summable fun n => a (n + p) := (summable_nat_add_iff p).2 hsum
  -- termwise bound
  have hterm : ∀ n : ℕ, ‖c (n + p) * w ^ (n + p)‖ ≤ a (n + p) * r ^ p := by
    intro n
    have hwp : ‖w‖ ^ (n + p) = s ^ (n + p) * r ^ (n + p) := by
      rw [hr, div_pow, mul_div_cancel₀]
      exact pow_ne_zero _ (ne_of_gt hs)
    calc ‖c (n + p) * w ^ (n + p)‖ = ‖c (n + p)‖ * ‖w‖ ^ (n + p) := by
          rw [norm_mul, norm_pow]
      _ = a (n + p) * r ^ (n + p) := by rw [hwp, ha]; ring
      _ ≤ a (n + p) * r ^ p := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 (Nat.le_add_left p n))
            (ha0 _)
  have hsumnorm : Summable fun n : ℕ => ‖c (n + p) * w ^ (n + p)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm ?_
    exact hshift.mul_right _
  calc ‖∑' n : ℕ, c (n + p) * w ^ (n + p)‖
      ≤ ∑' n : ℕ, ‖c (n + p) * w ^ (n + p)‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n : ℕ, a (n + p) * r ^ p :=
        Summable.tsum_le_tsum hterm hsumnorm (hshift.mul_right _)
    _ = (∑' n : ℕ, a (n + p)) * r ^ p := tsum_mul_right
    _ ≤ (∑' n : ℕ, a n) * r ^ p := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have := hsum.sum_add_tsum_nat_add (f := a) p
        have hnn : 0 ≤ ∑ i ∈ Finset.range p, a i :=
          Finset.sum_nonneg fun i _ => ha0 i
        linarith

/-- **[AF22]'s inequality (2.14), structurally.**  Combining the maximum modulus step with the
tail bound: if `g·f` is, on the circle of radius `ρ`, the tail from `p` of a power series
convergent at radius `s`, if `|f| ≥ m` there, and if the argument `w` stays below `r ≤ s`, then

  `|g(ξ)| ≤ (M/m)·(r/s)^p`,   `M := ∑ ‖c n‖ s^n`.

Every constant on the right is independent of everything [AF22] let vary with `k`. -/
@[category research solved, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem norm_le_of_tail_on_sphere {ξ : ℂ} {ρ s r : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (_hr0 : 0 ≤ r) (hrs : r ≤ s) {g f w : ℂ → ℂ} (hg : DiffContOnCl ℂ g (ball ξ ρ))
    {m : ℝ} (hm : 0 < m) (hf : ∀ z ∈ sphere ξ ρ, m ≤ ‖f z‖)
    {c : ℕ → ℂ} (hsum : Summable fun n => ‖c n‖ * s ^ n) {p : ℕ}
    (hw : ∀ z ∈ sphere ξ ρ, ‖w z‖ ≤ r)
    (hmul : ∀ z ∈ sphere ξ ρ, g z * f z = ∑' n : ℕ, c (n + p) * (w z) ^ (n + p)) :
    ‖g ξ‖ ≤ (∑' n : ℕ, ‖c n‖ * s ^ n) / m * (r / s) ^ p := by
  have hM0 : 0 ≤ ∑' n : ℕ, ‖c n‖ * s ^ n :=
    tsum_nonneg fun n => by positivity
  have hbd : ∀ z ∈ sphere ξ ρ, ‖(fun z => ∑' n : ℕ, c (n + p) * (w z) ^ (n + p)) z‖ ≤
      (∑' n : ℕ, ‖c n‖ * s ^ n) * (r / s) ^ p := by
    intro z hz
    refine le_trans (norm_tsum_tail_le hs hsum p (le_trans (hw z hz) hrs)) ?_
    refine mul_le_mul_of_nonneg_left ?_ hM0
    refine pow_le_pow_left₀ (by positivity) ?_ p
    gcongr
    exact hw z hz
  have := norm_le_div_of_mul_eq_on_sphere hρ hg hm hf hmul hbd
  rwa [mul_div_right_comm] at this

/-! ## From `(r/s)^p` to `e^{-γq^kp}` -/

/-- **The conversion to [AF22]'s exponential shape.**  With `r = t^Q`, `0 < t < 1`, one has
`(t^Q/s)^p ≤ e^{-γQp}` for all `Q ≫ 1` and all `p`, where `γ = log(1/t)/2` depends on neither `Q`
nor `p`.  Applied with `Q = q^{k-k₀}` this is `e^{-c₂q^kδ₁δ₂}` of (2.14). -/
@[category research solved, AMS 26, ref "AF22", group "af_mahler_alternative"]
theorem pow_div_le_exp {t s : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 < s) :
    ∀ᶠ Q : ℕ in atTop, ∀ p : ℕ,
      (t ^ Q / s) ^ p ≤ Real.exp (-(Real.log (1 / t) / 2 * (Q : ℝ) * (p : ℝ))) := by
  set γ : ℝ := Real.log (1 / t) / 2 with hγ
  have hlogt : Real.log t = -(2 * γ) := by
    rw [hγ, one_div, Real.log_inv]; ring
  have hγ0 : 0 < γ := by
    rw [hγ, one_div]
    have : 0 < Real.log t⁻¹ := by
      rw [Real.log_inv, neg_pos]
      exact Real.log_neg ht0 ht1
    linarith
  refine eventually_atTop.2 ⟨Nat.ceil (max 0 (-Real.log s / γ)), fun Q hQ p => ?_⟩
  have hQ' : -Real.log s / γ ≤ (Q : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (Nat.le_ceil _)) (by exact_mod_cast hQ)
  have hkey : -Real.log s ≤ γ * Q := by
    rw [div_le_iff₀ hγ0] at hQ'
    linarith
  have hpos : (0 : ℝ) < t ^ Q / s := by positivity
  have hlog : Real.log (t ^ Q / s) = Q * Real.log t - Real.log s := by
    rw [Real.log_div (by positivity) (ne_of_gt hs0), Real.log_pow]
  have hexp : (t ^ Q / s) ^ p = Real.exp (p * Real.log (t ^ Q / s)) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  rw [hexp, Real.exp_le_exp, hlog, hlogt]
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith [hkey, hp, hγ0.le]

end AF
