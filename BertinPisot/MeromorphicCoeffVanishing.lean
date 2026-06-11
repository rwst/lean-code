/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Lemma 5.4 — a meromorphic function with vanishing Taylor coefficients (Bertin §5.4)

Bertin's **Lemma 5.4** (*Pisot and Salem Numbers* [Ber92], §5.4):

> Let `φ` be a meromorphic function in an open set that contains the closed disk `D̄(0,1)`. Assume
> that `φ` has no pole at `0` and that the coefficients `ηₙ` of its Taylor expansion satisfy
> `ηₙ → 0`. Then `φ`, which is analytic in `D(0,1)`, has no poles on the circle `C(0,1)`.

**Layered formalization.** The two genuinely-analytic ingredients of Bertin's proof are **proved**:

* `summable_coeff_pow_of_tendsto_zero` — `ηₙ → 0` (so `(ηₙ)` is bounded) makes `∑ ηₙ zⁿ` converge
  for every `|z| < 1`: Bertin's *"the radius of convergence is at least `1`, hence `φ` is analytic in
  `D(0,1)`"*. (Geometric majorization `‖ηₙ zⁿ‖ ≤ B‖z‖ⁿ`.)
* `tendsto_one_sub_mul_norm_tsum` — the **radial estimate** that is the crux of the proof: for
  `ηₙ → 0`, `(1 − r)·‖∑ ηₙ rⁿ‖ → 0` as `r → 1⁻`. (Split the series at `n₀` with `‖ηₙ‖ < ε`: the head
  is `≤ M` and the tail is `≤ ε∑_{n≥n₀} rⁿ ≤ ε/(1−r)`, so `(1−r)‖∑ ηₙ rⁿ‖ ≤ (1−r)M + ε → ε`.)

The remaining step — *a pole of `φ` at a boundary point would force `(1 − r)φ(r)` to blow up (after a
rotation putting the pole at `z = 1`), contradicting the radial estimate* — needs Mathlib's
meromorphic pole-order asymptotics (and the WLOG rotation), which are not assembled here. So the
headline statement `lemma_5_4` (no poles on `C(0,1)`) is recorded as a `cited` axiom resting on the two
proved analytic lemmas; its full proof is in the `informal_result`
`"meromorphic-vanishing-coeff-no-boundary-pole"`.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.4, Lemma 5.4.
-/

open Filter Topology

namespace Bertin

/- The convergence half of Lemma 5.4 — "the radius of convergence of `∑ ηₙzⁿ` is at least `1`". A
power series whose coefficients are bounded (in particular tend to `0`) converges on the open unit
disk. **Proved** below by geometric majorization. -/
informal_result "bounded-coeff-radius-ge-one"
  latex "If the coefficients $\\eta_n$ of a power series $\\sum_n \\eta_n z^n$ are bounded, say $|\\eta_n|\\le B$ for all $n$ (which holds in particular when $\\eta_n\\to 0$), then its radius of convergence is at least $1$: for $|z|<1$ one has $|\\eta_n z^n|\\le B|z|^n$, and $\\sum_n B|z|^n$ converges as a geometric series, so $\\sum_n \\eta_n z^n$ converges absolutely. Hence the sum is analytic on the open disk $D(0,1)$."
  refs "Ber92"

/-- **Lemma 5.4, convergence half** (Bertin §5.4). If `ηₙ → 0` then the power series `∑ ηₙ zⁿ`
converges for every `z` in the open unit disk (`‖z‖ < 1`) — equivalently its radius of convergence is
`≥ 1`, so its sum is analytic on `D(0,1)`. **Proved** by majorizing `‖ηₙ zⁿ‖ ≤ B‖z‖ⁿ`
(`B` a bound for the convergent, hence bounded, sequence `(‖ηₙ‖)`) by a geometric series. -/
@[category research solved, AMS 30, ref "Ber92", informal_uses "bounded-coeff-radius-ge-one"]
theorem summable_coeff_pow_of_tendsto_zero (η : ℕ → ℂ) (hη : Tendsto η atTop (𝓝 0))
    (z : ℂ) (hz : ‖z‖ < 1) : Summable (fun n => η n * z ^ n) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖η n‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hη.norm).bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  apply Summable.of_norm_bounded (g := fun n => B * ‖z‖ ^ n)
  · exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left B
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hB n) (by positivity)

/- The crux of Lemma 5.4 — the radial (Abel-type) estimate. For `ηₙ → 0`, the analytic function
`f(r) = ∑ ηₙ rⁿ` on `[0,1)` satisfies `(1 − r)·‖f(r)‖ → 0` as `r → 1⁻`. This is exactly Bertin's
`lim_{r→1⁻} (1 − r)φ(r) = 0`, which contradicts the presence of a boundary pole. **Proved** below. -/
informal_result "abel-radial-decay"
  latex "Let $\\eta_n\\to 0$ and put $f(r)=\\sum_{n\\ge 0}\\eta_n r^n$ for $0\\le r<1$. Then $(1-r)\\,|f(r)|\\to 0$ as $r\\to 1^-$. Indeed, given $\\varepsilon>0$ choose $n_0$ with $|\\eta_n|<\\varepsilon$ for $n\\ge n_0$ and set $M=\\sum_{n<n_0}|\\eta_n|$. For $0<r<1$, $|f(r)|\\le \\sum_{n<n_0}|\\eta_n|r^n+\\sum_{n\\ge n_0}|\\eta_n|r^n\\le M+\\varepsilon\\sum_{n\\ge n_0}r^n\\le M+\\dfrac{\\varepsilon}{1-r}$, whence $(1-r)|f(r)|\\le (1-r)M+\\varepsilon$. Letting $r\\to 1^-$ gives $\\limsup_{r\\to 1^-}(1-r)|f(r)|\\le\\varepsilon$, and as $\\varepsilon$ is arbitrary the limit is $0$."
  refs "Ber92"

/-- **Lemma 5.4, radial estimate** (Bertin §5.4 — the heart of the proof). If `ηₙ → 0` then the radial
sum `f(r) = ∑ ηₙ rⁿ` obeys `(1 − r)·‖f(r)‖ → 0` as `r → 1⁻`. **Proved** by splitting the series at an
index `n₀` beyond which `‖ηₙ‖ < ε`: the head is bounded by a constant `M` and the tail by
`ε·∑_{n≥n₀} rⁿ ≤ ε/(1 − r)`, so `(1 − r)‖f(r)‖ ≤ (1 − r)M + ε`, which tends to `ε`; as `ε` is
arbitrary the limit is `0`. This is Bertin's `lim_{r→1⁻} (1 − r)φ(r) = 0`. -/
@[category research solved, AMS 30, ref "Ber92", informal_uses "abel-radial-decay"]
theorem tendsto_one_sub_mul_norm_tsum (η : ℕ → ℂ) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (1 - r) * ‖∑' n, η n * (r : ℂ) ^ n‖) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖η n‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hη.norm).bddAbove_range; exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hsummable : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun n => ‖η n‖ * r ^ n) := fun r hr0 hr1 =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n))
      (fun n => mul_le_mul_of_nonneg_right (hB n) (pow_nonneg hr0 n))
      ((summable_geometric_of_lt_one hr0 hr1).mul_left B)
  have hη0 : Tendsto (fun n => ‖η n‖) atTop (𝓝 0) := by simpa using hη.norm
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hη0 (ε / 2) (by positivity)
  set M : ℝ := ∑ i ∈ Finset.range n₀, ‖η i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨min (1 / 2) (ε / (2 * (M + 1))), by positivity, fun r hrlt hdist => ?_⟩
  simp only [Set.mem_Iio] at hrlt
  rw [Real.dist_eq] at hdist ⊢
  have h1r : 0 < 1 - r := by linarith
  have hr0 : 0 < r := by
    have hδ1 : |r - 1| < 1 / 2 := lt_of_lt_of_le hdist (min_le_left _ _)
    rw [abs_sub_comm, abs_of_pos h1r] at hδ1; linarith
  have hnorm_le : ‖∑' n, η n * (r : ℂ) ^ n‖ ≤ ∑' n, ‖η n‖ * r ^ n := by
    have hsm : Summable (fun n => ‖η n * (r : ℂ) ^ n‖) := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
      exact hsummable r hr0.le hrlt
    calc ‖∑' n, η n * (r : ℂ) ^ n‖ ≤ ∑' n, ‖η n * (r : ℂ) ^ n‖ := norm_tsum_le_tsum_norm hsm
      _ = ∑' n, ‖η n‖ * r ^ n := by
          congr 1; ext n; rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hsplit : ∑' n, ‖η n‖ * r ^ n
      = (∑ i ∈ Finset.range n₀, ‖η i‖ * r ^ i) + ∑' i, ‖η (i + n₀)‖ * r ^ (i + n₀) :=
    (Summable.sum_add_tsum_nat_add n₀ (hsummable r hr0.le hrlt)).symm
  have hhead : (∑ i ∈ Finset.range n₀, ‖η i‖ * r ^ i) ≤ M :=
    Finset.sum_le_sum (fun i _ => by
      calc ‖η i‖ * r ^ i ≤ ‖η i‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hr0.le hrlt.le) (norm_nonneg _)
        _ = ‖η i‖ := mul_one _)
  have htail : (∑' i, ‖η (i + n₀)‖ * r ^ (i + n₀)) ≤ (ε / 2) * (1 - r)⁻¹ := by
    have htb : ∀ i, ‖η (i + n₀)‖ * r ^ (i + n₀) ≤ (ε / 2) * r ^ i := by
      intro i
      have h1 : ‖η (i + n₀)‖ ≤ ε / 2 := by
        have := hn₀ (i + n₀) (Nat.le_add_left _ _)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this; linarith
      calc ‖η (i + n₀)‖ * r ^ (i + n₀) ≤ (ε / 2) * r ^ (i + n₀) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (ε / 2) * r ^ i * r ^ n₀ := by rw [pow_add]; ring
        _ ≤ (ε / 2) * r ^ i * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hr0.le hrlt.le) (by positivity)
        _ = (ε / 2) * r ^ i := mul_one _
    have hsk : Summable (fun i => ‖η (i + n₀)‖ * r ^ (i + n₀)) :=
      (hsummable r hr0.le hrlt).comp_injective (add_left_injective n₀)
    calc (∑' i, ‖η (i + n₀)‖ * r ^ (i + n₀)) ≤ ∑' i, (ε / 2) * r ^ i :=
          Summable.tsum_le_tsum htb hsk ((summable_geometric_of_lt_one hr0.le hrlt).mul_left _)
      _ = (ε / 2) * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hrlt]
  have hge0 : 0 ≤ (1 - r) * ‖∑' n, η n * (r : ℂ) ^ n‖ := by positivity
  rw [sub_zero, abs_of_nonneg hge0]
  have hMbound : (1 - r) * M < ε / 2 := by
    have hd2 : 1 - r < ε / (2 * (M + 1)) := by
      have := lt_of_lt_of_le hdist (min_le_right _ _)
      rwa [abs_sub_comm, abs_of_pos h1r] at this
    have hlt : (1 - r) * (2 * (M + 1)) < ε := (lt_div_iff₀ (by positivity)).mp hd2
    nlinarith [hlt, hM0, h1r]
  calc (1 - r) * ‖∑' n, η n * (r : ℂ) ^ n‖
      ≤ (1 - r) * (∑' n, ‖η n‖ * r ^ n) := mul_le_mul_of_nonneg_left hnorm_le h1r.le
    _ = (1 - r) * ((∑ i ∈ Finset.range n₀, ‖η i‖ * r ^ i)
          + ∑' i, ‖η (i + n₀)‖ * r ^ (i + n₀)) := by rw [hsplit]
    _ ≤ (1 - r) * (M + (ε / 2) * (1 - r)⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith [hhead, htail]) h1r.le
    _ = (1 - r) * M + ε / 2 := by field_simp
    _ < ε / 2 + ε / 2 := by linarith [hMbound]
    _ = ε := by ring

/- Bertin's full proof of Lemma 5.4, recorded. The genuine input beyond the two proved analytic
lemmas is the meromorphic pole-order asymptotics (a boundary pole forces radial blow-up) together with
the rotation reducing a general boundary pole to one at `z = 1`. -/
informal_result "meromorphic-vanishing-coeff-no-boundary-pole"
  latex "Let $\\varphi$ be meromorphic in an open set containing $\\overline{D}(0,1)$, with no pole at $0$ and Taylor coefficients $\\eta_n\\to 0$. The radius of convergence $R$ of $\\sum_n \\eta_n z^n$ is $\\ge 1$ (bounded coefficients), so $\\varphi$ is analytic in $D(0,1)$ and equals the series there. Suppose for contradiction that $\\varphi$ has a pole on $C(0,1)$; after a rotation assume it is at $z=1$. By the radial estimate, $(1-r)\\varphi(r)=(1-r)\\sum_n\\eta_n r^n\\to 0$ as $r\\to 1^-$. But a pole of order $k\\ge 1$ at $1$ makes $(z-1)^k\\varphi(z)$ analytic and non-zero at $1$, so $|(1-r)\\varphi(r)|=|(1-r)^{1-k}|\\,|(r-1)^k\\varphi(r)|$ stays bounded away from $0$ (for $k=1$) or tends to $+\\infty$ (for $k\\ge 2$) as $r\\to 1^-$ — contradicting $(1-r)\\varphi(r)\\to 0$. Hence $\\varphi$ has no pole on $C(0,1)$ (equivalently $R>1$)."
  refs "Ber92"

/-- **Lemma 5.4** (Bertin §5.4). Let `φ` be meromorphic on (a neighbourhood of) the closed unit disk,
with **no pole at `0`** and Taylor coefficients `ηₙ = φ⁽ⁿ⁾(0)/n! → 0`. Then `φ` has **no poles on the
unit circle** `C(0,1)`: it is analytic at every `z` with `‖z‖ = 1`.

By `summable_coeff_pow_of_tendsto_zero` the series `∑ ηₙ zⁿ` converges on `D(0,1)` (radius `≥ 1`), so
`φ` is analytic there; and `tendsto_one_sub_mul_norm_tsum` gives the radial decay
`(1 − r)‖∑ ηₙ rⁿ‖ → 0`. A boundary pole (rotated to `z = 1`) would make `(1 − r)φ(r)` blow up,
contradicting that decay. This last step needs Mathlib's meromorphic pole-order asymptotics and the
rotation, not assembled here, so the statement is recorded as a `cited` axiom resting on the two proved
analytic lemmas; the full proof is in `"meromorphic-vanishing-coeff-no-boundary-pole"`. -/
@[category research solved, AMS 30, ref "Ber92",
  formal_uses summable_coeff_pow_of_tendsto_zero tendsto_one_sub_mul_norm_tsum,
  informal_uses "meromorphic-vanishing-coeff-no-boundary-pole"]
axiom lemma_5_4 (φ : ℂ → ℂ) (hmero : MeromorphicOn φ (Metric.closedBall 0 1))
    (h0 : AnalyticAt ℂ φ 0)
    (hlim : Tendsto (fun n => iteratedDeriv n φ 0 / (n.factorial : ℂ)) atTop (𝓝 0)) :
    ∀ z ∈ Metric.sphere (0 : ℂ) 1, AnalyticAt ℂ φ z

end Bertin
